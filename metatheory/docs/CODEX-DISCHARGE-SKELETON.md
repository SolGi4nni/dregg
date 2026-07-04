# Codex — the #9 discharge induction skeleton (2026-06-25)

The formal structure for deriving the whole-chain binding (not assuming it). THREE soundness layers, cleanly separated:
1. EngineSound (per-node FRI/STARK) = ASSUMED crypto floor — provides ONLY local statement soundness (leaf_sound, combine_sound), NOT GenuineSeg/whole-history.
2. The induction (subtree_binding: EngineSound -> GenuineSeg) = DERIVED — the ordered-chain binding (THE discharge).
3. PoseidonSegBinding (Poseidon2 collision-resistance) = ASSUMED crypto floor — semantic uniqueness of the ordered digest (the SAME-endpoint case).

I’ll ground this in the repo’s durable record before answering, since this is exactly the kind of soundness claim the project notes warn against reconstructing from memory alone. I’ll read the continuity docs first, then the specific Lean/proof artifacts around the accumulator theorem.
exec
/bin/zsh -lc "pwd && rg --files -g 'REORIENT.md' -g 'HORIZONLOG.md' -g '*memory*' -g 'CLAIMS.md' -g 'Dregg2.lean' -g '*Claims*.lean' -g '*Sound*.lean' -g '*Segment*.lean' -g '*Accumulator*.lean'" in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
/Users/ember/dev/breadstuffs
starbridge-v2/src/agent_memory.rs
REORIENT.md
HORIZONLOG.md
metatheory/Dregg2.lean
metatheory/Metatheory/SettlementSoundness.lean
site-old-scavenge/src/_includes/studio/runtime-in-memory.js
metatheory/CLAIMS.md
metatheory/Dregg2/Spike/TransferAirSoundness.lean
deos-hermes/tests/agent_memory_as_umem.rs
metatheory/Dregg2/Circuit/Emit/EffectVmEmitTransferSound.lean
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean
metatheory/Dregg2/Circuit/CircuitSoundness.lean
metatheory/Dregg2/Circuit/SettlementSoundness.lean
metatheory/Dregg2/Circuit/CircuitSoundnessAssembled.lean
metatheory/Dregg2/Exec/CapTPHandoffSound.lean
metatheory/Dregg2/Claims.lean

exec
/bin/zsh -lc "sed -n '1,240p' REORIENT.md" in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
# REORIENT — read this first after any context loss

*(maintained for session continuity; update at every major landing. Last: 2026-06-21 — THE TWO-TRACK EPOCH: floor (soundness, ~14/30 light-client-forced + the rest closeable/irreducible) + house (capacity: reactive effect SHIPPED, 4 more building). Goal = "safely live within dregg" on two tracks.)*

> ⚑ POST-COMPACT: read `HORIZONLOG.md` → the "POST-COMPACT ORIENTATION (2026-06-21)" entry FIRST — it carries the
> live 8-agent swarm roster, the held-welds-to-bank, the Track-1 queue (the revokeCapability #1 route-FORGE is the
> top soundness pickup), the 3 irreducible floors, and the Track-2 capacity status. `docs/SAFELY-LIVE-CHECKLIST.md`
> is the goal's mechanical audit. Two tracks, SAME bar: VERIFIED-working (passing forge-rejection / mutation-red apex
> / end-to-end test), never named-or-designed. A green only counts if it reds when the thing it guards breaks.

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
v3Registry 26→34 + an EmitEvent axiom-hole fix).

⚑ THE CUTOVER IS PARKED at step-1 by EMBER DECISION (2026-06-13): **"finish cap-crown #103 first."**
Step 2 (the live-path rewrite, ~70 call-sites + executor PI reconstruction) is NOT started. Full
v1-deletion is HARD-GATED on 2 residue effects: **RevokeCapability (sel 24)** — needs its in-circuit
cap-root advance from the cap-crown reshape (#103); **Custom (sel 8)** — needs a new accumulator
constraint kind the per-row IR lacks. Sequence: cap-crown #103 → unblocks RevokeCapability → ONE
clean cutover deletes v1 entirely (no fallback tail). A read-only cap-crown state-mapping agent is
running (A-F stages + the RevokeCapability critical path); plan/launch the cap-crown completion off it.
The parked cutover checkpoint is `a0d0d45d3`; ROTATION-CUTOVER.md §2c/§3 has the precise remaining steps.


exec
/bin/zsh -lc "sed -n '1,240p' HORIZONLOG.md" in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
# HORIZONLOG — the named-follow-up burn-down

*(Standing rule: when a lane/commit NAMES a follow-up, residue, or closure lane,
it gets a line HERE in the same breath — "named in a report" is not durable.
Each line: what · where it was named · the closure shape. Remove lines when
closed (git history is the record). This is a burn-down list, not a parking
lot: per WE-DO-NOT-NAME-WE-SHIP, anything that sits here across many sessions
should be either scheduled or explicitly demoted to the Research tier with a
reason.)*

## NOW-STATE (late-2026-06-25 cluster — lanes that landed AFTER the entries below, recorded here for durability)
- ANDROID cap-graph COMPLETED: the whole ambient-AOSP surface reforged as cap-bounded gates — intent
  (`intentgate.rs` `76165ec4`, transport leg `63dfdca3`), content-providers (`contentgate.rs` `7451f6a6`),
  system-services→organs (`organgate.rs` `af7d1c00`), install=cap-gated-birth (`appfactory.rs` `63dfdca3`).
  The permission model is REAL: visible cap-badges (`e826335e`), a dangerous-perm hand-over mints a genuine
  `Effect::GrantCapability` over the verified executor (`542f640d`, `turn/src/action.rs:962`), and the confined
  app's `checkSelfPermission` is interposed over the cap-badge set + DENIED in-runtime on a dim cap (`d9a2ffc8`).
  SystemUI cap-chrome rendered ON THE GLASS for a focused AndroidCell window — status bar + quick-settings shade +
  hand-over sheet, a tap drives a REAL `Effect::GrantCapability`, the badge flips lit (`d361cfc5`/`76b43970`).
  NAMED TAIL: a clean painted gpui frame on-device still needs real arm64 Vulkan hw (emulator GPU wall, not a bug).
- SERVICE CELLS: three citizens on `invoke()` — kvstore (`0d1a3f8b`), nameservice (`21afb73c`), escrow-market
  (`d124ad8a`, first four-organ non-trivial). Non-degrading: identical canonical program ⇒ organ teeth re-enforce
  on every desugared turn, cap-gate bites at front-door AND executor. No `Effect::Invoke`, no kernel change.
- MATCHING faithfulness FULLY CLOSED both deployed paths: derivative determinizer (`Determinize.lean`) + legacy
  Thompson (`c14aa325`, `Thompson.lean` sorry-free); inter/neg route through the determinizer (`compiler.rs:692`).
- UMEM: the whole-image FOLD CHIP landed in-circuit (`74565bd5`, `dregg-circuit::whole_image_fold` discharges
  fc679a5f's `hpin`). NAMED TAIL: the universal-map rotation flip (umem becomes the prover — `umem_witness_enabled`
  still defaults FALSE, `turn/src/executor/mod.rs:815`) → Stage B heap-write effect.
- FIRMAMENT: the semihost interactive cockpit now runs the REAL verified `DreggEngine` (live-repaint-on-turn,
  `251692b7`) — closes `SEL4-INTERACTIVE-COCKPIT.md §3.5`. NAMED TAIL: §3.6 step 4, the executor-PD's bare-metal
  Lean-ELF runtime link (the real-seL4 WALL; gated on Microkit SDK on PATH, not a semihost blocker).
- MULTIPLAYER: a real two-instance session — two co-inhabitants sync via the membrane's field-granular stitch
  (`8159d322`). SURFACES: the Spotter + menus now reach EVERY session surface, each landing mold-ready (`f7e6765a`).

## ⚑ THE UMEM ROTATION-FLIP BURN-DOWN (the 5-rank plan, named in `6ec89500` + `UNIVERSAL-MAP-ROTATION.md`)
*(The flip = make the universal-memory prover LOAD-BEARING on the wire: `umem_witness_enabled`
still defaults FALSE (`turn/src/executor/mod.rs:815`), v1 is still the only prover. Each rank
carries its closure shape. Pure-Lean ranks are VK-risk-free and can soak before any flag-day.)*
- RANK 1 — the umem ADDRESS/VALUE CODEC ADAPTERS (the gating long pole, VK-RISK-FREE). ✅ DONE
  (`metatheory/Dregg2/Crypto/UMemCodec.lean`, 17 theorems `#assert_axioms`-clean): the REAL
  structured carriers replacing `effect_vm_umem_real_turn.rs`'s per-proof "dense injective
  relabeling" — `uaddrEnc=hash[domainTag d, coll, key]` + `uaddrEnc_injective` (the structured
  address codec, faithful under CR + injective tag); `capLeafOf=hash[holder,target,rights,op]` (=
  the deployed `siteCapEdgeLeaf` by `rfl`) + value codec WHERE/WHAT split + `capRoot_injective`
  (the cap boundary root binds its 4-felt cap cells, no new combinatorics); the MMR
  boundary-derivation analogue for the index domain (`index_boundary_root_{derived,bound,
  from_memcheck}`, riding `mroot_injective` + `memcheck_pins_final`). All on the SAME named
  `Poseidon2SpongeCR` floor (no narrower bit-count), non-vacuity both polarities on `refSponge`.
- RANK 2 — the `absent` map-op realization (`descriptor_ir2.rs:62-68`, declared in IR / refused by
  assembly today; the nullifier-insert lane needs it regardless). CLOSURE: assembly + a refuse-test.
- RANK 3 — the 3-verb EXECUTOR (the runtime long pole): `RecordKernelState` → the ONE universal
  map (`VerbCompression.lean:87-89` "rides THE ONE ROTATION"; `turn/`+`cell/`-shaped). The 3-verb
  circuit descriptors GATE on this — circuit semantics must not run ahead of runtime semantics.
- RANK 4 — the per-domain WHOLE-IMAGE fold-chip generalization: the cap/nullifier/index boundary
  folds reconciled against the universal boundary table (the `6ec89500` whole-image chip is the
  heap-plane proof-of-shape; extend to the other domains via the Rank-1 codecs). Still
  `umem_witness_enabled`-gated.
- RANK 5 — the LAYOUT FLAG-DAY (one motion, AFTER GATE 0 = IR-v2 size GREEN): registers 8→16 +
  `FactoryDescriptor.fields` · `heap_root`+`iroot` commitment limbs (`CommitBindsIndex`/
  `CommitBindsMMR`) · PI v3 · RESERVED/selector-block death · universal-memory table assembly →
  ONE descriptor regen → differential gauntlets (cell≡circuit per map · per-effect AGREE · the
  memory-argument adversarial suite, `UniversalMemory.lean` §6 as the templates) → VK/commitment
  bump → succession drill → persvati gauntlet → deploy when ember says deploy.

## web-deos DEEPENED: a SERVICE CELL invoked node-less in the browser (2026-06-25)
- WHAT: the web `ViewNode` path gained a fourth, richer surface — a KV-store SERVICE CELL driven entirely in a
  browser tab (`wasm/src/bindings_card.rs::KvStoreWorld` + `deos-view/src/web.rs::render_kvstore_live_document` +
  `deos-view/examples/web_render_card.rs` bakes `kvstore.html` + a gallery tile). Unlike counter/inspector/tally
  (bare `SetField` on a cell's own slots), the store publishes a typed `InterfaceDescriptor` (put·delete·get);
  clicking put/del ROUTES through `route_method` (the verified `dregg_dfa` router) BEFORE desugaring to the
  version-bump + register `SetField`s — no `Effect::Invoke`. `runtime::app_programs::kvstore_program` (Monotonic on
  the version slot, mirrors `starbridge_kvstore` which can't be a wasm dep) is installed on the store cell; the
  caller is a separate agent granted a reach cap. `tryRollback` proves the Monotonic guarantee BITES in-tab (a real
  executor refusal: "field[0] decreased"); `tryGet` proves get is the named Serviced OFE seam. VERIFIED by running:
  wasm-pack build + served + `scripts/drive-deos-kvstore.mjs` headless-Chrome CDP driver — all asserts pass
  (put 20→21, del 10→0, version 4→5→6, rollback refused, get named; receipts 5→6→7). Commit `f956a9514`.
- NAMED TAILS (closure shape): (a) `put`'s value is currently a single-arg "bump the register" (the ViewNode
  `Button` carries one `arg`); a richer put-with-explicit-value needs a text `Input`-bound value affordance (the web
  renderer already renders `Input`, just not yet wired to fire a 2-arg method). (b) `get`'s Serviced answer is
  NAMED-and-refused, not yet SERVED — closure = surface the OFE cross-cell-read result as a (read-only) bound row
  when the serviced-answer carrier (S2) lands. (c) the in-tab service-cell is wasm-mirrored (program VALUE +
  invoke() routing core re-expressed), like the subscription/governance app programs; if `starbridge_kvstore` ever
  sheds its axum/tokio deps it could be a direct wasm dep instead.

## deos-desktop document-collaboration UX DEEPENED: drivable branch→diverge→stitch→conflict→resolve + the umem boundary surfaced (2026-06-25)
- WHAT: the deos_desktop document-language surface (`starbridge-v2/src/deos_desktop/mod.rs`) is now drivable end to end:
  (a) a LIVE co-author draft editor — a second `InputState` (`branch_inputs`/`branch_subs`) so the co-author TYPES the
  divergence by hand (`set_branch_text` as `author^1`), not only the canned button; (b) the document's UMEM-HEAP BOUNDARY
  (`DocHeapCell::from_graph(...).commitment()`) is read out and watched MOVE through edit/branch/stitch/resolve — the
  conflict's boundary is labelled "binds both alternatives" (the anti-forge tooth surfaced); (c) richer ConflictView —
  alternatives attributed you-vs-co-author (`author_label`), a RESOLVED receipt row (the resolution patch id = the turn's
  receipt, `last_resolution`). New bake `--render-doc-collab` drives the whole flow on one large editor window + asserts the
  boundary moves, the conflict is held off-heap, and resolve publishes (height grows, receipt lands, boundary moves).
- NAMED TAILS (closure shape): (a) CLOSED 2026-06-25 (`83352a35d`) — `edit_doc` now persists the document INTO the cell's
  umem-heap (`commit_doc_to_umem_heap` → `DocHeapCell::from_graph_with_text` → `World::set_cell_heap`, an out-of-band
  `set_heap`/`reseal_heap_root`, no kernel effect), so the cell's committed `heap_root` IS the document commitment (boundary ==
  commitment, surfaced via `live_doc_boundary`); prose re-seeds on reopen from `dregg_doc::COLL_TEXT` (the one-way BLAKE3
  projection stays recoverable). Conflict/stitch/resolve ride the same heap. RESIDUAL (durable-image seam): `set_cell_heap`
  fail-fasts on a durable image whose doc cell a committed turn already touched (the genesis-mirror-after-turn guard) — the
  demo world is ephemeral so it passes, but a DURABLE runtime heap write awaits an ordered heap effect (no `Effect::SetHeap`
  exists; mirrors the `set_cell_program` runtime-vs-genesis tension). (b) the live branch editor re-seeds only on creation; a
  programmatic diverge after the widget exists needs a `branch_resync` (mirror of `doc_resync`) — closure = add it if a flow
  edits the branch out-of-band while its editor is open.


## umem Stage A LANDED: the per-cell heap is a first-class umem (additive); live producer is the named seam (2026-06-25)
- WHAT: `UMEM-PRIMITIVE.md §2/§7` Stage A — the per-cell heap (`CellState.heap_map`) projected as a
  first-class umem collection, additive on the recursion-gated bridge witness, the keystone's first
  cross-cell consumer. Shipped in `turn/`:
  - `UKey::Heap { cell, collection, key }` (heap domain) + `project_cell` emits one `UVal::Bytes32`
    per `heap_map` entry. `heap_root` is now the DERIVED commitment of the `Heap` plane (NOT
    separately projected — exactly the established `fields_root`/`Field` treatment; the sorted-
    Poseidon2 root over the projected cells EQUALS `cell.state.heap_root` by `boundary_root_derived`).
  - `JournalEntry::SetHeap` + `record_set_heap` + rollback + `touches_of_entry` → genuine `umem_op`
    rows on a heap write (the bridge re-reads a journaled heap write as its Blum WRITE).
  - `open_heap_against_committed` — the cross-cell read: binds another cell's committed `heap_root`
    as an init image and opens a key; a tampered preimage derives a different root → the binding
    REFUSES (the Rust shadow of the keystone `boundary_init_root_bound`).
  - reify_seam RESIDUAL #1 CLOSED: `reify_cell` rebuilds `heap_map` from the `Heap` plane + re-derives
    `heap_root`; a non-empty heap now round-trips. Tests: `turn/src/umem.rs` `heap_stage_a_tests` (3) +
    `turn/tests/umem_time_travel.rs::reify_round_trips_non_empty_heap`. All umem suites green.
- NAMED SEAM (closure lane, not parking): no live `Effect` journals a heap write yet — today the heap
  is mutated out-of-band (`CellState::set_heap`, e.g. `deos-js`/`dregg-doc`). The producer is a
  heap-writing effect = a NEW effect/circuit surface (Stage B+, with `UmemRef`/checkpoint), deliberately
  NOT built here. `JournalEntry::SetHeap` + `record_set_heap` carry `#[allow(dead_code)]` until it lands.
  Named in `turn/src/journal.rs` (the `SetHeap` NAMED SEAM doc).

## DERIVATIVE-MATCHING faithfulness: Stages 0/1/3 LANDED kernel-clean over dregg's Pred; Stage 4 language-half done, table-equality unblocked (2026-06-25)
- WHAT: a Brzozowski/Antimirov symbolic-derivative matcher built over dregg's OWN `Pred` algebra
  (`PredRE` = ERE≤'s `RE` minus the four lookarounds, `Pred` leaf), in dregg's own Lean — ERE≤ +
  ITP'25 `finiteness-derivatives` read as proof BLUEPRINTS only (no import; cloned to `~/dev/_research/`).
  All `#assert_axioms`-clean (`{propext, Classical.choice, Quot.sound}`), zero `sorry`. Modules:
  `metatheory/Dregg2/Crypto/Deriv/{Core,Correctness,Similarity,Determinize,Combinatorics,TTerm,Permute,
  SymbolicDerivative,Pieces,Finite,Monotone,Finiteness}.lean` (wired into `Dregg2.lean`).
  - Stage 0 (`Core`): `der`/`null`/`derives` + denotational `Matches` (starMetric termination) + non-vacuity `#guard`s (incl. the new `neg` deny-filter).
  - Stage 1 (`Correctness`): `correctness : derives w R = true ↔ Matches w R` — the "weeks in the design" middle theorem (seven per-ctor lemmas + the Kleene-star tower).
  - Stage 3 (`Finiteness.der_finite`): **Brzozowski FINITENESS** `∃ xs, ∀ {n}, steps r n ⊆[≅] xs` — the whole symbolic-derivative state space fits up to similarity in the fixed finite `⊕(pieces r)`. The full ITP'25 tower (TTerm/symbolic-derivative/pieces/neSubsets/Permute-nodup/`step_to_pieces`/`pieces_equiv'`) ported over `Pred`. `sim_sound` (`Similarity`) proves `≅` is language-sound so the finite ≅-quotient = finite recognized languages. (`DecidableEq PredRE` is CLASSICAL — kept clean.) The design rated this "months, not days"; it landed.
  - Stage 4 (`Determinize`): the derivative automaton presented AS the in-circuit `Dfa.lean` `DfaAccepts` run — `derivativeDfa_correct/_matches` (accepts ↔ `derives` = `Matches`); the in-circuit `Dfa.lean` cascade is IMPORTED, untouched.
- NAMED FOLLOW-UPS (closure lanes, not parking):
  - **Stage 4 table faithfulness — SUBSTANTIVELY CLOSED** (`Deriv/TableDfa.lean`): `tableDfa_faithful` proves ANY flat-table DFA (model of `compiler.rs::Dfa::matches`) whose `accepts` agrees with `derives` on every word decides EXACTLY `Matches R` — the compiled table's boolean meaning is now a THEOREM, construction-agnostic (the table-opaque regime the design says suffices). `tableRun_dfaAccepts` bridges the deployed AIR's relation-δ to a table FUNCTION (closes `DfaAcceptanceAir` GAP-A). `derivativeMatcher_faithful` + `der_finite` give the faithful table EXISTS + is FINITE. RESIDUAL (optional, narrow): a Lean MODEL of `compiler.rs::determinize`'s powerset construction proving ITS `accepts` agrees with `derives` — only needed to name the DEPLOYED table specifically; any agreeing table is already trusted by `tableDfa_faithful`. Named in `Deriv/{TableDfa,Determinize}.lean`.
  - **Stage 5 stateful `(old,new)` carrier** (policy/caveat trace) — gated open research; the binding soundness constraint is the right-skew (derivatives decide LANGUAGE; `FlowRefine.decideRefines` decides reactive SIMULATION; never conflate). Named in `docs/deos/DERIVATIVE-MATCHING-DESIGN.md §5.3`.

## `invoke()` + the SERVICE EXPLORER LANDED end-to-end in deos; serviced-answer + registry-wire are the named follow-ups (2026-06-25)
- WHAT: cells-as-service-objects INVOCATION shipped at the userspace layer (NO kernel `Effect::Invoke`, Effect enum
  untouched), end-to-end into the live deos cockpit:
  1. `dregg_app_framework::invoke` (`app-framework/src/invoke.rs`) — the front door: resolves a method against a cell's
     interface (derive-from-program OR an `InterfaceRegistry`), routes via the verified DFA `route_method`, cap-gates on
     `MethodSig::auth_required` (`InvokeAuthority` tiers), refuses Serviced methods as the named seam, desugars to an
     ordinary method-targeting `Action` + fires through the executor. 5 unit tests.
  2. `starbridge_v2::service_explorer::ServiceExplorer` (`starbridge-v2/src/service_explorer.rs`) — the deos-interior
     Postman-like model (gpui-free, 6 tests): discover→list→invoke off the live `World`, re-inspecting the post-state.
     New executor-entry `World::wrap_action_turn` (preserves the action's method symbol).
  3. The `🛰 SERVICES` cockpit tab (`cockpit/{mod,construct,nav,panels_workspace,panels_moldable}.rs`) — method list +
     args presets + underlying-effect picker + invoke buttons + outcome banner; `Tab::ServiceExplorer` registered, nav
     capture/restore, `CycleServiceFocus`. The `service` anchor boots publishing {ping,set_status,tick}. Verified by a
     headless render of the live element tree (the published methods + invoke affordances paint). 713 lib tests green.
- NAMED FOLLOW-UPS (closure lanes, not parking):
  - SERVICED-ANSWER CARRIER — a `Serviced` method's answer rides the OFE cross-cell-read (`crossCellRead_refines_observedField`);
    today both `invoke()` and the explorer REFUSE it in-band (the seam). The receipt shape that witnesses the serviced
    reads + produced result (so a light client re-checks a service answer) is the build. (Named in `cell/src/interface.rs` S2 list.)
  - REGISTRY WIRE-THROUGH — the cockpit explorer resolves derive-from-program only (`invoke`); the richer
    `InterfaceRegistry`/`build_with_descriptor` + `invoke_with_descriptor` (Signature-gated / Serviced methods) are built
    and tested but not yet surfaced in the cockpit (no UI to register a descriptor). Wire a registry panel.
  - METHOD CLEARTEXT NAMES — a `MethodSig` carries only the symbol; the explorer shows short-hex. A name-registry (or
    carrying the cleartext alongside the descriptor) would show {ping,…} instead of {53ee61…}. Cosmetic, userspace.
  - ARGS ENTRY — the args field uses preset buttons (the cockpit's text idiom); a live text input is the richer UX.

## mid-forest `yield_point` LANDED; promise-pipelining lift of the live yield is the named follow-up (2026-06-25)
- WHAT: the continuations lane's "THE SEAM — mid-forest checkpoint" is CLOSED. `TurnExecutor::maybe_umem_yield`
  (called from `executor/execute_tree.rs` after each effect appends to the journal) snapshots
  `project_executor_state(ledger)` LIVE between two effects when armed via `set_umem_yield_at`; the snapshot lands in
  `last_umem_yield`. `Continuation::from_yield` BINDS the live boundary to the committed Blum trace (admits only a
  snapshot equal to a trace-prefix fold; refuses foreign). Lean twin `Dregg2/Exec/Continuation.lean`:
  `midturn_split`/`yield_resume_sound`/`resumed_tail_disciplined`, 7 keystones `#assert_all_clean`. Tests:
  `turn/tests/mid_forest_yield_point.rs` (4 green). Banner in `turn/src/continuation.rs` rewritten LANDED + the
  receipt/atomicity boundary named precisely (yield is observation-only; commit/rollback stays whole-turn).
- THE NAMED INVARIANT (not a hole, by design): the captured mid-forest boundary is a REPRESENTATION of mid-flight
  state, NOT independently committable — a turn is all-or-nothing, so if the remaining forest would fail, the
  prefix boundary is a state the chain never commits. `midturn_split` proves only the STATE-fold half.
- CLOSURE SHAPE (the forward lane): wire the live yield into the partial-turn/promise EFFECT vocabulary
  (project-partial-turn-promises) — a `yield_point` that RETURNS a `Continuation` to a promise pipe (CapTP),
  resumed when the dependency lands, so promise pipelining inherits light-client unfoolability. The state half is
  proven; the lift is WIRE (ConditionalBatch ↔ the live yield), not new foundation.

## Touch UI (graphideOS shape) LANDED as a bake; the live-on-Android frame is the named follow-up (2026-06-25)
The touch-adapted deos UI shipped: `starbridge-v2/src/touch.rs` (`TouchShell`) — the bottom-bar five-mode
switch (Inhabit/Author/Dev/Inspect/Operate via gpui-component `TabBar`), the tappable cell garden (reusing
`wonder::WonderRoom` over the live `World`), and long-press → a bottom face-sheet (the reflected `Inspectable`
faces + the lit ACTUATE affordance firing a real `wonder::DragValue` predict-then-commit turn). Distinct from
the desktop cockpit; reuses the gpui-free view model. Baked headless via `--render-touch` (main.rs,
`render_touch_headless`; phone 390x844 default, `--render-mode <name>` selects a clean mode surface). NAMED
FOLLOW-UP (per MOBILE-DEOS.md §7 ⛔ STEP-2 wall, NOT this pass's scope): the SAME `TouchShell` painting a real
frame ON an Android device needs the gpui `PlatformAndroid` backend (window from `ANativeWindow`, an android
event/IME pump, lifecycle) — a gpui-fork change. CLOSURE SHAPE: lift upstream `gpui-mobile` + drive `TouchShell`
through it (the bake proves the element tree; the device frame waits on the backend). Also: touch gestures are
currently tap (`on_click`) + an explicit "⋯ faces" affordance standing in for long-press (gpui has no native
long-press); a real press-and-hold recognizer is the gesture-layer follow-up.

## reify_seam CLOSED at the value level; Lean uproj-injectivity is the named follow-up (2026-06-25)
`reify_cell`/`reify_ledger`/`reify_executor_state` landed (`turn/src/umem.rs`) — the byte-identical inverse of
`project_cell`/`project_ledger`, re-deriving the dropped commitments (`fields_root` from the `Field{slot≥16}`
plane; the ledger Merkle root lazily on `root()`; leaf/cap caches) rather than storing them. The round-trip law
`reify_ledger(project_ledger(L)) == L` is PROVEN over the faithful class (`turn/tests/umem_time_travel.rs`:
`reify_ledger_round_trips_a_populated_ledger`, `reify_restores_a_live_ledger_to_height_h`). HONEST RESIDUAL
(named precisely by `ReifyError` + two refusal tests `reify_refuses_heap_not_projected` /
`reify_refuses_cap_revocation_gap`): FOUR value planes `project_cell` does NOT yet carry — heap preimage
(`heap_map`; only the derived `heap_root` is projected), `Cell.interfaces`, `CapabilitySet.tombstones`, and the
post-revoke `next_slot` gap. CLOSURE SHAPE: extend the projection address space (`UKey`) with heap/interface/
tombstone planes (Rust + the Lean `UniversalBridge.UKey` twin + circuit domain codes, in lockstep), which makes
the faithful class total. NAMED LEAN FOLLOW-UP: `uproj` injectivity over the account-membership-gated class
(`metatheory/Dregg2/Exec/UniversalBridge.lean`) — the abstract reify witness (the projection determines the
state). It is a real multi-plane `funext`+codec-injectivity proof (the Lean kernel projects all 17 fields, so it
has NO heap/interface/tombstone gap — only the `accounts`-gating mirrors the Rust faithful-class restriction);
deferred rather than faked to keep `#assert_axioms`-clean. Not vacuous: the Rust round-trip is the deployed-system
guarantee and is green.

## ⚑ IVC mixed-root #1 — SAME-ENDPOINT digest: BUILT but BLOCKED on an in-circuit-Poseidon↔FRI-PoW conflict (2026-06-25)
Named by codex re-review #3 (`metatheory/docs/CODEX-IVC-REVIEW-3.md`). The distinct-endpoint mixed-root is
already structurally closed (the segment tooth binds genesis/final/count to the real descriptor leaves); the
residual is the SAME-genesis/final/count case, where the ordered-history `acc` was a one-felt QUADRATIC fold
`a*M1+b*M2+a*b*M3` — algebraically collidable (a directly-solvable colliding partner + degeneracy roots).
BUILT (`circuit-prove/src/ivc_turn_chain.rs`): `seg_hash2_in_circuit` → `seg_poseidon_commit`, a genuine
`SEG_DIGEST_WIDTH=4`-felt Poseidon2 duplex SPONGE + its host dual `seg_poseidon_commit_host`; carried
`chain_digest` widened to `[BabyBear;4]` (struct + `WholeChainProofBytes` envelope→v2 + consumers: lightclient
`AttestedHistory`, wasm views, pg-dregg transport `[[u8;32];4]` — all compile); codex #5 `num_turns < p` bound
added. **BLOCKER (empirically isolated, NOT yet fixed):** building the digest's in-circuit Poseidon2 perm via
the recursion `add_poseidon2_perm_for_challenger` (BABY_BEAR_D4_W16 — the SAME op the FRI challenger uses) makes
the real recursion fold PANIC at witness-gen: `WitnessConflict { WitnessId(0), existing [0,0,0,0], new <nonzero> }`

The live log confirms the exact issue: the segment tooth closes distinct endpoints, while the current same-endpoint residual is about the ordered `acc` binding. I’m narrowing now to the Lean theorem names and the IVC segment code/docs so the induction matches what exists rather than inventing new vocabulary.
exec
/bin/zsh -lc "sed -n '240,360p' HORIZONLOG.md" in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
the real recursion fold PANIC at witness-gen: `WitnessConflict { WitnessId(0), existing [0,0,0,0], new <nonzero> }`
in `run_aggregation_verification_circuit`, originating at the FRI verifier's `check_pow_witness` `assert_zero(bit)`.
PROVEN cause (isolation runs, ~80s each): the EXACT original quadratic fold (no perm) PASSES `mixed_root` (is_err,
forgery rejected); ANY Poseidon perm (W=1 or W=4) FAILS with the conflict; the bare sponge gadget passes
standalone. ROOT (cross-agent diagnosis): a circuit-GLOBAL connect-DSU collapse — exposed segment endpoints +
a challenger recompose output get unioned into `ExprId::ZERO`'s witness class (`WitnessId(0)`); the extra perm
rows reshape the graph so a genuinely-NONZERO value lands in that class and clobbers W0 at runtime. The first
"WitnessId(0) hazard via `decompose_ext_to_base_coeffs`" the task warned of was a RED HERRING (sidestepped by
ext-perm), but a DEEPER same-class collapse via `check_pow_witness`/recompose remains.
FIX IN PROGRESS (background agent `a7b40cb5d272fe949`): ISOLATE the digest onto a SEPARATE Poseidon2 op-type
(`BABY_BEAR_D4_W24` — distinct `NpoTypeId`/variant_name ⇒ isolated chain-state + per-op CTL) so it doesn't share
the FRI challenger's W16 machinery. RISK flagged: the connect-DSU is circuit-global (not per-op), so op-type
isolation may NOT change the collapse — agent to validate at `runner.run` BEFORE full W24 table-plumbing; if W24
doesn't help, pivot to the fork DSU root-fix (forbid a created/exposed NONZERO value from slot-aliasing into
`ExprId::ZERO`; emit an equality CONSTRAINT instead — generalize fork commit `72ffc56`). Two fork-side attempts
already tried + reverted (Add-executor verify-don't-clobber [sound but only moved the clobber]; NPO-output
relocation [write-side only, insufficient]). DO NOT revert to the weak quadratic fold — making Poseidon work IS
the task. NAMED RESIDUALS (by design): online accumulator scoped OUT (codex #4, single-felt binding leaf zero-
padded); ~124-bit (4 lanes) floor liftable to 8.
STATE: fork CLEAN @8d42900; dregg digest code BUILDS but the real folds (`mixed_root`, `k_fold`) FAIL until the
perm-isolation fix lands. Cheap ivc teeth 4/4; consumers compile.

## ⚑ FULL ZED AS THE DEFAULT DEV EDITOR — ONE native `links="sqlite3"` clash left (2026-06-24)
Named by the feature-collapse + zed-full-default lane (`starbridge-v2/Cargo.toml` feature table;
`deos-zed-full/Cargo.toml`; root `Cargo.toml` exclude; `dregg-tui/`). The cockpit's Dev editor is still
deos-zed's THIN integration, not the full Zed (`deos-zed-full`'s `ZedFullPane`, written + ready in
`starbridge-v2/src/zed_full_pane.rs`).
BLOCKER 2 (root-workspace `unicode-width` VERSION conflict) — **RESOLVED** (option b). `deos-zed-full` →
editor → markdown → merman needs `unicode-width ^0.2.2`, but the former root member `dregg-tui` → `ratatui
0.29` pinned `unicode-width =0.2.0` (exact). FIX: `dregg-tui` (the ONLY ratatui user) is now its OWN
root-EXCLUDED workspace — root `Cargo.toml` `exclude` += `dregg-tui`; `dregg-tui/Cargo.toml` carries its own
`[workspace]` + `[patch.crates-io]` (ark-serialize fork) + `dregg-tui/rust-toolchain.toml` (rolling nightly),
exactly the `discord-bot`/`deos-zed-full` root-exclusion pattern. Its path-deps (sdk/turn/circuit/verifier)
stay root members so their `workspace = true` deps resolve against root. Verified: root `cargo metadata`
(full deps) green; `dregg-tui` resolves + compiles standalone (`cd dregg-tui && cargo build` — its leaf deps
green; full build only hits the PRE-EXISTING root-wide `dregg-circuit-prove` `enable_expose_claim` breakage,
another lane's in-flight API change, identical from root, NOT this lane's).
BLOCKER 1 (native `links="sqlite3"` clash) — **STILL OPEN** (the prior "in-memory store RESOLVED it" note was
INCOMPLETE). Zed's `sqlez` links `libsqlite3-sys 0.30`. The root member `deos-matrix` (pulled into the cockpit
via `dev-surfaces`) cannot share a binary with it: cargo's links-UNIFIER pulls `matrix-sdk-sqlite` →
`libsqlite3-sys 0.35` whenever `sqlez` is co-present — EVEN with `deos-matrix`'s on-disk `live-matrix` store
OFF (measured: `cargo generate-lockfile` on `deos-zed-full[full-zed]` + `deos-matrix[cockpit-surface]` fails
the links check). The default `desktop`'s `web-shell` libservo lane (→ `servo` → `servo-storage` → `rusqlite
0.37` → `libsqlite3-sys 0.35`) is the SAME clash a second way. Two `links="sqlite3"` packages in one binary
is forbidden, so merely DECLARING the optional `deos-zed-full` dep on the root member `starbridge-v2`
re-breaks WHOLE-workspace resolution (the same "declaring breaks it" class the unicode-width pin used to
cause) — the dep + `zed-full`/`zed-full-pane`/`desktop-zed-full` features stay UNDECLARED (re-add block in
`starbridge-v2/Cargo.toml`). MEASURED-CLEAN in isolation: `deos-zed-full[full-zed]` + `servo`(swgl, no
libservo) resolves green — only the `sqlez`↔`{matrix-sdk-sqlite, servo-storage}` `libsqlite3-sys` split gates
it. CLOSURE — **VALIDATED, one line**: bump Zed's `sqlez` `libsqlite3-sys` pin from `0.30.1` → `0.35.0` in the
emberian/zed fork's workspace `Cargo.toml` (line ~620). PROVEN this session via a full-source `[patch.
"https://github.com/emberian/zed"]` to a local checkout with the bump: `deos-zed-full[full-zed]` +
`servo-render[libservo]` then RESOLVE TOGETHER on ONE `libsqlite3-sys 0.35` (`sqlez` + `servo-storage` both
present, exactly one libsqlite3-sys node) AND `sqlez` COMPILES unchanged against 0.35 (sqlite3 C ABI
0.30→0.35 is backward-compatible — no source edits beyond the pin). SHIP: commit the pin bump to emberian/zed
as a new rev + bump `rev = "54fbcb6943"` → new rev across breadstuffs (`grep -rl 54fbcb6943 --include=Cargo.toml`).
THEN uncomment the re-add block (`starbridge-v2/Cargo.toml`), wire `ZedFullPane` into `open_editor_pane`
(gated `zed-full-pane`) + build the live-cockpit `AppState` (the named mount seam in `zed_full_pane.rs` —
real `client::Client`/`session::Session`/`UserStore`/`WorkspaceStore`/`LanguageRegistry`/`NodeRuntime`,
`set_global`'d), fold `zed-full` into `desktop`, retire `desktop-zed-full`, and bake Dev showing the full Zed.
(BLOCKER 2 unicode-width already CLOSED — `dregg-tui` extracted, commit `678d47ced`.)
UPDATE 2026-06-24 (`9f339c98b`): the live-cockpit `AppState` MOUNT SEAM is CLOSED. `deos_zed_full::boot::
build_live_app_state` builds a genuine non-test `workspace::AppState` (real `Client` over `RealSystemClock`
+ `HttpClientWithUrl`/`BlockedHttpClient`; `Session` over the real `db::AppDatabase` — `ZED_STATELESS` →
in-mem fallback; real `LanguageRegistry`/`UserStore`/`WorkspaceStore`; `NodeRuntime::unavailable`) +
`AppState::set_global`. starbridge-v2 gets the WINDOW-ABLE API `ZedWindow::open(id, root, files, window, cx)
-> ZedWindowHandle{pane: ZedFullPane (CockpitSurface), project}` — each call an independent Zed window (own
Workspace + own FirmamentZedFs ledger), so the desktop hosts ONE or MANY. VERIFIED: `deos-zed-full[full-zed]`
green + new bake `tests/live_app_state_workspace_png_bake.rs` PASSES (a REAL Zed Workspace from the PRODUCTION
AppState renders the file tree proj/{src,lib.rs,main.rs} + an open editor over a cell, 3600x2200 PNG).
REMAINING SEAM (UNCHANGED, fork-gated): the `deos-zed-full` dep + `zed-full`/`zed-full-pane` features stay
COMMENTED in `starbridge-v2/Cargo.toml` — merely declaring the dep re-injects `sqlez → libsqlite3-sys 0.30`
into the ROOT lock graph, clashing (`links=sqlite3`) with `deos-matrix → libsqlite3-sys 0.35` (EMPIRICALLY
re-confirmed this session: `cargo generate-lockfile` fails the links check at rev `54fbcb6943`). The ONE-LINE
close is still pending: bump the emberian/zed fork's `sqlez` pin `0.30.1 → 0.35.0` + repin the rev across
breadstuffs, THEN uncomment. (The cockpit-side code is DONE — only the fork-rev/repin step remains; it is
fenced off as "don't touch the gpui fork" for this lane.)

## ✎ "MAKE YOUR FIRST CARD" — repeat entry from Author mode (2026-06-24)
Named by the onboarding commit (`12d072eff`; `starbridge-v2/src/dock/card_surface.rs::build_first_card_surface`,
`cockpit/frame.rs::{make_first_card, first_card_view, first_card_invite}`, the `--render-first-card` bake). The
"make your first card →" invite + the dedicated first-card view (mint → +1 a real turn → two receipted edit
affordances → re-render, all PROVEN by the bake: home-cell slot-0 0→1, card tape = 1 receipt, the added button in
the card's view_source, the before/after frames differ) close the FIRST-card gap on the Inhabit landing. CLOSURE
(small): the invite is first-run-only — a returning user who wants ANOTHER fresh card has no repeat entry (the
card stays minted + findable, and Author mode holds the card-editor, but there is no "+ new card" affordance from
within the full frame). Lane: surface a "+ new card" in Author mode reusing `build_first_card_surface` (the mint is
already a clean function; this is a button + a mount, not new machinery).

## ⚑ LIVE BRAIN DECIDES THE `deos.compose` STORY — the compose seam (2026-06-24)
Named by the bounded multi-cell compose commit (`deos-hermes/tests/hermes_composes_multi_cell.rs`,
`deos-hermes/src/live_js.rs::LiveComposeHands`). The confined agent can now decide-and-execute a genuinely
useful, BOUNDED, MULTI-CELL task through `run_js` — `deos.compose([...])` mints a card + seeds it + grants a
peer a cap as ONE all-or-nothing receipted gesture on the live World, refused in-band (nothing committed) on
over-reach (`held`/scope/grant-width). PROVEN end-to-end: the direct tool AND a real `AcpClient` session with a
scripted-brain stand-in (`MockHermesPeer`) emitting the compose JS as a `run_js` body → `LiveComposeHands` hook
→ `run_compose` → bounded story on the live ledger (3 receipts, the collaborator holds the cap). The ONE open
seam (identical to the authoring seam `live_authors_card_via_run_js`): a REAL `hermes-acp` brain reliably
emitting WELL-FORMED `deos.compose([...])` JSON as its `run_js` body (provider-gated; the scripted stand-in
proves the run_js→compose PATH, a live decide needs the model to cooperate). CLOSURE: an `#[ignore]` live test
mirroring `live_authors_card_via_run_js` (drive the subprocess with a "stand up a shared notebook" prompt + a
compose-API system hint), flipped on when a `hermes-acp` install + reachable provider is present.

## ⚑ WASM EXECUTOR WALL CLOCK — a real turn panics on wasm32 (`Instant::now`) (2026-06-24)
Named by the deos-card seam-closing commit (`d16b0af32`, `wasm/tests/card_fires_a_verified_turn.rs`). The
in-tab verified executor is drivable for everything EXCEPT a real turn: `turn/src/executor/{execute,
execute_tree}.rs` take unconditional `std::time::Instant::now()` profiling fences (`_pt*`/`_pf_*`, used only
under `DREGG_TURN_PROFILE`), and std's `wasm32-unknown-unknown` `Instant` is unbacked — it PANICS ("time not
implemented on this platform"), NOT routed through `performance.now()`, so the real browser playground hits
it on any `execute_turn` too (no existing wasm test fired a turn, which is why it was unsurfaced). The card
loop (`CardWorld::fire` → SetField+IncrementNonce → verified turn → re-read bound slot) is PROVEN on the host
target; the wasm32 smoke proves CardWorld instantiates + reads in a real module. CLOSURE: give `turn/` a wasm
clock — `web-time` gated on `target_arch="wasm32"`, or move the `_pt*`/`_pf_*` fences behind
`cfg(not(target_arch="wasm32"))` (they are measurement-only). Then the wasm32 `fire` test (+ the unknown-
affordance refusal) flips on and the in-tab card fires real turns end-to-end.

## ✅ REVOKE-DELEGATION EPOCH STEP — FORCED at the abstract descriptor (the last per-effect epoch residual closed) (2026-06-24)
The `RevokeDelegationEpochResidual` (parent epoch `+1`, child snapshot cleared, child stamp reset) is no
longer a carried fail-closed conjunct in any per-effect bridge. NEW dedicated DUAL descriptor
`Dregg2/Circuit/Inst/revokeDelegationFullA.lean` (`revokeDelegationFullE`): `active1 = caps` removeEdge,
`active2 = delegationStepComponent` binds the PRODUCT `(delegationEpoch, delegations, delegationEpochAt)` to

exec
/bin/zsh -lc 'rg -n "acc_attests_whole_history|EngineSound|segment|Seg|mixed-root|mixed root|chain_digest|WholeChain|attests|whole_history|history" metatheory circuit-prove circuit turn docs -S' in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
docs/reference/lean-circuit.md:196:## Whole-history aggregation (the light client over a chain)
docs/reference/lean-circuit.md:198:`Dregg2.Circuit.RecursiveAggregation` lifts single-turn soundness to a whole history.
docs/reference/lean-circuit.md:199:`light_client_verifies_whole_history` (`RecursiveAggregation.lean:200`): a verified
docs/reference/lean-circuit.md:200:aggregate root attests every per-step executor transition, the ordering, the genesis
docs/reference/lean-circuit.md:201:pin, and a genuine final fold (`AggregateAttests`). `attested_history_is_run`
docs/reference/lean-circuit.md:202:(`:234`) exposes the whole history as a `Run recChainedSystem` from genesis;
docs/reference/lean-circuit.md:203:`attested_history_conserves` (`:247`) and the verification-derived
docs/reference/lean-circuit.md:205:conservation over the whole history **without re-executing a single turn**. The named
turn/src/witnessed_receipt.rs:91:///   proof in `recursive_proof`, which attests "I re-ran the AIR over the
turn/src/witnessed_receipt.rs:107:/// semantic contract — "RecursiveProof attests the same acceptance as
turn/src/witnessed_receipt.rs:120:    /// `trace_rows`. The proof attests acceptance of the same trace; an
circuit-prove/src/custom_proof_bind.rs:92:/// inputs the proof attests.
circuit-prove/src/custom_proof_bind.rs:105:    /// The public inputs the sub-proof attests.
circuit-prove/src/accumulator.rs:27://!      `num_turns += 1`, `chain_digest = H(prev_digest, old, new, idx)`;
circuit-prove/src/accumulator.rs:35://! leaf so its digest reproduces the running `chain_digest`. So the running STATE is O(num_turns)
circuit-prove/src/accumulator.rs:39://! ## ⚠ SEGMENT-ACCUMULATOR FOLLOW-UP (the mixed-root analog, named)
circuit-prove/src/accumulator.rs:41://! The K-fold tree (`ivc_turn_chain`) closed the mixed-root hole by carrying an ordered
circuit-prove/src/accumulator.rs:42://! SEGMENT on every DESCRIPTOR leaf and combining segments in-circuit (so the whole-chain
circuit-prove/src/accumulator.rs:49://! segment tooth's by-construction binding. The follow-up is to port the segment model here:
circuit-prove/src/accumulator.rs:50://! each `accumulate` step's descriptor leaf carries its segment, and the running fold combines
circuit-prove/src/accumulator.rs:51://! `running.segment` with the new leaf's segment (the left-linear analog of the K-fold combine —
circuit-prove/src/accumulator.rs:53://! K-fold bar (the mixed-root witness) is the one that landed.
circuit-prove/src/accumulator.rs:63://! [`lightclient::verify_history`] accepts the accumulated artifact under its honest VK anchor.
circuit-prove/src/accumulator.rs:109://! whole-history attestation invariant, not the byte-level VK-shape fixpoint). It is a measured fixed
circuit-prove/src/accumulator.rs:134://! `acc_attests_whole_history`, `#assert_axioms`-clean): the running fold preserves whole-history
circuit-prove/src/accumulator.rs:135://! attestation by induction from genesis, carrying the SAME named `EngineSound` recursion boundary.
circuit-prove/src/accumulator.rs:153:    FinalizedTurn, RecursionVk, TurnChainBindingAir, WholeChainProof, ir2_leaf_wrap_config,
circuit-prove/src/accumulator.rs:171:/// Expose the accumulator's binding-leaf claims `[genesis, final, num_turns, chain_digest]`
circuit-prove/src/accumulator.rs:172:/// as a `SEG_WIDTH`-lane segment, ZERO-PADDING the single-felt binding digest to the K-fold
circuit-prove/src/accumulator.rs:174:/// `[genesis, final, num_turns, chain_digest, 0, …, 0]`.
circuit-prove/src/accumulator.rs:177:/// multi-felt segment (so `verify_turn_chain_recursive`'s tooth (4) reads a consistent
circuit-prove/src/accumulator.rs:179:/// codex #3 mixed-root close (its binding leaf is the separate, swappable single-felt
circuit-prove/src/accumulator.rs:181:fn accumulator_expose_padded_segment(
circuit-prove/src/accumulator.rs:186:    // Binding-leaf PI order: [genesis, final, num_turns, chain_digest] — i.e. the first
circuit-prove/src/accumulator.rs:192:        "binding leaf must expose [genesis, final, num_turns, chain_digest]"
circuit-prove/src/accumulator.rs:323:/// `WholeChainProof` exposes, advanced incrementally). Kept between fold steps so the binding leaf
circuit-prove/src/accumulator.rs:331:    /// The running ordered-history digest (`hash_4_to_1` over the `(old, new, idx)` pairs).
circuit-prove/src/accumulator.rs:332:    pub chain_digest: BabyBear,
circuit-prove/src/accumulator.rs:335:    /// The running Poseidon2 accumulator carrier (`acc_out` of the binding AIR; `chain_digest` IS
circuit-prove/src/accumulator.rs:344:/// [`Accumulator::finalize`] into a [`WholeChainProof`] a light client verifies.
circuit-prove/src/accumulator.rs:349:/// the per-turn `TurnChainBindingAir` leaf so its last-row digest reproduces `summary.chain_digest`
circuit-prove/src/accumulator.rs:350:/// EXACTLY (the AIR's `acc_out == chain_digest` constraint). This is precisely the component prereq
circuit-prove/src/accumulator.rs:585:    ///   5. advance the running summary (`head_root`, `chain_digest`, `num_turns`).
circuit-prove/src/accumulator.rs:729:        //     into the Poseidon2 carrier, in order — so it commits to the WHOLE ordered history
circuit-prove/src/accumulator.rs:732:        //     constraint (`acc_out == chain_digest`) holds — see `finalize_binding_leaf`'s note.
circuit-prove/src/accumulator.rs:740:                    chain_digest: acc_out,
circuit-prove/src/accumulator.rs:755:                    chain_digest: acc_out,
circuit-prove/src/accumulator.rs:768:    /// **Read the running accumulator out into a [`WholeChainProof`]** a light client verifies.
circuit-prove/src/accumulator.rs:772:    /// matching the [`WholeChainProof`] the K-fold path produces. The result verifies under
circuit-prove/src/accumulator.rs:773:    /// [`verify_turn_chain_recursive`] / [`lightclient::verify_history`] against the honest VK anchor
circuit-prove/src/accumulator.rs:778:    /// NOTE (the binding regeneration): the binding leaf attests the ordered `(old, new)` pairs of
circuit-prove/src/accumulator.rs:781:    /// last-row digest reproduces `summary.chain_digest` EXACTLY and tooth 2 of
circuit-prove/src/accumulator.rs:783:    /// head_root, num_turns, chain_digest]`) passes. The per-pair ordering is attested BOTH by this
circuit-prove/src/accumulator.rs:785:    pub fn finalize(self) -> Result<WholeChainProof, AccError> {
circuit-prove/src/accumulator.rs:805:        // running `chain_digest` exactly.
circuit-prove/src/accumulator.rs:821:            // chain_digest]`, so the accumulator's root carries the host-readable,
circuit-prove/src/accumulator.rs:825:            // (`SEG_DIGEST_WIDTH`-lane) Poseidon2 segment digest. The ONLINE accumulator
circuit-prove/src/accumulator.rs:826:            // (scoped OUT of the mixed-root close — its binding leaf is still the separate,
circuit-prove/src/accumulator.rs:831:            // unchanged from the 1-felt binding leaf; the structural mixed-root weakness
circuit-prove/src/accumulator.rs:836:                    accumulator_expose_padded_segment(cb, claims);
circuit-prove/src/accumulator.rs:894:                accumulator_expose_padded_segment(cb, claims);
circuit-prove/src/accumulator.rs:918:        // digest lane width (codex #3). The accumulator is scoped OUT of the mixed-root close; the
circuit-prove/src/accumulator.rs:921:        // (`summary.chain_digest` is the UNPADDED running carrier — a different, internal quantity.)
circuit-prove/src/accumulator.rs:922:        let mut chain_digest = [BabyBear::ZERO; crate::ivc_turn_chain::SEG_DIGEST_WIDTH];
circuit-prove/src/accumulator.rs:923:        chain_digest[0] = binding_pis[3];
circuit-prove/src/accumulator.rs:925:        Ok(WholeChainProof {
circuit-prove/src/accumulator.rs:930:            chain_digest,
circuit-prove/src/accumulator.rs:937:    /// client instead calls [`verify_turn_chain_recursive`] / `verify_history` with its CONFIGURED
circuit-prove/src/accumulator.rs:939:    pub fn finalize_and_self_verify(self) -> Result<(WholeChainProof, RecursionVk), AccError> {
circuit-prove/src/accumulator.rs:952:/// hash_4_to_1([acc_in, old, new, idx])` (the SAME fold `accumulate` ran into `summary.chain_digest`),
circuit-prove/src/accumulator.rs:955:/// head_root, num_turns, chain_digest]`. The first/last-row + continuity constraints hold by
circuit-prove/src/accumulator.rs:956:/// construction; the last-row `acc_out == chain_digest` reproduces the running digest exactly. Tooth 2
circuit-prove/src/accumulator.rs:995:    let chain_digest = trace.last().unwrap()[crate::ivc_turn_chain::COL_ACC_OUT];
circuit-prove/src/accumulator.rs:1001:        chain_digest,
circuit/src/cap_reshape_descriptor.rs:4://! two capability-security openings a light client must trust WITHOUT re-running history:
docs/reference/wasm-web.md:158:`#[wasm_bindgen]` over `dregg-lightclient::verify_history`: fold a whole finalized
docs/reference/wasm-web.md:159:history into ONE succinct recursive aggregate and verify it re-witnessing nothing
docs/reference/wasm-web.md:163:`AttestedHistory` — `attested`, genesis/final root, `chain_digest`, `num_turns`,
docs/reference/wasm-web.md:170:- `verify_history_against_anchor` — fold, then verify against a CALLER-supplied
docs/reference/wasm-web.md:172:- `produce_external_history_envelope` / `verify_devnet_history` — produce + verify
docs/reference/wasm-web.md:174:  `verify_history_bytes`, with the anchor a SEPARATE argument never read off the
circuit-prove/src/ivc_turn_chain.rs:28://!    sequential chain AND the running ordered-history digest. Each row carries
circuit-prove/src/ivc_turn_chain.rs:37://!        `acc_in == 0`, last row `acc_out == chain_digest` (public);
circuit-prove/src/ivc_turn_chain.rs:44://!    continuity and is UNSAT; a forged `chain_digest` has no satisfying Poseidon2
circuit-prove/src/ivc_turn_chain.rs:55://!    attests, then wrapped in its own **in-circuit verifier layer**
circuit-prove/src/ivc_turn_chain.rs:100://!      `final_root` / `num_turns` / `chain_digest` must verify as the public
circuit-prove/src/ivc_turn_chain.rs:102://!      (`WholeChainProof::binding_proof`, the same statement the fold wraps
circuit-prove/src/ivc_turn_chain.rs:111://! root that EXECUTED history A paired with a whole-chain CLAIM for a different history
circuit-prove/src/ivc_turn_chain.rs:115://! or built for a different history than the one the descriptor leaves executed.
circuit-prove/src/ivc_turn_chain.rs:117://! **THE FIX (codex's ordered segment-accumulator).** The separate binding leaf is GONE
circuit-prove/src/ivc_turn_chain.rs:121://!   - **leaf** ([`prove_descriptor_leaf_rotated_with_segment`]): `first_old`/`last_new`
circuit-prove/src/ivc_turn_chain.rs:124://!     the segment is tied to the ACTUAL execution this leaf re-proves — a prover cannot
circuit-prove/src/ivc_turn_chain.rs:126://!   - **aggregation combine** ([`aggregate_tree`]): both children expose a segment; the
circuit-prove/src/ivc_turn_chain.rs:129://!     left≠right ⇒ order-sensitive), then re-exposes the parent segment — up to the root.
circuit-prove/src/ivc_turn_chain.rs:131://!     tooth): the root's exposed segment `[first_old, last_new, count, acc]` is the
circuit-prove/src/ivc_turn_chain.rs:133://!     checks it equals the carried `[genesis_root, final_root, num_turns, chain_digest]`,
circuit-prove/src/ivc_turn_chain.rs:152://! - **Segment digest — a multi-felt Poseidon2 commitment** ([`seg_poseidon_commit`],
circuit-prove/src/ivc_turn_chain.rs:153://!   codex re-review #3, CLOSED). The ordered-history `acc` is a genuine
circuit-prove/src/ivc_turn_chain.rs:161://!   resistance, so a same-genesis/same-final/same-count history B with a different middle
circuit-prove/src/ivc_turn_chain.rs:164://!   #4 mixed-root weakness for that path is unchanged).
circuit-prove/src/ivc_turn_chain.rs:224:/// **The segment digest width** — the multi-felt Poseidon2 commitment carried as the
circuit-prove/src/ivc_turn_chain.rs:225:/// ordered-history `acc`. Codex re-review #3 replaced the algebraically-broken one-felt
circuit-prove/src/ivc_turn_chain.rs:234:/// comparing against `[genesis_root, final_root, num_turns, chain_digest_0..]`.
circuit-prove/src/ivc_turn_chain.rs:237:/// Segment field lanes (the order they are exposed in the `expose_claim` table).
circuit-prove/src/ivc_turn_chain.rs:244:/// A segment is exactly [`NUM_CHAIN_CLAIMS`] base-field lanes.
circuit-prove/src/ivc_turn_chain.rs:251:/// The Poseidon2 challenger perm config the segment-digest sponge runs over —
circuit-prove/src/ivc_turn_chain.rs:256:    // The ISOLATED segment-digest permutation: `BABY_BEAR_D4_W24` is a DISTINCT op-type
circuit-prove/src/ivc_turn_chain.rs:266:/// Sponge rate (in ext limbs) for the segment digest: `rate_ext` of `BABY_BEAR_D4_W24`
circuit-prove/src/ivc_turn_chain.rs:280:/// **The in-circuit ordered-segment digest** — a genuine multi-felt Poseidon2
circuit-prove/src/ivc_turn_chain.rs:294:/// made the old fold ignore an operand). A same-genesis/same-final/same-count history B
circuit-prove/src/ivc_turn_chain.rs:302:/// EXACT segment combine when it reconstructs the fold from the public building blocks.
circuit-prove/src/ivc_turn_chain.rs:356:                "segment-digest poseidon2 sponge step builds (perm op enabled by the \
circuit-prove/src/ivc_turn_chain.rs:377:            .expect("segment-digest poseidon2 squeeze step builds");
circuit-prove/src/ivc_turn_chain.rs:459:/// claims, host-readable and bus-bound to the verified history). Returns `None`
circuit-prove/src/ivc_turn_chain.rs:478:// One finalized turn: a whole-turn descriptor proof + the trace it attests +
circuit-prove/src/ivc_turn_chain.rs:563:    /// `genesis_root`/`final_root`/`num_turns`/`chain_digest` failed to
circuit-prove/src/ivc_turn_chain.rs:570:    /// **The byte envelope did not decode.** A serialized [`WholeChainProofBytes`]
circuit-prove/src/ivc_turn_chain.rs:631:// A forged `chain_digest` (a tampered `acc_out` on the last row) therefore has
circuit-prove/src/ivc_turn_chain.rs:648:/// AIR binding the finalized turn order AND the running ordered-history digest.
circuit-prove/src/ivc_turn_chain.rs:652:/// Public inputs `[genesis_root, final_root, num_turns, chain_digest]`.
circuit-prove/src/ivc_turn_chain.rs:661:///      `acc_in == 0`; last row `acc_out == chain_digest`.
circuit-prove/src/ivc_turn_chain.rs:666:///      `chain_digest` has no satisfying witness.
circuit-prove/src/ivc_turn_chain.rs:686:        4 // [genesis_root, final_root, num_turns, chain_digest]
circuit-prove/src/ivc_turn_chain.rs:728:        let chain_digest: AB::Expr = public_values[3].into();
circuit-prove/src/ivc_turn_chain.rs:753:            .assert_zero(acc_out.clone() - chain_digest);
circuit-prove/src/ivc_turn_chain.rs:832:/// folds these the SAME way the in-circuit combine does so it knows the root segment
circuit-prove/src/ivc_turn_chain.rs:835:pub(crate) struct HostSeg {
circuit-prove/src/ivc_turn_chain.rs:839:    /// The multi-felt Poseidon2 ordered-history digest (codex #3).
circuit-prove/src/ivc_turn_chain.rs:843:/// The per-turn (descriptor-leaf) segment: `first_old = old_root`, `last_new =
circuit-prove/src/ivc_turn_chain.rs:846:fn leaf_seg(old_root: BabyBear, new_root: BabyBear) -> HostSeg {
circuit-prove/src/ivc_turn_chain.rs:847:    HostSeg {
circuit-prove/src/ivc_turn_chain.rs:855:/// Combine two adjacent segments (the host mirror of the aggregation combine):
circuit-prove/src/ivc_turn_chain.rs:859:fn combine_seg(l: HostSeg, r: HostSeg) -> HostSeg {
circuit-prove/src/ivc_turn_chain.rs:863:    HostSeg {
circuit-prove/src/ivc_turn_chain.rs:871:/// Fold the per-turn leaf segments into the ROOT segment using the SAME pairwise
circuit-prove/src/ivc_turn_chain.rs:875:fn compute_root_segment(turns: &[&FinalizedTurn]) -> HostSeg {
circuit-prove/src/ivc_turn_chain.rs:876:    let mut level: Vec<HostSeg> = turns
circuit-prove/src/ivc_turn_chain.rs:884:        let mut next: Vec<HostSeg> = Vec::with_capacity(level.len().div_ceil(2));
circuit-prove/src/ivc_turn_chain.rs:945:    let chain_digest = trace.last().unwrap()[COL_ACC_OUT];
circuit-prove/src/ivc_turn_chain.rs:950:        chain_digest,
circuit-prove/src/ivc_turn_chain.rs:1155:///   `Seg = [first_old, last_new, count, acc]`
circuit-prove/src/ivc_turn_chain.rs:1159:///     acc       := H(first_old, last_new)        (the per-turn ordered-history seed)
circuit-prove/src/ivc_turn_chain.rs:1162:/// `air_public_targets` (not free prover scalars), the segment is tied to the ACTUAL
circuit-prove/src/ivc_turn_chain.rs:1163:/// execution this leaf re-proves. A prover cannot expose a segment whose endpoints differ
circuit-prove/src/ivc_turn_chain.rs:1164:/// from the descriptor it folded. This is what closes the mixed-root hole: there is no
circuit-prove/src/ivc_turn_chain.rs:1167:pub fn prove_descriptor_leaf_rotated_with_segment(
circuit-prove/src/ivc_turn_chain.rs:1195:    // commitments. Build the segment over them and expose it.
circuit-prove/src/ivc_turn_chain.rs:1232:    .map_err(|e| format!("rotated native-batch segment leaf-wrap failed: {e:?}"))
circuit-prove/src/ivc_turn_chain.rs:1243:pub struct WholeChainProof {
circuit-prove/src/ivc_turn_chain.rs:1249:    /// Fiat–Shamir binds `[genesis_root, final_root, num_turns, chain_digest]`
circuit-prove/src/ivc_turn_chain.rs:1259:    pub chain_digest: [BabyBear; SEG_DIGEST_WIDTH],
circuit-prove/src/ivc_turn_chain.rs:1264:impl WholeChainProof {
circuit-prove/src/ivc_turn_chain.rs:1282:    /// envelope ([`WholeChainProofBytes`]) that round-trips over a wire.
circuit-prove/src/ivc_turn_chain.rs:1284:    /// A whole [`WholeChainProof`] is NOT byte-encodable: its `root.1`
circuit-prove/src/ivc_turn_chain.rs:1290:    /// (a node/relayer that ran the history) ships this; the consumer (a wasm tab,
circuit-prove/src/ivc_turn_chain.rs:1296:        WholeChainProofBytes::from_proof(self).to_postcard()
circuit-prove/src/ivc_turn_chain.rs:1300:/// The versioned, wire-crossable byte envelope of a [`WholeChainProof`] — the S1
circuit-prove/src/ivc_turn_chain.rs:1303:/// It carries the VERIFY-SUFFICIENT subset of a [`WholeChainProof`]: the
circuit-prove/src/ivc_turn_chain.rs:1314:pub struct WholeChainProofBytes {
circuit-prove/src/ivc_turn_chain.rs:1322:    /// Postcard bytes of `WholeChainProof.root.0` — the root [`BatchStarkProof`].
circuit-prove/src/ivc_turn_chain.rs:1325:    /// Postcard bytes of `WholeChainProof.binding_proof` — the chain-binding
circuit-prove/src/ivc_turn_chain.rs:1332:    /// The multi-felt Poseidon2 ordered-history digest over the (old_root, new_root)
circuit-prove/src/ivc_turn_chain.rs:1335:    pub chain_digest: [u32; SEG_DIGEST_WIDTH],
circuit-prove/src/ivc_turn_chain.rs:1340:/// The on-the-wire version tag of [`WholeChainProofBytes`]. Bumped on any layout
circuit-prove/src/ivc_turn_chain.rs:1343:/// **v2** (codex re-review #3): `chain_digest` widened from one `u32` to
circuit-prove/src/ivc_turn_chain.rs:1347:impl WholeChainProofBytes {
circuit-prove/src/ivc_turn_chain.rs:1348:    /// Project a [`WholeChainProof`] to its verify-sufficient byte envelope.
circuit-prove/src/ivc_turn_chain.rs:1349:    pub fn from_proof(proof: &WholeChainProof) -> Self {
circuit-prove/src/ivc_turn_chain.rs:1354:        WholeChainProofBytes {
circuit-prove/src/ivc_turn_chain.rs:1361:            chain_digest: core::array::from_fn(|i| proof.chain_digest[i].as_u32()),
circuit-prove/src/ivc_turn_chain.rs:1368:        postcard::to_allocvec(self).expect("WholeChainProofBytes postcard-encodes")
circuit-prove/src/ivc_turn_chain.rs:1380:        let env: WholeChainProofBytes =
circuit-prove/src/ivc_turn_chain.rs:1440:/// Decodes the [`WholeChainProofBytes`] (fail-closed on malformed/wrong-version/
circuit-prove/src/ivc_turn_chain.rs:1454:    let env = WholeChainProofBytes::from_postcard(bytes)?;
circuit-prove/src/ivc_turn_chain.rs:1461:        core::array::from_fn(|i| BabyBear::new(env.chain_digest[i])),
circuit-prove/src/ivc_turn_chain.rs:1471:/// `root_blob` is the postcard of the root [`BatchStarkProof`] (`WholeChainProof.
circuit-prove/src/ivc_turn_chain.rs:1473:/// (`WholeChainProof.binding_proof`) — exactly the two blobs a transport
circuit-prove/src/ivc_turn_chain.rs:1474:/// (`pg-dregg`'s `SerializedWholeChainProof`, or the circuit's
circuit-prove/src/ivc_turn_chain.rs:1475:/// [`WholeChainProofBytes`]) carries. This decodes them inside the circuit crate
circuit-prove/src/ivc_turn_chain.rs:1486:    chain_digest: &[u32],
circuit-prove/src/ivc_turn_chain.rs:1490:    if chain_digest.len() != SEG_DIGEST_WIDTH {
circuit-prove/src/ivc_turn_chain.rs:1493:                "chain_digest must be {SEG_DIGEST_WIDTH} lanes, got {}",
circuit-prove/src/ivc_turn_chain.rs:1494:                chain_digest.len()
circuit-prove/src/ivc_turn_chain.rs:1526:        core::array::from_fn(|i| BabyBear::new(chain_digest[i])),
circuit-prove/src/ivc_turn_chain.rs:1560:) -> Result<WholeChainProof, TurnChainError> {
circuit-prove/src/ivc_turn_chain.rs:1586:) -> Result<WholeChainProof, TurnChainError> {
circuit-prove/src/ivc_turn_chain.rs:1612:) -> Result<WholeChainProof, TurnChainError> {
circuit-prove/src/ivc_turn_chain.rs:1630:) -> Result<WholeChainProof, TurnChainError> {
circuit-prove/src/ivc_turn_chain.rs:1657:    // The ROOT SEGMENT the host computes by folding the per-turn leaf segments through the SAME
circuit-prove/src/ivc_turn_chain.rs:1661:    let root_seg = compute_root_segment(turns);
circuit-prove/src/ivc_turn_chain.rs:1664:    let chain_digest = root_seg.acc;
circuit-prove/src/ivc_turn_chain.rs:1674:    // dependency of `verify_turn_chain_recursive` (see its tooth list: the segment tooth (4) over
circuit-prove/src/ivc_turn_chain.rs:1675:    // the root's exposed segment is what binds the claim now). It is NOT folded into the root.
circuit-prove/src/ivc_turn_chain.rs:1681:    // One rotated descriptor leaf per finalized turn, EACH carrying its ordered segment
circuit-prove/src/ivc_turn_chain.rs:1685:        let wrapped = prove_descriptor_leaf_rotated_with_segment(
circuit-prove/src/ivc_turn_chain.rs:1695:    // Aggregate the segment-carrying descriptor leaves to ONE root, COMBINING the segments
circuit-prove/src/ivc_turn_chain.rs:1697:    // segment is the whole-chain `[genesis_root, final_root, num_turns, chain_digest]`.
circuit-prove/src/ivc_turn_chain.rs:1700:    Ok(WholeChainProof {
circuit-prove/src/ivc_turn_chain.rs:1705:        chain_digest,
circuit-prove/src/ivc_turn_chain.rs:1772:            // THE SEGMENT COMBINE (close of the mixed-root hole): BOTH children carry an
circuit-prove/src/ivc_turn_chain.rs:1773:            // ordered segment `[first_old, last_new, count, acc]` in their `expose_claim`
circuit-prove/src/ivc_turn_chain.rs:1775:            // additivity, ordered-digest fold), and expose the parent segment. There is no
circuit-prove/src/ivc_turn_chain.rs:1777:            // descriptor leaves' segments.
circuit-prove/src/ivc_turn_chain.rs:1780:                    reason: "left aggregation child carries no segment (expose_claim) table"
circuit-prove/src/ivc_turn_chain.rs:1786:                    reason: "right aggregation child carries no segment (expose_claim) table"
circuit-prove/src/ivc_turn_chain.rs:1799:                    .expect("left segment instance present");
circuit-prove/src/ivc_turn_chain.rs:1802:                    .expect("right segment instance present");
circuit-prove/src/ivc_turn_chain.rs:1819:                // (2) parent segment: span [L.first_old .. R.last_new], count L+R, ordered
circuit-prove/src/ivc_turn_chain.rs:1872:///   3. **The segment tooth** — the root's exposed ORDERED SEGMENT
circuit-prove/src/ivc_turn_chain.rs:1875:///      `[genesis_root, final_root, num_turns, chain_digest]`. This closes the
circuit-prove/src/ivc_turn_chain.rs:1876:///      mixed-root hole: a root that executed history A cannot expose B's
circuit-prove/src/ivc_turn_chain.rs:1880:    proof: &WholeChainProof,
circuit-prove/src/ivc_turn_chain.rs:1888:        proof.chain_digest,
circuit-prove/src/ivc_turn_chain.rs:1895:/// [`WholeChainProof`] value.
circuit-prove/src/ivc_turn_chain.rs:1897:/// This is the byte-path's verifier: a [`WholeChainProof`] cannot be reconstructed
circuit-prove/src/ivc_turn_chain.rs:1903:/// [`verify_whole_chain_proof_bytes`] decodes a [`WholeChainProofBytes`] envelope and
circuit-prove/src/ivc_turn_chain.rs:1910:///   3. **The segment tooth** — the root's exposed ordered segment `[first_old,
circuit-prove/src/ivc_turn_chain.rs:1913:///      chain_digest]`. (The carried binding proof is NOT a soundness dependency.)
circuit-prove/src/ivc_turn_chain.rs:1920:    chain_digest: [BabyBear; SEG_DIGEST_WIDTH],
circuit-prove/src/ivc_turn_chain.rs:1946:    // (3) THE SEGMENT TOOTH (the close of the IVC mixed-root hole). The root proof carries an
circuit-prove/src/ivc_turn_chain.rs:1948:    // `[first_old, last_new, count, acc]`. That segment is built BY CONSTRUCTION from the real
circuit-prove/src/ivc_turn_chain.rs:1953:    // root-exposed segment is the WHOLE-CHAIN claim derived from the ACTUAL execution. The
circuit-prove/src/ivc_turn_chain.rs:1955:    // that executed history A cannot expose B's endpoints, so a B-claim against an A-execution
circuit-prove/src/ivc_turn_chain.rs:1959:            reason: "root proof carries no exposed segment table (segment channel absent)"
circuit-prove/src/ivc_turn_chain.rs:1967:    expected.extend_from_slice(&chain_digest);
circuit-prove/src/ivc_turn_chain.rs:1971:                "root-exposed segment {exposed:?} != carried claim {expected:?} \
circuit-prove/src/ivc_turn_chain.rs:2019:) -> Result<WholeChainProof, TurnChainError> {
docs/reference/deos-js.md:235:  card's `view_source` (a `ProgramSource` = a `dregg_doc::Doc` patch-history), re-sealed into
docs/reference/deos-js.md:320:- `program_doc` — a gadget's `view_source` is a `dregg_doc::Doc` patch-history:
docs/reference/sdk.md:43:  ONE succinct whole-history aggregate, re-witnessing nothing
docs/reference/sdk.md:87:  paid by the cell and belongs to the cell's own history
circuit-prove/src/plonky3_recursion_impl.rs:5://! attests "the inner proof is valid" — enabling unbounded recursion.
circuit-prove/src/plonky3_recursion_impl.rs:192:            // The ISOLATED segment-digest permutation: a SECOND Poseidon2 op-type
circuit-prove/src/plonky3_recursion_impl.rs:195:            // challenger's width-16 perm participates in. The ordered-history segment digest
circuit-prove/src/plonky3_recursion_impl.rs:740:        // The ISOLATED segment-digest permutation table (`baby_bear_d4_w24`): a distinct
circuit-prove/src/plonky3_recursion_impl.rs:741:        // Poseidon2 op-type the IVC segment-digest sponge runs over, so its rows never share
circuit-prove/src/plonky3_recursion_impl.rs:743:        // register it to interpret the W24 `poseidon2_perm` ops a segment-bearing root carries.
docs/reference/README.md:24:- [lean-circuit.md](lean-circuit.md) — Circuit soundness / unfoolability: the apex `lightclient_unfoolable`, per-effect refinement, freshness, whole-history aggregation, and settlement soundness.
metatheory/Dregg2.lean:66:import Dregg2.Exec.StepComplete -- step-completeness spine: cexec attests all 4 StepInv conjuncts; conservation_step realized; end-to-end soundness
metatheory/Dregg2.lean:67:import Dregg2.Exec.RecordKernel -- concrete cell: KernelState's bal:ℤ lifted to a content-addressed Value record; recKExec_conserves/recKExec_authorized/recCexec_attests proved over the named `balance` field (#assert_axioms-clean)
metatheory/Dregg2.lean:106:import Dregg2.Exec.RecordCellLive     -- Value/RecordProgram cell as a real Boundary.TurnCoalg: recCexec_attests (4-conjunct step-completeness) + recReplay_preserves_sumEquals (conservation over name-keyed records) + stepComplete_preserves instance; #assert_axioms-clean
metatheory/Dregg2.lean:117:import Dregg2.Spec.Authority          -- generative capability graph: introduce/amplify/mint + "only connectivity begets connectivity" (gen_step_traces proved); whole-history closure OPEN
metatheory/Dregg2.lean:129:import Dregg2.Proof.LTS                -- single-cell operational LTS: recAbsStep_forward + authAbsStep_forward united in absStep'_forward; cross-cell whole-history closure residual OPEN
metatheory/Dregg2.lean:166:import Dregg2.Exec.TurnExecutor        -- turn-executor: Turn = call-forest of catalog-typed Actions run all-or-nothing; execTurn_attests = all 4 StepInv conjuncts over the whole multi-action turn + execTurn_conserves/_balance_domain/_unauthorized_fails
metatheory/Dregg2.lean:167:import Dregg2.Exec.TurnForest          -- nested call-forest executor: execForest_no_amplify (Granovetter via derive_no_amplify) + execForest_conserves (N-ary CG-5, Σ=0 whole tree) + execForest_attests (4 StepInv conjuncts); cross-cell forest OPEN
metatheory/Dregg2.lean:177:import Dregg2.Exec.TurnExecutorFull    -- full op-set executor: FullAction = balance | delegate/revoke | mint/burn; execFull_attests = StepInv per kind + execFullTurn_ledger transaction-level conservation
metatheory/Dregg2.lean:180:import Dregg2.Exec.CrossCellForest     -- cross-cell nested forest: crossForest_no_amplify + crossForest_conserves (N-ary cross-cell Σ=0) + crossForest_attests; bilateral = Fin-2 slice; overlapping-cells OPEN
metatheory/Dregg2.lean:181:import Dregg2.Exec.FullForest          -- FullActionA call-forest (wholesale-swap keystone): execFullForestA = recursive all-or-nothing tree over the full per-asset op-set, proven equal to execFullTurnA over the pre-order lowering; execFullForestA_conserves_per_asset (conservation vector, not scalar) + execFullForestA_no_amplify + execFullForestA_each_attests; cross-target routed to CrossCellForest
metatheory/Dregg2.lean:206:import Dregg2.Apps.AgentOrchestration  -- verified multi-agent orchestration ("the orchestration is a theorem"): least-privilege attenuated sub-agent delegation (worker_authority_subset_orchestrator, strict write-drop) + real per-asset transfers conserve (workForest_conserves) + out-of-scope worker fail-closed (badWorkerForest_fails_closed = none) + escrow combined-conservation (escrowLock_combined_conserves) + credential+caveat auth gate (committed ⇒ credential ∧ caveats; forged-cred & false-caveat denied) + whole forest certified (orchestration_conserves ∧ _no_amplify ∧ _each_attests); #assert_axioms-clean
metatheory/Dregg2.lean:404:import Dregg2.Exec.Gas                  -- gas-metering layered beside execFullTurn: gasCost_pos (no free action) + gas_exhaustion_fails_closed (over-budget ⇒ none, no partial mutation) + gas_sufficient_runs (pure guard, identical state) + gas_conserves/_preserves_attests (removes no safety); Nat-resource orthogonal to ℤ-conservation
metatheory/Dregg2.lean:406:import Dregg2.Exec.ProofForest         -- proof-carrying forest composition: per-node StepProofValid × Linked ⇒ whole-run StepInv via execForest_attests; aggregation deferred
metatheory/Dregg2.lean:418:import Dregg2.Spec.ExecRefinementFull  -- general forward-sim refinement: exec_full_refines_spec (every execFull step is a permitted abstract step) + full operational square; whole-history closure OPEN
metatheory/Dregg2.lean:430:import Dregg2.Distributed.HistoryAggregation -- IVC FOLD MODEL under circuit/src/ivc_turn_chain.rs (the magnesium→gold meaning layer): a chain of ChainSteps = genuine recCexec transitions over RecChainedState whose roots are the §8 recStateCommit; the TurnChainBindingAir temporal tooth new_root[i]==old_root[i+1] (Continues/ChainBound); HEADLINE wellformed_attests_whole_history (every turn recCexec-correct + ChainBound ordered + the whole chain is Run recChainedSystem ⇒ wellformed_history_conserves no-mint/burn over ALL history); root_tooth_pins_state = the CR RECOVERY (recStateCommit_binds: matching seam roots ⇒ equal cellDigest+RH = the root IS the full-state commitment, so a light client seeing only roots learns state continuity); non-vacuity BOTH ways (honest_chain_wellformed positive over teethGenesis + tooth_rejects_broken_order = reordered chain is NOT ChainBound); #assert_axioms-clean
metatheory/Dregg2.lean:445:import Dregg2.Coord.CausalOrder          -- Layer-1 CAUSAL CHAINING (types/src/causal.rs CausalDag, the DAG net+coord share): faithful insertion-ordered Dag + insert (MissingDeps/Duplicate/self-cycle gates) + happenedBefore = transitive closure of the dep edges; PROVES the causal-ordering invariant is a STRICT PARTIAL ORDER (hb_irrefl from acyclicity, hb_trans, hb_asymm), insert_wf (the dep-presence gate preserves wellformedness across the whole history), hb_imp_index_lt (insertion order is a LINEAR EXTENSION ⇒ topological_order respects happened-before), fresh_is_maximal (frontier), concurrent_symm; GENUINELY uncovered by EntangledJoint (which models Layer-2/3, not Layer-1). Rust differential coord/src/coord_diff.rs vs the real dregg_types::CausalDag. #assert_axioms-clean
metatheory/Dregg2.lean:525:import Dregg2.Circuit.RecursiveAggregation -- RECURSIVE-AGGREGATION SOUNDNESS (THE magnesium→gold bridge over circuit/src/ivc_turn_chain.rs prove_turn_chain_recursive→WholeChainProof): the SNARK recursion layer over HistoryAggregation. Opaque (Proof,verify) = plonky3 RecursionCompatibleProof/verify_recursive_batch_proof; EngineSound bundles the 3 NAMED, REALIZABLE soundness hypotheses you cannot prove in Lean — recursive_sound (root verifies ⇒ all child leaves verify; the ONE FRI obligation §H1), leaf_sound (POSITIONAL Forall₂ pairing leaf↔step ⇒ verifying leaf attests its recCexec step; the EffectVm circuit⟺executor soundness), binding_sound (TurnChainBindingAir leaf ⇒ ChainBound + genesis/final root pins). HEADLINE light_client_verifies_whole_history: checking ONLY verify agg.root (re-witnessing NOTHING) ⇒ AggregateAttests (every turn executed correctly + correctly ordered + final root = genuine fold) = proofs-as-additive-attestation, the verification IS the trust + attested_history_conserves inherited. NON-VACUITY both ways: real_engine_sound/light_client_fires_on_real_chain/real_chain_first_turn_executed (witnessed over the honest teethGenesis step) + ANTI-GHOST tampered_aggregate_cannot_bind (reordered chain ⇒ binding_sound forces ChainBound = FALSE ⇒ no verifying aggregate) + leaf_pairing_defeats_swap (positional pairing ⇒ leaf not re-pointable). #assert_axioms-clean; the named hyps are structure FIELDS not axioms
metatheory/Dregg2.lean:526:import Dregg2.Distributed.FeeHistory       -- the Argus FEE-WRAPPED history conserves MODULO THE BURN (the apex inventory's statement): FeeChainStep = one ACCEPTED runTurn (commits : runTurn ctx hdr (transferStmt turn) pre = .bodyCommitted post; fee cells wired/live/distinct as load-bearing fields) + runTurn_bodyCommitted_inv (the ACCEPTED-outcome inversion); per-step keystone feeStep_conserves_modulo_burn (recTotal moves by EXACTLY −feeBurned: prologue −fee ∘ exact transfer body ∘ epilogue +fee−burn, via the owned recTotal accounting recTotal_commitPrologue/recTotal_distributeFee over sum_indicator) → HEADLINE wellformed_history_conserves_modulo_burn (recTotal endpoint + totalBurn = recTotal genesis over ANY state-chained fee history: arbitrary length leaks exactly the named sink, additively; the bare strand's exact law = the totalBurn=0 face); feeStep_exposes_body_strand_step CONSUMES Aggregate §6 argus_full_turn_body_links (the fee chain sits ON the light-client body strand — not re-proved); W1 runTurnV note: at the VK-rotation swap this collapses to totalBurn=0 paid to the burn-pot; non-vacuity both polarities #guard-EXECUTED (real accepted transfer turn: 100→98; the =100 and =90 claims both FALSE); #assert_axioms-clean
metatheory/Dregg2.lean:527:import Dregg2.Distributed.FinalizedLightClient -- THE THREE-LEG FINALIZED light client (the (aggregate, finalizedRoot, finalityCert) surface the lightclient/ Rust crate realizes): adds the FINALITY-CERT (quorum/tau) leg RecursiveAggregation lacks — a bare valid aggregate proves a chain CORRECT but not FINALIZED (a fork attack). FinalityCert carries the certified lace + anchor + finalizedRoot; CertValid = finalLeaderAt = some anchor (the node's REAL BlocklaceFinality super-ratification leader-slot rule, NOT bare isSuperRatified — certValid_has_quorum proves valid ⇒ CertQuorum). HEADLINE light_client_accepts_finalized_history: verify agg.root (leg1+2 via RecursiveAggregation) ∧ Bound (root seam agg.finalRoot = cert.finalizedRoot = shown) ∧ CertValid (leg3 quorum) ⇒ FinalizedHistoryAttested (whole history correct+ordered+conserving AND endpoint root is QUORUM-finalized) — gap-free, re-witnessing nothing. NON-VACUITY: finalized_light_client_fires_for (Prop headline fires given a realized cert) + §5b #guard executable witnesses (finalLeaderAt trace3 = some creator-1 genesis, CertQuorum true). ANTI-GHOST: not_final_leader_invalidates (forged creator-2 anchor ⇒ ¬CertValid; #guard witnessed on trace3 — HONEST: super-ratification alone insufficient, leader-slot is the discriminator) + root_mismatch_unbinds/agg_root_mismatch_unbinds (seam tooth: cannot pair proof-of-A with cert-for-B). #assert_axioms-clean
metatheory/Dregg2.lean:631:import Dregg2.Lightclient.AttestedQuery   -- THE NON-OMISSION THEOREM: a query answer = membership openings + gap openings (Gap.inner = the REUSED sorted_gap_excludes bracketing + below/above/empty boundary forms); answer_complete: a VERIFYING answer contains EVERY in-range key in the index (omission impossible — an omitted key would sit in a valid gap, absurd) + answer_sound (no forgery) + verifies_iff_exact (verifying ≡ THE unique exact answer) + exact_answer_verifies (honest prover total; gapsOf bracket-EXISTENCE proved); ROOT face server_cannot_omit; CHAIN face: CommitBindsIndex NAMES the rotation obligation (recStateCommit must absorb iroot as a sponge limb, the heap_root discipline) and light_client_query_non_omission composes with RecursiveAggregation: ONE verify(agg.root) ⇒ non-omission over the WHOLE history. Non-vacuity TRUE (complete answer verifies) and FALSE (dropped receipt REJECTED / forged covering gap INVALID / forged extra + tampered value REJECTED)
metatheory/Dregg2.lean:635:import Dregg2.Consensus.TauPrefixMonotone -- T5 RESOLVED with a SOUNDNESS FINDING: tauOrder finalized-prefix monotonicity is REFUTED unconditionally (honest-laggard counterexample lagBase→lagGrown: a lagging validator's late wave-end ratifier grows an ALREADY-FINAL wave's coverage and xsorts MID-PREFIX; insert-valid, equivocation-free — the node's executed_up_to index slicing at blocklace_sync.rs::poll_finalized_blocks would re-execute block 32 and PERMANENTLY skip block 41) + PROVED conditional: tau_finalized_prefix_monotone under FinalizedRegionStable (leaders_extend + fold_agrees = the finalized region undisturbed; executable mirror stableCheck = the check the node is MISSING; pointwise sufficient condition fold_agrees_of_pointwise; node-shaped corollary tau_executed_prefix_fixed = the executed region is bit-identical under take) + structural foldl_tauStep_fst_extend (tau's loop only APPENDS — reorder risk lives entirely in the leader list + segments); POS tooth trace3→trace6 (full second wave: stableCheck holds, 9→18 prefix) + NEG teeth isolate the failing field (leaders_extend holds, fold_agrees fails); #assert_axioms-clean
metatheory/Dregg2.lean:696:import Dregg2.Circuit.EngineSoundOfApex -- THE ENGINESOUND WELD: discharge RecursiveAggregation.EngineSound.leaf_sound BY the single-turn apex (lightclient_unfoolable_circuit_sound), so the multi-turn / finalized-history / distributed stack rests on circuit soundness, not on leaf_sound as a free sibling. ApexLeafBundle = per-leaf datum (batch pi/π + accepting verdict + the single ClosedWitness floor ⟹ apex FIRES) + the NAMED lowering apexLowers (the apex's kstepAll pi.effect, per-asset bal ledger, single FullActionA, ANY effect → the step's recCexec, legacy balOf-cell ledger, transfer Turn). engineSound_of_apex BUILDS EngineSound: leaf_sound DISCHARGED via leafStep_of_bundle∘the apex; recursive_sound/binding_sound = the two FRI legs (outside Lean) passed through. PAYOFF: multiTurn_rests_on_apex / finalized_rests_on_apex. THE RESIDUAL apexLowers is the THREE reconciliation mismatches NAMED (endpoint-binding · transfer-arm-only pi.effect=0 · cross-ledger bal-vs-balOf-cell, RingFFI projAsset agreement is column-only); realizable on honestStep (transfer arm) — honestStep_lowers. #assert_axioms-clean.
turn/src/aggregate_bilateral_prover.rs:456:/// the proof attests.
turn/src/aggregate_bilateral_prover.rs:655:    // proof, verify it ALGEBRAICALLY: the balance STARK attests the signed
turn/src/aggregate_bilateral_prover.rs:954:/// Each child is verified classically (so the tree never attests an invalid
docs/reference/lean-assurance.md:48:   `RecursiveAggregation.EngineSound.recursive_sound`).
docs/reference/lean-assurance.md:144:*A light client verifying a Q-chain learns A–D for the whole history while re-witnessing nothing.*
docs/reference/lean-assurance.md:145:Apex: `unfoolability_guarantee` (`:666`) conjoins (1) `light_client_verifies_whole_history` — checking
docs/reference/lean-assurance.md:147:genuine fold — with (2) `conserves_from_verification`: the whole history conserves value, **derived
docs/reference/lean-assurance.md:160:`RecursiveAggregation.light_client_verifies_whole_history` (the whole-history headline), and
docs/reference/lean-assurance.md:171:and C-c1 (every node attests `gatedActionInvG`, `execFullForestG_each_attests`). The gate is
docs/reference/lean-assurance.md:182:B = `execFullForestG_conserves_exact`, C-c1 = `execFullForestG_each_attests`, C-c2 = the whole-turn
docs/reference/lean-assurance.md:184:D = the noteSpend anti-replay triple, E = `light_client_verifies_whole_history` +
docs/reference/lean-assurance.md:187:integrity-attesting; the same verified history is fresh and unfoolable (`:822-824`).
docs/reference/circuit.md:5:fold into one succinct whole-history aggregate, and a light client verifies that
docs/reference/circuit.md:23:  (`WholeChainProof`) and obtain the verdict, re-witnessing nothing
docs/reference/circuit.md:139:   turn breaks continuity (UNSAT); a forged `chain_digest` has no satisfying
docs/reference/circuit.md:162:`WholeChainProof` carrying the root, the chain-binding proof, and the four public
docs/reference/circuit.md:163:scalars `genesis_root`/`final_root`/`chain_digest`/`num_turns`
docs/reference/circuit.md:190:   the carried binding proof to THIS root: a genuine root for history A paired
docs/reference/circuit.md:191:   with a genuine binding proof for a different history B fails here.
docs/reference/circuit.md:215:A whole `WholeChainProof` is NOT byte-encodable (its `root.1` is prover-only
docs/reference/circuit.md:216:`Rc<CircuitProverData>`); `WholeChainProofBytes`
docs/reference/circuit.md:228:`Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history`
docs/reference/circuit.md:231:- **`verify_history(agg, expected_vk)`**
docs/reference/circuit.md:235:  `genesis_root`/`final_root`/`chain_digest`/`num_turns`. `expected_vk` is the
docs/reference/circuit.md:239:  `verify_history_bytes` (`lightclient/src/lib.rs:196-212`).
docs/reference/circuit.md:243:- **The third leg — finality.** `verify_history` proves a *correct-looking*
docs/reference/circuit.md:244:  history, but an equivocating prover can fold a valid aggregate over a fork the
docs/reference/circuit.md:251:  (`lightclient/src/lib.rs:274-282`). `verify_finalized_history`
docs/reference/circuit.md:252:  (`lightclient/src/lib.rs:378-417`) runs three legs: (1) `verify_history`; (2)
docs/reference/circuit.md:255:  `Dregg2.Distributed.FinalizedLightClient.light_client_accepts_finalized_history`
docs/reference/circuit.md:263:test `light_client_attests_whole_history` folds a real K=3 chain and light-verifies
docs/reference/circuit.md:264:it (`lightclient/src/lib.rs:533-580`); `whole_history_demo`
docs/reference/circuit.md:265:(`lightclient/src/bin/whole_history_demo.rs:1-15`) is the runnable demo.
docs/reference/circuit.md:276:- `RecursiveAggregation.light_client_verifies_whole_history`
docs/reference/circuit.md:279:  UNDER the named `EngineSound` hypotheses.
docs/reference/circuit.md:280:- `EngineSound`
docs/reference/circuit.md:288:`light_client_verifies_whole_history`,
docs/reference/circuit.md:296:THEN the whole history is attested — but NAMES the FRI engine soundness it does
docs/reference/circuit.md:299:`EngineSound.recursive_sound`. You cannot prove plonky3 FRI soundness in Lean, and
docs/reference/lean-distributed.md:140:- Light-client unfoolability: a settled root attests authority-was-live-at-settle
docs/reference/lean-distributed.md:141:  (`settled_root_attests_live_authority`, `SettlementSoundness.lean:490`).
docs/reference/lean-distributed.md:246:  client adding a `FinalityCert` quorum leg; `light_client_accepts_finalized_history`
docs/reference/lean-distributed.md:247:  (`:187`), `finalized_history_conserves` (`:211`).
docs/reference/lean-distributed.md:274:name directory), **FeeHistory** (`:520`, history conserves modulo the burn),
turn/src/presence_discharge.rs:152:    /// Extract the claim requirement this discharge attests to.
docs/reference/turns.md:235:per-edge / root attestation (`FullForestAuth.execFullForestG_each_attests`,
docs/reference/turns.md:236:`...execFullForestG_root_attests`).
turn/src/reversible.rs:7://! [`ReversibleHistory::undo_to`] walks history *backward* — the dual of
turn/src/reversible.rs:13://! > Every effect has an inverse (the un-turn); a stretch of unsettled history
turn/src/reversible.rs:25://!   field value, the revoked cap's content), which the reversible-history
turn/src/reversible.rs:26://!   object supplies as the pre-state ledger. Sound only against the history
turn/src/reversible.rs:42://! window) and never claims to rewrite finalized history.
turn/src/reversible.rs:195:    /// Inverse needs the pre-image; sound only against the producing history.
turn/src/reversible.rs:567:/// One recorded step of reversible history — genesis installs and committed
turn/src/reversible.rs:586:/// Errors from the reversible-history navigation (fail-closed, mirroring
turn/src/reversible.rs:590:    /// Asked to navigate to a step beyond the recorded history.
turn/src/reversible.rs:617:                write!(f, "undo step {step} out of range (history len {len})")
turn/src/reversible.rs:639:/// The recorded, replayable AND reversible history of a world.
turn/src/reversible.rs:656:    /// A fresh, empty reversible history (free-metered).
turn/src/reversible.rs:661:    /// A fresh, empty reversible history metering at `costs`.
turn/src/reversible.rs:716:    /// rejected turn is NOT recorded — it did not change history).
turn/src/reversible.rs:767:    /// Reverse history back to step `k` by building and applying the inverse
turn/src/reversible.rs:811:                // history; if k sits below a genesis step, undoing it would
turn/src/reversible.rs:823:            // applied) — reconstruct + verify it from the recorded history.
turn/src/reversible.rs:1180:        // A fixture history of CLEAN turns only (transfers + a set-field), so the
circuit-prove/src/joint_turn_aggregation.rs:8://! happened-before chain *within* a cell's history. It explicitly does **not**
circuit-prove/src/joint_turn_aggregation.rs:26://! - col 0: `shared_turn_id`  — the turn identity this cell's proof attests
circuit-prove/src/joint_turn_aggregation.rs:103:/// vector it attests (the v1 prefix `[0..34)` + the 4 appended rotated commit/height/caveat
circuit-prove/src/joint_turn_aggregation.rs:113:    /// The 38-PI vector (`ROT_PI_COUNT`) the proof attests.
circuit-prove/src/joint_turn_aggregation.rs:300:/// resolve which cohort the leg attests. The rotated `Ir2BatchProof` is verified against its
turn/src/turn.rs:21://!   the same cell. The chain *is* the cell's history.
docs/reference/cells.md:186:  history are preserved; a second seal errors `AlreadySealed`, preserving the original
docs/reference/cells.md:213:(`cell/src/commitment.rs:179`). The context history (`v4→...→v9`) records each shape
circuit/src/predicate_program.rs:896:    pub temporal_history: HashMap<String, (Vec<u64>, Vec<BabyBear>)>,
circuit/src/predicate_program.rs:1034:                    .temporal_history
circuit/src/predicate_program.rs:2329:        // Provide temporal history.
circuit/src/predicate_program.rs:2335:            .temporal_history
circuit/src/predicate_program.rs:2348:    fn test_prove_temporal_insufficient_history() {
circuit/src/predicate_program.rs:2364:            .temporal_history
turn/src/executor/mod.rs:617:    /// history (every turn that TOUCHED the cell, agent or not). Distinct from the
turn/src/executor/mod.rs:1326:    /// history (e.g. after restart) so the receipt-chain check reflects the
turn/src/executor/mod.rs:1328:    /// pre-existing history would be rejected as `ReceiptChainMismatch`.
turn/src/executor/mod.rs:1394:    /// `previous_receipt_hash` source + any per-cell receipt-history walk. Advances
turn/src/executor/apply.rs:2330:        // attests that the prover did *not* take a specific action
turn/src/executor/execute.rs:624:                    // matches the proof, so the proof attests to the same
turn/src/error.rs:339:    /// - `expected: Some(h)`, `got: None` -- agent has a history but submitted
turn/src/error.rs:344:    /// This is the executor-side enforcement of "self-bound history" (the
turn/src/executor/atomic.rs:595:        // receipt history), not the authority chain — so the per-cell chain stays
turn/src/executor/atomic.rs:959:            // per-cell receipt history); the AUTHORITY head (which gates a turn's
turn/src/executor/authorize.rs:1426:                // path attests bearer-cap transitions). The recomputed scope vector that the v1
docs/deos/APPS-AS-CELLS.md:8:> mutations are turns, its history is a receipt chain, its documents speak the
docs/deos/APPS-AS-CELLS.md:162:- the **command history = a provenance chain** — each command is a turn, so the
docs/deos/APPS-AS-CELLS.md:163:  history *is* the receipt chain (`History`), time-travelable and replayable.
docs/deos/APPS-AS-CELLS.md:222:## 3. CHAT (deos-matrix) — room = a cell, messages = its history
docs/deos/APPS-AS-CELLS.md:249:- **room = a cell**; its **messages = its history** (the receipt/turn chain). A
docs/deos/APPS-AS-CELLS.md:266:object is the room cell + its turn history + the membrane payloads.
docs/deos/APPS-AS-CELLS.md:388:4. **Chat room=cell** — name the room a cell with messages as its turn history; the
circuit/src/descriptor_ir2.rs:5926:    //    EngineSound` names it. We model the engine + fire the anti-ghost BOTH ways. --
circuit/src/backends/mod.rs:364:    /// The accumulated hash committing to the chain history.
circuit/src/backends/mod.rs:400:    /// (e.g., by splitting into segments).
turn/src/rotation_witness.rs:6://! receipt log — whole-history non-omission, Lean `mroot_injective` /
turn/src/action.rs:1199:        /// The cell whose history attests to the non-action.
turn/src/action.rs:1235:    /// The cell rejects new effects after sealing but state and history
turn/src/executor/membership_verifier.rs:1729:        //     the adjacency STARK binds the specific leaves it attests.
circuit-prove/src/joint_turn_recursive.rs:105:// Per-cell input: a whole-turn descriptor proof + the trace it attests.
circuit-prove/src/joint_turn_recursive.rs:110:/// 186-column execution trace the proof attests — the prover-side witness from
circuit-prove/src/joint_turn_recursive.rs:141:    /// `(shared_turn_id, cell_commit)` pairs the binding leaf attests.
circuit-prove/src/joint_turn_recursive.rs:149:    /// [`WholeChainProof::root_vk_fingerprint`](crate::ivc_turn_chain::WholeChainProof::root_vk_fingerprint)
turn/src/executor/finalize.rs:1030:    /// attests it, since there is no Rust receipt to carry.
circuit/src/ivc.rs:74:    /// This commits to the entire history without storing it.
circuit/src/ivc.rs:97:    /// The accumulated hash committing to the entire chain history (single element, for STARK AIR).
circuit/src/ivc.rs:225:/// - All prior history (via old_hash)
circuit/src/ivc.rs:246:/// are absorbed, providing 124-bit binding to prior history.
turn/tests/umem_time_travel.rs:11://! Why this is cheap and witnessed (no chip table, no O(history) replay):
turn/tests/umem_time_travel.rs:17://!     memcheck program. No history replay is needed: the boundary IS the state.
turn/tests/umem_time_travel.rs:267:    // history replay; the boundary IS the state.
circuit/src/lean_descriptor_air.rs:1784:/// attests — same AIR (`EffectVmDescriptorAir`), same trace, same PI prefix.
docs/deos/REFLEXIVE-DISTRIBUTED-IMAGE.md:166:  session that edited a file) and **`cv blame <file>`** — a file's git history tied back to
docs/deos/REFLEXIVE-DISTRIBUTED-IMAGE.md:232:  *additive*: cv's corpus is the genesis history; deos's `History::replay_to` re-derives it,
docs/deos/REFLEXIVE-DISTRIBUTED-IMAGE.md:390:   designed that way); the lift must be *additive* (cv corpus = genesis history, re-derivable by
circuit-prove/tests/accumulator.rs:10://!     ACCEPTED by `verify_history` under its honest VK anchor, attests the right endpoints, and is
circuit-prove/tests/accumulator.rs:26:    FinalizedTurn, WholeChainProof, prove_turn_chain_recursive, verify_turn_chain_recursive,
circuit-prove/tests/accumulator.rs:202:/// the accumulated artifact attests the SAME `(genesis_root, final_root, num_turns)` a K-fold
circuit-prove/tests/accumulator.rs:203:/// `prove_turn_chain_recursive` of the same 3 turns attests (the running fold and the balanced tree
circuit-prove/tests/accumulator.rs:204:/// agree on the whole-history claim).
circuit-prove/tests/accumulator.rs:207:fn incremental_accumulate_verifies_whole_history() {
circuit-prove/tests/accumulator.rs:240:    // Cross-check the whole-history CLAIM against the K-fold balanced-tree artifact of the same 3
circuit-prove/tests/accumulator.rs:246:    // mixed-root hole) — each descriptor leaf carries `[first_old, last_new, count, acc]` and the
circuit-prove/tests/accumulator.rs:249:    // each internally-sound ordered-history commitments but, being different fold structures over
circuit-prove/tests/accumulator.rs:252:    // to its own root-exposed value (the segment tooth), which is what soundness requires.
circuit-prove/tests/accumulator.rs:254:    let kfold: WholeChainProof =
circuit-prove/tests/accumulator.rs:276:/// `incremental_accumulate_verifies_whole_history`, which passes PINNED end-to-end); this tooth
circuit-prove/tests/accumulator.rs:539:/// running proof for a spliced history is ever produced.
circuit-prove/tests/ivc_turn_chain_rotated.rs:41:    FinalizedTurn, TurnChainError, WholeChainProof, WholeChainProofBytes, fold_two_turns,
circuit-prove/tests/ivc_turn_chain_rotated.rs:53:// `WholeChainProof` is imported for type clarity even though it is only named via the
circuit-prove/tests/ivc_turn_chain_rotated.rs:56:use dregg_circuit_prove::ivc_turn_chain::WholeChainProof as _WholeChainProof;
circuit-prove/tests/ivc_turn_chain_rotated.rs:181:/// and RELABELED carried publics (final_root / chain_digest / num_turns /
circuit-prove/tests/ivc_turn_chain_rotated.rs:191:    let mut whole: WholeChainProof = prove_turn_chain_recursive(&turns)
circuit-prove/tests/ivc_turn_chain_rotated.rs:219:    // REFUSED: relabeled chain_digest (claiming a different ordered history) — the digest
circuit-prove/tests/ivc_turn_chain_rotated.rs:221:    let honest_digest = whole.chain_digest;
circuit-prove/tests/ivc_turn_chain_rotated.rs:222:    whole.chain_digest[0] = honest_digest[0] + BabyBear::ONE;
circuit-prove/tests/ivc_turn_chain_rotated.rs:225:        other => panic!("a relabeled chain_digest must be refused; got {other:?}"),
circuit-prove/tests/ivc_turn_chain_rotated.rs:227:    whole.chain_digest = honest_digest;
circuit-prove/tests/ivc_turn_chain_rotated.rs:254:/// versioned [`WholeChainProofBytes`] envelope, DESERIALIZES back, and VERIFIES over
circuit-prove/tests/ivc_turn_chain_rotated.rs:269:    let whole: WholeChainProof = prove_turn_chain_recursive(&turns)
circuit-prove/tests/ivc_turn_chain_rotated.rs:276:    let env = WholeChainProofBytes::from_postcard(&bytes).expect("the honest envelope must decode");
circuit-prove/tests/ivc_turn_chain_rotated.rs:296:        &env.chain_digest,
circuit-prove/tests/ivc_turn_chain_rotated.rs:346:        match WholeChainProofBytes::from_postcard(&bad.to_postcard()) {
circuit-prove/tests/ivc_turn_chain_rotated.rs:350:        match WholeChainProofBytes::from_postcard(&[]) {
circuit-prove/tests/ivc_turn_chain_rotated.rs:354:        match WholeChainProofBytes::from_postcard(&bytes[..bytes.len() / 2]) {
circuit-prove/tests/ivc_turn_chain_rotated.rs:361:        match WholeChainProofBytes::from_postcard(&empty_root.to_postcard()) {
circuit-prove/tests/ivc_turn_chain_rotated.rs:559:/// So a GENUINE root for history A, paired with a GENUINE binding proof for a DIFFERENT
circuit-prove/tests/ivc_turn_chain_rotated.rs:560:/// history B (and B's publics), passes all three teeth — a false whole-chain claim
circuit-prove/tests/ivc_turn_chain_rotated.rs:608:    // History B: a DIFFERENT history (different start balance ⇒ different roots/digest),
circuit-prove/tests/ivc_turn_chain_rotated.rs:619:        whole_a.chain_digest, whole_b.chain_digest,
circuit-prove/tests/ivc_turn_chain_rotated.rs:620:        "the two histories are genuinely distinct (different ordered-history digests)"
circuit-prove/tests/ivc_turn_chain_rotated.rs:624:    // publics. Every field is internally consistent (B's binding proof attests B's
circuit-prove/tests/ivc_turn_chain_rotated.rs:630:    forged.chain_digest = whole_b.chain_digest;
circuit-prove/tests/ivc_turn_chain_rotated.rs:643:        "the binding↔root linkage REJECTS a genuine root for history A paired with a \
circuit-prove/tests/ivc_turn_chain_rotated.rs:644:         genuine binding proof for a DIFFERENT history B (the cross-pairing forgery). \
circuit-prove/tests/ivc_turn_chain_rotated.rs:700:    let chain_digest = h1;
circuit-prove/tests/ivc_turn_chain_rotated.rs:701:    let pis = vec![genesis, final_root, BabyBear::new(2), chain_digest];
circuit-prove/tests/ivc_turn_chain_rotated.rs:718:/// `acc_out == hash_4_to_1([acc_in, old, new, idx])`, so a forged `chain_digest` (a
circuit-prove/tests/ivc_turn_chain_rotated.rs:740:    // FORGERY: claim a different chain_digest than the real hash chain. We move the
circuit-prove/tests/ivc_turn_chain_rotated.rs:749:    forged_pis[3] = forged_digest; // chain_digest public
circuit-prove/tests/ivc_turn_chain_rotated.rs:770:        "FINDING #2 CLOSED: a forged chain_digest must be REJECTED by the in-AIR \
circuit-prove/tests/ivc_turn_chain_rotated.rs:854:// THE FIX (codex's ordered segment-accumulator). The separate binding leaf is GONE
circuit-prove/tests/ivc_turn_chain_rotated.rs:858:// the segments (state continuity `L.last_new == R.first_old`, count additivity, ordered
circuit-prove/tests/ivc_turn_chain_rotated.rs:859:// digest `acc = H(L.acc, R.acc)`) up to the root. The root's exposed segment is thus
circuit-prove/tests/ivc_turn_chain_rotated.rs:865:// segment table at the root is the descriptor-derived one. The strongest remaining
circuit-prove/tests/ivc_turn_chain_rotated.rs:871:// the PUBLIC building blocks (`prove_descriptor_leaf_rotated_with_segment` + the segment
circuit-prove/tests/ivc_turn_chain_rotated.rs:874:// THIS is the close of the mixed-root hole.
circuit-prove/tests/ivc_turn_chain_rotated.rs:877:/// Find the instance index of the `expose_claim` (segment) non-primitive table in a
circuit-prove/tests/ivc_turn_chain_rotated.rs:894:// The in-circuit segment digest is the lib's `pub seg_poseidon_commit` (a multi-felt
circuit-prove/tests/ivc_turn_chain_rotated.rs:899:/// Fold history A's GENUINE segment-bearing descriptor leaves into ONE root (the real
circuit-prove/tests/ivc_turn_chain_rotated.rs:900:/// segment-accumulator fold), then carry B's claims to the verifier. The whole-chain
circuit-prove/tests/ivc_turn_chain_rotated.rs:901:/// claim for B must FAIL against a root that executed A — the segment tooth fires because
circuit-prove/tests/ivc_turn_chain_rotated.rs:905:#[ignore = "SLOW: a real segment fold (~minutes); run with --ignored — codex re-review #2 CLOSE"]
circuit-prove/tests/ivc_turn_chain_rotated.rs:910:        ir2_leaf_wrap_config, prove_descriptor_leaf_rotated_with_segment, seg_poseidon_commit,
circuit-prove/tests/ivc_turn_chain_rotated.rs:925:    // History A: the descriptor/execution leaves we fold (the REAL executed history).
circuit-prove/tests/ivc_turn_chain_rotated.rs:927:    // History B: a DIFFERENT history; its CLAIMS are what the forgery carries (so the
circuit-prove/tests/ivc_turn_chain_rotated.rs:937:    // (which is no longer a soundness dependency). B's `chain_digest` here is irrelevant to
circuit-prove/tests/ivc_turn_chain_rotated.rs:938:    // the rejection — the segment tooth fails on B's genesis/final/count already — but we
circuit-prove/tests/ivc_turn_chain_rotated.rs:958:    // B's carried multi-felt digest (irrelevant to the rejection — the segment tooth fails on
circuit-prove/tests/ivc_turn_chain_rotated.rs:960:    let mut b_chain_digest = [BabyBear::ZERO; SEG_DIGEST_WIDTH];
circuit-prove/tests/ivc_turn_chain_rotated.rs:961:    b_chain_digest[0] = b_pis[3];
circuit-prove/tests/ivc_turn_chain_rotated.rs:963:    // ----- The fold: A's REAL segment-bearing descriptor leaves -> one root. -----
circuit-prove/tests/ivc_turn_chain_rotated.rs:967:        let wrapped = prove_descriptor_leaf_rotated_with_segment(
circuit-prove/tests/ivc_turn_chain_rotated.rs:973:        .expect("A's rotated descriptor leaf wraps with its segment");
circuit-prove/tests/ivc_turn_chain_rotated.rs:977:    // Aggregate the segment leaves to ONE root (mirror the lib `aggregate_tree` combine:
circuit-prove/tests/ivc_turn_chain_rotated.rs:978:    // continuity + count additivity + ordered-digest fold, re-exposing the parent segment).
circuit-prove/tests/ivc_turn_chain_rotated.rs:985:            let left_idx = expose_claim_idx(&proofs[i].0).expect("left segment");
circuit-prove/tests/ivc_turn_chain_rotated.rs:986:            let right_idx = expose_claim_idx(&proofs[i + 1].0).expect("right segment");
circuit-prove/tests/ivc_turn_chain_rotated.rs:1029:            .expect("segment aggregation layer");
circuit-prove/tests/ivc_turn_chain_rotated.rs:1045:    // segment tooth reads A's root-exposed segment (= A's genesis/final/count/digest) and
circuit-prove/tests/ivc_turn_chain_rotated.rs:1052:        b_chain_digest,
circuit-prove/tests/ivc_turn_chain_rotated.rs:1057:    eprintln!("[codex-#2 mixed-root] verdict = {verdict:?}  (is_err = CLOSED; is_ok = STILL OPEN)");
circuit-prove/tests/ivc_turn_chain_rotated.rs:1060:    // ordered segment-accumulator binds the root-exposed [genesis, final, num_turns,
circuit-prove/tests/ivc_turn_chain_rotated.rs:1065:         leaves carrying a B whole-chain claim MUST be REJECTED by the segment tooth — A's \
circuit/src/bilateral_aggregation_air.rs:55://! attests that the outer AIR accepted its inputs, and the outer AIR's CG-2
docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md:45:1. **A past witness-cursor.** A point in the recorded history — for dregg, a
docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md:119:in the same history — they are incompatible). A *history* is then any set of
docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md:174:rewrite shared history. It is the operational meaning of *configuration*: a
docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md:251:serve a *slice* of history without the whole). *What is branching-time recursion?* —
docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md:298:- **Comonadic/coalgebraic history views.** "The state-as-seen-with-its-whole-past"
docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md:299:  is a comonad (the *non-empty-list / history comonad*, or the *causal-past*
docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md:314:settled history," but it adds vocabulary without changing the construction, so it is
docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md:372:only entertainable if its claimed history is one the origin could have committed —
docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md:454:(`verify_history`). Willow-style range-reconciliation over the receipt-stream Merkle
docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md:713:attested-fetch + `AttestedRoot` + light-client `verify_history` (`docs/DISTRIBUTED-SERVO.md`
circuit/src/stark.rs:889:/// `proof.trace_commitment`, the trace is provably the one the proof attests
circuit/src/effect_vm/columns.rs:294:    /// transition this proof attests. Row-0-pinned to PI[OWNER_CELL_ID_BASE..+4].
circuit/src/presentation.rs:193:    /// Each temporal proof attests that an attribute satisfied a predicate over
circuit/src/presentation.rs:1025:    /// Each proof attests that an attribute satisfied a predicate over N consecutive
circuit/src/effect_vm/effect.rs:317:    ///   trace and attests "this Burn occupied row X in the cell's
circuit/src/effect_vm/pi.rs:232:/// Single-felt boolean: 1 iff this per-cell proof attests to a
circuit/src/effect_vm/pi.rs:498:// attestations are the dual — a single cell self-attests to a property
circuit/src/effect_vm/pi.rs:603:// #132: OWNER_CELL_ID — the cell whose state transition this proof attests.
circuit/src/membership_adjacency_air.rs:735:    /// about which leaves it attests — the public-input binding rejects.
circuit/src/effect_vm/trace.rs:137:    /// Sovereign-witness teeth (Phase 1): when this proof attests to a
circuit/src/effect_vm/trace.rs:191:    /// this proof attests. Compressed to 4 felts via
docs/deos/DOCUMENT-LANGUAGE.md:17:> *content* is the result of applying its patch-history, transclusion is a verified
docs/deos/DOCUMENT-LANGUAGE.md:47:history as a fold of composable patches, and **conflicts as first-class states**. The two
docs/deos/DOCUMENT-LANGUAGE.md:49:*content-flat* (it is the rendered result, with no patch history of its own — `dregg-doc` is
docs/deos/DOCUMENT-LANGUAGE.md:66:| **the document's content** | the result of **applying the patch-history** (fold the turns from genesis) | yes — `dregg_doc::History::replay`/`replay_to`; content-as-patch-fold is `dregg_doc::content` |
docs/deos/DOCUMENT-LANGUAGE.md:98:  presentations (rendered / source / patch-history / conflict-view) the way Pharo gives an
docs/deos/DOCUMENT-LANGUAGE.md:103:What is *new beyond both*: the document is **patch-theoretic** (its content is a history of
docs/deos/DOCUMENT-LANGUAGE.md:116:another**. If states are objects and patches are morphisms, a repository's history is a path
docs/deos/DOCUMENT-LANGUAGE.md:390:- **`history`** — `History`: `commit`, `replay`/`replay_to` (time-travel), `branch` (fork a
docs/deos/DOCUMENT-LANGUAGE.md:393:  first-class `ConflictRegion` (`Segment::{Clean,Conflict}`, an antichain of ≥2 live
docs/deos/DOCUMENT-LANGUAGE.md:435:  conflict regions, patch-history) that the native cockpit renders — exactly the pattern
docs/deos/DOCUMENT-LANGUAGE.md:437:  where `DreggverseDocumentView` (already built) grows a patch-history and conflict-view
docs/deos/DOCUMENT-LANGUAGE.md:444:  a `Memo` over the patch-history signal; an edit POSTs a patch-turn through
docs/deos/DOCUMENT-LANGUAGE.md:473:| Presentable / Gadget framework | `INSPECTOR-FRAMEWORK.md` (to build) | a document's rendered/source/patch-history/conflict presentations; edit/resolve gadgets. |
docs/deos/DOCUMENT-LANGUAGE.md:486:4. **The patch-history fold = document content** — content as `History::replay`/`replay_to`
docs/deos/DOCUMENT-LANGUAGE.md:549:  - A document's *content* is the patch-history fold (`History::replay`/`replay_to`).
docs/deos/DOCUMENT-LANGUAGE.md:624:- **To the time-travel semantics (same object).** A document's patch-history is a path through
docs/deos/DOCUMENT-LANGUAGE.md:634:  `Provenance` (the patch-history scrubber + the transclusion provenance + the backlinks),
docs/deos/DOCUMENT-LANGUAGE.md:640:  quote to its source, sees "what links here," scrubs the patch-history — *clicking around,
docs/deos/DOCUMENT-LANGUAGE.md:677:patch,merge,history,content,regime,resolve,resolution,doc,depend,blame,threeway,composition,
docs/deos/DOCUMENT-LANGUAGE.md:682:patch history of its own) — `dregg-doc` is the patch layer that produces such a rendering.
metatheory/Polis/PolisAuthCoord.lean:97:membership booleans — `⟨hasOne, hasTwo⟩`. A single agent typically attests only one. -/
metatheory/Polis/PolisAuthCoord.lean:119:/-- **The real verifier**: a witness discharges a requirement iff it attests every required fact. This
metatheory/Polis/PolisAuthCoord.lean:134:/-- **The coalition jointly discharges the goal.** The pooled witness `witX ⊔ witY` attests both
metatheory/README.md:44:| **E** | **Unfoolability** — a light client checking only `verify agg.root` learns A–D for the whole history, re-witnessing nothing | `light_client_verifies_whole_history` (proofs as additive attestation; a reordered chain forces `ChainBound = False`) |
metatheory/README.md:99:`RecursiveAggregation`: checking one aggregate root attests the whole history). The whole
metatheory/Polis/PolisNonConfusion.lean:45:shown a forged history" — IS the deployed `unfoolability_guarantee` (whole-history
docs/deos/GRAPHIDEOS.md:59:| **The app model (APK · Activity · Service · ART)** | a per-app silo with its own process, lifecycle, and ambient permissions | **a cell** — a sovereign cell (or cell-subgraph) whose mutations are turns and whose history is a receipt chain; a "native" deos app is a cell, a **foreign APK runs as an android-cell** (the confined portal) | `cell/src/cell.rs`; `APPS-AS-CELLS.md`; `ANDROID-CELL.md` |
metatheory/docs/SOUNDNESS-RESIDUAL-CENSUS.md:86:- **Authority §6 whole-history closure** is a real proof (`Spec/Authority.lean:456`, all 4
metatheory/docs/SOUNDNESS-RESIDUAL-CENSUS.md:106:| S1 | Authority §6 whole-history closure | — proven; `:434` "OPEN" comment STALE | STALE-LABEL / DONE | (fix comment) | `Spec/Authority.lean:456,569` |
docs/deos/HYPERDREGGMEDIA-NOTES.md:37:| **Notion** | **Everything is a block** — one recursive composable draggable primitive. | Lego for software; the composable everything-app. | Blocks are rows in *their* Postgres; a block is a record, not a programmable object you own. | Every block is a **cell you own** — programmable (its own `run_js`), cap-bearing, with verifiable history. Composability that bottoms out in *sovereignty*. |
docs/deos/HYPERDREGGMEDIA-NOTES.md:61:the one before, so the whole life of this tool is a navigable causal history you can **rewind**
docs/deos/HYPERDREGGMEDIA-NOTES.md:155:provenanced transclusion, code-as-patch-history, renderer-independence, desktop-as-document.
metatheory/docs/DISCARD-CANDIDATES.md:28:`HARVEST-KEEPERS.md`. The remaining body is per-paper narrative + refuted-claim history that git
docs/deos/FIRST-CLASS-REVERSIBILITY.md:4:the history is a reversible computation with islands of deliberate, correct
docs/deos/FIRST-CLASS-REVERSIBILITY.md:18:> **A reversible system is one where the history is a navigable, undoable object:
docs/deos/FIRST-CLASS-REVERSIBILITY.md:19:> every effect has an inverse (the *un-turn*), a stretch of history can be rolled
docs/deos/FIRST-CLASS-REVERSIBILITY.md:78:  the inverse needs the pre-image, which the *reversible-history object* (§3.2)
docs/deos/FIRST-CLASS-REVERSIBILITY.md:79:  carries. These reverse against the history that produced them.
docs/deos/FIRST-CLASS-REVERSIBILITY.md:83:### 1.2 A history is reversible along its causal links — and consent is the cap-gate
docs/deos/FIRST-CLASS-REVERSIBILITY.md:104:So reversing a stretch of history is: walk the causal cone forward-most-first,
docs/deos/FIRST-CLASS-REVERSIBILITY.md:106:the forward turn needed. The history reverses *exactly as far as the caps reach*,
docs/deos/FIRST-CLASS-REVERSIBILITY.md:132:`starbridge-v2/src/replay.rs` is a *verified* navigation of history:
docs/deos/FIRST-CLASS-REVERSIBILITY.md:202:Three constructions: the substrate-wide `Effect::invert`; the reversible-history
docs/deos/FIRST-CLASS-REVERSIBILITY.md:240:### 3.2 The reversible-history object — `ReversibleHistory`
docs/deos/FIRST-CLASS-REVERSIBILITY.md:242:`History` (`replay.rs`) records steps and roots. The reversible-history object adds
docs/deos/FIRST-CLASS-REVERSIBILITY.md:296:   RevokeCapability-of-content) are sound *only against the history that produced
docs/deos/FIRST-CLASS-REVERSIBILITY.md:298:   undo-on-its-own-history path* — but a *free-standing* inverse effect applied to a
docs/deos/FIRST-CLASS-REVERSIBILITY.md:319:   region, clearly not claiming to rewrite history.
docs/deos/FIRST-CLASS-REVERSIBILITY.md:401:the reversal; the live image *is* the history. A reversible OS is one where you can
docs/deos/FIRST-CLASS-REVERSIBILITY.md:431:   for a fixture history of clean turns, `undo_to(k)` lands on the *identical verified
docs/deos/FIRST-CLASS-REVERSIBILITY.md:433:   fail-closed test: a history with a `Burn` or `NoteSpend` refuses to `undo_to` past
metatheory/docs/JOY-PATH-ROOMS.md:93:card's `view_source` document (`ProgramSource`, a `dregg_doc::Doc` patch-history,
metatheory/docs/JOY-PATH-ROOMS.md:222:   appends to a `ProgramSource` patch-history and carries blame per view line
docs/deos/DOC-CELL-COMPOSITION.md:57:  *subtree*. The child has its own atoms, its own caps, its own patch history,
docs/deos/DOC-CELL-COMPOSITION.md:207:embed-atom, instead of pushing `Segment::Clean(text)` it pushes a
docs/deos/DOC-CELL-COMPOSITION.md:208:`Segment::Embedded(resolved)` where `resolved` is the **child cell rendered
docs/deos/DOC-CELL-COMPOSITION.md:219:    emit Segment::Embedded { role: E.role, provenance: E.provenance, child }
docs/deos/DOC-CELL-COMPOSITION.md:535:   emits `Segment::Embedded` for embed-atoms. *(prototype)*
docs/deos/DOC-CELL-COMPOSITION.md:569:already is**, given a patch history and a conflict semantics. Two consequences:
docs/deos/DOC-CELL-COMPOSITION.md:738:content,merge,regime,history,doc,commit,substrate}.rs` (the full patch core —
docs/deos/CROSS-DEVICE-FIRMAMENT.md:259:  (`wasm/src/bindings_lightclient.rs::verify_history` — folds a finalized history
docs/deos/HUMAN-LAYER.md:69:  KERI KEL shape) — an auditable history of every rotation.
docs/deos/DURABLE-WORKFLOW.md:62:  history is never rewritten (the audit trail is append-only, tamper-evident).
metatheory/docs/CODEX-IVC-SEGMENT-ACCUMULATOR-DESIGN.md:1:# Codex design — the ordered segment-accumulator fix for the IVC mixed-root hole (2026-06-24)
metatheory/docs/CODEX-IVC-SEGMENT-ACCUMULATOR-DESIGN.md:3:Codex's recommended construction (gigabrain advice, not a review): close the mixed-root forgery by making the whole-chain claim sound-BY-CONSTRUCTION — a constant-size ordered segment accumulator carried by every descriptor leaf + each aggregation node, replacing the separate binding leaf in the soundness-critical path.
metatheory/docs/CODEX-IVC-SEGMENT-ACCUMULATOR-DESIGN.md:26:HORIZONLOG.md:4596:- ⚑ THE MISSING WELD (the single highest-leverage edit on the board): the multi-turn IVC / finalized-history /
docs/deos/SCRIPTING-AND-DISTRIBUTED-DOM.md:270:to history), and the data-plane Bus is the live delivery spine. `deos-matrix` is a **client/bridge**
metatheory/docs/DREGG-CALCULUS.md:459:surfaces antichains as `Segment::Conflict` for prose resolution.
metatheory/docs/DREGG-CALCULUS.md:583:- **A rehydrated context IS a turn history.** `replayedDeterministic_iff_confined`
docs/deos/HERMES-INTEGRATION.md:221:full-history posture; submodules would dangle). The breadstuffs repo is
docs/deos/DREGG-MUD.md:28:| **room** | a `Cell` (its contents/exits = state + c-list; its history = receipt chain) | `cell/src/cell.rs`, room-as-cell `deos-matrix/src/cell.rs:70` (`RoomCell`) |
docs/deos/DREGG-MUD.md:59:- The room's **history is its provenance chain** — every turn committed against the
docs/deos/DREGG-MUD.md:64:  history is the cell's turn history."
docs/deos/RECOVERY-SYSTEM.md:29:  history where one party held the whole secret. (Dealerless variants exist but
docs/deos/RECOVERY-SYSTEM.md:174:  committee the **state itself attests**, removing the host as a trust anchor.
docs/deos/UMEM-PRIMITIVE.md:169:  boundary IS the state* — instead of O(history) genesis replay. `History` captures
docs/deos/UMEM-PRIMITIVE.md:350:a merge failure"* (`lib.rs:7`; `ConflictRegion`/`Segment::Conflict`, each `Alternative` tagged
docs/MANUAL/USER.md:158:its history. The past is **cryptographically the same past for every observer** —
docs/MANUAL/USER.md:159:not a local undo buffer, a shared verified history.
docs/deos/HYPERDREGGMEDIA.md:120:  independence) · the document language at full fidelity (the patch-history living *in* the cell,
docs/deos/UMEM-CROSS-REVIEW.md:56:  - time-travel: a snapshot IS a boundary, rewind IS restoring it — no O(history) replay
metatheory/docs/ORPHANED-CAPABILITIES-CENSUS.md:155:| `reversible.rs` | **PARTIAL** | turn/src/reversible.rs | un-turn / RCCS inverse algebra (`Effect::invert`, ReversibleHistory) | **cockpit-alive**: `starbridge-v2/src/history_lens.rs`, `time_travel.rs` drive `Inversion`/undo as a UI feature — but **NO live `Effect` triggers a reverse turn in the protocol**; the inverse is a UI/audit algebra, not a kernel verb | to make reversal a *protocol* capability: an `Effect::Reverse` the executor + circuit witness (~L). As a cockpit feature it is already alive. |
metatheory/docs/ORPHANED-CAPABILITIES-CENSUS.md:265:| `verify_history` / `verify_finalized_history` / `fold_and_attest` | **ALIVE-WIRED** | lightclient/src/lib.rs | served via `sdk/src/lib.rs` re-export, wasm bindings (`wasm/src/bindings_lightclient.rs`), and the demo binary; recursive-STARK verify, VK-anchor pin, quorum check; non-vacuous tests with rejection teeth | — |
docs/MANUAL/DEVELOPER.md:60:  history — and recursive aggregation folds a whole history into one root a
docs/MANUAL/DEVELOPER.md:63:  integrity + freshness for the entire history, re-witnessing nothing.
docs/deos/BOOLEAN-MATCHING-REGROUND.md:142:  only if prior history matched B," a lookahead = "...only if a continuation
docs/deos/HIG.md:6:folders, permissions hidden in dialogs, history gone the instant you act. The genius
docs/deos/HIG.md:10:history. So the deos interface does **not** paste a metaphor over the machine. It shows
docs/deos/HIG.md:21:object, the real authority, the real action, the real history.
docs/deos/HIG.md:38:- **Reflection is one GESTURE.** Flip any cell around → its faces (state · history ·
docs/KERNEL.md:36:the abstract `Core.conservation_step` from `Dregg2.Exec.cexec_attests`
docs/KERNEL.md:37:(`Dregg2/Exec/StepComplete.lean:75`), which proves the executable machine attests all four
docs/KERNEL.md:68:  authorized generator; the whole-history closure is
docs/KERNEL.md:86:roots. Over the whole history this is
docs/KERNEL.md:87:`Dregg2.Circuit.light_client_verifies_whole_history`
docs/KERNEL.md:109:  root, cannot be shown a forged history.
docs/deos/SURFACE-MIGRATION.md:210:caps, and its history untouched and a verifiable receipt behind. "Where it runs"
docs/deos/MACRO-AS-CUSTOM-VK.md:48:            its WitnessedPredicate attests the composed execution;
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:29:  proof** (`WholeChainProof`) using **real plonky3 in-circuit FRI recursion** (the
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:32:- It is consumed by the **live light client**: `lightclient/src/lib.rs::verify_history`
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:34:  learns the whole history is correct/ordered/genuinely-folded.
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:36:  (`light_client_verifies_whole_history`, sorry-free, `#assert_axioms`-clean ⊆
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:39:  `RecursiveVerifierSound`) into `WellFormedChain` whole-history attestation.
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:41:**This is Mina-Pickles-shaped: a succinct proof that attests a whole chain, verified by
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:75:- **`lightclient/src/lib.rs::verify_history`** (line 147, calls
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:77:  of N, reads off the genuine `genesis_root → final_root` + `chain_digest`. This IS
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:81:  sorry-free, axiom-clean). `light_client_verifies_whole_history` (line ~169) +
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:85:  `AggregateAttests`. The three engine hypotheses (`EngineSound`, line 115) are
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:127:  shape into the node leg. ADDITIVE, NOT live-wired (Lean self-attests this).
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:129:**Answer to "what does one light-client check cover?":** at the whole-history level, a
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:130:single `verify_history` covers a WHOLE K-turn chain (axis A). At the turn level, a single
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:142:| Is the per-turn proof recursive (turn-proof attests prior turn-proof)? | **NO** at the per-turn layer — proofs are independent per-turn; the receipt chain threads a `previous_receipt_hash` ([u8;32] HASH, not a proof). Recursion lives in the SEPARATE `ivc_turn_chain` accumulator layer that folds N already-finalized turns. | `turn/src/witnessed_receipt.rs` (hash link), `turn/src/verify.rs` (hash-chain verify), vs `circuit-prove/src/ivc_turn_chain.rs` (the recursive fold) |
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:193:- Archived `STAGE-7-GAMMA-AGGREGATION-DESIGN.md` (deleted from `docs-history/` per git
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:196:  are design history, not the current state.
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:204:| Succinct proof of the whole chain, verified by a light client in constant work | `lightclient::verify_history` over `WholeChainProof` | **MATCHED, LIVE** |
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:206:| Each leaf proof attests genuine state transition | leaf = REAL Lean-descriptor turn circuit, executor-sound per-effect (`WholeTurnTriangle`) | **MATCHED + Lean-proven** |
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:232:   not research. This converts `WholeChainProof` from "sound under VK-pin + carried binding"
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:258:  fold is LIVE-WIRED (`ivc_turn_chain` → `lightclient::verify_history`) and Lean-proven
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:266:  `ivc_turn_chain`) already lifts this to a **whole-history** light-client attestation in
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:288:  (already deleted from `docs-history/` per git status) — ASPIRATIONAL-SKETCH of the OLD
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:290:  design history; ensure no live doc cites them as current state.
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:306:| Live light-client whole-history check | `lightclient/src/lib.rs::verify_history` (line 147) | ALIVE-WIRED |
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:307:| Lean recursive-aggregation soundness | `Dregg2/Circuit/RecursiveAggregation.lean::light_client_verifies_whole_history` (~169); `EngineSound` (115) | ALIVE-WIRED (proven, sorry-free) |
docs/deos/MOBILE-DEOS.md:166:  the affordances you hold caps for (lit), the faces (state · history · caps ·
docs/deos/MOBILE-DEOS.md:185:  history face.
docs/design-frontiers/AGENT-SWARM-UX.md:28:shows its held mandate, its receipted action history, its budget meter, and its
docs/design-frontiers/AGENT-SWARM-UX.md:214:and carries the refusal reason. This is the swarm's grounded seam history — the
docs/deos/RESHARING-CHAINS.md:174:A **configuration** is then a coherent prefix-plus-branches of resharing history: a
docs/deos/RESHARING-CHAINS.md:252:commitment stream + CR pins the entire *key history* (no alternative admitted history exists under
docs/deos/RESHARING-CHAINS.md:254:checks pin the entire *share-lineage* (no alternative `f(0)`-preserving history exists under the
docs/deos/RESHARING-CHAINS.md:255:same anchors). Both are "the public commitment chain forces the private history" — one for signing
docs/deos/RESHARING-CHAINS.md:271:genesis with zero share knowledge — the D-side of KERI's commitment-pinned key history — and this
docs/deos/RESHARING-CHAINS.md:373:> signing-key history by a public commitment chain so that compromising the current key cannot
docs/deos/RESHARING-CHAINS.md:375:> history by a public anchor chain so that compromising the current shares cannot reveal the past
docs/design-frontiers/ADOS.md:33:history) cannot fool the operator at the glass: the receipt chain and the
docs/design-frontiers/ADOS.md:256:drift): the **blocklace** panel (the receipt chain as a navigable causal history
docs/design-frontiers/ADOS.md:381:   The blocklace panel lets you time-travel the causal history. **This is what
docs/deos/SHARED-FORK-CONSENT.md:175:The guest's embedded turns accumulate as the fork's own history — a divergent
docs/deos/INSPECTOR-FRAMEWORK.md:50:    Timeline(TimelineView),              // ordered events (receipt chain, epoch history, attenuation).
docs/deos/INSPECTOR-FRAMEWORK.md:72:- **Provenance** ← "receipt chain", "attenuation lineage", "transfer history", "causal history scrubber", "epoch history", "create-spend lifecycle".
docs/deos/INSPECTOR-FRAMEWORK.md:189:| Asset (issuer-cell) | RF, DV(ledger/holders), G(transfer history), PV, IV(conservation Σδ=0) | Transfer Composer (commit), Mint Gating (commit), Burn Disclosure (commit) | **P** (balance) |
docs/deos/INSPECTOR-FRAMEWORK.md:297:| MacaroonToken | RF(root), PV(attenuation history), RF(discharge) | Root Minter, HMAC Replayer (verifier), Attenuation Chain | **N** |
docs/deos/INSPECTOR-FRAMEWORK.md:313:| FinalityLevel | DV(ladder), PV(history) | Finality Threshold Dial | **N** |
docs/deos/INSPECTOR-FRAMEWORK.md:328:| DKG / Epoch | DV(progress), PV(epoch history) | DKG Sim, Epoch Planner | **N** |
docs/design-frontiers/PG-DREGG-DX.md:317:total), per-cell time-travel (`cell_history` by `(id, ordinal)`), the receipt-chain
docs/design-frontiers/PG-DREGG-DX.md:325:history with one deliberate amplification for the audit to catch), and
metatheory/docs/CODEX-BUS-BALANCE-FIX.md:3:ROOT CAUSE (codex, the expose_claim bus designer): the W24 segment-digest expose_claim READS (mult=-1) have NO matching WRITES (mult=+1) in the aggregation child proof, because the W24 poseidon2_perm/baby_bear_d4_w24 table (whose output CTL emits the +1 writes) is registered at the LEAF layer but MISSING from the AGGREGATION layer's proof construction (only the W16 challenger + expose_claim are registered there). -> WitnessChecks global cumulative != 0 -> native verify_all_tables rejects GlobalCumulativeMismatch.
metatheory/docs/CODEX-BUS-BALANCE-FIX.md:8:## The invariant (per proof carrying the segment)
metatheory/docs/CODEX-BUS-BALANCE-FIX.md:9:- child segment values: PublicAir +1, expose_claim -1
metatheory/docs/CODEX-BUS-BALANCE-FIX.md:13:The bus does NOT carry upward — each aggregation layer re-exposes a new segment (new readers) needing new same-proof writers.
metatheory/docs/CODEX-IVC-REVIEW-2.md:3:VERDICT: the exposed-claim channel is SOUND (the old forgery rejects), but #1 NOT fully closed — a DEEPER mixed-root hole remains.
metatheory/docs/CODEX-IVC-REVIEW-2.md:15:1. valid descriptor leaves for history A, from the independent descriptor wrapping path at [ivc_turn_chain.rs:1300](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1300)
metatheory/docs/CODEX-IVC-REVIEW-2.md:16:2. a valid binding leaf for history B, wrapped with exposed claims at [ivc_turn_chain.rs:1313](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1313)
metatheory/docs/CODEX-IVC-REVIEW-2.md:25:- tooth 3: mixed root verifies: [ivc_turn_chain.rs:1537](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1537)
metatheory/docs/CODEX-IVC-REVIEW-2.md:41:The flipped test at [ivc_turn_chain_rotated.rs:595](/Users/ember/dev/breadstuffs/circuit-prove/tests/ivc_turn_chain_rotated.rs:595) covers only the old external cross-pairing shape. It does not cover the mixed-root attack above. I would add a test that constructs descriptor leaves from A, binding leaf from B, aggregates them into one root, carries B’s binding proof/claims, and asserts rejection. I expect current code to accept unless there is another cross-leaf equality constraint outside the reviewed paths.
metatheory/docs/CODEX-IVC-REVIEW-2.md:54:1. valid descriptor leaves for history A, from the independent descriptor wrapping path at [ivc_turn_chain.rs:1300](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1300)
metatheory/docs/CODEX-IVC-REVIEW-2.md:55:2. a valid binding leaf for history B, wrapped with exposed claims at [ivc_turn_chain.rs:1313](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1313)
metatheory/docs/CODEX-IVC-REVIEW-2.md:64:- tooth 3: mixed root verifies: [ivc_turn_chain.rs:1537](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1537)
docs/design-frontiers/WEB-FORWARD.md:23:in the tab, the `dregg-lightclient` already verifies a whole finalized history
docs/design-frontiers/WEB-FORWARD.md:61:2. **dregg already verifies in the tab.** `dregg-lightclient`'s `verify_history`
docs/design-frontiers/WEB-FORWARD.md:62:   checks ONE recursive `WholeChainProof` against a VK trust-anchor and reads off
docs/design-frontiers/WEB-FORWARD.md:63:   the bound commitments — re-witnessing nothing, cost independent of history
docs/design-frontiers/WEB-FORWARD.md:65:   whole finalized history evolved correctly. The unfoolability theorem
docs/design-frontiers/WEB-FORWARD.md:67:   `Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history`) has
docs/design-frontiers/WEB-FORWARD.md:152:│     dregg-lightclient::verify_history(root, vk_anchor) → AttestedHistory;    │
docs/design-frontiers/WEB-FORWARD.md:153:│     the tab independently confirms the whole finalized history. The state-   │
docs/design-frontiers/WEB-FORWARD.md:202:> `verify_history` against the devnet root and prints `AttestedHistory ✓ (N
docs/design-frontiers/WEB-FORWARD.md:204:> verified history, and he confirmed it himself.
docs/design-frontiers/WEB-FORWARD.md:210:DOM), the dark-on-revoke (the `n=1` collapse), the whole-history verify
docs/design-frontiers/WEB-FORWARD.md:243:3. **Verify, yourself.** Run `verify_history` against the devnet root (W4). The
docs/design-frontiers/WEB-FORWARD.md:244:   tab confirms the whole finalized history with no re-execution. *You did not
docs/design-frontiers/WEB-FORWARD.md:284:`verify_history` confirms a whole finalized history from one succinct aggregate
docs/design-frontiers/WEB-FORWARD.md:290:> the light client attests (chains to a finalized root she verified), and that
docs/design-frontiers/WEB-FORWARD.md:431:**S4 — `verify_history` in the tab (W4, the anti-pale-ghost tooth).** Compile
docs/design-frontiers/WEB-FORWARD.md:432:`dregg-lightclient`'s `verify_history` to wasm (it depends only on
docs/design-frontiers/WEB-FORWARD.md:434:`verify_devnet_history(root, vkAnchor) -> AttestedHistory` from the wasm module;
docs/design-frontiers/WEB-FORWARD.md:435:add the "verify the whole history yourself" button to the explorer (W6) and the
docs/design-frontiers/WEB-FORWARD.md:441:*Byte path CLOSED (§7).* The over-wire seam — a `WholeChainProof` had no serde
docs/design-frontiers/WEB-FORWARD.md:444:versioned `WholeChainProofBytes` envelope (`WholeChainProof::to_bytes()`), and
docs/design-frontiers/WEB-FORWARD.md:445:`dregg_lightclient::verify_history_bytes` runs the three teeth over the decoded
docs/design-frontiers/WEB-FORWARD.md:446:bytes. The wasm `produce_external_history_envelope` fills `proof_bytes_b64` and
docs/design-frontiers/WEB-FORWARD.md:447:`verify_devnet_history` decodes + verifies it for real (no longer a reported
docs/design-frontiers/WEB-FORWARD.md:485:- **The light client** — `dregg-lightclient::verify_history`: whole-history
docs/design-frontiers/WEB-FORWARD.md:521:whole history re-witnessing nothing, and paints surfaces that are the genuine
metatheory/docs/guides/executor.md:111:  authority-turn forward-simulation squares (single-cell complete; cross-cell whole-history closure
metatheory/docs/POLIS-HYPERPROPERTY-FRONTIER.md:124:  interleaved* turns — `Proof/ContendedCrossCell.lean`, the cross-cell whole-history OPEN), the
metatheory/docs/POLIS-HYPERPROPERTY-FRONTIER.md:127:  interleaved-multi-agent hyperproperty is *the same object* as the cross-cell whole-history
metatheory/docs/POLIS-HYPERPROPERTY-FRONTIER.md:158:   **`CoinductiveAdversary` / adversary-stream confluence** object (the cross-cell whole-history
metatheory/docs/POLIS-HYPERPROPERTY-FRONTIER.md:171:is the same object as the cross-cell whole-history adversary-stream confluence, so one proof serves
docs/design-frontiers/UNIFYING-STORY.md:54:  for the whole history (the *pale ghost on the wire*).
docs/design-frontiers/UNIFYING-STORY.md:199:the whole history evolved correctly — it cannot be fooled by the pale ghost. The
metatheory/docs/CODEX-IVC-REVIEW-3.md:1:# Codex re-review #3 — the segment-accumulator close + the weak-digest deviation (2026-06-24)
metatheory/docs/CODEX-IVC-REVIEW-3.md:3:VERDICT: PARTIAL CLOSE. Distinct-endpoint mixed-root forgery genuinely REJECTED (structural). But the digest deviation (base-field fold instead of codex's specified collision-resistant commitment) is a REAL soundness downgrade for same-endpoint/same-count histories — and it's ALGEBRAICALLY broken, not merely 31-bit.
metatheory/docs/CODEX-IVC-REVIEW-3.md:5:**Verdict: partial close.** The original mixed-root forgery with different genesis/final/count is closed in the K-fold path. The root proof exposes the descriptor-derived segment, and the verifier compares it to the carried claim at [ivc_turn_chain.rs:1757](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1757). So if A and B differ in genesis, final, or count, the rejection does not depend on the digest.
metatheory/docs/CODEX-IVC-REVIEW-3.md:11:1. **High: same-endpoint history binding is only the weak `acc` lane.**  
metatheory/docs/CODEX-IVC-REVIEW-3.md:12:   Leaf segments expose only `[old, new, 1, H(old,new)]` from PI 42/43 at [ivc_turn_chain.rs:1059](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1059). Aggregation exposes only `[first_old, last_new, count, acc]` at [ivc_turn_chain.rs:1632](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1632). The verifier does not pin intermediate roots independently; it checks only the folded root segment. The carried binding proof is explicitly ignored at [ivc_turn_chain.rs:1724](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1724).
metatheory/docs/CODEX-IVC-REVIEW-3.md:19:   Removing the swappable binding leaf from the soundness path was necessary. But now the only K-fold ordered-history commitment is the weak segment `acc`. The old Poseidon `TurnChainBindingAir` still exists and really constrains its digest at [ivc_turn_chain.rs:613](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:613), but it is no longer verified in the K-fold verifier.
metatheory/docs/CODEX-IVC-REVIEW-3.md:22:   [accumulator.rs:39](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:39) explicitly says the online accumulator still uses a separate binding leaf and retains the mixed-root structural weakness. Scope the close to the balanced K-fold path only.
metatheory/docs/CODEX-IVC-REVIEW-3.md:27:**Bottom line:** distinct-endpoint mixed-root forgery is genuinely rejected. Full ordered-history soundness is not achieved. Same-endpoint/same-count histories rely on a one-felt, algebraically weak digest; if an attacker can realize colliding intermediate roots as valid executions, a proof of A can stand in for B’s middle history. The fix should replace `seg_hash2_*` with an in-circuit collision-resistant multi-felt commitment, and the root claim should carry that wider digest.
metatheory/docs/CODEX-IVC-REVIEW-3.md:29:**Verdict: partial close.** The original mixed-root forgery with different genesis/final/count is closed in the K-fold path. The root proof exposes the descriptor-derived segment, and the verifier compares it to the carried claim at [ivc_turn_chain.rs:1757](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1757). So if A and B differ in genesis, final, or count, the rejection does not depend on the digest.
metatheory/docs/CODEX-IVC-REVIEW-3.md:35:1. **High: same-endpoint history binding is only the weak `acc` lane.**  
metatheory/docs/CODEX-IVC-REVIEW-3.md:36:   Leaf segments expose only `[old, new, 1, H(old,new)]` from PI 42/43 at [ivc_turn_chain.rs:1059](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1059). Aggregation exposes only `[first_old, last_new, count, acc]` at [ivc_turn_chain.rs:1632](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1632). The verifier does not pin intermediate roots independently; it checks only the folded root segment. The carried binding proof is explicitly ignored at [ivc_turn_chain.rs:1724](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1724).
metatheory/docs/CODEX-IVC-REVIEW-3.md:43:   Removing the swappable binding leaf from the soundness path was necessary. But now the only K-fold ordered-history commitment is the weak segment `acc`. The old Poseidon `TurnChainBindingAir` still exists and really constrains its digest at [ivc_turn_chain.rs:613](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:613), but it is no longer verified in the K-fold verifier.
metatheory/docs/CODEX-IVC-REVIEW-3.md:46:   [accumulator.rs:39](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:39) explicitly says the online accumulator still uses a separate binding leaf and retains the mixed-root structural weakness. Scope the close to the balanced K-fold path only.
metatheory/docs/guides/distributed.md:11:> git history). The Lean `file:line` pointers below remain valid; line numbers drift between commits
metatheory/docs/guides/distributed.md:20:predecessors (the DAG = the causal history), and a Cordial-Miners-style wave protocol + Stingray
metatheory/docs/HARVEST-KEEPERS.md:4:strata, so those source files can be discarded (they live in git history) without losing anything we
docs/OVERVIEW.md:3:A light client holding one root knows every transition in the whole history was
docs/OVERVIEW.md:36:  checking only a succinct root — learns the whole history is genuine
docs/OVERVIEW.md:40:  capability, history is the receipt chain, sharing is a cap-confined membrane. The
metatheory/docs/guides/authority.md:11:> removed (it lives in git history). The Lean `file:line` pointers below remain valid; line numbers
metatheory/docs/DA-MESH-AUDIT.md:7:check that a commitment is the honest fold of a real history (`lightclient/src/lib.rs`,
metatheory/docs/DA-MESH-AUDIT.md:8:`verify_history`/`verify_finalized_history`). But verifiable ≠ **AVAILABLE**: can the client actually
metatheory/docs/DA-MESH-AUDIT.md:152:- **VERIFIABLE — DONE.** `lightclient/src/lib.rs` gives a light client whole-history attestation
metatheory/docs/DA-MESH-AUDIT.md:153:  (`verify_history`) + finality (`verify_finalized_history`) from one succinct proof + a quorum cert,
metatheory/docs/CELL-PROGRAM-LANGUAGE.md:128:causal/history-dependent guards that read the trace (`RelPred.eval` is a function of the post-record
docs/desktop-os-research/SEL4-RENDER-PATH.md:317:new seL4 capability: the `aarch64-sel4-roottask-musl` target links `--no-rosegment`,
docs/desktop-os-research/SEL4-RENDER-PATH.md:326:[render-pd] JIT W->X arena: 16384 KiB static RWX (--no-rosegment image)
docs/desktop-os-research/SEL4-RENDER-PATH.md:472:  success on the `--no-rosegment` already-X image). This is the one genuinely-new OS
metatheory/docs/FRONTIERS-BEYOND-DEOS.md:16:`sortition_select`, `verify_history`, or any `bridge::{ethereum,mina,midnight}`
metatheory/docs/FRONTIERS-BEYOND-DEOS.md:211:  `lightclient/src/lib.rs`: `verify_history` (`:147-162`, three teeth: VK-anchor
metatheory/docs/FRONTIERS-BEYOND-DEOS.md:213:  `verify_finalized_history` (`:357-396`, + root-seam + 2n/3+1 quorum). Reached
metatheory/docs/FRONTIERS-BEYOND-DEOS.md:215:  `whole_history_demo` binary — but **zero `node/src/` callers** (verified). A
metatheory/docs/FRONTIERS-BEYOND-DEOS.md:216:  node does not call `verify_history`; the trust boundary is external.
metatheory/docs/FRONTIERS-BEYOND-DEOS.md:219:  `light_client_verifies_whole_history` and
metatheory/docs/FRONTIERS-BEYOND-DEOS.md:221:  `light_client_accepts_finalized_history` are gap-free theorems with anti-ghost
docs/desktop-os-research/FRUSTUM-REPLAY-MEMBRANE.md:33:  tamper-evidence rules out an *adversary substituting* a divergent history; determinism
docs/desktop-os-research/FRUSTUM-REPLAY-MEMBRANE.md:68:   *different* history. This is `chain_tamper_evident` under the §8 digest oracle. It defends
docs/desktop-os-research/FRUSTUM-REPLAY-MEMBRANE.md:223:> authority is the meet of the *whole* ask-history with the *original* ceiling, a single
docs/desktop-os-research/FRUSTUM-REPLAY-MEMBRANE.md:230:Together: the chain neither exceeds nor depends-on-its-history — the two ways drift could
metatheory/docs/INTENT-FLUIDITY-AUDIT.md:268:the soundness theorem `recCexec_attests` (`:815`) *demands* `s'.log = t :: s.log`.
metatheory/docs/INTENT-FLUIDITY-AUDIT.md:326:`turn/`: `lib.rs:181` re-exports the names; the cockpit's `history_lens.rs` uses
metatheory/docs/INTENT-FLUIDITY-AUDIT.md:328:calls `effect.invert(pre)` at `history_lens.rs:98` to *label* changes, never to
metatheory/docs/INTENT-FLUIDITY-AUDIT.md:331:(`cockpit/panels_main.rs:886` → `history_lens::CellReversibility::from_world`),
metatheory/docs/INTENT-FLUIDITY-AUDIT.md:334:### The document merge/stitch (`dregg-doc/src/merge.rs`, `history.rs`) — substrate LIVE, merge PROVEN-DISCONNECTED
metatheory/docs/INTENT-FLUIDITY-AUDIT.md:339:of `History::stitch`/`merge` (`history.rs:95`/`merge.rs:30`) is a test, demo, or
metatheory/Metatheory/ResharingChain.lean:11:  > COMMITMENT chain pins the key history). A resharing chain gives forward-secure COMMITTEE SECRETS
metatheory/Metatheory/ResharingChain.lean:119:"the committed key history is pinned" — here the recoverable VALUE is pinned while the carrier
metatheory/Metatheory/ResharingChain.lean:254:history contains both re-randomizations. This is the structural reason a fork must be STITCHED OR
metatheory/Metatheory/ResharingChain.lean:287:line has no conflict). So "the secret's history up to epoch `k`" is a genuine time-travel
metatheory/Metatheory/ResharingChain.lean:304:    quantity is the SIGNING-key history (`rotChain_pinned_by_commitments`);
metatheory/Metatheory/ResharingChain.lean:306:    (`forward_blind`), the protected quantity is the COMMITTEE-secret history
metatheory/docs/POLIS.md:45:| Foundational anti-Mythos floor (no forged history) | pin of `unfoolability_guarantee` |
metatheory/Metatheory/ConstructiveKnowledge.lean:353:step really attests its full invariant) is what makes the coinduction *productive* rather
metatheory/Metatheory/ConstructiveKnowledge.lean:366:(what it attests to know at a state). If the knower is **step-complete** (every transition
metatheory/Metatheory/ConstructiveKnowledge.lean:367:attests the full `StepInv = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance` — the
metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md:9:   **Attack:** take a valid recursive root proof for history A with the expected root VK shape, pair it with a separately valid binding proof claiming history B/endpoints/digest. The final verifier has no in-band equality tying those objects together, so false whole-chain claims can verify.
metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md:13:   **Attack:** produce a binding proof for arbitrary `chain_digest` and arbitrary `num_turns` by choosing accumulator columns that satisfy only the carry constraints. This breaks the claimed ordered-history commitment even before considering recursion.
metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md:40:   `EngineSound` assumes recursive soundness, positional leaf-to-step pairing, and binding soundness at [RecursiveAggregation.lean](/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/RecursiveAggregation.lean:115). The unbounded accumulator stores a `leanWitness` directly at [RecursiveAggregation.lean](/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/RecursiveAggregation.lean:487), and `acc_attests_whole_history` is just projection at [RecursiveAggregation.lean](/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/RecursiveAggregation.lean:628).  
metatheory/docs/NAVIGATION.md:4:> **harvested and removed** (it lives in git history). Its still-wanted content was lifted into
metatheory/Dregg2/Spec/JointViaHyper.lean:24:     participant pre-state, so *canonicity* (which valid history wins a double-spend) is a
metatheory/Dregg2/Spec/JointViaHyper.lean:177:becomes THE history (a double-spend resolution) — is a SEPARATE obligation. We make
metatheory/Dregg2/Spec/JointViaHyper.lean:396:This is the faithful meaning of "ONE root proof attests all `N` legs": the root accepts iff every
metatheory/Dregg2/Spec/JointViaHyper.lean:414:/-- The multiset of leaves of an aggregation tree (the bundle it attests). -/
metatheory/Dregg2/Spec/JointViaHyper.lean:471:/-- **`recursive_agg_constant_shape` — the root attests the WHOLE bundle regardless of tree shape
metatheory/Dregg2/Spec/JointViaHyper.lean:474:does not change WHAT the root attests — only one root proof is checked either way. This underwrites
metatheory/Metatheory/SettlementSoundness.lean:485:root attests authority-was-LIVE-at-settlement. Whatever a verifier concludes from an
metatheory/Metatheory/SettlementSoundness.lean:490:theorem settled_root_attests_live_authority
metatheory/Metatheory/SettlementSoundness.lean:515:#assert_axioms settled_root_attests_live_authority
metatheory/Metatheory/SettlementSoundness.lean:538:  * Light-client unfoolability — `settled_root_attests_live_authority` (accept ⟹ live-at-settlement).
metatheory/Metatheory/Open/CrossCellBisim.lean:8:item — is, for the single cell, **complete** … the residual is the **cross-cell whole-history closure
metatheory/Metatheory/Open/CrossCellBisim.lean:39:     EXECUTABLE kernel** (`xcell_whole_history_confluent`). Lifting `applyHalfOut_comm_disjoint` from a
metatheory/Metatheory/Open/CrossCellBisim.lean:59:The whole-history confluence here is the *single-edge-commutes-past-a-history* form (one disjoint
metatheory/Metatheory/Open/CrossCellBisim.lean:67:(`coupled_no_schedule_agnostic_commit`), so its whole-history "closure" is the consensus/escalation
metatheory/Metatheory/Open/CrossCellBisim.lean:195:/-- **KEYSTONE — `xcell_whole_history_confluent` — the adversary-stream confluence over
metatheory/Metatheory/Open/CrossCellBisim.lean:200:whole-history (all-`n`) lift of the two-point `applyHalfOut_comm_disjoint` — the
metatheory/Metatheory/Open/CrossCellBisim.lean:203:theorem xcell_whole_history_confluent
metatheory/Metatheory/Open/CrossCellBisim.lean:243:schedule: `xcellNext`-congruence (`xcellNext_xeq_congr`) iterated through `traj`. The whole-history lift
metatheory/Metatheory/Open/CrossCellBisim.lean:259:with `xcell_whole_history_confluent` it says the disjoint-commuted history is observationally
metatheory/Metatheory/Open/CrossCellBisim.lean:273:never overdraws — `applyHalfOut` gates on `amt ≤ bal srcA`), so it holds along the WHOLE history. -/
metatheory/Metatheory/Open/CrossCellBisim.lean:311:produce DISTINCT committed sets, so there is NO whole-history confluence there. We re-export that
metatheory/Metatheory/Open/CrossCellBisim.lean:317:`xcell_whole_history_confluent`'s `hdis` cannot be dropped — off the disjoint fragment the
metatheory/Metatheory/Open/CrossCellBisim.lean:318:whole-history closure is the consensus/escalation boundary, not a confluence (the research residue we
metatheory/Metatheory/Open/CrossCellBisim.lean:332:#assert_axioms xcell_whole_history_confluent
metatheory/Metatheory/Open/CrossCellBisim.lean:341:FRAGMENT (axiom-clean) of the README's "cross-cell whole-history closure":
metatheory/Metatheory/Open/CrossCellBisim.lean:345:  * `xcell_whole_history_confluent` — THE adversary-stream confluence over `inducedSystem`
metatheory/Metatheory/Open/CrossCellBisim.lean:353:    executable history (the `stepComplete_carries_infinite` "no drifting future" on the kernel);
metatheory/Metatheory/Open/CrossCellBisim.lean:355:    no whole-history confluence), so the fragment is non-vacuous and its boundary is exactly drawn.
metatheory/Metatheory/Open/CrossCellBisim.lean:362:--       multiset of pairwise-disjoint debits reach `xeq` ledgers. `xcell_whole_history_confluent`
metatheory/Metatheory/Open/CrossCellBisim.lean:363:--       gives the single-edge-slides-through-a-history generator; the full closure is its `List.Perm`
metatheory/Metatheory/Open/CrossCellBisim.lean:367:--       (`coupled_no_schedule_agnostic_commit`), so its whole-history "closure" is the
metatheory/docs/docs-old/REVIEW-explorer.md:19:history (`/api/events` with `proof_status`). Both mean correct node data is
metatheory/docs/docs-old/REVIEW-explorer.md:69:### F2 — [MEDIUM] Activity page ignores `/api/events` history + its `proof_status`
metatheory/docs/docs-old/REVIEW-explorer.md:84:history (with a `proof_status` badge) alongside / seeded-before the live SSE
metatheory/docs/docs-old/REVIEW-explorer.md:163:- F2: poll `/api/events`, render committed history (+`proof_status` badge),
metatheory/Dregg2/DSL.lean:7:`recCexec_attests` apply to the exact elaborated term.
metatheory/Dregg2/DSL.lean:208:`recCexec_attests` apply to this term. -/
metatheory/Dregg2/Spec/Authority.lean:434:whole-history invariant below is OPEN — see the note.) -/
metatheory/Dregg2/Spec/Authority.lean:443:/-- **`only_connectivity_begets_connectivity`** — the whole-history non-forgeability closure
metatheory/Dregg2/Spec/Authority.lean:449:      authorized generative act (`AddedByAuthorizedGen`) along the history.
metatheory/docs/CODEX-IVC-FINAL-REVIEW.md:3:VERDICT: for the K-fold segment path, NO critical soundness hole — the same-endpoint mixed-root forgery is GENUINELY CLOSED under the Poseidon2 truncated-output commitment assumption.
metatheory/docs/CODEX-IVC-FINAL-REVIEW.md:7:- THE DIGEST IS NOT ~31-bit coeff-0-only: dregg compares a 7-felt segment claim — genesis, final, count, + FOUR BabyBear digest lanes (ivc_turn_chain.rs:224 + :1963). ~124-bit digest collision resistance.
metatheory/Metatheory/Open/AuthorityClosure.lean:99:no right ever appears ex nihilo, no matter how long the production history.
metatheory/Dregg2/World.lean:141:/-- **The block-id history substrate.** For the network-driven finality model a "history"
metatheory/Dregg2/Substrate/Heap.lean:25:       makes the root a function of the map's MEANING, not its build history).
metatheory/Dregg2/Substrate/Heap.lean:267:MEANING: however a heap was built (any insert order, any update history), the sorted leaf list —
metatheory/Dregg2/Substrate/Heap.lean:425:the same lookup semantics have the SAME root (via canonicity `ext_get`; NO crypto). Build history
metatheory/Dregg2/Spec/Lifecycle.lean:32:  * **archival is the IVC/recursive-fold reused as history-compression** — an
metatheory/Dregg2/Spec/Lifecycle.lean:35:    compressing history rather than verifying it.
metatheory/Dregg2/Spec/Lifecycle.lean:76:reversible quiescence; `Archived` keeps the cell live (history pruned only);
metatheory/Dregg2/Spec/Lifecycle.lean:142:  /-- Reversible quiescence: rejects new effects, state/history preserved, `unseal`
metatheory/Dregg2/Spec/Lifecycle.lean:160:`archived` ONLY (archival prunes history but the cell stays live); `false` for
metatheory/Dregg2/Spec/Lifecycle.lean:229:  /-- `live → archived` (history fold; cell stays live). -/
metatheory/Dregg2/Spec/Lifecycle.lean:329:**history-compression**. Modelled as a `foldl` over an abstract step `accum` from an
metatheory/Dregg2/Spec/Lifecycle.lean:340:reused for history compression — `Archived` keeps the cell live (`acceptsEffects`) but
metatheory/Dregg2/Spec/Lifecycle.lean:341:replaces its prior history with this one digest. -/
metatheory/Dregg2/Spec/Lifecycle.lean:352:*history*, not the cell's capacity to act (`lifecycle.rs:351` test). Reinforces that
metatheory/Dregg2/Spec/Lifecycle.lean:353:archival is history-compression, NOT a step toward termination. -/
metatheory/Dregg2/Circuit.lean:5:`Exec/StepComplete.lean` proves every committed step attests the four `fullStepInv`
metatheory/Dregg2/Circuit.lean:237:`←` half). Composed with `cexec_attests`, the EXECUTOR produces circuit-satisfying witnesses
metatheory/Dregg2/Circuit.lean:245:`cexec_attests` (step-completeness) with `bridge` (circuit completeness). This is the
metatheory/Dregg2/Circuit.lean:249:  circuit_complete s t s' (cexec_attests h)
metatheory/Dregg2/Spec/ExecRefinement.lean:310:reading `execGraph caps h c` as a *connectivity claim* attests it tautologically — a "spec" that IS the
metatheory/Dregg2/Spec/ExecRefinement.lean:334:so a guarantee leg that uses a bare `execGraph caps h c` as a CONNECTIVITY claim attests it
metatheory/Dregg2/Spec/ExecRefinement.lean:737:`Spec.Authority.only_connectivity_begets_connectivity`'s OPEN (the whole-history graph
metatheory/Dregg2/Spec/WholeTurnTriangle.lean:342:(which valid cross-cell history wins under Byzantine ordering) — a SEPARATE consensus obligation
metatheory/Dregg2/Distributed/HistoryAggregation.lean:16:the succinct aggregate learns the whole history is correct.
metatheory/Dregg2/Distributed/HistoryAggregation.lean:20:     (its `commits` field), so the step proof, when sound, attests the verified executor actually
metatheory/Dregg2/Distributed/HistoryAggregation.lean:25:**The headline (`wellformed_attests_whole_history`):** a `WellFormedChain` from a genesis state
metatheory/Dregg2/Distributed/HistoryAggregation.lean:28:chain is a `Run recChainedSystem` from genesis whose final state is the genuine fold of the history,
metatheory/Dregg2/Distributed/HistoryAggregation.lean:29:so `recChained_run_conserves` (no mint/burn over the entire history) applies.
metatheory/Dregg2/Distributed/HistoryAggregation.lean:81:sound, attests. -/
metatheory/Dregg2/Distributed/HistoryAggregation.lean:141:/-! ## 4. The genuine final root of the whole history.
metatheory/Dregg2/Distributed/HistoryAggregation.lean:143:The accumulator's final claim is "`final_root` = the genuine fold of the whole history"
metatheory/Dregg2/Distributed/HistoryAggregation.lean:219:/-! ## 6. THE HEADLINE — a well-formed chain attests the WHOLE history. -/
metatheory/Dregg2/Distributed/HistoryAggregation.lean:231:run-level theorems apply to the whole history. -/
metatheory/Dregg2/Distributed/HistoryAggregation.lean:243:/-- **`wellformed_history_conserves` (KEYSTONE).** Value is conserved across the WHOLE
metatheory/Dregg2/Distributed/HistoryAggregation.lean:244:folded history: the ledger total at the folded endpoint equals the genesis total. The aggregate
metatheory/Dregg2/Distributed/HistoryAggregation.lean:245:attests a no-mint/no-burn history of arbitrary length. Rides `recChained_run_conserves`
metatheory/Dregg2/Distributed/HistoryAggregation.lean:247:theorem wellformed_history_conserves (g : RecChainedState) (steps : List ChainStep)
metatheory/Dregg2/Distributed/HistoryAggregation.lean:252:/-! ### Conservation-over-history from KERNEL continuity alone (the §8 root binds the kernel, not the log).
metatheory/Dregg2/Distributed/HistoryAggregation.lean:258:demands — conservation-over-history — needs ONLY kernel continuity (`recTotal` reads the kernel), so we
metatheory/Dregg2/Distributed/HistoryAggregation.lean:301:conserved across the whole history given only KERNEL continuity from genesis: the ledger total at the
metatheory/Dregg2/Distributed/HistoryAggregation.lean:366:/-- **`verified_history_conserves` (THE HEADLINE CLOSURE — conservation from VERIFICATION ALONE).**
metatheory/Dregg2/Distributed/HistoryAggregation.lean:367:Conservation across the WHOLE history with NO `StateChained` hypothesis: given the genesis pin, the
metatheory/Dregg2/Distributed/HistoryAggregation.lean:372:the precise statement the critique asked for: "trusting the aggregate trusts a no-mint/no-burn history"
metatheory/Dregg2/Distributed/HistoryAggregation.lean:374:theorem verified_history_conserves
metatheory/Dregg2/Distributed/HistoryAggregation.lean:400:/-- **`wellformed_attests_whole_history` (THE HEADLINE).** A well-formed chain from genesis
metatheory/Dregg2/Distributed/HistoryAggregation.lean:401:`g` GENUINELY attests the whole history:
metatheory/Dregg2/Distributed/HistoryAggregation.lean:406:  (3) **the final root is the genuine fold of the whole history** — `foldedFinalRoot` commits the
metatheory/Dregg2/Distributed/HistoryAggregation.lean:409:This is the meaning the IVC accumulator's `WholeChainProof` claims; `RecursiveAggregation.lean`
metatheory/Dregg2/Distributed/HistoryAggregation.lean:411:theorem wellformed_attests_whole_history (g : RecChainedState) (steps : List ChainStep)
metatheory/Dregg2/Distributed/HistoryAggregation.lean:448:non-empty history, not a vacuous `none`. -/
metatheory/Dregg2/Distributed/HistoryAggregation.lean:455:/ `verified_history_conserves`) fires on a REAL chain, not a vacuous one. -/
metatheory/Dregg2/Distributed/HistoryAggregation.lean:496:#assert_axioms Dregg2.Distributed.HistoryAggregation.wellformed_history_conserves
metatheory/Dregg2/Distributed/HistoryAggregation.lean:497:#assert_axioms Dregg2.Distributed.HistoryAggregation.wellformed_attests_whole_history
metatheory/Dregg2/Distributed/HistoryAggregation.lean:499:-- the §8-root binds the KERNEL (not the log): conservation-over-history from VERIFICATION, not from a
metatheory/Dregg2/Distributed/HistoryAggregation.lean:505:#assert_axioms Dregg2.Distributed.HistoryAggregation.verified_history_conserves
metatheory/Dregg2/Boundary.lean:130:/-- **`StepComplete`** — every reachable transition of `Impl` attests the *full*
metatheory/Dregg2/Deos/Transclusion.lean:76:finalized history (`imp.provenance` — the cited receipt; `imp.sourceField` — the field quoted) bound to
metatheory/Dregg2/Deos/Transclusion.lean:121:diverge from its source).** When the transclusion's citation is VALID against the source history
metatheory/Dregg2/Deos/Transclusion.lean:232:/-- The SOURCE document cell's history: an older receipt finalized `title = 7`; the head left it `7`. -/
metatheory/Dregg2/Spec/ExecRefinementFull.lean:18:   permitted `AbsStep`. By case-split, reusing `execFull_attests`.
metatheory/Dregg2/Spec/ExecRefinementFull.lean:26:The single named residue is `OnlyConnectivityCloses` — the whole-history connectivity
metatheory/Dregg2/Spec/ExecRefinementFull.lean:36:open Dregg2.Exec.TurnExecutorFull (FullAction execFull ledgerDelta fullActionInv execFull_attests
metatheory/Dregg2/Spec/ExecRefinementFull.lean:113:kind and reuse `execFull_attests` (the per-kind step-completeness witness):
metatheory/Dregg2/Spec/ExecRefinementFull.lean:178:and supply (mint/burn). By case-split, reusing `execFull_attests` and `ledgerDelta`. -/
metatheory/Dregg2/Spec/ExecRefinementFull.lean:295:/-! ## §5 — The NAMED residue: the whole-history connectivity closure (an open named obligation).
metatheory/Dregg2/Spec/ExecRefinementFull.lean:311:/-- **`OnlyConnectivityCloses`** — the whole-history connectivity-closure property (PROVED as
metatheory/Dregg2/Spec/ExecRefinementFull.lean:323:/-- **`onlyConnectivityCloses` — the whole-history connectivity closure, PROVED (not a hypothesis).**
metatheory/Dregg2/Spec/ExecRefinementFull.lean:408:turn-level `AbsRun`) are proved, and the whole-history closure `onlyConnectivityCloses` is now PROVED
docs/desktop-os-research/patches/gpui-offscreen.patch:88: unicode-segmentation.workspace = true
metatheory/Dregg2/Exec/ProofForest.lean:19:    reducing to `execForest_attests`.
metatheory/Dregg2/Exec/ProofForest.lean:28:--   `crossForest_attests`. The `δ` surface is already on `ProofNode`; the cross-cell `Linked`
metatheory/Dregg2/Exec/ProofForest.lean:122:`Linked`, the composite attests the full `StepInv`: Conservation ∧ Authority ∧ ChainLink ∧
metatheory/Dregg2/Exec/ProofForest.lean:123:ObsAdvance. (P) discharges `pf.attested` to a real committed `execForest` run; `execForest_attests`
metatheory/Dregg2/Exec/ProofForest.lean:124:then attests all four conjuncts. The per-node validity is the hypothesis; the linking + composition
metatheory/Dregg2/Exec/ProofForest.lean:133:— the §8 seam, a hypothesis) and (L) the forest is `Linked`, the composite attests the full
metatheory/Dregg2/Exec/ProofForest.lean:135:`Forest.execForest_attests` over the witness run `pf.attested` yields from (P). The
metatheory/Dregg2/Exec/ProofForest.lean:142:  exact execForest_attests (pf.attested hvalid)
metatheory/Dregg2/Exec/ProofForest.lean:221:linked, `proofForest_sound` attests the full `StepInv` over the whole forest. -/
metatheory/Dregg2/Circuit/DescriptorIR2.lean:289:Aggregation.EngineSound.recursive_sound`, `circuit/src/joint_turn_recursive.rs`'s leaf verifier,
metatheory/Dregg2/Circuit/DescriptorIR2.lean:295:the GENUINE commitment of a verifying sub-proof — a forged one no sub-proof attests is
metatheory/Dregg2/Circuit/DescriptorIR2.lean:844:`circuit/src/joint_turn_recursive.rs`), and the program VK `vkOf` a proof attests (the
metatheory/Dregg2/Circuit/DescriptorIR2.lean:863:`RecursiveAggregation.EngineSound.recursive_sound` / the leaf-verifier's soundness — the one FRI
metatheory/Dregg2/Circuit/DescriptorIR2.lean:907:verifying sub-proof exposing that same commitment attests the SAME program VK. A forged row that
metatheory/Dregg2/Circuit/DescriptorIR2.lean:1708:-- (123) attests EXACTLY the row's vk (45) — a forgery exposing a DIFFERENT vk cannot verify at
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:5:NOTHING of the history — learns that the WHOLE chain of N finalized turns is correct:
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:7:reorder/drop/insert), and the final root is the genuine fold of the whole history. This is the model
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:9:`WholeChainProof`) realizes; `verify_turn_chain_recursive` checks only the root, cost independent of N.
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:12:re-execute the history, does NOT re-hash the states, does NOT walk the blocklace. It checks the
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:14:`HistoryAggregation.WellFormedChain` (`aggregate_attests_whole_history`) — so trusting the aggregate
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:15:is trusting the whole history. The verification IS the trust.
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:24:  * **`InnerProofSound`** — an inner whole-turn step proof that VERIFIES attests the verified executor
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:29:  * **`BindingAirSound`** — a `TurnChainBindingAir` leaf proof that VERIFIES attests the temporal
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:33:  * **`RecursiveVerifierSound`** — an AGGREGATE proof that VERIFIES attests EVERY wrapped child leaf
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:39:the whole-history correctness + conservation — is PROVED here in Lean, gap-free. The composition is
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:73:`Aggregate` is the `WholeChainProof` (`ivc_turn_chain.rs:430`): the single root recursion proof, plus
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:81:the four public commitments are exactly the `WholeChainProof` fields. The `leafProofs` are the per-turn
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:84:  /-- The single root recursion proof (the whole tree folded to one — `WholeChainProof.root`). -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:90:  /-- Public: the genesis root the chain starts from (`WholeChainProof.genesis_root`). -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:92:  /-- Public: the final root the chain reaches (`WholeChainProof.final_root`). -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:94:  /-- Public: the running digest of the ordered (old,new) pairs (`WholeChainProof.chain_digest`). -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:96:  /-- Public: the number of finalized turns folded (`WholeChainProof.num_turns`). -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:102:soundness). They are bundled in `EngineSound` as a hypothesis the headline takes — NOT an axiom. The
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:112:/-- **`EngineSound agg g steps`** — the three named recursion-soundness hypotheses, interpreted
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:115:structure EngineSound (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep) : Prop where
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:123:  leaf proof attests ITS paired step's verified-executor transition `recCexec pre turn = some post`.
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:130:  /-- **H-BIND (`BindingAirSound`)** — a verifying `TurnChainBindingAir` leaf attests the temporal
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:140:/-! ## 3. THE LIGHT-CLIENT HEADLINE — verifying the aggregate attests the WHOLE history.
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:143:engine is sound, the named hypotheses), then EVERY turn in the history executed correctly, the chain
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:144:is correctly ordered, and the final root is the genuine fold of the whole history. No re-witnessing. -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:169:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:184:  /-- (3) the public final root IS the genuine fold of the whole history. -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:192:/-- **`light_client_verifies_whole_history` (THE MAGNESIUM→GOLD HEADLINE).**
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:196:insert), and the public final root is the genuine fold of the whole history — UNDER the named,
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:198:the whole history; proofs are additive attestation, and this theorem is exactly that statement,
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:200:theorem light_client_verifies_whole_history
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:202:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:218:history — all WITHOUT the light client re-running a single turn. We expose the run + conservation
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:220:the aggregate attests is consistent with the verified leaves. -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:222:/-- **`attested_history_is_run`.** Given the executor-genuine chain (`StateChained` — the
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:224:whole attested history is a `Run recChainedSystem` from genesis to the folded endpoint. The light
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:234:theorem attested_history_is_run
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:239:/-- **`attested_history_conserves` (KEYSTONE).** Value is conserved across the WHOLE attested
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:240:history: the ledger total at the folded endpoint equals the genesis total. A light client trusting the
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:241:aggregate trusts a no-mint/no-burn history of arbitrary length, having re-executed nothing. Rides
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:242:`HistoryAggregation.wellformed_history_conserves`.
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:247:theorem attested_history_conserves
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:250:  wellformed_history_conserves g steps hch
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:252:/-! ### CRITICAL-3 CLOSURE — conservation-over-history DERIVED from `verify agg.root`, no `StateChained`.
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:254:The critique: `attested_history_conserves` takes `StateChained` (state continuity) as a SEPARATE
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:259:`verified_history_conserves` rides that to conservation through `KernelChained` — so conservation
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:266:history conserves value — the ledger total at the folded endpoint equals the genesis total — with NO
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:270:state-continuity assertion), `verified_history_conserves` DERIVES kernel continuity from that tooth
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:272:closed: "trusting the aggregate trusts a no-mint/no-burn history" now follows from VERIFICATION, not
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:281:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:287:  have hatt := light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:290:  exact verified_history_conserves CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:297:The headline would be hollow if `EngineSound` were unsatisfiable, or if `verify agg.root = true`
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:300:whose root/leaf/binding all verify, and an `EngineSound` proof — so the headline fires on a real
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:302:gives a vacuously-true `EngineSound` (no obligation), and the headline is not invoked — the tooth is
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:338:SATISFIABLE on a real chain: `EngineSound` holds for the accepting verifier, the realizing aggregate,
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:341:the binding soundness yields the singleton `ChainBound` + the genuine root pins. So `EngineSound` is
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:344:    EngineSound RealProof acceptAll zCH zRH zcmb zcompress zcompressN
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:367:root attests the honest 1-step history. So `light_client_verifies_whole_history` is non-vacuous — it
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:372:  light_client_verifies_whole_history RealProof acceptAll zCH zRH zcmb zcompress zcompressN
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:376:of the witnessed headline: the first (only) turn of the realizing history executed —
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:388:Additive attestation is only meaningful if the aggregate cannot attest a BROKEN history. The teeth:
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:390:`ChainBound` is FALSE, so any `EngineSound` whose `binding_sound` fires on such a chain is
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:412:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g [s, s'])
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:420:/-- **`leaf_pairing_defeats_swap` (the leg-swap tooth).** A verifying leaf proof attests the
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:430:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g (s :: ss))
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:442:§§1–6 prove the FLAT statement: given a `WholeChainProof` over a *finite* K-turn window, verifying its
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:443:root attests `WellFormedChain` for that window. That is the BOUNDED-K light client (`ivc_turn_chain.rs::
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:447:(`acc_n = accumulate(acc_{n-1}, turn_n)`), extending the attested history ONE step at a time, with O(1)
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:449:step — so by induction from genesis, `acc_n` attests the WHOLE history `0..n`. This is the IVC soundness
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:452:  `accumulate_preserves_wellformed` — IF `acc` attests `WellFormedChain g steps` AND the next turn `s`
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:454:  (`s.pre = lastStateOf g steps`), THEN `accumulate acc s` attests `WellFormedChain g (steps ++ [s])`.
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:456:  `acc_attests_whole_history` — folding `accumulate` from the genesis accumulator over a state-extending
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:462:IVC fixed point) is the SAME named, realizable `EngineSound` boundary §2 already carries; nothing new is
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:484:list; the list is the SPECIFICATION the proof attests), and the live `WellFormedChain` attestation. The
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:486:which is exactly what the running recursion proof is sound for (`EngineSound`). -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:488:  /-- The steps folded so far, in chain order (the history the running proof attests). -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:582:prover keeps only `acc` (its running proof); `acc.steps` is the SPEC the proof attests, extended by one.
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:608:PRESERVED by one fold step: `accumulate acc s …` attests `WellFormedChain g (acc.steps ++ [s])`. This is
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:619:/-- **`acc_attests_whole_history` (THE IVC HEADLINE — by induction from genesis).** The running
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:620:accumulator attests the WHOLE history it has folded: `acc.leanWitness` IS a `WellFormedChain` from
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:623:maintain the invariant) carries the whole-history attestation in its `leanWitness`. Composed with
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:624:`light_client_verifies_whole_history` (§3) — whose `EngineSound` is sound for exactly this
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:625:`WellFormedChain` — a light client verifying the running root learns the whole accumulated history is
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:628:theorem acc_attests_whole_history {g : RecChainedState}
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:633:/-- **`acc_attests_run` (the run the accumulator inherits).** The accumulated history is a genuine
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:635:verified record cell (incl. conservation) applies to the whole O(1)-memory-folded history, with NO
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:637:theorem acc_attests_run {g : RecChainedState}
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:642:/-- **`acc_conserves` (conservation over the whole accumulated history).** Value is conserved across the
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:643:entire history the running accumulator folded: the ledger total at the head equals the genesis total. A
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:644:light client trusting the running aggregate trusts a no-mint/no-burn history of UNBOUNDED length, having
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:649:  wellformed_history_conserves g acc.steps acc.leanWitness.chained
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:674:/-- **`ivc_accumulate_fires` (IVC non-vacuity).** The realizing accumulator attests a REAL well-formed
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:675:1-step history from genesis — the IVC step genuinely fired and preserved the invariant. -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:678:  acc_attests_whole_history zCH zRH zcmb zcompress zcompressN ivcRealAcc
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:680:/-- **`ivc_acc_conserves_real` (the accumulated history conserves — a TRUE arithmetic fact).** The
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:681:realizing accumulator's folded history conserves the ledger total: head total = genesis total. So the
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:695:#assert_axioms Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:696:#assert_axioms Dregg2.Circuit.RecursiveAggregation.attested_history_conserves
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:697:-- the CRITICAL-3 closure: conservation-over-history DERIVED from `verify agg.root`, no StateChained:
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:704:-- the UNBOUNDED IVC accumulator: the running left-fold preserves whole-history attestation, by
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:711:#assert_axioms Dregg2.Circuit.RecursiveAggregation.acc_attests_whole_history
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:712:#assert_axioms Dregg2.Circuit.RecursiveAggregation.acc_attests_run
metatheory/Dregg2/Exec/RecordCellLive.lean:19:- **`recCexec_attests`** — the record-cell shadow of `cexec_attests`: every committed transition
metatheory/Dregg2/Exec/RecordCellLive.lean:20:  attests the four `StepInv` facts (Admitted ∧ Apply ∧ ChainLink ∧ ObsAdvance), with the program
metatheory/Dregg2/Exec/RecordCellLive.lean:80:/-! ## `recCexec_attests` — step-completeness on the running record machine. -/
metatheory/Dregg2/Exec/RecordCellLive.lean:82:/-- **`recCexec_attests` — the four `StepInv` facts on a committed record transition.**
metatheory/Dregg2/Exec/RecordCellLive.lean:83:Every commit attests: (Admitted) the program admitted the candidate; (Apply) the new value is
metatheory/Dregg2/Exec/RecordCellLive.lean:86:shadow of `Exec.cexec_attests` — the structure-map gates the living arrow. -/
metatheory/Dregg2/Exec/RecordCellLive.lean:87:theorem recCexec_attests {s s' : RecChained} {op : RecOp} (h : recCexec s op = some s') :
metatheory/Dregg2/Exec/RecordCellLive.lean:110:  exact (recCexec_attests h).2.2.2.1
metatheory/Dregg2/Exec/RecordCellLive.lean:145:  ⟨(recCexec_attests h).2.2.2.2.1, (recCexec_attests h).2.2.2.2.2⟩
metatheory/Dregg2/Exec/RecordCellLive.lean:155:    rw [← hprog]; exact (recCexec_attests h).1
metatheory/Dregg2/Exec/RecordCellLive.lean:210:/-- **`recordCell_stepComplete`** — the record cell attests its four `StepInv` conjuncts at
metatheory/Dregg2/Exec/RecordCellLive.lean:219:  · have a := recCexec_attests hc
metatheory/Dregg2/Exec/RecordCellLive.lean:273:#assert_axioms recCexec_attests
metatheory/Dregg2/Circuit/StateCommit.lean:556:`recStateCommit_binds_kernel`). Stated standalone so the history-aggregation seam can lift it. -/
metatheory/Dregg2/Distributed/MembershipSafety.lean:271:linearizable amendment history `constitution.rs` keeps (`history.push`). A `false` (no-op) apply
metatheory/Dregg2/Exec/ForestMemoryProgram.lean:31:     all-or-nothing fold, the SAME shape as `FullForestAuth.execFullTurnG_each_attests`.
metatheory/Dregg2/Exec/ForestMemoryProgram.lean:320:`execFullTurnG_each_attests`, with `memprog_trans` welding adjacent steps. -/
metatheory/Dregg2/Circuit/RotationLayout.lean:133:sponge absorbing the index root as its last limb. Whole-history non-omission
metatheory/Dregg2/Exec/DistributedExports.lean:119:  | [hS, gSeg, heSeg, geSeg] =>
metatheory/Dregg2/Exec/DistributedExports.lean:121:      let gS ← stripReq? "g=" gSeg
metatheory/Dregg2/Exec/DistributedExports.lean:122:      let heS ← stripReq? "he=" heSeg
metatheory/Dregg2/Exec/DistributedExports.lean:123:      let geS ← stripReq? "ge=" geSeg
metatheory/Dregg2/Exec/DistributedExports.lean:253:  | [hS, fSeg, sSeg] =>
metatheory/Dregg2/Exec/DistributedExports.lean:255:      let fS ← stripReq? "f=" fSeg
metatheory/Dregg2/Exec/DistributedExports.lean:256:      let sS ← stripReq? "s=" sSeg
metatheory/Dregg2/Exec/DistributedExports.lean:344:  | [qS, eSeg] =>
metatheory/Dregg2/Exec/DistributedExports.lean:346:      let eS ← stripReq? "e=" eSeg
metatheory/Dregg2/Exec/DistributedExports.lean:432:  | [yS, nSeg, nnSeg, tSeg] =>
metatheory/Dregg2/Exec/DistributedExports.lean:434:      let nS ← stripReq? "n=" nSeg
metatheory/Dregg2/Exec/DistributedExports.lean:435:      let nnS ← stripReq? "N=" nnSeg
metatheory/Dregg2/Exec/DistributedExports.lean:436:      let tS ← stripReq? "t=" tSeg
metatheory/Dregg2/Exec/DistributedExports.lean:533:  | [gS, aSeg, bSeg] =>
metatheory/Dregg2/Exec/DistributedExports.lean:535:      let aS ← stripReq? "a=" aSeg
metatheory/Dregg2/Exec/DistributedExports.lean:536:      let bS ← stripReq? "b=" bSeg
metatheory/Dregg2/Exec/DistributedExports.lean:635:  | [bS, dSeg] =>
metatheory/Dregg2/Exec/DistributedExports.lean:637:      let dS ← stripReq? "D=" dSeg
metatheory/Dregg2/Distributed/Fibration.lean:42:   PREFIX-CLOSED (`HistoryAggregation.wellformed_history_conserves`), so a partition cannot skew
metatheory/Dregg2/Distributed/Fibration.lean:43:   the visible total at all. (Honest scope: the EXACT body executor; the FEE-wrapped history's
metatheory/Dregg2/Distributed/Fibration.lean:482:has received ANY prefix of the history already sees the genesis total. The window is `0` at
metatheory/Dregg2/Distributed/Fibration.lean:486:The FEE-wrapped history (`runTurn`) burns per turn, so two nodes at different heights see totals
metatheory/Dregg2/Distributed/Fibration.lean:488:`Distributed/FeeHistory.wellformed_history_conserves_modulo_burn`, and its reconciliation window
metatheory/Dregg2/Distributed/Fibration.lean:494:  (ChainStep StateChained lastStateOf wellformed_history_conserves honestStep)
metatheory/Dregg2/Distributed/Fibration.lean:508:`wellformed_history_conserves` applied to the local prefix. The §8 named open is closed — and the
metatheory/Dregg2/Distributed/Fibration.lean:513:  reconciledAfter b t _ := wellformed_history_conserves g (view b t) (hview b t)
metatheory/Dregg2/Distributed/Fibration.lean:522:/-- **Non-vacuity**: the discharged conservation fibre FIRES on a real executed history — at
metatheory/Dregg2/Distributed/StrandAdmission.lean:68:/-- **`Vouch`** — voucher `voucher` attests for candidate strand `candidate` (a follow-graph
metatheory/Dregg2/Distributed/StrandAdmission.lean:541:  | [nS, mSeg, sSeg, vSeg, boSeg, qSeg] =>
metatheory/Dregg2/Distributed/StrandAdmission.lean:543:      let mS ← stripReq? "m=" mSeg
metatheory/Dregg2/Distributed/StrandAdmission.lean:544:      let sS ← stripReq? "S=" sSeg
metatheory/Dregg2/Distributed/StrandAdmission.lean:545:      let vS ← stripReq? "V=" vSeg
metatheory/Dregg2/Distributed/StrandAdmission.lean:546:      let boS ← stripReq? "Bo=" boSeg
metatheory/Dregg2/Distributed/StrandAdmission.lean:547:      let qS ← stripReq? "q=" qSeg
metatheory/Dregg2/Deos/Rehydration.lean:238:well-linked chain agreeing on the head receipt IS the same history (`Dregg2.Exec.Receipts.
metatheory/Dregg2/Deos/Rehydration.lean:239:chain_tamper_evident`). So a confined context replays to a UNIQUE, non-forgeable history — "replays
metatheory/Dregg2/Deos/TransclusionChain.lean:91:middle source history `bHist`: A's `sourceField` IS the local field B used to hold its quote of C
metatheory/Dregg2/Deos/TransclusionChain.lean:92:(`ab.sourceField = bc.localField`), and at A's cited receipt in B's history the field held EXACTLY the
metatheory/Dregg2/Deos/TransclusionChain.lean:164:against C's history, so it cannot be opened to feed the chain. An adversary cannot smuggle a false value
metatheory/Dregg2/Deos/TransclusionChain.lean:169:never committed — is NOT valid against C's history, so it cannot be the middle link of any chain. The
metatheory/Dregg2/Deos/TransclusionChain.lean:256:    -- the weld holds against the ADVANCED middle history (the cited B-receipt is in the past, frozen):
metatheory/Dregg2/Deos/TransclusionChain.lean:352:/-- The inner quote `bcQuote` is valid against C's history. -/
metatheory/Dregg2/Deos/TransclusionChain.lean:358:/-- The outer quote `abQuote` is valid against B's history. -/
metatheory/Dregg2/Deos/TransclusionChain.lean:420:field A quotes (`quoteC`) held `7` in B's history, but the forged inner quote claims value `99`, so the
metatheory/Dregg2/Exec/Factory.lean:221:`StepComplete.cexec_attests`, scoped to a factory's published contract. -/
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:16:tree; the proof attempt refutes the unconditional statement. A wave's segment is its
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:41:  (2) `fold_agrees` — replaying the OLD leaders' segment computation in the GROWN lace
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:42:      reproduces the same segments and coverages (no late ratifier grew an old wave's
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:85:  splices a segment mid-order);
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:86:* `fold_agrees` — replaying the OLD leaders through `B'`'s segment computation
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:87:  (`tauStep B'`) reproduces the `B` fold exactly: same emitted segments AND same coverage
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:120:        leaderSegment B' P wl c l = leaderSegment B P wl c l)
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:126:      (∀ l ∈ L, ∀ c : List BlockId, leaderSegment B' P wl c l = leaderSegment B P wl c l) →
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:144:/-- One `tauStep` extends the accumulated order by the leader's segment (definitional). -/
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:147:    (tauStep B P wl acc l).1 = acc.1 ++ leaderSegment B P wl acc.2 l := rfl
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:152:per-leader segments — exactly the two fields of `FinalizedRegionStable`. -/
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:159:    exact ⟨leaderSegment B P wl acc.2 l ++ r, by
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:272:round-4 block 23) is super-ratified at round 6, its segment — the nine new blocks — is
metatheory/Dregg2/Exec/TurnExecutor.lean:16:  * `RecChainedState` / `recCexec` / `recFullStepInv` / `recCexec_attests` (the per-step
metatheory/Dregg2/Exec/TurnExecutor.lean:33:multi-`Action` turn, generalizing `recCexec_attests` from one op to the Action list:
metatheory/Dregg2/Exec/TurnExecutor.lean:35:  * `execTurn_attests`     — every committed turn attests `fullStepInv` over the WHOLE turn:
metatheory/Dregg2/Exec/TurnExecutor.lean:137:/-! ## §4 — Step-completeness BY CONSTRUCTION: every action attests all four `StepInv` conjuncts.
metatheory/Dregg2/Exec/TurnExecutor.lean:139:The replacement's correctness. We generalize `recCexec_attests` (one op ⊢ four conjuncts) to the
metatheory/Dregg2/Exec/TurnExecutor.lean:142:/-- The per-action attestation: **every action of a committed turn attests `recFullStepInv`**
metatheory/Dregg2/Exec/TurnExecutor.lean:144:This is `recCexec_attests` threaded along the transaction — step-completeness holds at EVERY action,
metatheory/Dregg2/Exec/TurnExecutor.lean:146:theorem execTurn_each_attests :
metatheory/Dregg2/Exec/TurnExecutor.lean:158:        · -- `b` is the head: its own step attests via `recCexec_attests`.
metatheory/Dregg2/Exec/TurnExecutor.lean:160:          exact ⟨s, s1, hca, recCexec_attests hca⟩
metatheory/Dregg2/Exec/TurnExecutor.lean:162:          exact execTurn_each_attests s1 s' rest hexec b hbrest
metatheory/Dregg2/Exec/TurnExecutor.lean:171:  obtain ⟨sa, sa', hstep, hinv⟩ := execTurn_each_attests s s' tt h a ha
metatheory/Dregg2/Exec/TurnExecutor.lean:196:        -- Conservation of the head step (via `recCexec_attests`'s first conjunct).
metatheory/Dregg2/Exec/TurnExecutor.lean:197:        have hhead : recTotal s1.kernel = recTotal s.kernel := (recCexec_attests hca).1
metatheory/Dregg2/Exec/TurnExecutor.lean:218:/-! ## §6 — `execTurn_attests`: the WHOLE turn attests all four `StepInv` conjuncts.
metatheory/Dregg2/Exec/TurnExecutor.lean:221:multi-`Action` turn, generalizing `recCexec_attests` from one op to the Action list:
metatheory/Dregg2/Exec/TurnExecutor.lean:253:        have hhead : s1.log = a.move :: s.log := (recCexec_attests hca).2.2.1
metatheory/Dregg2/Exec/TurnExecutor.lean:280:/-- **`execTurn_attests` — THE REPLACEMENT IS STEP-COMPLETE BY CONSTRUCTION.** Every
metatheory/Dregg2/Exec/TurnExecutor.lean:281:committed turn attests the FULL `StepInv` over the WHOLE multi-`Action` transaction: Conservation
metatheory/Dregg2/Exec/TurnExecutor.lean:283:`recCexec_attests` from one op to the Action forest (linear list); the four conjuncts are exactly
metatheory/Dregg2/Exec/TurnExecutor.lean:286:theorem execTurn_attests {s s' : RecChainedState} {tt : TxTurn} (h : execTurn s tt = some s') :
metatheory/Dregg2/Exec/TurnExecutor.lean:301:  hpres s tt s' hs (execTurn_attests h)
metatheory/Dregg2/Exec/TurnExecutor.lean:306:#assert_axioms execTurn_each_attests
metatheory/Dregg2/Exec/TurnExecutor.lean:312:#assert_axioms execTurn_attests
metatheory/Dregg2/Exec/TurnForest.lean:5:transaction (`execTurn`, all-or-nothing, `execTurn_attests` = all four `StepInv` conjuncts over the
metatheory/Dregg2/Exec/TurnForest.lean:17:    attesting all four `StepInv` conjuncts over ONE op — `recCexec_attests`);
metatheory/Dregg2/Exec/TurnForest.lean:36:  * **`execForest_attests`** — a committed forest attests the four `StepInv` conjuncts over the
metatheory/Dregg2/Exec/TurnForest.lean:39:    chain grew by exactly the node count). Generalizes `execTurn_attests` recursively over the tree.
metatheory/Dregg2/Exec/TurnForest.lean:168:`execTurn_attests`, …) to the forest — the recursion threads the chained state in exactly the
metatheory/Dregg2/Exec/TurnForest.lean:244:Every node's `recCexec` step preserves `recTotal` (`recKExec_conserves`, via `recCexec_attests`'s
metatheory/Dregg2/Exec/TurnForest.lean:272:/-! ## §6 — `execForest_attests`: the committed forest attests all four `StepInv` conjuncts.
metatheory/Dregg2/Exec/TurnForest.lean:274:Generalizing `execTurn_attests` recursively over the tree: a committed forest attests Conservation
metatheory/Dregg2/Exec/TurnForest.lean:284:/-- **`execForest_attests` — THE NESTED FOREST IS STEP-COMPLETE BY CONSTRUCTION.** Every
metatheory/Dregg2/Exec/TurnForest.lean:285:committed forest attests the FULL `StepInv` over the WHOLE tree: Conservation (balance field) ∧
metatheory/Dregg2/Exec/TurnForest.lean:286:Authority (every node) ∧ ChainLink ∧ ObsAdvance. This generalizes `execTurn_attests` recursively
metatheory/Dregg2/Exec/TurnForest.lean:289:theorem execForest_attests {s s' : RecChainedState} {f : TurnForest}
metatheory/Dregg2/Exec/TurnForest.lean:293:  exact execTurn_attests h
metatheory/Dregg2/Exec/TurnForest.lean:328:#assert_axioms execForest_attests
metatheory/Dregg2/Exec/TurnForest.lean:404:  * `execForest_attests` — the four `StepInv` conjuncts over the WHOLE tree (step-complete BY
metatheory/Dregg2/Exec/TurnForest.lean:405:    CONSTRUCTION), generalizing `execTurn_attests` recursively;
metatheory/Dregg2/Intent/Core.lean:5:is a *co-receipt*: the same string-diagram a receipt attests, but with the interior left as a TYPED HOLE
metatheory/Dregg2/Intent/Core.lean:120:/-- **`fulfill_outcome`** — the receipt attests the DEMANDED outcome (`= wanted`), definitionally. -/
metatheory/Dregg2/Intent/Core.lean:174:the escrow is locked. The receipt attests `res 0 1`. -/
metatheory/Dregg2/Intent/Core.lean:232:/-- A frame-validity twin of `demoIntent` (authority attests `T = 1000` within `δ = 5`). -/
metatheory/Dregg2/Consensus/OnDemandFeasibility.lean:86:segment, one permutation = the verified `tauOrder` restriction, the other = the causal
metatheory/Dregg2/Consensus/OnDemandFeasibility.lean:100:linearization `tauSeg` and the fast path's causal application order `fastSeg` are
metatheory/Dregg2/Consensus/OnDemandFeasibility.lean:104:theorem tau_agrees_with_fastpath (step : S → T → S) {tauSeg fastSeg : List T}
metatheory/Dregg2/Consensus/OnDemandFeasibility.lean:105:    (hperm : tauSeg.Perm fastSeg) (hcomm : PairwiseCommuting step tauSeg) (s : S) :
metatheory/Dregg2/Consensus/OnDemandFeasibility.lean:106:    tauSeg.foldl step s = fastSeg.foldl step s :=
metatheory/Dregg2/Exec/CapTPHandoffSound.lean:327:construction — the signature attests intent, but connectivity must already exist. -/
metatheory/Dregg2/Exec/EffectsPaired.lean:30:    `recCexec_attests.1` / `recCexec`'s `recKExec_conserves`;
metatheory/Dregg2/Exec/EffectsPaired.lean:31:  * the authority gate (`authorizedB`) comes VERBATIM from `recCexec_attests.2.1`;
metatheory/Dregg2/Exec/EffectsPaired.lean:236:  have hcore : recTotal s1.kernel = recTotal s.kernel := (recCexec_attests hc).1
metatheory/Dregg2/Exec/EffectsPaired.lean:259:  exact (recCexec_attests hc).2.1
metatheory/Dregg2/Proof/CordialMiners.lean:37:  super-ratified leader **anchors** a segment of the total order (`tau`).
metatheory/Dregg2/Proof/CordialMiners.lean:78:  * **OPEN-CM-XSORT.** The deterministic intra-segment `xsort` total order (`ordering.rs::xsort`,
metatheory/Dregg2/Proof/CordialMiners.lean:81:    safety question, not the within-segment tie-break.
metatheory/Dregg2/Proof/CordialMiners.lean:341:*single* segment of `tau` — recovered as a theorem about the protocol dregg1 runs. -/
metatheory/Dregg2/Deos/ReplayMembrane.lean:231:chain neither EXCEEDS the original (`reshareN_attenuates`) nor DEPENDS on its history to widen (this) —
metatheory/Dregg2/Distributed/Consensus.lean:51:   keys cannot re-anchor history. PROVED: `no_conflicting_finalized_state_reconfig` — two
metatheory/Dregg2/Distributed/Consensus.lean:72:* `OPEN-CM-XSORT` — the intra-segment `tau` linearization tie-break is still open in
metatheory/Dregg2/Distributed/Consensus.lean:296:Finality must survive validator-set CHANGE: retired keys cannot re-anchor history. We pin finality
metatheory/Dregg2/Distributed/Consensus.lean:299:corruption attack — retired keys re-signing an OLD height to rewrite history — is excluded because
metatheory/Dregg2/Distributed/Consensus.lean:325:height than every LATER one. This is the "history only moves forward" invariant (strictly stronger
metatheory/Dregg2/Distributed/Consensus.lean:331:  one's. The authenticated-monotone anchor: history cannot be re-rooted below the current height. -/
metatheory/Dregg2/Distributed/Consensus.lean:397:sits above the head. Hence a rewrite that tries to anchor history at a height *not exceeding* the
metatheory/Dregg2/Distributed/Consensus.lean:411:retired keys cannot re-root history below the head. NON-VACUOUS: the rewrite IS excluded
metatheory/Dregg2/Distributed/Consensus.lean:449:round-robin ANCHOR LABEL (which block a segment is named after), not a process whose proposal must
metatheory/Dregg2/Distributed/Consensus.lean:486:metadata (which segment a block anchors), not a liveness-critical authority.
metatheory/Dregg2/Circuit/Argus/Receipt.lean:292:SAME published value"). The receipt index the EPOCH publishes is an MMR (`Lightclient/MMR.lean`): history
metatheory/Dregg2/Exec/TurnExecutorFull.lean:5:`Action`s as an all-or-nothing transaction, step-complete by construction (`execTurn_attests`: the
metatheory/Dregg2/Exec/TurnExecutorFull.lean:25:We then PROVE that EVERY kind attests its `StepInv` obligations, packaged as `fullActionInv`:
metatheory/Dregg2/Exec/TurnExecutorFull.lean:28:    delegated VERBATIM to `recCexec_attests` (the `TurnExecutor` spine, one op);
metatheory/Dregg2/Exec/TurnExecutorFull.lean:40:The headline `execFull_attests` bundles these per-kind: every committed `FullAction` attests the
metatheory/Dregg2/Exec/TurnExecutorFull.lean:359:      rw [(recCexec_attests h).1]; ring
metatheory/Dregg2/Exec/TurnExecutorFull.lean:426:(`authorizedB` at the pre-state), via `recCexec_attests`. -/
metatheory/Dregg2/Exec/TurnExecutorFull.lean:429:  (recCexec_attests (by simpa [execFull] using h)).2.1
metatheory/Dregg2/Exec/TurnExecutorFull.lean:536:      exact (recCexec_attests h).2.2.1
metatheory/Dregg2/Exec/TurnExecutorFull.lean:564:The headline invariant: every committed `FullAction` attests EXACTLY its sound `StepInv` content for
metatheory/Dregg2/Exec/TurnExecutorFull.lean:603:/-- **`execFull_attests` — THE FULL OP-SET IS STEP-COMPLETE BY CONSTRUCTION.** Every
metatheory/Dregg2/Exec/TurnExecutorFull.lean:604:committed `FullAction` — balance/effect, authority (delegate/revoke), OR supply (mint/burn) — attests
metatheory/Dregg2/Exec/TurnExecutorFull.lean:608:theorem execFull_attests {s s' : RecChainedState} {fa : FullAction} (h : execFull s fa = some s') :
metatheory/Dregg2/Exec/TurnExecutorFull.lean:657:/-- **Every action of a committed full-turn attests `fullActionInv`.** Step-completeness
metatheory/Dregg2/Exec/TurnExecutorFull.lean:659:the fold. The full-op-set generalization of `TurnExecutor.execTurn_each_attests`. -/
metatheory/Dregg2/Exec/TurnExecutorFull.lean:660:theorem execFullTurn_each_attests :
metatheory/Dregg2/Exec/TurnExecutorFull.lean:671:          · subst hbeq; exact ⟨s, s1, ha, execFull_attests ha⟩
metatheory/Dregg2/Exec/TurnExecutorFull.lean:672:          · exact execFullTurn_each_attests s1 s' rest h b hbrest
metatheory/Dregg2/Exec/TurnExecutorFull.lean:1501:    representation flag and PRESERVES balance/state/history (NO value moves into commitment-form on the
metatheory/Dregg2/Exec/TurnExecutorFull.lean:1856:              `lifecycle.rs:109`) but state/history survive — REVERSIBLE quiescence (`cell.rs:533-545`).
metatheory/Dregg2/Exec/TurnExecutorFull.lean:3061:asset-orthogonal: they edit the log / `caps`, not the `bal` ledger). `execFullTurnA_each_attests`
metatheory/Dregg2/Exec/TurnExecutorFull.lean:3063:attestation (`FullForest.execFullForestA_each_attests`) lifts straight off the bridge. -/
metatheory/Dregg2/Exec/TurnExecutorFull.lean:3945:       -- (`execGraph_eq_any := rfl`) — so this leg attests genuine connectivity, not a tautology.
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4025:       -- `execFullA_exerciseA_recurses` ∘ `execFullA_attests_per_asset` (discharged below). NO
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4110:A left-to-right, all-or-nothing chain where EACH inner action attests its own per-action
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4117:`execFullA_exerciseA_recurses` ∘ `execFullA_attests_per_asset` ∘ `innerActions_attest_of_execInnerA`. -/
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4124:/-- **`execFullA_attests_per_asset` — THE PER-ASSET OP-SET IS STEP-COMPLETE BY CONSTRUCTION
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4125:.** Every committed `FullActionA` attests its full `StepInv` content: the per-asset ledger
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4127:`execFull_attests`, carrying the conservation VECTOR (not the scalar). The `exerciseA` arm now
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4129:the mutually-recursive `execInnerA_attests` — the executor's `execInnerA` run is refined to the
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4131:theorem execFullA_attests_per_asset {s s' : RecChainedState} {fa : FullActionA}
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4187:             execInnerA_attests _ s' inner hinner⟩
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4239:/-- **`execInnerA_attests` — the executor inner-fold REFINES the independent `innerActionsAttest`.** A
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4241:action attests its own `fullActionInvA` (via the mutually-recursive `execFullA_attests_per_asset`)
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4245:theorem execInnerA_attests (s s' : RecChainedState) (inner : List FullActionA)
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4257:          exact ⟨s1, execFullA_attests_per_asset ha, execInnerA_attests s1 s' rest h⟩
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4260:/-- **`execFullTurnA_each_attests`.** Step-completeness holds at EVERY action of a committed
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4262:all-or-nothing fold. The per-asset analog of `execFullTurn_each_attests` — the carrier the forest's
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4263:per-node attestation (`FullForest.execFullForestA_each_attests`) lifts off the bridge. -/
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4264:theorem execFullTurnA_each_attests :
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4275:          · subst hbeq; exact ⟨s, s1, ha, execFullA_attests_per_asset ha⟩
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4276:          · exact execFullTurnA_each_attests s1 s' rest h b hbrest
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4300:#assert_axioms execFull_attests
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4303:#assert_axioms execFullTurn_each_attests
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4324:#assert_axioms execFullA_attests_per_asset
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4325:#assert_axioms execFullTurnA_each_attests
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4342:-- `execFullA_attests_per_asset` (re-extended above) carries ALL into the forest by construction
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4367:-- all pinned kernel-clean. The keystone `execFullA_attests_per_asset` (re-extended above) carries
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4393:-- keystone `execFullA_attests_per_asset` (re-extended above) carries ALL into the forest by
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4687:`introduceA 0 1 7` against the live fixture `fmaA` (a real per-asset step attests its full invariant,
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4688:via `execFullA_attests_per_asset`), and REFUTES any same-state instance `fullActionInvA s fa s` (the
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4695:  · -- ACCEPTED: the fixture step commits and attests its full per-asset invariant.
metatheory/Dregg2/Exec/TurnExecutorFull.lean:4697:    exact ⟨s', hs', execFullA_attests_per_asset hs'⟩
metatheory/Dregg2/Proof/LTS.lean:371:-- OPEN: the cross-cell / whole-history graph bookkeeping lifted to a multi-cell adversary model
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:8:STRAND / LIGHT-CLIENT layer: a history is a `List ChainStep` (each carrying an executor witness
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:11:(`light_client_verifies_whole_history`), with an apex anti-ghost (tamper any seam ⇒ reject).
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:38:  * `argus_strand_light_client` — **THE APEX.** Threaded into `light_client_verifies_whole_history`
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:42:    history. Plus `argus_strand_conserves` (value conserved over the whole Argus strand) and the apex
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:59:   (`RecursiveAggregation`) names `EngineSound.leaf_sound : verify p = true → recCexec s.pre s.turn =
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:82:   WellFormedChain wellformed_is_run wellformed_history_conserves seam_roots_chain
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:85:  (Aggregate EngineSound AggregateAttests light_client_verifies_whole_history
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:86:   attested_history_is_run attested_history_conserves tampered_aggregate_cannot_bind
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:145:point: the Argus-produced strand IS a genuine verified-executor history. -/
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:175:verified-executor history produced by the Argus IR. -/
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:212:/-! ## §4 — THE APEX: the light client verifies the whole Argus history.
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:216:(`EngineSound`, REUSED) — learns the whole Argus history executed correctly, is correctly
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:223:public final root is the genuine fold of the whole Argus history — UNDER the layer's named, realizable
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:224:engine-soundness hypotheses (`EngineSound`, REUSED verbatim). The strand the layer's headline talks
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:227:`argus_strand_stateChained`), pinning that the attested history is the actual Argus producer's run — not
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:228:merely some list satisfying `EngineSound`. -/
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:237:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:243:  ⟨light_client_verifies_whole_history Proof verify CH RH cmb compress compressN agg g steps es hroot,
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:249:that each Argus turn in the history is a real verified-executor step. -/
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:258:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:265:verified record cell over the whole Argus history, having re-executed nothing. Rides the layer's
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:275:aggregate over an Argus strand trusts a no-mint/no-burn history of arbitrary length, having re-executed
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:276:nothing. Rides the layer's `wellformed_history_conserves` over the Argus strand's `StateChained`
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:283:  wellformed_history_conserves g steps (argus_strand_stateChained g turns steps hstrand)
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:287:The connection is only meaningful if the aggregate cannot attest a BROKEN Argus history. We surface the
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:300:REJECTS a tampered Argus history — tampering any guarantee-relevant seam-state field (which
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:308:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g [s, s'])
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:316:proof in the Argus strand's aggregate attests the transition of ITS OWN positionally-paired Argus step,
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:327:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g (s :: ss))
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:393:Argus history. So the apex/run/conservation theorems apply to a REAL non-empty Argus strand. -/
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:2:# Dregg2.Circuit.EngineSoundOfApex — THE WELD: discharge `EngineSound.leaf_sound` BY the single-turn apex.
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:4:**The high-leverage weld.** The multi-turn / finalized-history / distributed light-client stack
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:5:(`RecursiveAggregation.light_client_verifies_whole_history`,
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:6:`FinalizedLightClient.light_client_accepts_finalized_history`) rides `RecursiveAggregation.EngineSound`,
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:7:whose per-step obligation `leaf_sound` ASSERTS that each verifying leaf proof attests its step's
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:14:This module WELDS them: it builds an `EngineSound` whose `leaf_sound` is DERIVED from the apex — so the
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:61:  * `engineSound_of_apex` — BUILDS `RecursiveAggregation.EngineSound` from a `Forall₂` of
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:67:    into `light_client_verifies_whole_history` / `light_client_accepts_finalized_history`, the multi-turn
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:68:    + finalized-history attestations now follow from {the apex + the recursion legs}, with `leaf_sound`
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:82:namespace Dregg2.Circuit.EngineSoundOfApex
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:95:open Dregg2.Circuit.RecursiveAggregation (Aggregate EngineSound)
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:103:`Proof`/`verify` are the OPAQUE aggregation-engine carriers (the same the `Aggregate`/`EngineSound`
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:182:/-! ## §4 — `engineSound_of_apex` — BUILD `EngineSound` (discharge `leaf_sound`) FROM the apex.
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:186:`EngineSound` legs (`recursive_sound` = the FRI recursive-verifier soundness, `binding_sound` = the
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:191:/-- **`leafSound_of_bundles`.** The `EngineSound.leaf_sound` field — the positional `Forall₂` that
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:192:"each verifying leaf attests its step's `recCexec`" — built by mapping the apex (`leafStep_of_bundle`)
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:208:/-- **`engineSound_of_apex` — THE WELD.** Builds `RecursiveAggregation.EngineSound` from:
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:215:The resulting `EngineSound` is the one `light_client_verifies_whole_history` /
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:216:`light_client_accepts_finalized_history` ride — with `leaf_sound` now resting on the single-turn apex. -/
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:233:    EngineSound Proof verify CH' RH' cmb' compress' compressN' agg g steps where
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:244:(`RecursiveAggregation.light_client_verifies_whole_history`) and the finalized-history headline
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:245:(`FinalizedLightClient.light_client_accepts_finalized_history`): both now follow from {the apex's
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:246:per-leaf bundles + the two recursion legs}, with `EngineSound.leaf_sound` discharged by circuit
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:261:/-- **`multiTurn_rests_on_apex`.** The whole-history attestation
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:263:obtained WITHOUT carrying `EngineSound` as a free sibling: its `leaf_sound` is the apex
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:282:  Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:289:/-- **`finalized_rests_on_apex`.** The three-leg finalized-history verdict
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:290:(`FinalizedLightClient.FinalizedHistoryAttested` — the whole correct history PLUS the BFT-quorum
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:291:finalization) obtained with `EngineSound.leaf_sound` discharged by the apex. The whole distributed
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:313:  Dregg2.Distributed.FinalizedLightClient.light_client_accepts_finalized_history
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:361:end Dregg2.Circuit.EngineSoundOfApex
metatheory/Dregg2/Proof/WPCatalog.lean:87:The eDSL surface IS the verified term: `recReplay_preserves_sumEquals`/`recCexec_attests` apply to
metatheory/Dregg2/Time/Deadline.lean:53:  * `frameWithin fs att` — a FRAME CONVENTION: "authority `fs.authority` attests frame-time `fs.T`
metatheory/Dregg2/Time/Deadline.lean:61:  /-- The FRAME-CONVENTION deadline: authority attests `fs` (with explicit `δ`), witnessed by `att`. -/
metatheory/Dregg2/Time/Deadline.lean:188:  * an ACCEPTED frame attestation `hacc : FrameWithin reg stmtOf fs att` (the authority attests `T`
metatheory/Dregg2/Time/Deadline.lean:298:/-- A demo frame deadline: authority attests `(T=1000, δ=5)`. -/
metatheory/Dregg2/Distributed/FeeHistory.lean:2:# Dregg2.Distributed.FeeHistory — the Argus FEE-WRAPPED history conserves MODULO THE BURN.
metatheory/Dregg2/Distributed/FeeHistory.lean:5:conservation"). `Distributed/HistoryAggregation.lean` proves `wellformed_history_conserves`: a
metatheory/Dregg2/Distributed/FeeHistory.lean:7:the whole history. But the deployed turn is not the bare body: `Circuit/Argus/Turn.lean`'s
metatheory/Dregg2/Distributed/FeeHistory.lean:17:wired, live, and distinct); `wellformed_history_conserves_modulo_burn` proves that over any
metatheory/Dregg2/Distributed/FeeHistory.lean:25:arbitrary-length fee-wrapped history is the named protocol sink, additively.
metatheory/Dregg2/Distributed/FeeHistory.lean:38:  (`feeStep_conserves_modulo_burn`), and the whole-history fold.
metatheory/Dregg2/Distributed/FeeHistory.lean:45:* This is the LEGACY-SCALAR fee law composed over history (`recTotal`, the scalar `balance`
metatheory/Dregg2/Distributed/FeeHistory.lean:48:  the executor swaps onto it at the VK rotation, this history law collapses to `totalBurn = 0`
metatheory/Dregg2/Distributed/FeeHistory.lean:149:/-- **One accepted fee-wrapped turn of the history**: the host context, the turn header, the
metatheory/Dregg2/Distributed/FeeHistory.lean:231:re-proving it): the fee-wrapped history sits ON the body-executor strand the light client
metatheory/Dregg2/Distributed/FeeHistory.lean:252:/-! ## §4 — The whole-history fold: conservation MODULO the summed burn. -/
metatheory/Dregg2/Distributed/FeeHistory.lean:265:/-- **The total burn of the history**: the sum of each accepted turn's burned fee residue. -/
metatheory/Dregg2/Distributed/FeeHistory.lean:269:/-- **THE KEYSTONE — `wellformed_history_conserves_modulo_burn`.** Over ANY state-chained
metatheory/Dregg2/Distributed/FeeHistory.lean:270:fee-wrapped history, the endpoint ledger total PLUS the summed per-turn burns equals the genesis
metatheory/Dregg2/Distributed/FeeHistory.lean:272:whole-history composition of the per-turn fee law: arbitrary-length histories leak EXACTLY the
metatheory/Dregg2/Distributed/FeeHistory.lean:274:`wellformed_history_conserves` is the `totalBurn = 0` face of this.) -/
metatheory/Dregg2/Distributed/FeeHistory.lean:275:theorem wellformed_history_conserves_modulo_burn (g : RecChainedState)
metatheory/Dregg2/Distributed/FeeHistory.lean:292:#assert_axioms wellformed_history_conserves_modulo_burn
metatheory/Dregg2/Distributed/FeeHistory.lean:361:/-- The whole-history keystone FIRES on the (one-step) real fee chain. -/
metatheory/Dregg2/Distributed/FeeHistory.lean:362:theorem demo_history_conserves_modulo_burn :
metatheory/Dregg2/Distributed/FeeHistory.lean:365:  wellformed_history_conserves_modulo_burn ts0 [demoStep] ⟨rfl, trivial⟩
metatheory/Dregg2/Distributed/FeeHistory.lean:369:#assert_axioms demo_history_conserves_modulo_burn
metatheory/Dregg2/Circuit/Emit/EffectVmEmitV2.lean:1296:engine binding, the program VK a Custom row attests is FORCED by its `custom_proof_commitment`: a
metatheory/Dregg2/Time/Frame.lean:7:`F` (a fault-tolerant clock-sync quorum, Lamport–Melliar-Smith 1985) attests a frame-time `t`, valid
metatheory/Dregg2/Time/Frame.lean:72:attests its frame-clock has reached `T`, within skew `δ`. TrueTime's `TT.after(T)` with the interval
metatheory/Dregg2/Time/Frame.lean:244:as a `TimeAuthority`. The freshness bit becomes "the time authority attests `now` lies within `δ` of
metatheory/Dregg2/Time/Frame.lean:302:/-- A frame claim: authority `F` attests frame-time `T = 1000` within skew `δ = 5`. -/
metatheory/Dregg2/Exec/ConsensusExec.lean:7:`RecChainedState`, the content-addressed cell with `recCexec_attests`/`recChained_run_conserves`)
metatheory/Dregg2/Exec/ConsensusExec.lean:15:super-ratified leader (`Proof.CordialMiners.Committed`) *anchors* a segment, and the segment's
metatheory/Dregg2/Exec/ConsensusExec.lean:16:blocks are linearized (the intra-segment `xsort` tie-break, OPEN-CM-XSORT). The node then
metatheory/Dregg2/Exec/ConsensusExec.lean:28:   `some` branch every step `recCexec_attests`, so:
metatheory/Dregg2/Exec/ConsensusExec.lean:33:   * `finalized_attests_each` — every finalized step attests `recFullStepInv` (Conservation ∧
metatheory/Dregg2/Exec/ConsensusExec.lean:55:  (`OPEN-CM-XSORT`, the intra-segment tie-break) — `cordial_agreement` is about *which leader
metatheory/Dregg2/Exec/ConsensusExec.lean:70:`recCexec_attests`/`recChained_run_conserves`/`cordial_*` lemmas. Verified with
metatheory/Dregg2/Exec/ConsensusExec.lean:102:maps each finalized block to its segment's leader; `anchor_committed` is the finality evidence
metatheory/Dregg2/Exec/ConsensusExec.lean:108:  /-- Each finalized block's segment-anchoring committed leader. -/
metatheory/Dregg2/Exec/ConsensusExec.lean:183:/-- **`finalized_sound`.** Any state-predicate `Good` preserved by every step that attests
metatheory/Dregg2/Exec/ConsensusExec.lean:353:Every keystone rides only fully-proved lemmas: `recCexec_attests` / `recChained_run_conserves` /
metatheory/Dregg2/Distributed/FinalityGate.lean:108:/-- Parse the `B=` lace segment (a `|`-separated list of `BLOCKW`, or empty). -/
metatheory/Dregg2/Distributed/FinalityGate.lean:125:  -- split into the three `;`-separated segments: "<w>", "P=<...>", "B=<...>".
metatheory/Dregg2/Distributed/FinalityGate.lean:127:  | [wS, pSeg, bSeg] =>
metatheory/Dregg2/Distributed/FinalityGate.lean:129:      let pS ← stripReq? "P=" pSeg
metatheory/Dregg2/Distributed/FinalityGate.lean:130:      let bS ← stripReq? "B=" bSeg
metatheory/Dregg2/Circuit/TurnAdmission.lean:6:refinement (what the commit-time STARK over the folded turn circuit attests, supplied as `hstep`) plus
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:2:# Dregg2.Distributed.FinalizedLightClient — the THREE-LEG finalized-history light client.
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:7:(`light_client_verifies_whole_history`). But "internally correct" is NOT "finalized": a valid
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:16:  (1) the succinct aggregate verifies  (the recursion engine — `RecursiveAggregation.EngineSound`),
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:21:When all three hold, the light client obtains `FinalizedHistoryAttested`: the whole history executed
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:22:correctly + is correctly ordered + value is conserved over the whole history + the endpoint root it
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:28:trusts a *correct-looking* history, not a *finalized* one — the exact gap a fork attack exploits. Leg
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:35:soundness — carried, exactly as in `RecursiveAggregation`, by the NAMED, REALIZABLE `EngineSound`
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:52:  (Aggregate EngineSound AggregateAttests light_client_verifies_whole_history)
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:84:NOT see the whole history — only this certificate + the aggregate. -/
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:142:must equal the `finalizedRoot` (so the proven-correct history's endpoint IS the shown root), and the
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:144:equalities glue "the proof attests this root" to "the quorum finalized this root". -/
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:148:three legs talk about ONE root — without it, an adversary could pair a valid proof of history A with a
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:149:valid finality cert for history B. -/
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:156:/-! ## 3. THE THREE-LEG HEADLINE — verifying aggregate + cert + binding attests a FINALIZED history. -/
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:159:`(agg, finalizedRoot, cert)` when all three legs hold: the whole-history correctness of
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:163:whole history that executed correctly AND was finalized by a supermajority — and I re-executed
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:168:  /-- Leg 1+2: the whole history is correct (every turn executed, correctly ordered, genuine fold). -/
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:169:  history : AggregateAttests Proof CH RH cmb compress compressN agg g steps
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:173:  attested correct history's endpoint IS the quorum-finalized root the client trusts. -/
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:176:/-- **`light_client_accepts_finalized_history` (THE THREE-LEG HEADLINE).**
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:182:obtains `FinalizedHistoryAttested`: the whole history executed correctly + is correctly
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:184:ride `light_client_verifies_whole_history` (under the named `EngineSound`); leg 3 is fully proved from
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:186:count IS the trust in the whole FINALIZED history — gap-free, no prose seam. -/
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:187:theorem light_client_accepts_finalized_history
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:190:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:195:  { history := light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:203:conservation over the WHOLE finalized history — the client trusts a no-mint/no-burn ledger reaching a
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:206:/-- **`finalized_history_conserves` (KEYSTONE).** A light client that accepts a finalized
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:207:history (the three legs) inherits value conservation over the whole history: the ledger total at the
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:209:is finalized*; this rides `HistoryAggregation.wellformed_history_conserves` for *that the conserved
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:211:theorem finalized_history_conserves
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:214:  Dregg2.Distributed.HistoryAggregation.wellformed_history_conserves g steps hch
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:274:hold, the finalized-history light client concludes `FinalizedHistoryAttested` over the
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:277:`light_client_accepts_finalized_history` is non-vacuous — it fires on a real chain finalized by a real
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:286:  light_client_accepts_finalized_history RealProof acceptAll zCH zRH zcmb zcompress zcompressN
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:292:AND a real executor step for the (only) turn of the realizing history (from leg 1). So the finalized
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:303:  have h := fired.history.every_turn
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:324:    cannot satisfy `Bound` (the seam tooth), so a valid proof of history A cannot be paired with a
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:372:history A (proving root `rA`) with a finality cert that finalized a DIFFERENT root `rB ≠ rA`. The seam
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:396:#assert_axioms Dregg2.Distributed.FinalizedLightClient.light_client_accepts_finalized_history
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:397:#assert_axioms Dregg2.Distributed.FinalizedLightClient.finalized_history_conserves
metatheory/Dregg2/Exec/FullForest.lean:7:the forest (`execForest_no_amplify`) and the four `StepInv` conjuncts (`execForest_attests`).
metatheory/Dregg2/Exec/FullForest.lean:39:  * **`execFullForestA_each_attests`** — every tree node attests its `fullActionInvA` (the per-asset
metatheory/Dregg2/Exec/FullForest.lean:41:    bridge into `execFullTurnA_each_attests`;
metatheory/Dregg2/Exec/FullForest.lean:266:`execFullTurnA` theorem (`execFullTurnA_ledger_per_asset`, `execFullTurnA_each_attests`, …) to the
metatheory/Dregg2/Exec/FullForest.lean:446:/-! ## §7 — Per-node attestation: every tree node attests its `fullActionInvA` (membership-lift).
metatheory/Dregg2/Exec/FullForest.lean:449:`execFullTurnA_each_attests` proves every action of the committed lowered turn attests `fullActionInvA`
metatheory/Dregg2/Exec/FullForest.lean:451:tree node attests its per-asset step-completeness. -/
metatheory/Dregg2/Exec/FullForest.lean:484:/-- **`execFullForestA_each_attests` (per-node step-completeness, whole tree).** Every node
metatheory/Dregg2/Exec/FullForest.lean:485:of a committed full-forest attests its `fullActionInvA`: the per-asset ledger VECTOR ∧ ChainLink ∧
metatheory/Dregg2/Exec/FullForest.lean:486:ObsAdvance ∧ the kind-specific obligation. Read through the bridge into `execFullTurnA_each_attests`
metatheory/Dregg2/Exec/FullForest.lean:490:theorem execFullForestA_each_attests (s s' : RecChainedState) (f : FullForestA)
metatheory/Dregg2/Exec/FullForest.lean:494:  exact execFullTurnA_each_attests s s' (lowerForestA f) h
metatheory/Dregg2/Exec/FullForest.lean:496:/-- **The root node itself attests (corollary).** The root's own action attests its
metatheory/Dregg2/Exec/FullForest.lean:499:theorem execFullForestA_root_attests (s s' : RecChainedState) (f : FullForestA)
metatheory/Dregg2/Exec/FullForest.lean:502:  execFullForestA_each_attests s s' f h f.action (execFullForestA_node_mem_lowered f)
metatheory/Dregg2/Exec/FullForest.lean:528:carried CG-5; `crossForest_no_amplify`; `crossForest_attests`), where the whole-forest conservation is
metatheory/Dregg2/Exec/FullForest.lean:578:    for its effect on `t` (`execFullForestA_each_attests` carries the per-node obligation). The forest
metatheory/Dregg2/Exec/FullForest.lean:663:#assert_axioms execFullForestA_each_attests
metatheory/Dregg2/Exec/FullForest.lean:664:#assert_axioms execFullForestA_root_attests
metatheory/Dregg2/Exec/FullForest.lean:939:  * `execFullForestA_each_attests` (+ `_root_attests`) — every node attests its `fullActionInvA` (the
metatheory/Dregg2/Exec/FullForest.lean:953:--   Σ=0 binding-carried CG-5; `crossForest_no_amplify`; `crossForest_attests`). This module is the
metatheory/Dregg2/Circuit/Emit/EffectVmEmitReceiptArchiveWide.lean:78:gate segment. NEITHER reads the hash sites, so the runnable per-cell soundness depends ONLY on the gates
metatheory/Dregg2/Circuit/Emit/EffectVmEmitReceiptArchiveWide.lean:83:gates (a constraint-list segment), on an audit-write row decoded by `ArchiveRowEncodes`, force
metatheory/Dregg2/Apps/AgentOrchestration.lean:22:  * auth gate committed⇒(credential ∧ caveats): `execFullForestG_root_attests` on the gated tree.
metatheory/Dregg2/Apps/AgentOrchestration.lean:193:keystone `execFullForestG_root_attests` gives the attestation on a committed node; `execFullForestG_unauthorized_fails`
metatheory/Dregg2/Apps/AgentOrchestration.lean:201:∧ caveats discharged.** If the good gated forest commits, its root attests `gatedActionInvG`:
metatheory/Dregg2/Apps/AgentOrchestration.lean:203:`execFullForestG_root_attests` on the concrete `goodFullForestG`. -/
metatheory/Dregg2/Apps/AgentOrchestration.lean:213:    execFullForestG_root_attests world s' goodFullForestG h
metatheory/Dregg2/Apps/AgentOrchestration.lean:247:  * **every committed node attested its StepInv** — `execFullForestA_each_attests` (per-asset ledger
metatheory/Dregg2/Apps/AgentOrchestration.lean:283:/-- **`orchestration_each_attests` — ⑥c every committed node attested its StepInv.** Every node attests
metatheory/Dregg2/Apps/AgentOrchestration.lean:285:`execFullForestA_each_attests` on the concrete run, inherited. -/
metatheory/Dregg2/Apps/AgentOrchestration.lean:286:theorem orchestration_each_attests (s' : RecChainedState)
metatheory/Dregg2/Apps/AgentOrchestration.lean:290:  execFullForestA_each_attests world s' orchestration h
metatheory/Dregg2/Apps/AgentOrchestration.lean:313:#assert_axioms orchestration_each_attests
metatheory/Dregg2/Apps/AgentOrchestration.lean:425:  certifies "gate_committed_implies_credential_and_caveats (= execFullForestG_root_attests)"
metatheory/Dregg2/Apps/AgentOrchestration.lean:439:  certifies "orchestration_conserves ∧ orchestration_no_amplify ∧ orchestration_each_attests"
metatheory/Dregg2/Circuit/Emit/EffectVmEmitEmitEventWide.lean:78:gates (a constraint-list segment), on an emit row decoded by `RowEncodesEmit` with `s_noop = 0`, force
metatheory/Dregg2/Distributed/CheckpointPrune.lean:6:# NEVER drops a finalized turn from the RECOVERABLE history, and a node that recovers from a
metatheory/Dregg2/Distributed/CheckpointPrune.lean:53:  deleted. So the prune is a STORAGE operation only; it does not erase causal history.
metatheory/Dregg2/Distributed/CheckpointPrune.lean:177:  /-- The blake3 content hash the federation QC attests (`checkpoint.rs:97 content_hash`). -/
metatheory/Dregg2/Distributed/CheckpointPrune.lean:282:the hot store, but NO id is lost to the recoverable history — `catchupOnto_keyset` shows the recovered
metatheory/Dregg2/Distributed/CheckpointPrune.lean:324:NEVER drops a finalized turn from the recoverable history: the finalized prefix is preserved
metatheory/Dregg2/Distributed/CheckpointPrune.lean:382:the prune deleted. So `--enable-pruning` bounds storage growth WITHOUT erasing any causal history —
metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:591:/-- The selector-binding gate, as a one-element constraint list (the descriptor segment). -/
metatheory/Dregg2/Circuit/Emit/EffectVmFullStateRunnable.lean:359:The per-row gates of the transfer descriptor (a constraint-list segment), on a transfer row decoded by
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBurnRunnable.lean:92:gates of `burnVmDescriptor` (a constraint-list segment), on a burn row decoded by `RowEncodes`, force
metatheory/Dregg2/Exec/Durability.lean:342:`(live (durTraj s sched n)).isSome` for all `n`. So a crash at any point in the system's entire history is
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:18:     (union of causal pasts of ratifying wave-end blocks), take the blocks NEW to this segment
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:49:* `xsort` intra-segment tie-break is the OPEN-CM-XSORT residual (named in `ConsensusExec`); here we
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:50:  linearize a segment by `(round, id)` — deterministic, causal-respecting on the traces we exhibit;
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:235:append. The intra-segment linearization is the OPEN-CM-XSORT residual; here we sort by `(round, id)`
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:249:/-- Deterministic intra-segment linearization by `(round, id)` — the OPEN-CM-XSORT stand-in. A
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:256:/-- **`leaderSegment B participants wavelength prevCovered l`** — the blocks a final leader `l`
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:258:from the leader, linearized by `xsortBy`. The per-leader segment of `ordering.rs::tau`'s loop
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:261:def leaderSegment (B : Lace) (participants : List AuthorId) (wavelength : Nat)
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:271:segment to the order accumulated so far, and replace `prevCovered` with this leader's coverage
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:276:  (acc.1 ++ leaderSegment B participants wavelength acc.2 l,
metatheory/Dregg2/Circuit/Emit/EffectVmEmitMintRunnable.lean:88:gates of `mintVmDescriptor` (a constraint-list segment), on a mint row decoded by `RowEncodes`, force
metatheory/Dregg2/Circuit/Emit/EffectVmEmitExerciseWide.lean:79:gates (a constraint-list segment), on an exercise row decoded by `RowEncodesExercise`, force
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapReshape.lean:6:properties a light client must trust WITHOUT re-running history:
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapReshape.lean:496:/-! ### §4.1 — the descriptor's constraint segments. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapReshape.lean:648:/-- The non-amp segment has `3·MASK_BITS + 2` gates (held-bool + granted-bool + submask + 2 recon), and
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapReshape.lean:649:the production segment has 2 (the PI binding + the control gate). The descriptor is non-trivial. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapReshape.lean:783:/-- The delegation non-amp segment has `3·MASK_BITS + 2` gates (held-bool + granted-bool + submask + 2
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoopWide.lean:108:gates (a constraint-list segment), on a row decoded by `RowEncodes`, force `CellFreezeSpec` (the whole
metatheory/Dregg2/Circuit/Emit/EffectVmEmitPipelinedSendWide.lean:87:per-row gates (a constraint-list segment), on a pipelined-send row decoded by `RowEncodesSend`, force
metatheory/Dregg2/Exec/FFI.lean:774:`_each_attests` (`TurnExecutorFull.lean §10`): every committed turn attests the four StepInv
metatheory/Dregg2/Exec/FFI.lean:1056:`_no_amplify` / `_each_attests` (`FullForest.lean §5-§7`). The codec carries the `Authorization`
metatheory/Dregg2/Exec/FFI.lean:2788:`_conserves_per_asset` / `_no_amplify` / `_each_attests`). The envelope fields + the per-node
metatheory/Dregg2/Exec/FFI.lean:3250:`execFullForestG`, carrying `execFullForestG_conserves_per_asset` / `_no_amplify` / `_each_attests` /
metatheory/Dregg2/Claims.lean:70:`cexec_attests` realizes `Core.ConservesStep` as a theorem about the executable machine;
metatheory/Dregg2/Claims.lean:73:#assert_axioms Dregg2.Exec.cexec_attests
metatheory/Dregg2/Claims.lean:79:#assert_axioms Dregg2.Exec.RecordCell.recCexec_attests
metatheory/Dregg2/Claims.lean:127:/-! ## §6 — Spec.Authority: the generative capability graph (whole-history closure OPEN). -/
metatheory/Dregg2/Claims.lean:278:  * whole-history connectivity closure: PROVED — `ExecRefinementFull.onlyConnectivityCloses`
metatheory/Dregg2/Claims.lean:417:`ProofForest`: per-node `StepProofValid` × `Linked` ⇒ whole forest attests StepInv.
metatheory/Dregg2/Exec/GatedForestCfg.lean:247:via `execFullAGated_attests`), and REFUTES the SAME node taken to its own pre-state (the `fullActionInvA`
metatheory/Dregg2/Exec/GatedForestCfg.lean:255:  · -- ACCEPTED: the gated transfer commits and attests all four conjuncts.
metatheory/Dregg2/Exec/GatedForestCfg.lean:260:    exact ⟨s', hga, execFullAGated_attests fma0 s' (mkAuth goodCred [trueCaveat]) (.balanceA ⟨0, 0, 1, 30⟩ 0) hga⟩
metatheory/Dregg2/Finality.lean:4:Canonicity — *which valid history is THE history* — is a per-cell pluggable tier layered
metatheory/Dregg2/Finality.lean:92:/-- **The one underlying history substrate: a CvRDT DAG.** Per §2.2 the four tiers all
metatheory/Dregg2/Finality.lean:98:/-- **Quorum / commit predicate (kept abstract).** `committed H h` says block/history
metatheory/Dregg2/Finality.lean:104:/-- **`Canonical` — which valid history is THE history (§2.2 canonicity).** The single
metatheory/Dregg2/Finality.lean:130:is the rule's soundness obligation — a committed history is the canonical one. -/
metatheory/Dregg2/Finality.lean:244:no-downgrade safety property lives over: the *commit history* of one value, where each
metatheory/Dregg2/Exec/Gas.lean:5:transaction, step-complete by construction (`execFull_attests`, `execFullTurn_ledger`,
metatheory/Dregg2/Exec/Gas.lean:14:metering does not alter semantics), and therefore the resulting state still attests everything
metatheory/Dregg2/Exec/Gas.lean:38:  * `gas_preserves_attests`     — every action of a committed metered run attests `fullActionInv`
metatheory/Dregg2/Exec/Gas.lean:39:                                  (delegates to `execFullTurn_each_attests`) — gas removes no safety.
metatheory/Dregg2/Exec/Gas.lean:228:/-! ## §6 — Safety preserved: a committed metered run still attests everything `execFull` does.
metatheory/Dregg2/Exec/Gas.lean:234:(`execFullTurn_each_attests`). Gas adds a liveness bound and removes no safety. -/
metatheory/Dregg2/Exec/Gas.lean:276:/-- **`gas_preserves_attests`.** Every action of a committed metered run attests its full
metatheory/Dregg2/Exec/Gas.lean:279:`execFullTurn_each_attests`. Gas adds a liveness bound and removes NO safety. -/
metatheory/Dregg2/Exec/Gas.lean:280:theorem gas_preserves_attests (budget : Nat) (acts : List FullAction) (s s' : RecChainedState)
metatheory/Dregg2/Exec/Gas.lean:283:  execFullTurn_each_attests s s' acts (execGas_refines_execFullTurn budget acts s s' g h)
metatheory/Dregg2/Exec/Gas.lean:296:#assert_axioms gas_preserves_attests
metatheory/Dregg2/Proof/CrossCellLTS.lean:2:# Dregg2.Proof.CrossCellLTS — the CROSS-CELL operational LTS (bilateral whole-history forward
metatheory/Dregg2/Proof/CrossCellLTS.lean:8:pole named at `LTS.lean §8 OPEN` is the **cross-cell / whole-history** lift — a `JointTurn` over
metatheory/Dregg2/Proof/CrossCellLTS.lean:262:the ledger pair (a whole history of cross-cell turns). Head-recursive (one step prepended), so the
metatheory/Dregg2/Proof/CrossCellLTS.lean:276:/-- **`crossAbsRun_forward`.** The whole-history cross-cell forward simulation:
metatheory/Dregg2/Protocol/Workflow.lean:124:receipt; prior history is never rewritten (the log is append-only). -/
metatheory/Dregg2/Exec/RecordCell.lean:18:`Exec/StepComplete.lean`'s `cexec_attests`: the program **gates the arrow**.
metatheory/Dregg2/Exec/RecordCell.lean:113:the executable `denote`-only-tightens fact for the record cell (the `cexec_attests` shadow at the
metatheory/Dregg2/Exec/FullForestAuth.lean:7:(`execFullForestA_each_attests`). But that executor is **credential-BLIND**: it authorizes a node
metatheory/Dregg2/Exec/FullForestAuth.lean:41:    cap-authority ∧ caveats-discharged) onto the UNCHANGED `fullActionInvA`. `execFullAGated_attests`
metatheory/Dregg2/Exec/FullForestAuth.lean:42:    and `execFullForestG_each_attests` prove every committed node carries them — credential-blindness
metatheory/Dregg2/Exec/FullForestAuth.lean:1025:onto the UNCHANGED `fullActionInvA`. `execFullAGated_attests` proves a committed gated node carries all
metatheory/Dregg2/Exec/FullForestAuth.lean:1026:four (the gate Bools forced true by `gatedNode_check_eq_use`, the fourth by `execFullA_attests_per_asset`
metatheory/Dregg2/Exec/FullForestAuth.lean:1027:UNCHANGED). `execFullForestG_each_attests` lifts it forest-wide; `execFullForestG_unauthorized_fails`
metatheory/Dregg2/Exec/FullForestAuth.lean:1041:/-- **`execFullAGated_attests` (the committed⇒all-four headline, per node).** Every committed
metatheory/Dregg2/Exec/FullForestAuth.lean:1042:gated node attests `gatedActionInvG`: credential-valid ∧ cap-authority ∧ caveats-discharged ∧ the full
metatheory/Dregg2/Exec/FullForestAuth.lean:1046:`execFullA_attests_per_asset` UNCHANGED. -/
metatheory/Dregg2/Exec/FullForestAuth.lean:1047:theorem execFullAGated_attests (s s' : RecChainedState)
metatheory/Dregg2/Exec/FullForestAuth.lean:1058:  exact ⟨h3.1, h3.2.1, h3.2.2, execFullA_attests_per_asset hfa⟩
metatheory/Dregg2/Exec/FullForestAuth.lean:1079:/-- **`execFullTurnG_each_attests`.** Every `(na, a)` of a committed gated linear turn attests
metatheory/Dregg2/Exec/FullForestAuth.lean:1082:theorem execFullTurnG_each_attests (s s' : RecChainedState)
metatheory/Dregg2/Exec/FullForestAuth.lean:1103:            exact ⟨s, s1, hga, execFullAGated_attests s s1 na a hga⟩
metatheory/Dregg2/Exec/FullForestAuth.lean:1106:/-- **`execFullForestG_each_attests` (per-node step-completeness, whole gated tree).** Every
metatheory/Dregg2/Exec/FullForestAuth.lean:1107:node `(na, a)` of a committed gated full-forest attests its `gatedActionInvG`: credential passed the §8
metatheory/Dregg2/Exec/FullForestAuth.lean:1110:(`execFullForestG_eq_execFullTurnG`) into `execFullTurnG_each_attests` over the pre-order lowering. -/
metatheory/Dregg2/Exec/FullForestAuth.lean:1111:theorem execFullForestG_each_attests (s s' : RecChainedState)
metatheory/Dregg2/Exec/FullForestAuth.lean:1118:  exact execFullTurnG_each_attests s s' (lowerForestG f) h
metatheory/Dregg2/Exec/FullForestAuth.lean:1120:/-- **`execFullForestG_root_attests` (corollary).** The root node's own `(auth, action)`
metatheory/Dregg2/Exec/FullForestAuth.lean:1121:attests its `gatedActionInvG` (the per-node membership-lift specialized to the root — the root pair is
metatheory/Dregg2/Exec/FullForestAuth.lean:1123:theorem execFullForestG_root_attests (s s' : RecChainedState)
metatheory/Dregg2/Exec/FullForestAuth.lean:1133:  exact execFullForestG_each_attests s s' ⟨na, a, kids⟩ h (na, a) hmem
metatheory/Dregg2/Exec/FullForestAuth.lean:1167:#assert_axioms execFullAGated_attests
metatheory/Dregg2/Exec/FullForestAuth.lean:1169:#assert_axioms execFullTurnG_each_attests
metatheory/Dregg2/Exec/FullForestAuth.lean:1170:#assert_axioms execFullForestG_each_attests
metatheory/Dregg2/Exec/FullForestAuth.lean:1171:#assert_axioms execFullForestG_root_attests
metatheory/Dregg2/Proof/Refine.lean:42:whole-history connectivity closure (`ExecRefinementFull.OnlyConnectivityCloses`), the contended
metatheory/Dregg2/Proof/Refine.lean:304:cross-vat `refine_cross_vat_step`, async `refine_async_run`), each with teeth. The whole-history
metatheory/Dregg2/Proof/Refine.lean:310:  * **Whole-history connectivity closure** — `Spec.ExecRefinementFull.OnlyConnectivityCloses`:
metatheory/Dregg2/Proof/Refine.lean:328:/-- The whole-history connectivity-closure property, re-exported at this assembly point (the SAME
metatheory/Dregg2/Proof/Refine.lean:333:/-- **The whole-history connectivity closure, PROVED** — re-exported from its home module. Along any
metatheory/Dregg2/Exec/Program.lean:85:  prefix over the record substrate (each path segment is a named scalar). Fail-closed: a missing segment
metatheory/Dregg2/Exec/Program.lean:418:/-- Read the ordered scalar path from a list of segment field-names (`none` if ANY segment is
metatheory/Dregg2/Exec/Program.lean:730:/-- **`prefixOf` admit-char.** Admits IFF the path reads (all segments present) AND the
metatheory/Dregg2/Exec/Program.lean:932:-- prefixOf: a 2-segment path must register UNDER the namespace [10, 20] (owned by the actor).
metatheory/Dregg2/Exec/Program.lean:938:-- REJECT: a segment missing ⇒ fail-closed.
metatheory/Dregg2/Exec/Receipt.lean:14:    or fork history without breaking a `prevHash` link: two well-linked chains agreeing on the
metatheory/Dregg2/Exec/Receipt.lean:15:    head receipt-hash ARE the same history. The hash's collision-resistance is taken as a
metatheory/Dregg2/Exec/Receipt.lean:20:    receipt, lifting the `chainP` (ChainLink) + `obsP` (ObsAdvance) conjuncts of `cexec_attests`.
metatheory/Dregg2/Exec/Receipt.lean:99:or fork history without breaking a `prevHash` link. The collision-resistance of the digest is the
metatheory/Dregg2/Exec/Receipt.lean:122:equal are the SAME chain — i.e. history under a well-linked head is unique; no fork/insert/rewrite
metatheory/Dregg2/Exec/Receipt.lean:124:(the §8 oracle), the head receipt commits to its entire predecessor history: if the heads agree
metatheory/Dregg2/Exec/Receipt.lean:129:Stated via `head?`: "same head receipt ⇒ same history." -/
metatheory/Dregg2/Exec/Receipt.lean:240:of `cexec_attests`. We lift those to the receipt layer: a committed step corresponds to appending
metatheory/Dregg2/Exec/Receipt.lean:251:Lifting `cexec_attests`'s `chainP` (the new log is `t :: oldlog` — the ChainLink) and `obsP` (the
metatheory/Dregg2/Exec/Receipt.lean:257:  have hfull := cexec_attests h
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:16:  1. **OPEN-CM-XSORT — the deterministic intra-segment total order (`ordering.rs::xsort`).**
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:17:     `ordering.rs` orders the blocks *within* a super-ratified segment deterministically, tie-broken
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:20:     segment (a `List Block`), i.e. a genuine total preorder — and define `Block.xsort` (the
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:22:     `xsort_perm`/`xsort_length` (it permutes the segment, losing nothing), `xsort_idem`
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:23:     (determinism: re-sorting is a no-op), and `xsort_segment_total_order` (the output is a
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:24:     **linear extension**: any two distinct segment blocks are strictly comparable by id). This is
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:25:     the within-segment determinism `cordial_agreement` deliberately scoped out — now a theorem.
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:87:/-! ## 1. OPEN-CM-XSORT closed: the deterministic intra-segment total order.
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:89:`ordering.rs::xsort` deterministically orders the blocks *within* a super-ratified segment, tie-
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:90:broken by block id so two honest nodes computing `tau` over the same segment agree on the order.
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:92:transitive, total — over an arbitrary segment, then build the sort and prove it is a genuine
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:93:linear extension (sorted + a permutation of the segment + idempotent). -/
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:102:/-! ### 1a. `xsort_consistency`: reflexive, transitive, total over a segment.
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:104:These are the three laws the task asks for. Stated *over a segment* `seg : List Block` (the
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:105:super-ratified segment `xsort` orders) — though `xleq` is in fact a total preorder on ALL blocks,
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:124:is a genuine total preorder over any segment `seg`: reflexive, transitive, and total on the segment's
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:126:the same segment get the same order. Packaged as one statement over an explicit segment. -/
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:141:/-- **`Block.xsort seg`** (`ordering.rs::xsort`): the deterministic ordering of a segment, sorting
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:142:by block id via insertion sort over `xleq`. The within-segment total order `cordial_agreement`
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:151:/-- **`xsort_perm`** — `xsort` only *reorders*: it is a permutation of the segment, so the
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:152:total order loses no block and invents none (the `tau` segment is exactly the super-ratified blocks,
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:161:/-- **`xsort_mem`** — membership is preserved both ways: a block is in the sorted segment
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:162:iff it was in the segment. -/
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:166:/-- **`xsort_idem` (DETERMINISM).** Re-sorting an already-sorted segment is a no-op:
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:173:/-- **`xsort_segment_total_order` (the linear-extension keystone).** On a *canonical*
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:174:segment (distinct blocks have distinct ids — the content-addressing invariant, exactly
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:175:`Lace.Canonical` restricted to the segment), `xsort` realizes a genuine **linear order**: any two
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:176:DISTINCT blocks of the segment are *strictly* id-comparable (`a.id < b.id ∨ b.id < a.id`), and the
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:177:sorted output puts them in that strict order. So `tau` is a total order on the segment, not merely a
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:178:preorder — the deterministic within-segment ranking `ordering.rs::xsort` guarantees. This closes
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:180:theorem xsort_segment_total_order (seg : List Block)
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:517:#assert_axioms xsort_segment_total_order
metatheory/Dregg2/Verify/AllowanceFactoryProbe.lean:161:before `start` belong to epoch 0's pre-history). The schedule's ground truth the committed cursor is
metatheory/Dregg2/Exec/VatBoundary.lean:51:  have hchain : s'.log = t :: s.log := (cexec_attests h).2.2.1
metatheory/Dregg2/Exec/EffectsSupply.lean:591:  exact (recCexec_attests hc).1
metatheory/Dregg2/Exec/EffectsSupply.lean:607:  exact (recCexec_attests hc).2.1
metatheory/Dregg2/Exec/EffectsSupply.lean:620:  have : s1.log = lockTurn owner lockCell value :: s.log := (recCexec_attests hc).2.2.1
metatheory/Dregg2/Exec/EffectsSupply.lean:641:  (recCexec_attests h).1
metatheory/Dregg2/Exec/EffectsSupply.lean:647:  (recCexec_attests h).2.1
metatheory/Dregg2/Exec/EffectsSupply.lean:655:  have : s'.log = cancelTurn owner lockCell value :: s.log := (recCexec_attests h).2.2.1
metatheory/Dregg2/Exec/StepComplete.lean:5:`stepComplete_preserves`: *if* every step attests the full `StepInv = Conservation ∧
metatheory/Dregg2/Exec/StepComplete.lean:18:ObsAdvance carrier) and prove every committed chained step attests all four conjuncts.
metatheory/Dregg2/Exec/StepComplete.lean:71:/-- **`cexec_attests` — the executable kernel is STEP-COMPLETE.** Every committed
metatheory/Dregg2/Exec/StepComplete.lean:72:chained step attests the FULL `StepInv`: Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance.
metatheory/Dregg2/Exec/StepComplete.lean:75:theorem cexec_attests {s s' : ChainedState} {t : Turn} (h : cexec s t = some s') :
metatheory/Dregg2/Exec/StepComplete.lean:94:  (cexec_attests h).1
metatheory/Dregg2/Exec/StepComplete.lean:177:every step that attests `fullStepInv` holds at every reachable configuration of the whole
metatheory/Dregg2/Exec/StepComplete.lean:186:  exact hpres a t b ha (cexec_attests ht)
metatheory/Dregg2/Exec/EffectTransfer.lean:27:Each catalog effect copies the five-step skeleton. The mechanical steps reuse `recCexec_attests`
metatheory/Dregg2/Exec/EffectTransfer.lean:169:bump. The bridge every downstream theorem reuses to inherit `recCexec_attests`. -/
metatheory/Dregg2/Exec/EffectTransfer.lean:210:  have hcore : recTotal s1.kernel = recTotal s.kernel := (recCexec_attests hc).1
metatheory/Dregg2/Exec/EffectTransfer.lean:232:obligation, reused from `recCexec_attests`'s Authority conjunct. -/
metatheory/Dregg2/Exec/EffectTransfer.lean:237:  exact (recCexec_attests hc).2.1
metatheory/Dregg2/Exec/CrossCellForest.lean:44:  * **`crossForest_attests`** — a committed cross-cell forest attests the four `StepInv` conjuncts
metatheory/Dregg2/Exec/CrossCellForest.lean:302:/-! ## §6 — `crossForest_attests`: the four `StepInv` conjuncts over the whole cross-cell tree.
metatheory/Dregg2/Exec/CrossCellForest.lean:304:A committed cross-cell forest attests, over the WHOLE tree, the four `StepInv` conjuncts — read
metatheory/Dregg2/Exec/CrossCellForest.lean:325:/-- **`crossForest_attests` — THE CROSS-CELL FOREST IS STEP-COMPLETE BY CONSTRUCTION.**
metatheory/Dregg2/Exec/CrossCellForest.lean:327:attests the FULL N-ary cross-cell `StepInv` over the WHOLE tree: Conservation (JOINT total,
metatheory/Dregg2/Exec/CrossCellForest.lean:331:`TurnForest.execForest_attests`, with the cross-cell binding as an explicit HYPOTHESIS. -/
metatheory/Dregg2/Exec/CrossCellForest.lean:332:theorem crossForest_attests (f : CrossCellForest) (cellOf : CellId → KernelState) (sid : SharedId)
metatheory/Dregg2/Exec/CrossCellForest.lean:343:theorem crossForest_attests_conserves (f : CrossCellForest) (cellOf : CellId → KernelState)
metatheory/Dregg2/Exec/CrossCellForest.lean:349:  (crossForest_attests f cellOf sid cells' hbind h).1
metatheory/Dregg2/Exec/CrossCellForest.lean:363:  forestAbsStep_grounded (crossForest_attests f cellOf sid cells' hbind h)
metatheory/Dregg2/Exec/CrossCellForest.lean:429:#assert_axioms crossForest_attests
metatheory/Dregg2/Exec/CrossCellForest.lean:430:#assert_axioms crossForest_attests_conserves
metatheory/Dregg2/Exec/CrossCellForest.lean:557:  * `crossForest_attests` — the four `StepInv` conjuncts over the WHOLE cross-cell tree
metatheory/Dregg2/Exec/CellRuntime.lean:68:A replay is sound because every step is step-complete (`cexec_attests` ⇒ `conservation_step_realized`). -/
metatheory/Dregg2/Exec/CellRuntime.lean:97:continuations are valid (step-complete by `cexec_attests`), both conserve the snapshot's badge, and
metatheory/Dregg2/Exec/AuthTurn.lean:48:so a guarantee leg that reads `execGraph caps h c` as a CONNECTIVITY claim attests it tautologically.
metatheory/Dregg2/Exec/RecordKernel.lean:814:/-- **`recCexec_attests` — the record kernel is STEP-COMPLETE.** Every committed chained
metatheory/Dregg2/Exec/RecordKernel.lean:815:record-cell step attests the FULL `StepInv` over the content-addressed cell: Conservation (of the
metatheory/Dregg2/Exec/RecordKernel.lean:816:`balance` field) ∧ Authority ∧ ChainLink ∧ ObsAdvance. This is `StepComplete.cexec_attests` lifted
metatheory/Dregg2/Exec/RecordKernel.lean:819:theorem recCexec_attests {s s' : RecChainedState} {t : Turn} (h : recCexec s t = some s') :
metatheory/Dregg2/Exec/RecordKernel.lean:837:every step that attests `recFullStepInv` holds at every reachable configuration of the whole chained
metatheory/Dregg2/Exec/RecordKernel.lean:845:  exact hpres a t b ha (recCexec_attests ht)
metatheory/Dregg2/Exec/RecordKernel.lean:1051:#assert_axioms recCexec_attests
metatheory/Dregg2/Apps/SealedBidAuction.lean:126:accepts (`rfl`), the escrow is locked (`rfl`). The receipt attests "3 art" allocated to the winner. -/
metatheory/Dregg2/Proof/WP.lean:17:- **`wp_sound`** — per-step soundness; it factors through `recCexec_attests` (definitional).
metatheory/Dregg2/Proof/WP.lean:78:`recCexec_attests`. The WP only ever asserts properties of the gated post-state. -/
metatheory/Dregg2/Proof/WP.lean:89:`recCexec_attests` (the committed value is exactly `applyOp`, admitted). -/
metatheory/Dregg2/Proof/WP.lean:95:/-- **`wp_attests`** — the bridge to step-completeness: a committed `recCexec` step
metatheory/Dregg2/Proof/WP.lean:96:attests its candidate was admitted (`recCexec_attests`), so any `wp` asserting an admitted-state
metatheory/Dregg2/Proof/WP.lean:97:property is discharged by the gate. This is `recCexec_attests` re-packaged as the WP-soundness
metatheory/Dregg2/Proof/WP.lean:99:theorem wp_attests {s s' : RecChained} {op : RecOp} (h : recCexec s op = some s') :
metatheory/Dregg2/Proof/WP.lean:101:  ⟨(recCexec_attests h).1, (recCexec_attests h).2.1⟩
metatheory/Dregg2/Proof/WP.lean:105:#assert_axioms wp_attests
metatheory/Dregg2/Proof/WP.lean:125:unfolded through `recCexec_attests`: a commit's post-value is exactly `applyOp s.value op` and
metatheory/Dregg2/Proof/WP.lean:173:`recCexec_attests`); on a stay-put the value is unchanged (VC 2, trivially). This is the `hpres`
metatheory/Dregg2/Proof/WP.lean:188:      have a := recCexec_attests hc
metatheory/Dregg2/Exec/Consensus.lean:188:downgrades along its finalization-event run. We model the cell's commit history as an
metatheory/Dregg2/Apps/NameService.lean:232:bindings remain registered at EVERY index of EVERY trajectory: the ownership history is append-only and
metatheory/Dregg2/Lightclient/AttestedQuery.lean:29:    composes it with `RecursiveAggregation.light_client_verifies_whole_history`: a light client
metatheory/Dregg2/Lightclient/AttestedQuery.lean:30:    holding ONLY the aggregation root gets non-omission over the WHOLE history.
metatheory/Dregg2/Lightclient/AttestedQuery.lean:34:the named `Poseidon2SpongeCR` hypothesis + `RecursiveAggregation.EngineSound`'s named fields (both
metatheory/Dregg2/Lightclient/AttestedQuery.lean:342:(`iroot_injective`), so soundness + completeness + exactness all pin to the genuine history. -/
metatheory/Dregg2/Lightclient/AttestedQuery.lean:370:/-! ## §5 — the CHAIN face: non-omission over the WHOLE history.
metatheory/Dregg2/Lightclient/AttestedQuery.lean:378:`RecursiveAggregation.light_client_verifies_whole_history`: ONE `verify agg.root` check pins every
metatheory/Dregg2/Lightclient/AttestedQuery.lean:380:non-omission over the whole history from a single succinct verification. -/
metatheory/Dregg2/Lightclient/AttestedQuery.lean:410:/-- **`light_client_query_non_omission` — non-omission over the WHOLE history.** A light client
metatheory/Dregg2/Lightclient/AttestedQuery.lean:413:  * the recursion engine is sound (`EngineSound` — the three named, realizable hypotheses of
metatheory/Dregg2/Lightclient/AttestedQuery.lean:419:then for ANY step of the history, ANY server-supplied opening of that step's attested commitment,
metatheory/Dregg2/Lightclient/AttestedQuery.lean:423:anywhere in history from a client that verified one succinct root. -/
metatheory/Dregg2/Lightclient/AttestedQuery.lean:431:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/Lightclient/AttestedQuery.lean:450:  exact ⟨light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
metatheory/Dregg2/Exec/FFI/Refine.lean:29:(`execFullForestG_conserves_per_asset`/`_no_amplify`/`_each_attests`/`_unauthorized_fails`, the admission
metatheory/Dregg2/Exec/FFI/Refine.lean:160:encoding of the PROVED `runGatedForestTurn` output, whose `_conserves`/`_no_amplify`/`_each_attests`
metatheory/Dregg2/Lightclient/HistoryIndex.lean:183:block commitment must absorb for whole-history non-omission (`AttestedQuery` §chain face). -/
metatheory/Dregg2/Apps/EpistemicSheaf.lean:234:verified history). -/
metatheory/Dregg2/Exec/Cell.lean:6:(`cexec_attests` proves all four `StepInv` conjuncts on the running machine), and
metatheory/Dregg2/Exec/Cell.lean:86:conjunct of `cexec_attests`, as `conservation_step_realized`), and the stay-put self-loop trivially
metatheory/Dregg2/Exec/Cell.lean:99:conjunct of `cexec_attests`, routed through `cell_h_step` — is *exactly* what makes the bisimulation
metatheory/Dregg2/Exec/Cell.lean:153:successor (the unfold is a function), so a cell's history is faithfully re-derivable from the log
metatheory/Dregg2/Apps/PreRotation.lean:34:    public commitment stream + CR pins the ENTIRE key history; no alternative admitted history
metatheory/Dregg2/Apps/PreRotation.lean:55:  commitment (`rotateWrite_exhibits_preimage`) — so the register's receipt-chained history IS the
metatheory/Dregg2/Apps/PreRotation.lean:220:under the named CR the PUBLIC commitment stream pins the ENTIRE key history: two admitted chains
metatheory/Dregg2/Apps/PreRotation.lean:222:link, and land in the SAME final state. No alternative admitted key history exists under the same
metatheory/Dregg2/Apps/PreRotation.lean:357:key set's commitment — the register's receipt-chained history is the key-event log; one register
metatheory/Dregg2/Apps/PreRotation.lean:384:pre-state register — so the register history is the chain of key-set commitments. -/
metatheory/Dregg2/Exec/CellPrivacy.lean:11:attests `Σ committed = const` **without revealing the amounts**. A committed transfer moves a
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:159:/-- **`execFullForestG_each_attests_satisfiable`.** Every node of the committed forest attests its
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:162:theorem execFullForestG_each_attests_satisfiable :
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:167:  exact ⟨s', hs', execFullForestG_each_attests fma0 s' transferForestG hs'⟩
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:169:/-- **`execFullForestG_root_attests_satisfiable`.** The root node's own `(auth, action)` attests its
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:171:theorem execFullForestG_root_attests_satisfiable :
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:176:  exact ⟨s', hs', execFullForestG_root_attests fma0 s' transferForestG hs'⟩
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:198:`conserves` (the ledger total `100` is preserved) and `light_client` (a concrete `EngineSound` over the
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:207:open Dregg2.Circuit.RecursiveAggregation (Aggregate EngineSound AggregateAttests
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:208:  light_client_verifies_whole_history)
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:250:    (es : EngineSound RealProof acceptAll zCH zRH zcmb zcompress zcompressN realAggregate teethGenesis [s, s'])
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:283:/-- The accepting `EngineSound` over the honest Argus strand. Each step's `commits` field IS the
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:287:    EngineSound RealProof acceptAll zCH zRH zcmb zcompress zcompressN
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:361:    satisfiable := Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_each_attests_satisfiable
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:363:def execFullForestG_each_attests_KS :=
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:364:  @Dregg2.Exec.FullForestAuth.execFullForestG_each_attests
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:367:    satisfiable := Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_root_attests_satisfiable
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:369:def execFullForestG_root_attests_KS :=
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:370:  @Dregg2.Exec.FullForestAuth.execFullForestG_root_attests
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:398:#keystone_audit Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_each_attests_KS
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:399:#keystone_audit Dregg2.Verify.KeystoneAuditRunnable.execFullForestG_root_attests_KS
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:416:#assert_axioms execFullForestG_each_attests_satisfiable
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:417:#assert_axioms execFullForestG_root_attests_satisfiable
metatheory/Dregg2/Projection.lean:14:     (`JointTurn.lean`, CG-2 ⊗ CG-5, tier ≥ 3). The classifier is Whittaker's segmented
metatheory/Dregg2/Lightclient/MMR.lean:4:THE EPOCH's per-structure choice for the receipt index (docs/EPOCH-DESIGN.md): history keys are
metatheory/Dregg2/Lightclient/MMR.lean:32:    `RecursiveAggregation.light_client_verifies_whole_history` identically. The obligation list
metatheory/Dregg2/Lightclient/MMR.lean:38:the named `Poseidon2SpongeCR` hypothesis (the one floor) + `EngineSound`'s named fields at the
metatheory/Dregg2/Lightclient/MMR.lean:535:/-- **`light_client_position_non_omission` — non-omission over the WHOLE history, on the MMR
metatheory/Dregg2/Lightclient/MMR.lean:539:  * a sound recursion engine (`EngineSound`) and `verify agg.root = true` (the ONE client check),
metatheory/Dregg2/Lightclient/MMR.lean:548:server cannot skip a position anywhere in history. -/
metatheory/Dregg2/Lightclient/MMR.lean:556:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/Lightclient/MMR.lean:575:  exact ⟨light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
metatheory/Dregg2/Hyperedge.lean:293:family: a tuple-transition attests the joint conjunct iff *every* incidence attests its own. -/
metatheory/Dregg2/JointTurn.lean:152:participants' per-cell predicates. A joint transition `(x₁,x₂) -t→ (x₁',x₂')` attests a
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:8:    history, attested_history_conserves, conserves_from_verification, real_engine_sound,
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:10:  • the HISTORY-AGGREGATION tooth (`Distributed.HistoryAggregation.{wellformed_attests_whole_history,
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:11:    verified_history_conserves, kernelChained_conserves, root_tooth_pins_kernel}`);
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:56:def light_client_verifies_whole_history_KS :=
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:57:  @Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:63:def attested_history_conserves_KS :=
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:64:  @Dregg2.Circuit.RecursiveAggregation.attested_history_conserves
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:73:-- (4) REAL-ENGINE-SOUND (the EngineSound carrier is inhabited).
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:87:/-! ### the history-aggregation tooth. -/
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:93:def wellformed_attests_whole_history_KS :=
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:94:  @Dregg2.Distributed.HistoryAggregation.wellformed_attests_whole_history
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:100:def verified_history_conserves_KS :=
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:101:  @Dregg2.Distributed.HistoryAggregation.verified_history_conserves
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:142:#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.light_client_verifies_whole_history_KS
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:143:#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.attested_history_conserves_KS
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:147:#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.wellformed_attests_whole_history_KS
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:148:#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.verified_history_conserves_KS
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:157:#assert_axioms light_client_verifies_whole_history_KS
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:158:#assert_axioms attested_history_conserves_KS
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:162:#assert_axioms wellformed_attests_whole_history_KS
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:163:#assert_axioms verified_history_conserves_KS
metatheory/CLAIMS.md:71:| 1 | `Dregg2.Exec.cexec_attests` | `Exec.StepComplete` | the executable machine attests all 4 `StepInv` conjuncts — realizes `Core.conservation_step` AS A THEOREM about `cexec` |
metatheory/CLAIMS.md:74:| 1b | `Dregg2.Exec.RecordCell.recCexec_attests`, `…recReplay_preserves_sumEquals`, `…recordCell_stepComplete`, `…recordCell_run_preserves_sumEquals`, `…recordCell_obs_advances` | `Exec.RecordCell` | the name-keyed record cell GROWS νF life: 4-conjunct step-completeness + conservation over records |
metatheory/CLAIMS.md:127:* `Dregg2.Spec.only_connectivity_begets_connectivity` — the Authority **whole-history
metatheory/CLAIMS.md:172:| `Dregg2.Core.conservation_step` (Law 1's balance: turns move/withhold/erase but never create/destroy units) | `Core` | the operational semantics / the circuit; **realized as a theorem** downstream by `Exec.cexec_attests` (which IS pinned) |
metatheory/Dregg2/Verify/LoadBearingLint.lean:8:rfl` shape) attests NOTHING — proving "executor meets spec" against it is `rfl`, a tautology.
metatheory/Dregg2/Verify/LoadBearingLint.lean:167:                 `:= rfl` collapse); proving executor⟺spec against it attests nothing" }
metatheory/CONSTRUCTIVE-KNOWLEDGE.md:146:Step-completeness (each step really attests its full invariant) is what makes the coinduction
metatheory/CONSTRUCTIVE-KNOWLEDGE.md:266:history was a genuine kernel transition.
metatheory/CONSTRUCTIVE-KNOWLEDGE.md:281:light client ran nothing and cannot be shown a forged history.
metatheory/CONSTRUCTIVE-KNOWLEDGE.md:283:Over the *whole* history this is `light_client_verifies_whole_history`
metatheory/CONSTRUCTIVE-KNOWLEDGE.md:286:insert), and the public final root is the genuine fold of the whole history. Conservation rides the same
metatheory/CONSTRUCTIVE-KNOWLEDGE.md:290:reordered chain — *the pale ghost (a forged history that type-checks) cannot be produced*, because the
metatheory/CONSTRUCTIVE-KNOWLEDGE.md:292:*is* the trust in the whole history; this is the unfoolability of the assurance case's guarantee E
metatheory/CONSTRUCTIVE-KNOWLEDGE.md:437:patch (a turn), the content is the fold of the patch-history. Patches are additive (add/delete-as-
metatheory/Dregg2/Authority/RelationalClosure.lean:42:    a CAUSAL/history-dependent guard reading the trace (§8 Axis 2) — is NOT a `RelPred`; it routes
metatheory/Dregg2/Authority/RelationalClosure.lean:327:  3. **Causal / history-dependent guards (§8 Axis 2)** — a guard reading the lace/trace, not just the
metatheory/Dregg2/Authority/RelationalClosure.lean:333:no trace, no history, no other cell. That is the closure's boundary, stated as a theorem. -/
metatheory/Dregg2/Privacy/Metadata.lean:201:An observer holds a `corpus : Finset Transcript` (the published DAG history). The **payload
metatheory/Dregg2/AssuranceCase.lean:38:  7. **FRI / the STARK soundness chain** — a verifying proof attests its statement; the one
metatheory/Dregg2/AssuranceCase.lean:39:     recursion obligation `RecursiveAggregation.EngineSound.recursive_sound`.
metatheory/Dregg2/AssuranceCase.lean:61:     history while re-witnessing nothing; a tampered aggregate cannot bind.
metatheory/Dregg2/AssuranceCase.lean:70:TURN), and `unfoolability_guarantee` states the whole-history attestation conjoined with conservation
metatheory/Dregg2/AssuranceCase.lean:79:import Dregg2.Circuit.RecursiveAggregation   -- unfoolability: light_client_verifies_whole_history
metatheory/Dregg2/AssuranceCase.lean:81:import Dregg2.Distributed.HistoryAggregation -- unfoolability: the strand/history aggregation surface
metatheory/Dregg2/AssuranceCase.lean:333:    index the epoch publishes is an MMR (`Lightclient/MMR.lean`), history keys are dense positions,
metatheory/Dregg2/AssuranceCase.lean:609:*A light client verifying a Q-chain learns A–D for the WHOLE history; re-witnessing nothing.*
metatheory/Dregg2/AssuranceCase.lean:611:This is the apex that COMPOSES A–D over an entire history and hands them to a verifier who
metatheory/Dregg2/AssuranceCase.lean:615:  • `Circuit.RecursiveAggregation.light_client_verifies_whole_history` — THE headline:
metatheory/Dregg2/AssuranceCase.lean:618:  • `Circuit.RecursiveAggregation.attested_history_conserves` — the whole attested history
metatheory/Dregg2/AssuranceCase.lean:625:    the seam tooth `new_root[i] = old_root[i+1]` pins the whole history.
metatheory/Dregg2/AssuranceCase.lean:632:    conservation across the whole history follows from `verify agg.root` ALONE (the verified `ChainBound`
metatheory/Dregg2/AssuranceCase.lean:635:    `Run` (which `attested_history_is_run` still takes `StateChained` for), never conservation — the
metatheory/Dregg2/AssuranceCase.lean:640:Floor: FRI / STARK soundness (`EngineSound.recursive_sound`, the ONE recursion obligation),
metatheory/Dregg2/AssuranceCase.lean:655:/-- **`unfoolability_guarantee` (NOW A REAL STATEMENT — the whole-history headline, conjoined).**
metatheory/Dregg2/AssuranceCase.lean:659:public final root is the genuine fold of the whole history — AND (2) the WHOLE history conserves value
metatheory/Dregg2/AssuranceCase.lean:662:(the CRITICAL-3 closure). So E genuinely COMPOSES A–D over the whole history handed to a
metatheory/Dregg2/AssuranceCase.lean:663:`verify agg.root`-only client. This conjoins `light_client_verifies_whole_history` with
metatheory/Dregg2/AssuranceCase.lean:668:    (es : EngineSound AProof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/AssuranceCase.lean:676:  ⟨light_client_verifies_whole_history AProof verify CH RH cmb compress compressN agg g steps es hroot,
metatheory/Dregg2/AssuranceCase.lean:684:#assert_axioms Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history
metatheory/Dregg2/AssuranceCase.lean:685:#assert_axioms Dregg2.Circuit.RecursiveAggregation.attested_history_conserves
metatheory/Dregg2/AssuranceCase.lean:689:#assert_axioms Dregg2.Distributed.HistoryAggregation.wellformed_attests_whole_history
metatheory/Dregg2/AssuranceCase.lean:692:-- the CRITICAL-3 closure (conservation-over-history DERIVED from verification, no StateChained):
metatheory/Dregg2/AssuranceCase.lean:695:#assert_axioms Dregg2.Distributed.HistoryAggregation.verified_history_conserves
metatheory/Dregg2/AssuranceCase.lean:755:  * **C (per-node attestation):** every node, at every nesting depth, attests
metatheory/Dregg2/AssuranceCase.lean:783:   execFullForestG_each_attests s s' f h⟩
metatheory/Dregg2/AssuranceCase.lean:791:#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_each_attests
metatheory/Dregg2/AssuranceCase.lean:792:#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_root_attests
metatheory/Dregg2/AssuranceCase.lean:817:  * unfoolability (E) is `light_client_verifies_whole_history` + `conserves_from_verification` over a
metatheory/Dregg2/AssuranceCase.lean:819:    published history — architecturally a distinct object from one node's local forest run).
metatheory/Dregg2/AssuranceCase.lean:824:verified history is fresh and unfoolable.
metatheory/Dregg2/AssuranceCase.lean:861:  * **C — INTEGRITY:** (c1) every node of the forest attests `gatedActionInvG` — credential checked,
metatheory/Dregg2/AssuranceCase.lean:862:    caveats discharged, cap-authority, the per-asset obligation (`execFullForestG_each_attests`); AND
metatheory/Dregg2/AssuranceCase.lean:875:  * **E — UNFOOLABILITY:** a light client checking ONLY `verify agg.root` learns the WHOLE history
metatheory/Dregg2/AssuranceCase.lean:877:    conserves value over the whole history — DERIVED FROM VERIFICATION, with no `StateChained`
metatheory/Dregg2/AssuranceCase.lean:903:    (es : EngineSound AProof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/AssuranceCase.lean:920:    -- E: unfoolability — whole-history attestation + conservation FROM VERIFICATION
metatheory/Dregg2/AssuranceCase.lean:929:    exact execFullForestG_each_attests s s' f hrun
metatheory/Dregg2/AssuranceCase.lean:935:  · -- E1: the light-client whole-history attestation.
metatheory/Dregg2/AssuranceCase.lean:936:    exact light_client_verifies_whole_history AProof verify CH RH cmb compress compressN
metatheory/Dregg2/AssuranceCase.lean:938:  · -- E2: conservation-over-history DERIVED from `verify agg.root` (no StateChained).
metatheory/Dregg2/AssuranceCase.lean:955:  1. **The prover partition (which circuit attests which turn).** The descriptor prover —
metatheory/Dregg2/Apps/GovernedParameters.lean:341:about what the constitution said cannot even be CITED. We exhibit a concrete constitution history where
metatheory/Dregg2/Apps/GovernedParameters.lean:363:on the constitution history; the lying import (claims 99) is NOT — its cited value does not match what
metatheory/site/index.html:13:    --sans:-apple-system,BlinkMacSystemFont,"Segoe UI",Inter,system-ui,sans-serif;
metatheory/site/index.html:195:    <span class="d">└─ certified by</span> <span class="b">orchestration_conserves ∧ _no_amplify ∧ _each_attests</span>
metatheory/Dregg2/Coord/CausalOrder.lean:49:     across the whole insertion history, not just asserted on a fixed snapshot. This is the property
metatheory/Dregg2/Coord/CausalOrder.lean:90:and appends it afterward, the natural-history order of insertion is a faithful witness of "deps
metatheory/Dregg2/Coord/CausalOrder.lean:169:appends it last — so it cannot break `wf`. Inducting over the insertion history, the partial-order
metatheory/Dregg2/Coord/CausalOrder.lean:180:since the append only extends. So a coordinated op's dependency discipline keeps the WHOLE history
metatheory/Dregg2/HandlerTransformer.lean:272:`Hᵢ = Hⱼ`), then the whole forest attests `fullProofForestInv`.
metatheory/Dregg2/Authority/CrossCellImport.lean:47:/-! ## The source cell's committed history. -/
metatheory/Dregg2/Authority/CrossCellImport.lean:49:/-- A SOURCE cell's committed history: its `Exec.Receipt` chain (newest-first) paired with the
metatheory/Dregg2/Authority/CrossCellImport.lean:91:/-- **Anti-lie (uniqueness).** For a fixed source history, cited receipt, and source field, AT MOST
metatheory/Dregg2/Authority/CrossCellImport.lean:163:/-- **`liveRead_changes_under_source_advance`.** There is a source history, a fresh head, and a
metatheory/Dregg2/Authority/CrossCellImport.lean:166:coordination-freeness is not vacuous. (Witness: an empty-history source, advanced with a head whose
metatheory/Dregg2/Authority/CrossCellImport.lean:178:fresh sentinel), a valid import's cited receipt cannot be denied by any well-linked history that
metatheory/Dregg2/Authority/CrossCellImport.lean:179:presents the same head: same head ⇒ same history (`chain_tamper_evident`), so `provenance` is in it.
metatheory/Dregg2/Authority/CrossCellImport.lean:194:no history. -/
metatheory/Dregg2/Authority/CrossCellImport.lean:214:/-- The two-receipt source history (newest-first) for the staleness witness. -/
metatheory/Dregg2/Authority/SelectiveDisclosure.lean:43:predicate proof attests — the genuine arithmetic content the circuit binds. -/
metatheory/Dregg2/Authority/SelectiveDisclosure.lean:63:predicate proof attests of the (hidden) attribute value. This is the genuine
metatheory/Dregg2/Authority/ImportBinding.lean:51:  * **§NON-VACUITY** — a concrete source history + binding: the truthful binding ADMITS and its keystone
metatheory/Dregg2/Authority/ImportBinding.lean:74:(checked against the source's history); the enforcement obligation is the projected cell-program
metatheory/Dregg2/Authority/ImportBinding.lean:146:binding's import is VALID against the source history (`importValid H source b.imp`: the cited receipt is
metatheory/Dregg2/Authority/TemporalAlgebra.lean:42:    history (where every admission is serialized through the cell) the register read is exact.
metatheory/Dregg2/Authority/TemporalAlgebra.lean:135:  tau-serialized history. -/
metatheory/Dregg2/Authority/ArithmeticClosure.lean:351:  3. **CAUSAL / history-dependent guards (§8 Axis 2)** — a guard reading the lace/trace, not just the

exec
/bin/zsh -lc "ls -la ~/.claude/projects/-Users-ember-dev-breadstuffs/memory && sed -n '1,220p' ~/.claude/projects/-Users-ember-dev-breadstuffs/memory/MEMORY.md" in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
total 1968
drwxr-xr-x@ 116 ember  staff    3712 Jun 25 15:39 .
drwxr-xr-x@ 132 ember  staff    4224 Jun 25 14:45 ..
-rw-r--r--    1 ember  staff   31688 Jun 25 09:41 MEMORY.md
-rw-r--r--    1 ember  staff    5295 Jun 13 02:44 feedback-argus-orchestration-method.md
-rw-r--r--@   1 ember  staff    1812 May 23 14:14 feedback-avoid-npm-direct.md
-rw-r--r--    1 ember  staff    2304 Jun 25 09:40 feedback-be-thoughtful-not-trigger-happy.md
-rw-r--r--    1 ember  staff    2485 Jun 13 19:21 feedback-braids-not-waves.md
-rw-r--r--    1 ember  staff    4397 Jun 24 17:20 feedback-byte-identity-differential-is-not-faithfulness.md
-rw-r--r--    1 ember  staff    2639 Jun 21 19:35 feedback-capture-intrinsic-not-a-feature.md
-rw-r--r--    1 ember  staff    3411 Jun 23 21:13 feedback-cockpit-edits-need-the-gpui-build-check.md
-rw-r--r--@   1 ember  staff   17529 Jun  6 04:21 feedback-conservation-is-not-correctness.md
-rw-r--r--@   1 ember  staff    1435 Jun 11 14:04 feedback-differential-pins-are-my-crutch.md
-rw-r--r--@   1 ember  staff    1798 Jun 10 11:56 feedback-docs-teach-what-is.md
-rw-r--r--@   1 ember  staff    1574 Jun  2 01:38 feedback-dont-cheap-out-on-hard-proofs.md
-rw-r--r--    1 ember  staff    3728 Jun 19 00:16 feedback-dont-launder-a-load-bearing-insecurity.md
-rw-r--r--@   1 ember  staff    3084 Jun  6 19:23 feedback-dont-launder-vacuity-as-honest.md
-rw-r--r--    1 ember  staff    3026 Jun 22 22:22 feedback-dont-over-ember-gate.md
-rw-r--r--@   1 ember  staff    7000 Jun  4 21:11 feedback-ember-code-review-executor-holes.md
-rw-r--r--    1 ember  staff    2657 Jun 15 01:28 feedback-empirical-validation-n3.md
-rw-r--r--@   1 ember  staff    1639 Jun 10 21:23 feedback-green-or-bust-no-artifact-fallbacks.md
-rw-r--r--    1 ember  staff    1332 Jun 12 09:31 feedback-horizonlog-standing-practice.md
-rw-r--r--@   1 ember  staff    2889 May 24 16:01 feedback-improve-dont-degrade.md
-rw-r--r--@   1 ember  staff    2055 May 22 10:19 feedback-kimchi-circuit-agents.md
-rw-r--r--    1 ember  staff    2892 Jun 12 17:51 feedback-memory-grammar-reform.md
-rw-r--r--    1 ember  staff    5454 Jun 24 14:06 feedback-named-seam-is-not-a-hole.md
-rw-r--r--@   1 ember  staff    2471 Jun  2 04:12 feedback-never-git-checkout-never-dismiss-stuck-proof.md
-rw-r--r--@   1 ember  staff    3479 Jun  4 18:11 feedback-no-phantom-commits-metatheory-is-the-jam.md
-rw-r--r--@   1 ember  staff     577 May 22 09:05 feedback-no-tracker-table.md
-rw-r--r--@   1 ember  staff    1845 May 23 14:00 feedback-no-worktree-isolation.md
-rw-r--r--@   1 ember  staff    4464 Jun  5 10:00 feedback-one-executor-entry-real-tests-rust-is-buggy.md
-rw-r--r--    1 ember  staff    6027 Jun 18 13:57 feedback-orient-from-the-record.md
-rw-r--r--@   1 ember  staff    1455 Jun 10 12:51 feedback-rise-to-meet-the-claim.md
-rw-r--r--@   1 ember  staff    3016 Jun  8 20:47 feedback-seams-are-work-not-walls.md
-rw-r--r--    1 ember  staff    1862 Jun 15 20:36 feedback-sober-demonstrative-register.md
-rw-r--r--@   1 ember  staff    5000 Jun  7 12:33 feedback-stop-auditing-internalize-guarantees.md
-rw-r--r--    1 ember  staff    1969 Jun 19 22:25 feedback-swarm-self-heals-progress-the-workstream.md
-rw-r--r--    1 ember  staff    3653 Jun 24 10:09 feedback-swarm-shared-tree-clobber-hazard.md
-rw-r--r--@   1 ember  staff    1212 May 28 23:28 feedback-switch-to-better-approach.md
-rw-r--r--    1 ember  staff    1235 Jun 12 17:45 feedback-verification-economy.md
-rw-r--r--@   1 ember  staff    1181 May 22 09:10 feedback-verify-agent-claims.md
-rw-r--r--@   1 ember  staff    1597 Jun 11 01:18 feedback-we-do-not-name-we-ship.md
-rw-r--r--@   1 ember  staff    1756 Jun  4 00:55 feedback-workflows-resume-on-interrupt.md
-rw-r--r--    1 ember  staff    2711 Jun 23 17:56 minted-handler-floors-retire-gate-hole-class.md
-rw-r--r--    1 ember  staff    2887 Jun 24 14:04 minted-house-via-factory-route.md
-rw-r--r--    1 ember  staff    4603 Jun 24 18:16 minted-perf-sin-sweep.md
-rw-r--r--    1 ember  staff    6639 Jun 24 15:01 minted-proof-integrity-discipline.md
-rw-r--r--@   1 ember  staff   22709 Jun  3 22:03 project-2026-06-02-ambition-program.md
-rw-r--r--@   1 ember  staff    8490 Jun  4 18:54 project-2026-06-04-tracks-and-studies.md
-rw-r--r--@   1 ember  staff    5318 Jun  5 12:51 project-2026-06-05-diamond-wave-day.md
-rw-r--r--@   1 ember  staff    5062 Jun  6 18:43 project-2026-06-06-circuit-audit-synthesis.md
-rw-r--r--@   1 ember  staff    7976 Jun  6 21:58 project-2026-06-06-verifiable-execution-session.md
-rw-r--r--@   1 ember  staff    7494 Jun  7 18:31 project-2026-06-07-coherence-campaign.md
-rw-r--r--@   1 ember  staff    9604 Jun  7 22:00 project-2026-06-07-one-circuit-migration.md
-rw-r--r--@   1 ember  staff   10049 Jun  7 15:25 project-2026-06-07-swap-and-tidy-escalation.md
-rw-r--r--@   1 ember  staff    6782 Jun  8 00:42 project-2026-06-08-distributed-protocols-verified.md
-rw-r--r--@   1 ember  staff   22172 Jun  8 15:09 project-2026-06-08-overnight-campaign.md
-rw-r--r--@   1 ember  staff    4416 Jun  2 00:02 project-adjunction-thesis-verdict.md
-rw-r--r--    1 ember  staff    2291 Jun 15 16:21 project-agpl-relicense.md
-rw-r--r--@   1 ember  staff    2984 May 24 03:28 project-apps-audit-framing.md
-rw-r--r--@   1 ember  staff    6198 May 23 08:04 project-architecture-2025-05-23.md
-rw-r--r--    1 ember  staff   10400 Jun 24 20:40 project-argus-vision.md
-rw-r--r--    1 ember  staff    4692 Jun 24 17:18 project-cap-reshape-plan.md
-rw-r--r--    1 ember  staff    5371 Jun 25 15:39 project-cells-as-service-boolean-matching.md
-rw-r--r--@   1 ember  staff    1227 May 22 08:14 project-circuit-roadmap.md
-rw-r--r--    1 ember  staff   12998 Jun 24 20:39 project-circuit-soundness-apex.md
-rw-r--r--@   1 ember  staff    6920 May 28 23:55 project-circuit-state.md
-rw-r--r--    1 ember  staff    7349 Jun 24 17:20 project-coherence-census.md
-rw-r--r--    1 ember  staff    5549 Jun 23 00:29 project-crate-split-campaign.md
-rw-r--r--@   1 ember  staff    6559 May 24 10:26 project-demo-passes-2026-05-24.md
-rw-r--r--    1 ember  staff    5710 Jun 19 15:39 project-deos-desktop-frontier.md
-rw-r--r--    1 ember  staff    4287 Jun 22 17:45 project-deos-self-hosting-epoch.md
-rw-r--r--    1 ember  staff    4661 Jun 19 21:27 project-deos-ux-vision.md
-rw-r--r--    1 ember  staff    7531 Jun 19 19:51 project-distributed-houyhnhnm-frontier.md
-rw-r--r--    1 ember  staff    1334 Jun 15 16:04 project-domain-fg-goose.md
-rw-r--r--    1 ember  staff    3637 Jun 13 15:39 project-dregg-integrators-one-seam.md
-rw-r--r--@   1 ember  staff    1968 May 29 12:15 project-dregg-rebuild-research.md
-rw-r--r--@   1 ember  staff  103621 May 31 06:12 project-dregg2-architecture.md
-rw-r--r--@   1 ember  staff   26607 Jun  1 02:22 project-dregg2-coverage-map.md
-rw-r--r--    1 ember  staff   22574 Jun 24 20:40 project-dregg3-campaign.md
-rw-r--r--@   1 ember  staff    9215 May 31 11:39 project-dregg4-vision.md
-rw-r--r--    1 ember  staff    7473 Jun 25 15:39 project-firmament-sel4-boots.md
-rw-r--r--    1 ember  staff    3061 Jun 14 23:35 project-flow-algebra-right-skew.md
-rw-r--r--@   1 ember  staff    2834 Jun  1 19:59 project-forest-delegation-decorative.md
-rw-r--r--    1 ember  staff    4596 Jun 25 15:39 project-graphideos-android-epoch.md
-rw-r--r--    1 ember  staff    5881 Jun 21 11:05 project-house-capacities.md
-rw-r--r--    1 ember  staff   14987 Jun 24 16:10 project-hyperdreggmedia-agent-in-deos-epoch.md
-rw-r--r--@   1 ember  staff    8470 Jun  4 20:46 project-linear-doctrine-weld.md
-rw-r--r--@   1 ember  staff    1995 May 23 02:57 project-midnight-strategy.md
-rw-r--r--    1 ember  staff   16722 Jun 20 00:33 project-moldable-inspector-epoch.md
-rw-r--r--    1 ember  staff    3210 Jun 13 17:20 project-notify-primitive.md
-rw-r--r--    1 ember  staff    8383 Jun 18 12:54 project-partial-turn-promises.md
-rw-r--r--    1 ember  staff    8100 Jun 24 20:40 project-perf-kernel-supply-epoch.md
-rw-r--r--@   1 ember  staff    3955 Jun  3 23:32 project-phase2-intent-core-done.md
-rw-r--r--    1 ember  staff   16357 Jun 21 15:19 project-polisware-constitution.md
-rw-r--r--@   1 ember  staff   12989 Jun  2 18:45 project-postcompaction-2026-06-02-design-recovery.md
-rw-r--r--@   1 ember  staff   10945 Jun  5 15:13 project-proof-system-reorientation-2026-06-05.md
-rw-r--r--    1 ember  staff    1458 Jun 12 17:48 project-pug-handoff.md
-rw-r--r--@   1 ember  staff    1206 May 28 16:08 project-pyana-renamed-dregg.md
-rw-r--r--    1 ember  staff   19837 Jun 12 21:16 project-refinement-epoch.md
-rw-r--r--@   1 ember  staff    1036 Jun 10 22:59 project-refinement-era.md
-rw-r--r--    1 ember  staff    5562 Jun 16 05:08 project-rhizomatic-dregg-slotting.md
-rw-r--r--@   1 ember  staff    4340 May 23 12:08 project-session-2025-05-23b.md
-rw-r--r--@   1 ember  staff    9175 Jun 24 15:33 project-silver-and-golden-visions.md
-rw-r--r--@   1 ember  staff    4908 May 28 17:20 project-site-build.md
-rw-r--r--@   1 ember  staff    3271 May 29 00:13 project-soundness-audit-2026-05-29.md
-rw-r--r--@   1 ember  staff    3273 May 24 17:29 project-studio-substrate.md
-rw-r--r--@   1 ember  staff    2457 May 31 03:17 project-swap-framing.md
-rw-r--r--@   1 ember  staff    8318 Jun  2 04:52 project-the-swap-roadmap.md
-rw-r--r--    1 ember  staff    5119 Jun 25 15:39 project-umem-as-primitive-epoch.md
-rw-r--r--@   1 ember  staff    3995 Jun 21 15:43 reference-dregg-atlas.md
-rw-r--r--    1 ember  staff    3052 Jun 23 21:12 reference-dregg-mcp-harness.md
-rw-r--r--@   1 ember  staff    1643 May 29 12:14 reference-kagi-paper-search.md
-rw-r--r--    1 ember  staff    4482 Jun 14 21:39 reference-persvati-remote-build.md
-rw-r--r--@   1 ember  staff    2017 Jun  5 11:35 reference-subagent-529-overload.md
-rw-r--r--    1 ember  staff    2399 Jun 12 21:19 seal-note-fable-5-2026-06-12.md
# dregg memory index — one line per memory; open the topic file for the detail.
# ⚑ ORIENT FROM THIS RECORD, not the compaction summary (see feedback-orient-from-the-record):
#   REORIENT.md → HORIZONLOG.md → this index WHOLE → flagged (⚑) topic files → docs + captured artifacts.
#   Read the record for the SHAPE; verify code vs HEAD for the STATE (memories are dated/point-in-time).
# ⚑ GROUNDED WHAT-IS: `docs/reference/` (committed, grounded to file:line at HEAD) is the source-of-truth
#   for what each subsystem IS + the Lean theorems backing it. When a memory and docs/reference disagree,
#   the doc wins. Start: docs/OVERVIEW.md → docs/reference/README.md (lean-circuit/lean-assurance/lean-authority/turns/...).
# The one-sentence through-line: macaroons/biscuits → biscuit's Datalog became the derivation circuit →
#   "a turn is the exercise of an attenuable proof-carrying token over owned state, leaving a verifiable receipt."

## ⚑ CURRENT — the live state + vision (read these first)
- [⚑⚑⚑ umem-as-a-Primitive Epoch](project-umem-as-primitive-epoch.md) — 2026-06-24/25: universal memory became a sovereign portable WITNESSED primitive (per-cell heaps · working mem · passable intermediate states · composable). The KEYSTONE (boundary→committed-state + the cross-cell-read, `99a8dc94`) + per-cell/whole-image/OFE proofs all `#assert_axioms`-clean (`f0372f22`/`bf200960`/`bee42d4a`); 6 revolutions prototyped (agent-memory, membrane, continuations, checkpointable-runtime, time-travel, proof-shrink); PQ-plausible; Codex cross-reviewed. Open tails named. `docs/deos/UMEM-*.md`.
- [⚑⚑⚑ Cells-as-Service + Boolean-Matching](project-cells-as-service-boolean-matching.md) — 2026-06-25: service-objects belong ABOVE the effectvm (NOT a kernel effect — `Effect::Invoke` killed, S1 v9→v10 commitment BACKED OUT; invoke desugars at the SDK/app layer). Re-ground dregg's 4+ scattered boolean-matching surfaces on a boolean-closed DERIVATIVE algebra à la RE#/ERE≤ (Lean-formalized, free-use) — prove over OUR `Pred` (= the EBA shape), ERE≤ a blueprint. `dregg-dfa` = the verified dispatch primitive. `docs/deos/{DERIVATIVE-MATCHING-DESIGN,BOOLEAN-MATCHING-REGROUND,…}.md`.
- [⚑⚑⚑ graphideOS + Android Epoch](project-graphideos-android-epoch.md) — 2026-06-24/25: deos reaches android BOTH ways — android-cell (foreign app cap-bounded + interactive, live on the emulator via HVF, reuses servo's compositor) + graphideOS (deos AS android = a GrapheneOS-fork ALTERVERSE; the verified core RUNS on android, the gpui PlatformAndroid renderer initializes on-device, painted-frame needs real arm64 hw). One gpui workspace-wide (`0ef7ba84`/`498321a4`).
- [⚑⚑ Be Thoughtful, Not Trigger-Happy](feedback-be-thoughtful-not-trigger-happy.md) — from thin/rolled context do NOT fire kernel/effect/commitment changes (the `Effect::Invoke`/custom-AIR scar); service-matching above the effectvm; "keep developing" = the app layer (gpui-component, not raw gpui) in PARALLEL while circuit/soundness gets THOUGHT.
- [⚑⚑⚑ Hyperdreggmedia + Agent-in-deos Epoch](project-hyperdreggmedia-agent-in-deos-epoch.md) — 2026-06-23: the agent INHABITS the live cockpit (run_js drives the real World; a live Copilot Claude decided JS + drove it, receipted + confined) + HYPERDREGGMEDIA authoring opened (the card-editor KEYSTONE landed — edit a card from within as receipted patches, agent authors a card's UI). dregg-as-host DECIDED (jail hermes, no fork). Frame: Rust cockpit = the dev-VM basement; the world arises fully inside dregg, renderer-independent. Release cut (292M), pop-out crash hardened. **06-24:** authoring epoch FANNED OUT (8 surfaces + `HYPERDREGGMEDIA.md` charter `72cddf9c`); workspace UNIFIED (12 elephants→root, one target, ~271G reclaimed, `4d19f7cb`) + forks GIT-ified (zed/gpui-component/stylo on GitHub → buildable by anyone + CI fixed, `47cff3190`); MUD reframed (GM-as-privileged-server, richness not fog-of-war). ⚑ LIVE FRONTIER = the **FULLY-REFLECTIVE COCKPIT** (convert its surfaces to deos-js cards so the agent reflects-on+rewrites the REAL cockpit — the counter demo `a326b3215` was only the loop-proof).
- [⚑⚑⚑ Perf+Kernel+Supply Epoch](project-perf-kernel-supply-epoch.md) — 2026-06-23: per-turn commitment made cheap — the full-65k-leaf rebuild-every-recompute was the bomb; no-copy `lean_object*` FFI + sparse Merkle + field-`%` + cap-root cache + incremental commitment, all byte-identical (the "~370ms→~2.85µs / ~130,000×" headline is a DATED profiler-comment note, not a committed benchmark — `turn/.../turn_profile.rs:5`; treat the exact µs/× as approximate-unverified); the Rust↔Lean kernel equivalence AUDITED (state-agreement ≠ rejection-parity → built `rejection_parity.rs`) + 6 Rust under-enforcements aligned to the verified spec (self-transfer, 9 lifecycle-liveness arms, archive, …); and a coherent per-asset-well SUPPLY MODEL (`docs/SUPPLY-MODEL.md`: cap-gated Mint/Burn) — Stages 1+2 SHIPPED (first-class provable `Effect::Mint` w/ dedicated `sel::MINT` circuit selector). Also: the "~17 fixes" circuit memory was STALE (now a proven-class taxonomy).
- [⚑⚑⚑ deos Self-Hosting Epoch SHIPPED](project-deos-self-hosting-epoch.md) — 2026-06-22: the desktop epoch is BUILT + GREEN. Editor+terminal as cockpit DOCK PANES (⌘K → real PTY/editor split), document language (dregg-doc patch core + editor-as-document + conflict-viewer), dregg-pilled Matrix chat (the MEMBRANE star: a message = a cap-bounded world-fork you drive+stitch), confined Hermes (ACP↔ToolGateway), gpui-component cockpit overhaul, atlas refreshed (31 surfaces incl. offscreen app bakes). All tested. METHODS minted: file-partitioned swarm + main-loop seam-resolution; offscreen-capture-for-atlas; gpui-component Theme-init-on-every-App.
- [⚑⚑ Refinement Epoch](project-refinement-epoch.md) — THE MODE: the dregg3 substrate epoch CLOSED; now REFINE — usability/teaching/the "lamesauce" predicate-caveat LANGUAGE uplift/not-a-toy apps/green-down-the-board. Wide seat of wonder; don't scope down.
- [⚑⚑ dregg3 Campaign](project-dregg3-campaign.md) — the kernel REDESIGN: 6 nouns, **8 verbs** (a DESIGN ABSTRACTION + its `minimality` theorem over `Substrate/VerbRegistry.lean`, NOT the deployed count — `turn/src/action.rs::Effect` is 32 variants / ~36-way tag at HEAD), 6 unifications (one Pred algebra · sorted-Poseidon2 everywhere · AssetId:=issuer-cell Σδ=0 · one executor · one circuit · one codec). The constructive-knowledge correction (authority = PRODUCTION under non-forgeability, NOT affine descent — the §3 error I must never repeat). The Metatheory/* trunk. Product ladder (dregg-auth = the gateway; adoption IS attenuation).
- [⚑⚑ deos UX Vision](project-deos-ux-vision.md) — THE desktop north star: 1999-AOL-4-year-old WONDER (click around, absorb, no comprehension needed) FUSED with Pharo/Smalltalk LIVENESS (the image IS its own IDE/inspector/debugger, malleable from within). starbridge-v2 = the desktop; needs a big overhaul to reach it. site/studio was v1. Test: would a 5-year-old click it with delight AND can an adept inspect/modify it live?
- [⚑⚑ deos Desktop Frontier](project-deos-desktop-frontier.md) — the live desktop NOW: the LIVE IMAGE VIEWER boots on seL4 (`make run-image` — a Pharo-style browser of REAL sovereign cells, four substances, BALANCE_SUM=0; commit `bbccc03ca`). **✅ THE #1 PRECIOUS IS CLOSED** (`d92d0526c`): the gpui-offscreen render reaches the seL4 framebuffer. NEW frontier = make that hosted image INTERACTIVE (input already boots; live-repaint-on-turn = copy net.system) — `docs/desktop-os-research/SEL4-INTERACTIVE-COCKPIT.md`. The desktop UX build now lives in [[moldable-inspector-epoch]].
- [⚑⚑ Moldable Inspector Epoch](project-moldable-inspector-epoch.md) — THE LIVE STARBRIDGE BUILD (2026-06-19): Pharo-moldable multiplicity of inspectors+gadgets over the COMPLETE protocol (151 types censused; `Presentable`/`Gadget`/`Spotter`/`Halo`; `docs/deos/INSPECTOR-FRAMEWORK.md`). Liveness wave shipped (inspect→act · workspace · wonder); L1 spine building; L2-L10 to fan out. Also: `docs/ARCHEOLOGY-LEDGER.md` corpus dig + `docs/desktop-os-research/SEL4-INTERACTIVE-COCKPIT.md` (input is NOT greenfield).
- [⚑⚑ Circuit-Soundness Apex](project-circuit-soundness-apex.md) — light-client unfoolability (`verifyBatch accept ⟹ ∃ genuine kernel transition`). The apex `theorem lightclient_unfoolable` (`CircuitSoundness.lean:453`) + the FIVE guarantee apexes (`unfoolability/authority/conservation/integrity/freshness_guarantee`, `AssuranceCase.lean`) + the cap-reshape crown #103 + whole-history aggregation (`light_client_verifies_whole_history`) + `only_connectivity_begets_connectivity` + `settlement_soundness` + the macaroon↔cap arrow `chainGateG_implies_capAuthorityG` (`CaveatCapBridge.lean:168`) are ALL `#assert_axioms`-clean; corpus sorry-free; the 3 epoch-stamp residuals CLOSED/SUPERSEDED. Per-effect rungs PROVEN individually (dominant label CLASS A, `ClosureAll.lean`; the VALUE_FORCED/… labels are header-only, not a clean partition). GENUINE open = a short named tail: un-assembled `∀ e, descriptorRefines` · intra-turn receipt-LOG seam (kernel half forced) · faithful-encoding crypto carriers · attenuate v3-registry cutover. ⚑ `docs/reference/` is the grounded what-is. Verify CODE vs HEAD.
- [⚑ ARGUS Vision](project-argus-vision.md) — the circuit must witness the protocol's CORRECT EVOLUTION so a light client CAN'T BE FOOLED; foil = the pale ghost. Bar = no-malleability + no-forgotten-precondition + refines. The LINCHPIN LANDED (authority/non-amp/production in-circuit via the cap-reshape crown); the apex + five guarantees are `#assert_axioms`-clean. The fidelity column (kernel-state→circuit→interpreter→turn→aggregate→light-client) is climbed: the denotational interpreter-edge differential is BUILT, the recursive whole-chain fold is LIVE, only a small named tail (receipt-LOG seam · node leg-iterate wiring · recursion-fork follow-ups) remains. The whole stack = ONE transformer algebra, ONE Lean-derived circuit/VK.
- [⚑ Firmament/seL4 BOOTS](project-firmament-sel4-boots.md) — dregg-on-seL4 (Robigalia v0) BOOTS (M0/M1/M2/M-STARK/M5, native-macOS Microkit). Firmament = ONE cap across DISTANCE (local seL4-cap ↔ distributed dregg-cap ↔ surface=window; n=1 collapse). The executor-PD Lean-runtime blocker is **REFUTED + BOOTS** (embeddable runtime measured; pg full-D = days). NEVER re-haze from a `which`/`ls` probe.
- [⚠ House Capacities — UNPROVEN/UNWIRED SKETCHES](project-house-capacities.md) — CORRECTED 2026-06-22: 8 Track-2 "capacities" are Rust `cell/src/*.rs` DESIGN SKETCHES with SMOKE TESTS (forge-detectors ≠ Lean proofs), NOT wired into the living protocol (no live Effect/circuit; only reactive is wired). To be real = the formal route in ./metatheory (Lean effect + descriptor + apex rung). The drift lesson: build capacities IN the formal setup, not the Rust periphery.
- [⚑ Coherence Census](project-coherence-census.md) — the whole-tree harsh look + docs/DREGG3.md; circuit ~11.5K live of 112K (~33K deletable); strata = a good tower ×8 not ×52.
- [⚑ Cap-Reshape Crown — LANDED](project-cap-reshape-plan.md) — the openable capability_root (depth-16 sorted-Poseidon2 Merkle) welded to the `is_attenuation` lattice → in-circuit non-amp + production-authority, the ARGUS linchpin #103, `#assert_axioms`-clean (`capReshapeVmDescriptor` + teeth). The SDK Phase-D payoff is wired (`verify_full_turn_bound` binds the cap-membership leg to the canonical root, anti-forgery teeth bite). One deployed-route residual: route `attenuate` through the recompute descriptor as its v3-registry LEAD. CLOSED, not a plan.
- [⚑ Pug Handoff Target](project-pug-handoff.md) — the stranger-usable bar: works without ember in the loop.
- [dregg Integrators + One-Seam](project-dregg-integrators-one-seam.md) — agents are intricate LOOPS; dregg closes the enforcement gap at ONE seam (the tool-call/verdict record); ADOS = substrate not a new loop.
- [⚠ dregg2 Architecture](project-dregg2-architecture.md) — DATED: `./metatheory` IS dregg2 (Lean4, l4v-shaped); but its "seed / not-yet-an-OS / rbg-not-ours-to-boot" framing is SUPERSEDED (it boots — see firmament-sel4-boots + refinement-epoch).

## ⚑ FORWARD vision
- [⚑⚑ Polisware Constitution](project-polisware-constitution.md) — the "fair playground for superintelligences" is a BUILDING kernel-clean Lean artifact: `metatheory/Metatheory/{Polis,DreggPolis,PolisNonConfusion}.lean` welds the dregg⋈svenvs⋈Lacan synthesis to the real tree (polis_safety ∀-opaque · legitimacy=non-regression · disclosure=EpistemicDial · authority=l4v Auth+camera Fpu · non-confusion+unfoolability from deployed proofs · first concrete politician bar). `~/dev/svenvs` grounds it: inhabitant is the ∀-term the proof never reasons about (shadow inert), govern trace-shape not motive, polis edge = empty meet of EXPORTED floors.
- [⚑⚑ Distributed-Houyhnhnm Frontier](project-distributed-houyhnhnm-frontier.md) — THE 2026-06-19 SYNTHESIS: dregg IS the cap-secure witnessed realization of fare's Houyhnhnm Computing (read whole; resolves the Urbit critique). Distributed time-travel = event-structure config lattice + RCCS reversibility + revocation-non-monotone-at-settlement; the **Settlement Soundness theorem** (authority-live-at-settlement) extends light-client unfoolability → lands in circuit-soundness. Branch-and-stitch protocol (consensual virtualized pasts · nesting=firmament-confinement-safety · lossy stitch w/ linear-drop, pushout-correct). PATCH THEORY = the same event-structure object in VC clothes (turn-layer already IS it); new value at the DOCUMENT LANGUAGE (Pijul-shaped, conflicts-as-objects) + the stitch. Docs: `docs/deos/{DISTRIBUTED-TIMETRAVEL-SEMANTICS,BRANCH-AND-STITCH-PROTOCOL,DOCUMENT-LANGUAGE,IMPLEMENTATION-ROADMAP}.md`.
- [⚑ Partial-Turn / Promises](project-partial-turn-promises.md) — ember's idea: an effect that WITNESSES/EMITS a partial turn with holes/promises, braiding CapTP promise pipelining DOWN into the circuit/effect layer. THE INSIGHT: a promise-hole IS a nullifier; resolution = a spend; one-shot linearity = the double-spend non-membership the circuit ALREADY enforces (noteSpend grow-gate). ⚑ CENSUS 2026-06-19 (a504ad88): NOT just pieces — LARGELY BUILT + PROVEN. ConditionalBatch+EventualRef+Slots (Kahn topo, atomic: `condTurn_atomic/conserves/dependency_sound`), the Await algebra (one-shot continuations: `commit_resumes_once`, `four_faces_unify`), GUARDED HOLES (`holeFill_binds_in_circuit` — a fill binds δ AND guard, lazy-witness/eager-shape, fail-closed — the genuinely-new keystone), CapTP pipelining (`drainAll_preserves_caps/_head_authorized`, `overAuthorized_send_rejected`). Rust: turn/src/{eventual,conditional,pending}.rs + captp/src/pipeline.rs. THE GAP IS ARCHITECTURAL not foundational: lift ConditionalBatch into the first-class EFFECT vocabulary + the circuit/light-client semantics of a batch-bearing effect (read execConditionalTurn + FullForest + apex fold). Move = WIRE, not build. STRONG guarded hole (undetermined-δ) is INEXPRESSIBLE = safe-by-inexpressibility (dregg's load-bearing line). Payoff: promise pipelining gets light-client-unfoolability.
- [dregg4 Vision](project-dregg4-vision.md) — turn = guarded comodel/lens; attestation dial-cube; the SINGLE-MACHINE PRINCIPLE (n=1 collapses distributed bounds to strong-local — consistent checkpoint/sync commit/immediate revocation); hypersystem/simplicial joint turns (tensor non-finality = the price).
- [Adjunction Thesis Verdict](project-adjunction-thesis-verdict.md) — Lawvere hyperdoctrine (Predicate⊣Witness base + graded ∃⊣q*⊣∀; agreement=limit; adjudication=a separate graded reflector); the REFUTED adjoint thesis; novel theorem (reflector-failure ≅ dual-H¹ Byzantine non-gluing).
- [Flow-Algebra Right-Skew](project-flow-algebra-right-skew.md) — dregg's workflow/flow composition is PROVEN right-skewed (RSKA_d⊓, Pradic 2408.14999): choice ⊔ does NOT left-distribute over compose ⋆ — the algebraic shadow of the reactive rung (online sim, not trace language); payoff = DECIDABLE flow/policy refinement via the Büchi game (the ARGUS "refines" bar).
- [Silver/Golden Visions](project-silver-and-golden-visions.md) — Silver (integration-complete) precedes Golden (full algebraic / folded-DAG). · [Midnight Strategy](project-midnight-strategy.md) — Midnight/Cardano interop; ZKIR v3 backend; observation-bridge.
- [Rhizomatic↔dregg Slotting](project-rhizomatic-dregg-slotting.md) — `~/dev/rhizomatic` (separate repo: Merkle-CRDT/G-Set portable data format) IS dregg's I-confluent fragment taken globally; they diverge on exactly ONE axis = conservation; slots in as dregg's read/query face (L2–L5) for the monotone substrate + the unbuilt `merge` interpretation (DREGG3 §2.4).

## ⚑ METHOD — how to work here (feedback)
- [⚑⚑ A Named Seam Is NOT A Hole](feedback-named-seam-is-not-a-hole.md) — 2026-06-24: what misled us into recurring OVER-pessimism — reading dregg's honest seam/residual/carrier NAMING as uniform debt. CLASSIFY each (TERMINAL-CRYPTO-FLOOR by design / REDUCIBLE-OPEN / CLOSED / CALIBRATION); measure TRACTABILITY not coverage; VERIFY-BEFORE-PESSIMISM (the dual of measure-before-claiming). Instances: "~17 fixes" stale, "∀-comp 44 tough proofs" was assembled-mod-floor, "supply decorative" load-bearing, execGraph "debt" was calibration. Corollary (43→110): don't be fooled optimistic either — genuine witnesses, no overlooking.
- [⚑⚑ Orient From The Record](feedback-orient-from-the-record.md) — orient from the durable record, NEVER the compaction summary + a shallow probe (probes LIE — the seL4-haze scar); read for SHAPE, verify code vs HEAD for STATE.
- [⚑⚑ We Do Not Name — We Ship](feedback-we-do-not-name-we-ship.md) — every caveat arrives WITH its closure lane running; "named" = a burn-down, never a parking lot.
- [⚑ Seams Are Work, Not Walls](feedback-seams-are-work-not-walls.md) — a labeled seam / out-of-band gate is a SEVERE PROBLEM not a wall; drive every divergence to ONE worthwhile semantics; terminal only = a named crypto primitive or an ember-decision.
- [⚑ Rise To Meet The Claim](feedback-rise-to-meet-the-claim.md) — overclaim found = fix the text AND open the closure lane in the same breath (caveat lifetime: hours).
- [⚑ Green Or Bust](feedback-green-or-bust-no-artifact-fallbacks.md) — never ship stale/last-good artifacts or non-fatal CI; fail loudly, fix the root.
- [⚑ Empirical Validation > Paper-Green](feedback-empirical-validation-n3.md) — the live N=3 testnet run VALIDATES whether things work; green CI is NOT its prerequisite. Run it to learn (likely cures devnet latest_height:0). Tag/publish come AFTER seeing it work.
- [⚑ Don't Launder Vacuity](feedback-dont-launder-vacuity-as-honest.md) — a labeled vacuity is still BROKEN; prove every load-bearing spec non-vacuous (true AND false).
- [⚑ Conservation ≠ Correctness](feedback-conservation-is-not-correctness.md) — conservation is a PROJECTION not soundness; the 3-corner triangle per effect (full-state eSpec ⟸ executor⟺spec + circuit⟺spec) + the anti-ghost tooth.
- [⚑ Stop Auditing — Internalize](feedback-stop-auditing-internalize-guarantees.md) — issue EMPOWERED DOERS that fix/implement; an out-of-band guarantee = failure to internalize → make the protocol ENFORCE inline.
- [⚑⚑ Don't Launder a Load-Bearing Insecurity](feedback-dont-launder-a-load-bearing-insecurity.md) — SCAR: I rationalized a 31-bit commitment as "consistent w/ the existing scheme / pre-existing audited floor" + stacked 5 trust waves on it. "Load-bearing AND everywhere" = the BUG not a defense; MEASURE the bits (31 vs 62 vs 124), MATCH the system's own soundness (FRI ~130bit → 8-felt commit, not the reserved 4), cite the doc not your assumption; a floor that sits UNDER other work comes FIRST. (Fix: `docs/FAITHFUL-STATE-COMMITMENT.md`.)
- [⚑ Braids Not Waves](feedback-braids-not-waves.md) — finish a cluster → IMMEDIATELY launch/integrate the next strand; main loop = continuous launcher+integrator (commits agent drafts by file set); proofs = subagent work.
- [⚑⚑ Swarm Shared-Tree Clobber Hazard](feedback-swarm-shared-tree-clobber-hazard.md) — all agents share ONE working tree; concurrent edits to shared manifests (Cargo.toml/lib.rs/mod.rs) CLOBBER (scar: the unification edit-war). Main loop owns ALL shared-file edits + cargo; agents draft DISJOINT new files only; shared-manifest restructures in a quiet window. NO WORKTREES (ember-banned, "harsh the vibe"). Don't be scarred by one clobber; dregg-self-host (patches/conflict-objects) is the real cure.
- [⚑ Verification Economy](feedback-verification-economy.md) — NO full-suite re-runs between turns; trust lane logs + targeted spot-checks; full gauntlet = background persvati only.
- [⚑ Cockpit Edits Need the gpui Build Check](feedback-cockpit-edits-need-the-gpui-build-check.md) — starbridge-v2 `cockpit.rs` is in `main.rs` gated `#[cfg(gpui-ui)]`, NOT the lib; the gpui-free `--lib` suite never compiles it (a `crate::` vs `starbridge_v2::` break shipped green ×4). After ANY cockpit/gpui edit: `cargo check --features native-full --bin starbridge-v2`.
- [⚑ HORIZONLOG Standing Practice](feedback-horizonlog-standing-practice.md) — every named follow-up enters git-tracked HORIZONLOG in the same breath; reports/commits aren't durable.
- [⚑⚑ Don't Over-Ember-Gate](feedback-dont-over-ember-gate.md) — drive ALL artifact work (incl. VK-affecting) to green + commit without asking; don't label work "ember-gated". (The redeploy half is now MOOT — the devnet is GONE as of 2026-06-22; see the DEVNET line below.)
- [⚑ Docs Teach What-Is](feedback-docs-teach-what-is.md) — present tense, first principles; NEVER trajectory-narrativize (minimality = a property, history = git).
- [⚑ Sober Demonstrative Register](feedback-sober-demonstrative-register.md) — outward material = what-it-is / play-with-it / what-it-does / what-it-enables for sober programmers; NO pride/boast/scoreboard-vs-prior-art ("Xanadu that shipped" was TOXIC). Broader site sweep owed.
- [⚑ One Executor Entry · Rust is Buggy](feedback-one-executor-entry-real-tests-rust-is-buggy.md) — Rust `turn/` = the BUGGY thing dregg2 replaces, never an oracle; ONE gated entry + ONE @[export]; `#guard` not `#eval`; .md can be stale, read CODE.
- [⚑ No Phantom Commits / Metatheory IS the Jam](feedback-no-phantom-commits-metatheory-is-the-jam.md) — VERIFY THE REFLOG (agents draft-and-return, main loop commits); don't ship the easy 60% + defer the hard core.
- [⚑ Never git-checkout / Don't Dismiss a Stuck Proof](feedback-never-git-checkout-never-dismiss-stuck-proof.md) — WIP-commit not revert; a stuck proof may be a REAL BUG; step back + split, don't thrash.

## MINTED — capabilities earned (write here as eagerly as to scars; each carries a witness)
- [⚑ Perf-Sin Sweep + Verify-Before-Optimism](minted-perf-sin-sweep.md) — 2026-06-24: the system-wide perf-debt sweep as a velocity swarm (hunt→fix the mechanical sins: Vec-as-set→HashSet, clone→borrow, recompute→cache; result-identity-gated, one build at the end). The discipline: dont manufacture sins, LEAVE load-bearing clones (tamper-witness re-folds, API-required moves), STOP-REPORT the risky. Traps: the gpui-build feature trap, the reseal-once soundness-delicacy (NOT a velocity fix), the API throttle + SendMessage-resume. Commits 800214b7a→449a61f04.
- [⚑⚑ Proof-Integrity Discipline + MEASURE-Don't-Claim](minted-proof-integrity-discipline.md) — 2026-06-24: the "decorative proofs" alarm (mine, twice-overstated) was EMPIRICALLY REFUTED — mutation canary (`scripts/mutation-canary.sh`) + `@[load_bearing]` linter (`Dregg2/Verify/LoadBearingLint.lean`: import-boundary + `isDefEq spec gate` + non-vacuity, LIVE in CI) measured 55/60+ specs GENUINE; the ONE real gate-copy (`execGraph` defeq, reaching the C-c1 `deployed_system_secure` guarantee) was found + FIXED (independent `authConnects` + genuine refinement, `61ff2306c`); both residuals closed (`3ff827b4c`/`784894bff`); `ForestLTS` collateral fixed (`0603392d5`); `deployed_no_replay` banked (`0f87f8449`). NEVER call a proof load-bearing/decorative without the structural+mutation test.
- [⚑ Handler-Floors Retire the Gate-Hole Class](minted-handler-floors-retire-gate-hole-class.md) — the proof-carrying `FloorObligation` pattern: a forgotten gate becomes a TYPE ERROR (w: handler-floors P0–P4 `b9a70cecc`→`e649e89bb`, 6/6 floors, the structural answer to the 2026-06-23 review-cycle whack-a-mole; forest inherits for free).
- [⚑ House via the Factory Route](minted-house-via-factory-route.md) — the house capacities weld as PROVEN factory-born cells (vault `0cb50239` + allowance `3f544330` SHIPPED), NOT new Effects; corrects project-house-capacities' 'needs a new verb' prescription (heavier than reality — a vault is a COMPOSITION).
- THE WELD METHOD: census first — the capability usually already EXISTS, disconnected; welding beats building (w: ORGANS.md, the three organ welds).
- MEASURE BEFORE BELIEVING A LEVER (w: #174, `0b05afc1a`) · THE MODEL-FINDS-THE-BUG LOOP (w: QueueRoot→hardening) · STAGED-ADDITIVE-THEN-CUTOVER (w: IR-v2, the rotation train, PATH-PRESERVE) · THE LANE-FINISHER PATTERN · ONE-CORRELATING-OBSERVABLE (`4173d6103`) · TWO-GATES-PROVABLY-AGREE (`7da845758`) · CONVERGENCE ROUNDS catch what narrow verification can't (`55318b702`).
- ⚑ VERIFY-BEFORE-ASSERTING REFUTES BANKED PREMISES: a measured spike overturned the "mimalloc-override + worker-threads block embedding" premise BOTH frontiers leaned on — the executor PD already boots; pg full-D = days (w: the embeddable-runtime spike `c93293686`, `docs/EMBEDDABLE-LEAN-RUNTIME.md`).

## REFERENCE (operational)
- [AGPL Relicense (2026-06-15)](project-agpl-relicense.md) — repo is AGPL-3.0-or-later via a STEALTH full-history rewrite (LICENSE woven at root, NO announce commit) + build-artifact strip (4.0G→276M; pdfs kept); ALL hashes changed; vendored pathfinder + lockfiles deliberately untouched. Don't panic at the reflog.
- [Canonical Domain: fg-goose](project-domain-fg-goose.md) — **dregg.fg-goose.online** is the real domain (dregg.dev NEVER existed); genuine refs fixed in `5e14d8add`, ~125 macaroon-location test fixtures deferred (signed → hash-risky to sweep).
- **DEVNET: GONE (2026-06-22, ember).** The servers are down/decommissioned — there is NO live devnet to redeploy and it must NOT be mentioned in outward docs (README scrubbed). The old box (`34.224.208.52`) had already gone dark 2026-06-19. The redeploy directive is MOOT; don't chase a dead server.
- [Persvati Remote Build](reference-persvati-remote-build.md) — `ssh persvati` (24-core) / `git push persvati main`; `scripts/pbuild <lane> <cmd>` for workspace-scale cargo; Lean stays LOCAL (warm mathlib).
- [Kagi Paper Search](reference-kagi-paper-search.md) — `KAGI_API_KEY` in `~/dev/allgame/.env`; `$ANNAS_SECRET_KEY` for papers.
- [⚑ dregg-mcp Driving Harness](reference-dregg-mcp-harness.md) — the MCP server (`.mcp.json` `dregg-image`) that drives the starbridge-v2 LIVE verified image: inspect/act/map/screenshot the REAL embedded executor. Firebug-for-a-verified-OS. Found its first bug (`AuthRequired::None` cap-badge inversion). Manual: `docs/deos/DREGG-MCP.md`.
- [⚑ THE DREGG ATLAS](reference-dregg-atlas.md) — self-built offline interactive map (game tree + ocap web + 28-surface UI atlas + deep protocol ref), crawled via dregg-mcp. Open `dregg-atlas/site/index.html`. 700-state radial game tree w/ value flows; 28 code-grounded surface explainers; 3 findings. Regenerable: `crawl.py && shoot.py && build.py`.

## HISTORICAL — dated campaign logs + early-project (compressed; superseded by CURRENT above)
- [Distributed Protocols Verified 06-08](project-2026-06-08-distributed-protocols-verified.md) · [Coherence Campaign 06-07](project-2026-06-07-coherence-campaign.md) · [Swap & Tidy Escalation 06-07](project-2026-06-07-swap-and-tidy-escalation.md) · [Overnight Campaign 06-08](project-2026-06-08-overnight-campaign.md) · [Verifiable-Execution 06-06](project-2026-06-06-verifiable-execution-session.md) · [Circuit Audit Synthesis 06-06](project-2026-06-06-circuit-audit-synthesis.md) · [Proof-System Reorientation 06-05](project-proof-system-reorientation-2026-06-05.md) · [Diamond Wave Day 06-05](project-2026-06-05-diamond-wave-day.md) · [Tracks B/D-GST/F + Studies 06-04](project-2026-06-04-tracks-and-studies.md) · [Phase 2 Intent Core](project-phase2-intent-core-done.md) · [dregg2 Coverage Map](project-dregg2-coverage-map.md) · [Postcompaction Design Recovery 06-02](project-postcompaction-2026-06-02-design-recovery.md) · [THE SWAP Roadmap](project-the-swap-roadmap.md) · [Forest Delegation Decorative](project-forest-delegation-decorative.md) · [Swap Framing](project-swap-framing.md) · [Soundness Audit 05-29](project-soundness-audit-2026-05-29.md) · [Demo Passes 05-24](project-demo-passes-2026-05-24.md) · [Dregg Rebuild Research](project-dregg-rebuild-research.md) · [Architecture 05-23](project-architecture-2025-05-23.md) · [Session 2 05-23b](project-session-2025-05-23b.md) · [Apps Audit Framing](project-apps-audit-framing.md) · [Site Build](project-site-build.md) · [Studio Substrate](project-studio-substrate.md) · [Circuit State](project-circuit-state.md) · [Pyana→Dregg rename](project-pyana-renamed-dregg.md) · [SEAL NOTE Fable 5 06-12](seal-note-fable-5-2026-06-12.md).
- [Crate-Split Campaign](project-crate-split-campaign.md) — killed guarantee-gating cargo features by composition (A-with-B cratemap); cell-crypto·no-lean-link·prover·sdk-net all cut. FEATURE-GATING IS DEAD.

The repo has both the abstract Lean whole-history model and the newer Rust segment accumulator comments. I’m reading those two surfaces side by side: `RecursiveAggregation.lean` gives the current `EngineSound` shape, and `ivc_turn_chain.rs` documents the segment construction that the new Lean theorem should model.
exec
/bin/zsh -lc "sed -n '1,320p' metatheory/Dregg2/Circuit/RecursiveAggregation.lean" in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
/-
# Dregg2.Circuit.RecursiveAggregation — RECURSIVE-AGGREGATION SOUNDNESS (magnesium → gold).

**The headline.** A light client that verifies ONE succinct aggregate proof — and re-witnesses
NOTHING of the history — learns that the WHOLE chain of N finalized turns is correct:
every turn executed correctly per the verified executor, the chain is correctly ordered (no
reorder/drop/insert), and the final root is the genuine fold of the whole history. This is the model
that the IVC accumulator (`circuit/src/ivc_turn_chain.rs::prove_turn_chain_recursive` →
`WholeChainProof`) realizes; `verify_turn_chain_recursive` checks only the root, cost independent of N.

**Why proofs are ADDITIVE ATTESTATION here, and that is the POINT.** The light client does NOT
re-execute the history, does NOT re-hash the states, does NOT walk the blocklace. It checks the
succinct aggregate. The aggregate's validity, UNDER the named soundness hypotheses below, IS exactly
`HistoryAggregation.WellFormedChain` (`aggregate_attests_whole_history`) — so trusting the aggregate
is trusting the whole history. The verification IS the trust.

**What is PROVED vs. what is a NAMED, REALIZABLE hypothesis (the boundary).** You cannot prove
plonky3/pickles FRI-recursion soundness in Lean — it is the soundness of a concrete Rust prover over
a concrete field. So we NAME the three soundness facts the recursion engine supplies, as `structure`
fields the headline takes as hypotheses (each realizable: it is the standard SNARK soundness of a
fixed verifier circuit, which `DESIGN-recursion-aggregation-private-joint-turns.md` §H1 argues is a
BOUNDED obligation for plonky3's single fixed verifier AIR + differential testing):

  * **`InnerProofSound`** — an inner whole-turn step proof that VERIFIES attests the verified executor
    ran that turn (`recCexec pre turn = some post`). This is the EffectVm/descriptor
    circuit⟺executor soundness, ALREADY proved per-effect in Lean (`WholeTurnTriangle`,
    `EffectVmEmit*`) — here lifted to the leaf-proof boundary as the realized hypothesis the
    recursion engine carries up.
  * **`BindingAirSound`** — a `TurnChainBindingAir` leaf proof that VERIFIES attests the temporal
    tooth `new_root[i] == old_root[i+1]` over the whole chain (`HistoryAggregation.ChainBound`). The
    AIR's continuity constraint is `ivc_turn_chain.rs:246`; its in-circuit soundness is what the leaf
    proof's verification delivers.
  * **`RecursiveVerifierSound`** — an AGGREGATE proof that VERIFIES attests EVERY wrapped child leaf
    proof verifies. This is the recursion engine's in-circuit verifier (`verify_p3_batch_proof_circuit`
    run as a circuit, `prove_aggregation_layer`) being sound — the ONE big FRI obligation (§H1), the
    part outside Lean.

EVERYTHING ELSE — that these three, COMPOSED, yield the full `WellFormedChain` attestation, and hence
the whole-history correctness + conservation — is PROVED here in Lean, gap-free. The composition is
the load-bearing content: it is where a real aggregation bug (verify proof-of-step-7 but export
step-3's roots; swap a leg; drop a turn) would HAVE to show up, and the proof shows the named
hypotheses leave no such gap.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}). The named
hypotheses are `structure` FIELDS, not axioms — they appear in the theorem statements, witnessed
non-vacuously (§5: a realizing instance exists). Verified with
`lake build Dregg2.Circuit.RecursiveAggregation`.
-/
import Dregg2.Distributed.HistoryAggregation

namespace Dregg2.Circuit.RecursiveAggregation

open Dregg2.Exec (RecChainedState recCexec recChainedSystem recTotal)
open Dregg2.Execution (Run)
open Dregg2.Distributed.HistoryAggregation
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective RestHashIffFrame)

section Engine

/-! ## 0. The SNARK proof object + verifier (opaque carriers).

`Proof` is an abstract STARK/recursion proof (the `RecursionCompatibleProof` /
`RecursionOutput` of `plonky3_recursion_impl`). `verify` is the native verifier
(`verify_recursive_batch_proof`). We treat them as opaque — the WHOLE point is that the light client
calls `verify` and nothing else. Soundness of `verify` w.r.t. the protocol is supplied by the named
hypotheses; we never inspect a proof's internals. -/

variable (Proof : Type)
variable (verify : Proof → Bool)

/-! ## 1. The aggregate artifact — the light client's whole view.

`Aggregate` is the `WholeChainProof` (`ivc_turn_chain.rs:430`): the single root recursion proof, plus
the PUBLIC commitments it exposes — `genesisRoot`, `finalRoot`, `chainDigest`, `numTurns`. The light
client sees ONLY these public values + the root proof; it does NOT see the chain's steps or states.
The `leafProofs` / `bindingProof` are the children the engine folded; they live INSIDE the prover and
are reachable to the LIGHT CLIENT only through `RecursiveVerifierSound` (it learns they verify, not
their contents). -/

/-- The succinct aggregate the light client verifies. `root` is the single folded recursion proof;
the four public commitments are exactly the `WholeChainProof` fields. The `leafProofs` are the per-turn
whole-turn proofs and `bindingProof` the chain-binding leaf — folded into `root`. -/
structure Aggregate where
  /-- The single root recursion proof (the whole tree folded to one — `WholeChainProof.root`). -/
  root        : Proof
  /-- The per-finalized-turn whole-turn (EffectVm) leaf proofs, in chain order. -/
  leafProofs  : List Proof
  /-- The `TurnChainBindingAir` chain-binding leaf proof (the temporal tooth). -/
  bindingProof : Proof
  /-- Public: the genesis root the chain starts from (`WholeChainProof.genesis_root`). -/
  genesisRoot : ℤ
  /-- Public: the final root the chain reaches (`WholeChainProof.final_root`). -/
  finalRoot   : ℤ
  /-- Public: the running digest of the ordered (old,new) pairs (`WholeChainProof.chain_digest`). -/
  chainDigest : ℤ
  /-- Public: the number of finalized turns folded (`WholeChainProof.num_turns`). -/
  numTurns    : Nat

/-! ## 2. The named, realizable soundness hypotheses (the boundary).

These are the three facts the recursion engine supplies that we CANNOT prove in Lean (FRI/recursion
soundness). They are bundled in `EngineSound` as a hypothesis the headline takes — NOT an axiom. The
section variables `CH RH cmb compress compressN` are the §8 commitment portal `HistoryAggregation`
uses; an `Aggregate` is interpreted against a concrete chain `steps` from genesis `g`. -/

variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-- **`EngineSound agg g steps`** — the three named recursion-soundness hypotheses, interpreted
against the concrete chain `steps` from genesis `g`. Realizable (§5 exhibits an instance) and
NON-vacuous. -/
structure EngineSound (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep) : Prop where
  /-- **H-RECURSE (`RecursiveVerifierSound`)** — if the root aggregate verifies, then every child leaf
  AND the binding leaf verify. The recursion engine's in-circuit verifier soundness (the ONE FRI
  obligation, §H1). This is the only hypothesis outside Lean's reach. -/
  recursive_sound : verify agg.root = true →
    (∀ p ∈ agg.leafProofs, verify p = true) ∧ verify agg.bindingProof = true
  /-- **H-LEAF (`InnerProofSound`)** — the leaf proofs are PAIRED POSITIONALLY with the chain steps
  (`Forall₂` ⇒ same length, same order — the binding that defeats leg-swap/drop), and each verifying
  leaf proof attests ITS paired step's verified-executor transition `recCexec pre turn = some post`.
  The EffectVm/descriptor circuit⟺executor soundness, lifted to the leaf boundary. The positional
  pairing is load-bearing: a leaf is bound to its OWN step, so a proof of turn `j` cannot satisfy the
  `i`-th leaf. -/
  leaf_sound : List.Forall₂
    (fun (p : Proof) (s : ChainStep) => verify p = true → recCexec s.pre s.turn = some s.post)
    agg.leafProofs steps
  /-- **H-BIND (`BindingAirSound`)** — a verifying `TurnChainBindingAir` leaf attests the temporal
  tooth over the whole chain (`ChainBound`), AND pins the public genesis/final roots to the chain's
  endpoints. The chain-binding AIR's in-circuit soundness. -/
  binding_sound : verify agg.bindingProof = true →
    ChainBound CH RH cmb compress compressN steps
      ∧ agg.genesisRoot = (match steps.head? with
          | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
          | some s => ChainStep.oldRoot CH RH cmb compress compressN s)
      ∧ agg.finalRoot = foldedFinalRoot CH RH cmb compress compressN g steps

/-! ## 3. THE LIGHT-CLIENT HEADLINE — verifying the aggregate attests the WHOLE history.

The light client runs `verify agg.root` and NOTHING ELSE. We prove: if that one check passes (and the
engine is sound, the named hypotheses), then EVERY turn in the history executed correctly, the chain
is correctly ordered, and the final root is the genuine fold of the whole history. No re-witnessing. -/

/-- Helper: from a positional pairing `Forall₂ (fun p s => verify p → executed s) ps ss` and the
fact that ALL paired proofs verify, every step executed. Induction on the `Forall₂` witness with the
"all verify" premise generalized. -/
theorem forall₂_all_verify_executed
    {ps : List Proof} {ss : List ChainStep}
    (hpair : List.Forall₂
      (fun (p : Proof) (s : ChainStep) => verify p = true → recCexec s.pre s.turn = some s.post) ps ss)
    (hall : ∀ p ∈ ps, verify p = true) :
    ∀ s ∈ ss, recCexec s.pre s.turn = some s.post := by
  induction hpair with
  | nil => intro s hs; cases hs
  | @cons p s ps' ss' hps _htail ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | hrest
    · exact hps (hall p (List.mem_cons_self))
    · exact ih (fun q hq => hall q (List.mem_cons_of_mem p hq)) a hrest

/-- **`every_leaf_verifies_implies_executed`.** From the recursion-soundness + leaf-soundness
hypotheses, a verifying root implies every step's verified-executor transition holds. The chain of
in-circuit verifications collapses to "every turn executed correctly" — `recursive_sound` (root ⇒
leaves verify) composed with `leaf_sound` (positional pairing ⇒ each step executed). -/
theorem every_leaf_verifies_implies_executed
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true) :
    ∀ s ∈ steps, recCexec s.pre s.turn = some s.post := by
  obtain ⟨hleaves, _hbind⟩ := es.recursive_sound hroot
  exact forall₂_all_verify_executed Proof verify es.leaf_sound hleaves

/-- **`AggregateAttests agg g steps`** — the full attestation the light client obtains: every turn
executed correctly, the chain is correctly ordered, the whole chain is a verified-executor `Run` from
genesis, and the public roots are pinned to the genuine endpoints. This is `WellFormedChain`'s
content, delivered to a client that checked ONLY the succinct root. -/
structure AggregateAttests (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep) : Prop where
  /-- (1) every turn executed correctly per the verified executor. -/
  every_turn : ∀ s ∈ steps, recCexec s.pre s.turn = some s.post
  /-- (2) the chain is correctly ordered (the temporal tooth holds — no reorder/drop/insert). -/
  ordered : ChainBound CH RH cmb compress compressN steps
  /-- (3) the public final root IS the genuine fold of the whole history. -/
  final_is_genuine_fold :
    agg.finalRoot = foldedFinalRoot CH RH cmb compress compressN g steps
  /-- (4) the public genesis root is the chain's start. -/
  genesis_pinned : agg.genesisRoot = (match steps.head? with
      | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
      | some s => ChainStep.oldRoot CH RH cmb compress compressN s)

/-- **`light_client_verifies_whole_history` (THE MAGNESIUM→GOLD HEADLINE).**

A light client that checks ONLY `verify agg.root = true` (re-witnessing NOTHING) obtains
`AggregateAttests`: every turn executed correctly, the chain is correctly ordered (no reorder/drop/
insert), and the public final root is the genuine fold of the whole history — UNDER the named,
realizable engine-soundness hypotheses. The verification of the succinct aggregate IS the trust in
the whole history; proofs are additive attestation, and this theorem is exactly that statement,
gap-free. -/
theorem light_client_verifies_whole_history
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true) :
    AggregateAttests Proof CH RH cmb compress compressN agg g steps := by
  obtain ⟨_hleaves, hbind⟩ := es.recursive_sound hroot
  obtain ⟨hbound, hgen, hfin⟩ := es.binding_sound hbind
  exact
    { every_turn := every_leaf_verifies_implies_executed Proof verify CH RH cmb compress compressN agg g steps es hroot
    , ordered := hbound
    , final_is_genuine_fold := hfin
    , genesis_pinned := hgen }

/-! ## 4. The RUN + CONSERVATION the light client inherits (no re-execution).

`AggregateAttests` gives the per-step executor transitions + the ordering; composed with state-level
continuity (the strong form the root tooth recovers under CR, `HistoryAggregation.root_tooth_pins_-
state`), it yields a full `Run recChainedSystem` from genesis, hence conservation over the WHOLE
history — all WITHOUT the light client re-running a single turn. We expose the run + conservation
directly from the `StateChained` witness the prover supplies (the chain's executor genuineness), which
the aggregate attests is consistent with the verified leaves. -/

/-- **`attested_history_is_run`.** Given the executor-genuine chain (`StateChained` — the
prover's witness that the steps are a real run, which the verifying leaves attest step-by-step), the
whole attested history is a `Run recChainedSystem` from genesis to the folded endpoint. The light
client inherits every run-level theorem of the verified record cell.

NOTE (the run vs conservation split): a full `Run recChainedSystem` is a relation on `RecChainedState`
configs, so composing the steps requires the receipt LOG to chain (`s.post = s'.pre`), which the §8
state commitment does NOT bind (it commits the kernel, not the log). The full `Run` therefore genuinely
needs `StateChained`. CONSERVATION, by contrast, reads only the kernel — so it is derivable from the
VERIFIED root without `StateChained`; that is `conserves_from_verification` below (the CRITICAL-3
closure). The log being uncommitted is the exact, named residual: it blocks the full RUN, never
conservation. -/
theorem attested_history_is_run
    (g : RecChainedState) (steps : List ChainStep) (hch : StateChained g steps) :
    Run recChainedSystem g (lastStateOf g steps) :=
  wellformed_is_run g steps hch

/-- **`attested_history_conserves` (KEYSTONE).** Value is conserved across the WHOLE attested
history: the ledger total at the folded endpoint equals the genesis total. A light client trusting the
aggregate trusts a no-mint/no-burn history of arbitrary length, having re-executed nothing. Rides
`HistoryAggregation.wellformed_history_conserves`.

This form takes `StateChained` as a hypothesis (the legitimate producer-supplied path —
`Argus/Aggregate.lean` DERIVES `StateChained` from the genuine producer run). The verification-derived
form that needs NO such hypothesis is `conserves_from_verification` below. -/
theorem attested_history_conserves
    (g : RecChainedState) (steps : List ChainStep) (hch : StateChained g steps) :
    recTotal (lastStateOf g steps).kernel = recTotal g.kernel :=
  wellformed_history_conserves g steps hch

/-! ### CRITICAL-3 CLOSURE — conservation-over-history DERIVED from `verify agg.root`, no `StateChained`.

The critique: `attested_history_conserves` takes `StateChained` (state continuity) as a SEPARATE
prover-supplied hypothesis — exactly what a malicious prover controls — and the tool that could close
it (`root_tooth_pins_state`) recovered only commitment-equality, not state-equality. We close it:
the strengthened `HistoryAggregation.root_tooth_pins_kernel` recovers KERNEL-equality from the verified
root tooth (under the standard Poseidon CR set + the preserved `AccountsWF` invariant), and
`verified_history_conserves` rides that to conservation through `KernelChained` — so conservation
follows from `verify agg.root` itself (which delivers the `ChainBound` tooth via `AggregateAttests`),
plus the genesis pin + the non-cryptographic structural envelope `SeamStruct`. The `StateChained`
hypothesis is GONE from the conservation headline. -/

/-- **`conserves_from_verification` (THE CRITICAL-3 HEADLINE — conservation from `verify agg.root`).**
A light client that checks ONLY `verify agg.root = true` (re-witnessing NOTHING) learns the WHOLE
history conserves value — the ledger total at the folded endpoint equals the genesis total — with NO
`StateChained` hypothesis. The verified root gives `AggregateAttests` (hence the `ChainBound` root
tooth); under the standard Poseidon CR set + the genesis pin + the structural envelope `SeamStruct`
(matched turns + the preserved `AccountsWF` invariant, both non-cryptographic, neither a
state-continuity assertion), `verified_history_conserves` DERIVES kernel continuity from that tooth
(`root_tooth_pins_kernel`) and rides it to conservation. This is the exact gap the critique flagged,
closed: "trusting the aggregate trusts a no-mint/no-burn history" now follows from VERIFICATION, not
from the prover's honesty about state continuity. (The receipt LOG — the one `RecChainedState`
component the §8 root does not bind — blocks only the full `Run`, never conservation; named, not
hidden.) -/
theorem conserves_from_verification
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true)
    (hgen : KernelGenesisPin g steps)
    (hstruct : SeamStruct steps) :
    recTotal (lastStateOf g steps).kernel = recTotal g.kernel := by
  -- the verified root delivers the ordering tooth (ChainBound) — no re-witnessing.
  have hatt := light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
    agg g steps es hroot
  -- conservation follows from the VERIFIED tooth + genesis pin + structural envelope; no StateChained.
  exact verified_history_conserves CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
    g steps hgen hatt.ordered hstruct

end Engine

/-! ## 5. NON-VACUITY — the named hypotheses are REALIZABLE (witnessed BOTH ways).

The headline would be hollow if `EngineSound` were unsatisfiable, or if `verify agg.root = true`
could not occur. We exhibit a CONCRETE realizing instance over the `HistoryAggregation.honestStep`
chain (a real 1-step executor run over the teeth genesis): a `verify` that accepts, an `Aggregate`
whose root/leaf/binding all verify, and an `EngineSound` proof — so the headline fires on a real
chain and concludes a real `AggregateAttests`. We ALSO witness the negative: a `verify` that REJECTS
gives a vacuously-true `EngineSound` (no obligation), and the headline is not invoked — the tooth is
in the `binding_sound`/`leaf_sound` implications, which §6 shows separate honest from
tampered. -/

section Realize

open Dregg2.Exec.ConsensusExec (teethGenesis honestTurn)

/-- A trivial proof carrier (Unit) and an ACCEPTING verifier — the realizing engine instance. -/
abbrev RealProof := Unit
def acceptAll : RealProof → Bool := fun _ => true

/-- The §8 portal realized by constant-zero hashes for the witness (the realizing instance only needs
the structure to typecheck + the soundness implications to hold; the CR carriers are not invoked here
because the engine hypotheses are supplied DIRECTLY as the realized facts). -/
def zCH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ := fun _ _ => 0
def zRH : Dregg2.Exec.RecordKernelState → ℤ := fun _ => 0
def zcmb : ℤ → ℤ → ℤ := fun _ _ => 0
def zcompress : ℤ → ℤ → ℤ := fun _ _ => 0

exec
/bin/zsh -lc "sed -n '1,220p' docs/reference/lean-circuit.md && sed -n '600,700p' metatheory/Dregg2/AssuranceCase.lean" in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
# Lean: circuit soundness & unfoolability

What this subsystem IS at HEAD. The Lean proof that a light client which verifies a
batch proof and **runs nothing else** cannot be fooled: every accepted proof decodes
to a genuine kernel transition whose endpoints are the published commitments. Lives
under `metatheory/Dregg2/Circuit/` (the soundness story) and
`metatheory/Dregg2/Lightclient/` (the verifier-side data structures). Every
load-bearing claim below is cited to a `Module.decl` or file:line.

This is the Lean companion to the Rust `docs/reference/circuit.md` (the
prove/verify crates). Here the object is the *theorem*, not the prover.

## The target (what soundness means)

`Dregg2.Circuit.CircuitSoundness` states the goal directly: a light client verifies a
batch proof against the live VK and runs nothing; soundness is

> `verifyBatch vk pi π = accept ⟹ ∃ a genuine kernel transition s ⟶ s'` with
> `pi.pre = stateCommit s ∧ pi.post = stateCommit s'`

(`CircuitSoundness.lean:11-14`). The "genuine kernel transition" is the declarative
kernel `ActionDispatch.fullActionStep`, composed over a turn by `turnSpec` and
identified with the real executor `execFullTurnA` via `execFullTurnA_iff_turnSpec`
(`CircuitSoundness.lean:16-21`).

## The three load-bearing pieces

1. **`StateDecode`** — the faithful witness→kernel-state decode
   (`CircuitSoundness.StateDecode`, `CircuitSoundness.lean:187`). It says the
   witness's published OLD/NEW commitments *equal* the surface commitment of the
   bound kernels (`preBinds`/`postBinds`) over a fixed `CommitSurface`, and that
   those kernels are `AccountsWF`. Faithfulness is **not assumed**: it is a theorem.
   `stateDecode_pre_faithful` / `stateDecode_post_faithful`
   (`CircuitSoundness.lean:201`, `:210`) prove that two states decoding the *same*
   published commitment have *equal* kernels — by `CommitSurface.commit_binds`
   (`CircuitSoundness.lean:144`), which is `recStateCommit_binds_kernel` repackaged:
   the commitment binds the kernel under the Poseidon CR set, using **no** authority
   gate and **no** frame assumption.

2. **`descriptorRefines d kstep`** — the per-effect rung
   (`CircuitSoundness.descriptorRefines`, `CircuitSoundness.lean:232`): any
   `Satisfied2` witness of descriptor `d` whose published commitments decode (via a
   faithful `StateDecode`) to `pre`/`post` forces `kstep pre post`. Its antecedent is
   the named hash-CR carrier `Poseidon2SpongeCR hash` (`:234`) — the floor the
   per-descriptor published-PI↔limb binding consumes. This is the genuine obligation
   each effect discharges; the apex carries the registry-wide family of these.

3. **`lightclient_unfoolable`** — the apex (`CircuitSoundness.lean:453`). Its only
   data inputs are what a light client actually has — the public inputs `pi` and the
   proof `π`. It does **not** take `pre`/`post` or a `StateDecode` as hypotheses;
   those would hide the hardest rung. Instead it *derives* the decode from named
   floors and concludes the existence of a genuine kernel boundary.

## The apex and its carried floors

```
theorem lightclient_unfoolable
    (hash) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (kstep) (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (pi) (π) (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = accept) :
    ∃ pre post, StateDecode S pi.toPublished pre post ∧ kstep pi.effect pre post
              ∧ pi.pre = S.commit pre.kernel pi.turn
              ∧ pi.post = S.commit post.kernel pi.turn
```
(`CircuitSoundness.lean:453-465`). The derivation chain: `StarkSound` extracts a
`Satisfied2` witness of the *claimed* descriptor whose published commitments are
`pi.toPublished` → `WitnessDecodes` produces `pre`/`post` with a `StateDecode` →
`hrefines` turns witness + decode into `kstep pi.effect pre post` → the decode's
binding re-exports `pi.pre`/`pi.post` as the genuine endpoint commitments
(`CircuitSoundness.lean:466-479`).

The **carried obligations ledger** — every named, deferred premise (nothing
laundered to `True` or an open hole):

- **`StarkSound hash R`** (`class`, `CircuitSoundness.lean:382`) — the audited p3
  batch-STARK soundness / FRI extraction: a verifying batch yields a `Satisfied2`
  witness of the claimed descriptor whose published PI agree with `pi`. Realizable,
  audited, **not provable in Lean**; carried as a class.
- **`Poseidon2SpongeCR hash`** + the `CommitSurface` CR fields (`CommitSurface`,
  `CircuitSoundness.lean:113-134`) — the standard Poseidon collision-resistance set
  (`cmbInj`, `compInj`, `compNInj`, `leafInj`, `restFrame`) the full-state root
  `recStateCommit` binds under. Realizable; bundled, never an axiom.
- **`hrefines`** — the per-effect refinement family, the genuine remaining rung work
  (discharged effect-by-effect downstream).
- **`WitnessDecodes hash R S pi`** (`def`, `CircuitSoundness.lean:446`) — the
  witness→kernel-state **existence** rung: a witness publishing `pi` decodes to some
  `(pre, post)`. A light client cannot supply `pre`/`post`; this rung supplies them
  (the surjectivity of the commitment surface on the published roots). Carried
  explicitly, never discharged by assuming the conclusion.

The minimal honest STARK-batch interface (`VerifyKey`, `vkOfRegistry`,
`BatchPublicInputs`, `verifyBatch`, `Verdict.accept`, `StarkSound`,
`tracePublishedCommit`) is **defined here** because none existed
(`CircuitSoundness.lean:290-387`); `verifyBatch` is `opaque` — the apex reasons only
through the verdict and the `StarkSound` extraction (`:351-353`).

## Scope — what the apex proves, and the freshness boundary

`lightclient_unfoolable` proves **single-transition** soundness: every accepted batch
decodes to a genuine kernel step committing to `pi.pre`/`pi.post`, taking `pi.turn`
as given. It establishes **nothing** about whether that transition is *fresh*
(unreplayed) or its ordering (`CircuitSoundness.lean:412-435`).

Cross-turn freshness / no-replay is a **separate** theorem,
`Dregg2.Circuit.CrossTurnFreshness`. `no_replay` (`CrossTurnFreshness.lean:164`)
proves a proof is applicable at most once; `replay_rejected_after_apply`
(`:177`) is the mutation-confirm. It rides the agent nonce bound *into*
`recStateCommit` (it lives in the agent cell's leaf and strictly increases each
turn, so the commitment sequence never cycles) — `commit_neq_of_nonce_neq`
(`:72`), `TurnChain.commit_no_repeat` (`:130`). The named residual is wiring the
full `runTurn`-driven accepted sequence into a monotone `TurnChain`; the
prologue-bump legs are proved (`runTurn_failed_strictly_advances`, `:229`;
`runTurn_strictly_advances_agentNonce`, `:246`).

## Whole-turn composition: the chain and its derived frame

§4–§9 of `CircuitSoundness` lift the single-effect apex to a whole turn. A turn is a
`List` of per-step circuit witnesses, each publishing its own OLD/NEW commitment (the
prover's chained-root column). The cross-step **frame** — that one step's post-state
*is* the next step's pre-state — is **derived, not assumed**:

- `stateDecodeChain_frame_continuous` (`CircuitSoundness.lean:279`) — equal published
  seam commitments + faithfulness force `a.post.kernel = b.pre.kernel`.
- `TurnDecodeChain` (`structure`, `CircuitSoundness.lean:570`) — a turn threaded
  left-to-right; `turnDecodeChain_seam_kernel_derived` (`:593`) proves the kernel
  half of every seam from the published kernel-root column (the frame **tooth**: a
  prover whose published seam disagrees with the threaded kernel is rejected).
- `turnDecodeChain_refines_turnSpec` (`:633`) folds the per-step `descriptorRefines`
  along the chain into `∃ acts, turnSpec start acts fin`.
- `lightclient_turn_unfoolable_forest` (`:836`) — the whole-turn headline: a verified
  turn + the per-effect family + floors ⟹ a genuine `execFullTurnA s acts = some s'`
  whose endpoints commit to the published turn-level `(pre, post)`.

### The receipt-log seam (§9)

`recStateCommit` is kernel-only — it does not bind the `RecChainedState.log` receipt
chain — so the full-state seam carried its **log** half as a free residue. §9 closes
it, mirroring the kernel tooth: `LogDecode` (`CircuitSoundness.lean:891`) binds
published log commitments to `pre.log`/`post.log` through the realizable
`logHashInjective LH` carrier; `logDecodeChain_frame_continuous` (`:914`) forces
`a'.log = b.log` across a seam; `turnDecodeChainLog_seam_full_derived` (`:985`)
recovers the whole `RecChainedState` continuity `a.post = b.pre` on both components;
`turnDecodeChainLog_rejects_forged_log` (`:1008`) is the mutation-confirm — a forged
intermediate receipt-log is UNSAT. Non-vacuity of the `logHashInjective` carrier is
exhibited inline (`:1031` — a collapsing hash cannot be injective).

## The closed apex and the per-effect taxonomy

`lightclient_unfoolable` carries `hrefines : ∀ e, descriptorRefines …` as a
hypothesis. The closure layer *discharges* that family from genuine per-effect rungs:

- `Dregg2.Circuit.ClosureAll` holds one `<effect>_closedLog` rung per effect family
  (transfer tag 0 `transfer_closedLog`, `ClosureAll.lean:152`; cellSeal 52, revoke 2,
  delegate 1, attenuate 12, mint 3, burn 4, noteSpend 27, … — 55 `_closedLog`
  theorems covering the effect set). Each is a one-liner over the generic combinator
  `closedLog_of_encode` (`:121`): it derives the `.log` advance through
  `logHashInjective` and bridges to `kstepAll` via the effect's landed
  `<effect>_descriptorRefines` rung. The dominant class is **CLASS A** — the
  effect's write is *forced from a deployed `Satisfied2` descriptor* (e.g.
  `cellSeal_closedLog_sat` forces the seal from the deployed `cellSealV3`,
  `ClosureAll.lean:189`; the cap family from `delegateWriteCapOpenV3`,
  `revokeCapabilityV3`, `attenuateCapOpenEffV3`, etc., `:983-1198`), not a modelled
  gate. The earlier per-effect refinement classes (`VALUE_FORCED`,
  whole-kernel-freeze) appear in `RotatedKernelRefinement*` (e.g.
  `RotatedKernelRefinementMisc.lean:30,629`).

- `Dregg2.Circuit.ClosureFinal` bundles them into **one** parametric floor.
  `ClosedWitness` (`structure`, `ClosureFinal.lean:131`) carries, for the published
  effect only, the `WitnessDecodes` existence rung + the single `ClosedLogExtract`
  decode + the `logHashInjective` log enrichment — "one floor, parametric in
  `pi.effect`; NOT a 36-way family" (`:117-123`).
  `lightclient_unfoolable_circuit_sound` (`:161`) is the headline on exactly the
  standard SNARK-soundness foundations. `closedWitness_of_readouts` (`:202`) builds
  that floor from the genuine `ClosureReadouts` bundle whose `ext` routes through
  every proven `<e>_closedLog` rung (`:190-196`) — keeping the per-effect rungs
  load-bearing, not decorative.

- `Dregg2.Circuit.ClosureForest.lightclient_unfoolable_circuit_sound_turn`
  (`ClosureForest.lean:144`) is the **whole-turn closed apex** over heterogeneous
  effects (`hidx` identifies each step's descriptor as `Rfix e` for any effect, freely
  mixed) — no transfer-only residual. Non-vacuity is exhibited:
  `closedLogExtract_family_covers_mixed` (`:190`) inhabits the rung at cellSeal/revoke/
  mint simultaneously; `lightclient_unfoolable_circuit_sound_turn_empty` (`:239`)
  shows the floors jointly compose.

- `Dregg2.Circuit.CircuitSoundnessAssembled` instantiates the apex at the concrete
  `Rfix`/`kstepAll`/`hrefinesAll`: `kstepAll := dispatchArm`
  (`CircuitSoundnessAssembled.lean:380`), `EffectDecodeBridge` *is*
  `descriptorRefines … (kstepAll e)` (`:410`), and `hrefinesAll` (`:427`) assembles
  the per-effect bridge family into the apex's `∀`.
  `lightclient_unfoolable_assembled` (`:440`) and
  `lightclient_turn_unfoolable_forest_assembled` (`:463`) are the capstones.

## Whole-history aggregation (the light client over a chain)

`Dregg2.Circuit.RecursiveAggregation` lifts single-turn soundness to a whole history.
`light_client_verifies_whole_history` (`RecursiveAggregation.lean:200`): a verified
aggregate root attests every per-step executor transition, the ordering, the genesis
pin, and a genuine final fold (`AggregateAttests`). `attested_history_is_run`
(`:234`) exposes the whole history as a `Run recChainedSystem` from genesis;
`attested_history_conserves` (`:247`) and the verification-derived
`conserves_from_verification` (the CRITICAL-3 closure, `:252` ff.) inherit
conservation over the whole history **without re-executing a single turn**. The named
residual is exactly the uncommitted receipt **log**: it blocks the full `Run` (which
needs `StateChained`) but never conservation, which reads only the kernel
(`:227-233`).

## Settlement soundness

`Dregg2.Circuit.SettlementSoundness.settlement_soundness`
(`SettlementSoundness.lean:210`) extends single-transition unfoolability across a
settlement: authority is live-at-settlement (`settled_revocation_bounded` `:139`,
`settled_revocation_immediate` `:150`, `finalized_commit_binds_revoked` `:168`).
`settlement_soundness_single_machine` (`:251`) is the n=1 collapse; `settlement_bites`
/ `settlement_gap_real` (`:314`,`:324`) witness it non-vacuous.

## The light-client data structures

#assert_axioms Dregg2.Apps.CapSlotFactory.stored_cap_only_fresh_if_epoch_unrevoked
#assert_axioms Dregg2.Apps.CapSlotFactory.revoke_stales_stored_cap
#assert_axioms Dregg2.Apps.CapSlotFactory.store_then_revoke_refused
-- the negative-lifecycle teeth: liveness/death is not decidable (consensus-bound, like revocation):
#assert_axioms Dregg2.Liveness.dead_undecidable

/-! ===========================================================================
## Guarantee E — UNFOOLABILITY

*A light client verifying a Q-chain learns A–D for the WHOLE history; re-witnessing nothing.*

This is the apex that COMPOSES A–D over an entire history and hands them to a verifier who
runs nothing but `verify agg.root`.

DAG:
  • `Circuit.RecursiveAggregation.light_client_verifies_whole_history` — THE headline:
    checking ONLY `verify agg.root` (re-witnessing NOTHING) ⇒ every turn executed correctly,
    correctly ordered, and the final root is a genuine fold. Proofs-as-additive-attestation.
  • `Circuit.RecursiveAggregation.attested_history_conserves` — the whole attested history
    conserves (guarantee B, lifted to the full run).
  • `Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind` — the ANTI-GHOST: a
    reordered chain forces `ChainBound = False`, so no verifying aggregate exists.
  • `Circuit.RecursiveAggregation.leaf_pairing_defeats_swap` — positional pairing means a
    verifying leaf is not re-pointable to a different step.
    the seam tooth `new_root[i] = old_root[i+1]` pins the whole history.
  • `Distributed.HistoryAggregation.root_tooth_pins_kernel` — the STRENGTHENED CR recovery: a light
    client seeing only the matching roots learns the adjacent KERNELS coincide (state-equality, not
    merely commitment-equality), via `recStateCommit_binds_kernel` under the standard Poseidon CR set
    + the preserved `AccountsWF` invariant. This is what `root_tooth_pins_state` (commitment-equality
    only) could not deliver — the CRITICAL-3 fix.
  • `Circuit.RecursiveAggregation.conserves_from_verification` — THE CONSERVATION-OVER-HISTORY CLOSURE:
    conservation across the whole history follows from `verify agg.root` ALONE (the verified `ChainBound`
    tooth ⇒ kernel continuity ⇒ conservation), with NO prover-supplied `StateChained` hypothesis. The
    one `RecChainedState` component the §8 root does not bind is the receipt LOG; it blocks the full
    `Run` (which `attested_history_is_run` still takes `StateChained` for), never conservation — the
    exact, named residual.
  • `Circuit.Argus.Aggregate.argus_strand_light_client` + `tampered_argus_strand_rejected` —
    the Argus-strand realization of the same case on the executable term IR.

Floor: FRI / STARK soundness (`EngineSound.recursive_sound`, the ONE recursion obligation),
Poseidon2-CR (`recStateCommit` binds the seam roots), ed25519 (strand-block signatures),
PostGSTProgress (a FINALIZED — not merely valid — chain, via the finality-cert leg).
=========================================================================== -/

section UnfoolabilityApex
open Dregg2.Circuit.RecursiveAggregation
open Dregg2.Distributed.HistoryAggregation (ChainStep KernelGenesisPin SeamStruct lastStateOf)
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective RestHashIffFrame)

variable {AProof : Type} (verify : AProof → Bool)
variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)

/-- **`unfoolability_guarantee` (NOW A REAL STATEMENT — the whole-history headline, conjoined).**
The unfoolability apex, stated as an actual proposition rather than a `True` anchor: a light client
that checks ONLY `verify agg.root = true` (re-witnessing NOTHING) learns BOTH (1) `AggregateAttests`
— every turn executed correctly, the chain is correctly ordered (no reorder/drop/insert), and the
public final root is the genuine fold of the whole history — AND (2) the WHOLE history conserves value
(the endpoint ledger total equals genesis), DERIVED FROM VERIFICATION under the standard Poseidon CR
set + the genesis pin + the structural envelope, with NO prover-supplied `StateChained` hypothesis
(the CRITICAL-3 closure). So E genuinely COMPOSES A–D over the whole history handed to a
`verify agg.root`-only client. This conjoins `light_client_verifies_whole_history` with
`conserves_from_verification`; the game-based reduction (`LightClientUC.unfoolable_of_floor`) and the
anti-ghost teeth (`tampered_aggregate_cannot_bind`) are pinned below. -/
theorem unfoolability_guarantee
    (agg : Aggregate AProof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound AProof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    (hgen : KernelGenesisPin g steps) (hstruct : SeamStruct steps) :
    AggregateAttests AProof CH RH cmb compress compressN agg g steps
      ∧ recTotal (lastStateOf g steps).kernel = recTotal g.kernel :=
  ⟨light_client_verifies_whole_history AProof verify CH RH cmb compress compressN agg g steps es hroot,
   conserves_from_verification AProof verify CH RH cmb compress compressN
     hCmb hCompress hCompressN hLeaf hRest agg g steps es hroot hgen hstruct⟩

#assert_axioms unfoolability_guarantee

end UnfoolabilityApex
-- the underlying keystones, re-pinned under Unfoolability:
#assert_axioms Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history
#assert_axioms Dregg2.Circuit.RecursiveAggregation.attested_history_conserves
#assert_axioms Dregg2.Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind
#assert_axioms Dregg2.Circuit.RecursiveAggregation.leaf_pairing_defeats_swap
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_engine_sound
#assert_axioms Dregg2.Distributed.HistoryAggregation.wellformed_attests_whole_history
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_state
#assert_axioms Dregg2.Distributed.HistoryAggregation.tooth_rejects_broken_order
-- the CRITICAL-3 closure (conservation-over-history DERIVED from verification, no StateChained):
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_kernel
#assert_axioms Dregg2.Distributed.HistoryAggregation.kernelChained_conserves
#assert_axioms Dregg2.Distributed.HistoryAggregation.verified_history_conserves
#assert_axioms Dregg2.Circuit.RecursiveAggregation.conserves_from_verification
#assert_axioms Dregg2.Circuit.Argus.Aggregate.argus_strand_light_client
#assert_axioms Dregg2.Circuit.Argus.Aggregate.argus_strand_conserves
#assert_axioms Dregg2.Circuit.Argus.Aggregate.tampered_argus_strand_rejected
-- the GAME-BASED unfoolability reduction (`Crypto.LightClientUC`): the soundness game `Foolable`

exec
/bin/zsh -lc "sed -n '1,180p' ~/.claude/projects/-Users-ember-dev-breadstuffs/memory/project-circuit-soundness-apex.md && sed -n '1,180p' ~/.claude/projects/-Users-ember-dev-breadstuffs/memory/project-argus-vision.md" in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
---
name: project-circuit-soundness-apex
description: "Light-client unfoolability — the apex (lightclient_unfoolable) + the five guarantee apexes + the cap-reshape crown + the macaroon↔cap convergence arrow are #assert_axioms-clean; per-effect rungs PROVEN individually (dominant label CLASS A); the genuine open is a short named-residual tail. docs/reference/ is the grounded what-is."
metadata: 
  node_type: memory
  type: project
  originSessionId: 3b829648-9d41-4dad-bd2e-1a3eb7f618ab
---

⚑ GROUNDED SOURCE-OF-TRUTH (committed, grounded to file:line at HEAD): `docs/reference/` is now the what-is reference for the whole system — start at `docs/reference/lean-circuit.md` (circuit soundness/unfoolability), `lean-assurance.md` (the five guarantees), `lean-authority.md` (the macaroon↔cap bridge). When a memory claim and `docs/reference/` disagree, the doc wins (it's regenerated against HEAD).

THE PROPERTY: `verifyBatch accept ⟹ ∃ a genuine kernel transition committing to the published (pre,post)` — a light client that runs nothing but the verifier cannot be fooled. Map + state: `metatheory/CLAIMS.md` (§OPEN is the real-debt list, build-enforced), `metatheory/docs/COMPOSITION-SOUNDNESS-CENSUS.md` (the turn/turn-sequence seam census), `metatheory/docs/RECURSION-AGGREGATION-CENSUS.md` (the whole-history fold), `docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md` (the per-effect obligation table = a proven-class taxonomy). The `Dregg2.lean` per-import annotations are a rich, current per-module map.

⚑⚑⚑ THE APEX + THE FIVE GUARANTEES + THE CROWN ARE `#assert_axioms`-CLEAN-CLOSED (verified at HEAD `1097938e3`). The corpus carries ZERO open holes (`sorry`/`admit`/`native_decide`) — whole-corpus scan = 0; the only `axiom`-keyword decls are the two named DEMO axioms in `Widget/Basic.lean`. `lake env lean Dregg2/Claims.lean` is the build-enforced ledger (165 theorem pins + 50 namespace pins), failing loudly if any keystone regresses to an open-hole axiom.

WHAT IS CLOSED (every theorem's `collectAxioms` is exactly `{propext, Classical.choice, Quot.sound}`):
- **The light-client apex** `theorem lightclient_unfoolable` (`Dregg2/Circuit/CircuitSoundness.lean:453`, `#assert_axioms`-pinned `:1058`) — `accept ⟹ ∃ pre post, StateDecode ∧ kstep ∧ pre/post commit to the published roots`; data inputs are ONLY what a light client holds (`pi`, `π`) — no `pre`/`post`/`StateDecode` smuggled in. Carries the named crypto floor only: `StarkSound` (FRI extraction), `Poseidon2SpongeCR`, the per-effect `descriptorRefines` family, `WitnessDecodes`. (This IS a real theorem of that name — NOT a phantom. Source-of-truth: `docs/reference/lean-circuit.md:48,57`.)
- **The five guarantee apexes** (`Dregg2/AssuranceCase.lean`, each home-pinned + re-pinned): `authority_guarantee` (`:166`), `conservation_guarantee` (`:259`), `integrity_guarantee` (`:412`, + `_whole_turn` `:452`), `freshness_guarantee` (`:581`), `unfoolability_guarantee` (`:666`). The whole-history headline is `RecursiveAggregation.light_client_verifies_whole_history`; `Crypto.LightClientUC.unfoolable_of_floor` reduces light-client soundness to STARK/Fiat-Shamir extractability + sponge-CR, and `fooling_breaks_floor` extracts a concrete floor-break from any fooling attack. (Note: `lean-assurance.md` is right that the *AssuranceCase aggregation* has no theorem literally named `lightclient_unfoolable` — that name lives in `CircuitSoundness.lean`; the assurance apex is `unfoolability_guarantee`. Both real, different homes.) Source-of-truth: `docs/reference/lean-assurance.md`.
- **THE CAP-RESHAPE CROWN (ARGUS linchpin #103) LANDED** — `capReshapeVmDescriptor` (`Dregg2/Circuit/Emit/EffectVmEmitCapReshape.lean`): in-row sites RECOMPUTE the held-entry leaf + the openable `capability_root` (depth-16 sorted-Poseidon2), and the gates force non-amp + production-authority over the GENUINE `is_attenuation` lattice (`Cap`/`ExecAuth = Finset Auth`, NOT a bare bitwise mask). The teeth: `capReshape_nonAmp_in_circuit` (a satisfying witness FORCES the submask non-amp), `capReshape_production_in_circuit` (forces the held-cap-controls-the-well production leg), and the two-valued anti-ghost `capReshape_rejects_amplify` + `capReshape_rejects_no_control`. All `#assert_axioms`-clean. The cap_root↔is_attenuation weld + the production-authority leg are no longer a "plan" (see the closed plan, folded below).
- **Whole-history aggregation** — `light_client_verifies_whole_history` (`Dregg2/Circuit/RecursiveAggregation.lean`, sorry-free, axiom-clean): one constant-cost check yields `AggregateAttests` (every turn executed, chain correctly ordered, final root is the genuine fold). `conserves_from_verification` rides the same root with no prover-supplied continuity; `tampered_aggregate_cannot_bind` + `leaf_pairing_defeats_swap` are the chain-level anti-ghost teeth. This is LIVE-WIRED: `circuit-prove/src/ivc_turn_chain.rs::prove/verify_turn_chain_recursive` (real plonky3 in-circuit FRI recursion) ← `lightclient/src/lib.rs::verify_history` (line 147). dregg ALREADY does the Mina-Pickles-shaped succinct-whole-chain thing, with a Lean-proven composition Mina lacks (see RECURSION-AGGREGATION-CENSUS — the "Silver→Golden / future" framing UNDERSTATES the live state). Cross-cell width axis (`bilateral_aggregation_air.rs` → node `/turns/aggregate`) is also live.
- **Whole-history non-forgeability** `Spec.only_connectivity_begets_connectivity` (`Spec/Authority.lean:456`, home-pinned) — the Granovetter closure across an ENTIRE history (the old "confirmed DIRTY" verdict is gone).
- **The distributed extension** `settlement_soundness` (`Metatheory/SettlementSoundness.lean:153`, `#assert_axioms`-clean) — a SETTLED turn exercised a LIVE-at-tip authority; `revoke_before_tip_unsettleable` the operational contrapositive; collapses to immediate at n=1. (`BindsLiveAuthority` is a typed hypothesis the deployed settlement predicate discharges — the named §8-style composition obligation, with `deployedSettle_binds_live_authority` instantiating it.)
- **THE NAMED EPOCH-STAMP RESIDUALS ARE CLOSED.** `SpawnEpochStampResidual` / `RevokeDelegationEpochResidual` / `RefreshEpochStampResidual` (`Circuit/EffectRefinement.lean`, `EffectRefinementBatch2.lean`) each carry the source verdict "CLOSED (NOT an open residual). SUPERSEDED by the deployed `spawnE`/refresh descriptor" — the moving-face descriptor cutover (§3.EPOCH) LANDED; the `delegationEpoch += 1` freshness tick is now in-circuit-forced (`revokeDelegationFullA`, `EffectVmEmitRotationV3.lean`). The hostile-witness extraction lane is fully closed (`Circuit.CircuitOpenFronts.countOpenFronts = 0`, 32/32 effects).
- **The cross-turn replay residual is closed.** `BodyNonceNondecreasing` is DISCHARGED for the live forest body — `forest_body_nonceNondecreasing` (`Circuit/CrossTurnFreshness.lean:1170`, via `execFullForestA_agentNonce_nondecr`); `acceptedSeq_to_TurnChain` wires the abstract `TurnChain` to the accepted-`runTurn` sequence. The COMPOSITION-SOUNDNESS-CENSUS "rank-2" gap is resolved at the assembly.
- **The whole circuit corpus is sorry-free**, including every `CircuitCompleteness*.lean` (sound ∧ complete, the floor asymmetry between directions kept explicit — SOUND needs `WitnessDecodes`+`StarkSound`; COMPLETE needs only `stateDecode_construct`+`StarkComplete`).

THE PER-EFFECT CLASSES (PROVEN INDIVIDUALLY, per `docs/reference/lean-circuit.md` + `docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md`): at HEAD the DOMINANT per-effect closure label is **CLASS A** — the effect's gate is FORCED from the DEPLOYED v3-registry descriptor (`= Rfix <tag>` by `rfl`) so a satisfying `Satisfied2` witness forces the kernel step (`Dregg2/Circuit/ClosureAll.lean`: cellSeal/receiptArchive/heapWrite/exercise/revoke/delegate/introduce/delegateAtten/… are all annotated CLASS A). The earlier per-effect-refinement labels VALUE_FORCED / RECORD-DIGEST-ANCHORED / MAP-OP-FORCED survive only in a few module headers and the older obligation doc — they describe the *kind of column forced*, not a clean three-way partition of the deployed corpus. Treat CLASS A (Satisfied2-forced) as the live framing; don't recite the three-class taxonomy as the partition. `mint` is forced + deployed under its own `sel::MINT=14` selector + cap-reshape-bound authority (supply Stage 2b, `51488682f`); the cap family (attenuate/delegate/delegateAtten/introduce/revokeCapability) is forced via the cap-reshape crown's recompute+submask; noteSpend forces double-spend non-membership.

THE GENUINE OPEN (CLAIMS.md §OPEN — the real-debt list; honest named residuals, NOT open holes):
- **Composition — the intra-turn receipt-LOG seam** (COMPOSITION-SOUNDNESS-CENSUS seam #3, rank-1): the commitment surface binds `RecChainedState.kernel`, so the KERNEL half of the intra-turn seam is FORCED (`turnDecodeChain_seam_kernel_derived`), but the receipt-LOG continuity is a CARRIED chain field, not yet a forced one. The apex's unfoolability "this is a real kernel evolution" HOLDS; "the receipts are the genuine receipts" is the carried half. Closure = add a log-root limb to `CommitSurface` and re-derive the log half exactly as the kernel half. Small.
- **The un-assembled `∀ e, descriptorRefines (R e) (kstep e)` COMPOSITION** — per-effect rungs are proven; the universally-quantified single assembly over the live registry is the remaining structural fold (the per-turn/per-effect folds `turnDecodeChain_refines_turnSpec` + `lightclient_unfoolable_circuit_sound_turn` ARE proven; the `∀ e` registry-wide statement is the residual).
- **The faithful-encoding carriers** — cap-tree↔Caps, nullifier-tree↔set, the §8 `CryptoKernel`/`Poseidon2SpongeCR` floor (TERMINAL crypto, by design never Lean's). The denotational Lean↔Rust eval-agreement differential is BUILT (`circuit/tests/ir2_denotational_differential.rs`; see [[feedback-byte-identity-differential-is-not-faithfulness]]) — the interpreter edge is no longer a directive.
- **Deployed-side `attenuate` is VALUE_PARTIAL** — the in-circuit submask non-amp is proven and the cap Phase-D membership-into-`capability_root` leg is WIRED (`sdk/src/full_turn_proof.rs` `CapMembershipExpectation` + `verify_full_turn_bound`: root-binding `CapRootMismatch` + leaf-binding `CapLeafMismatch` + leg-present teeth, anti-forgery tests bite). The residual is the v3 registry-cutover (route `attenuate` through the recompute descriptor as its deployed lead), NOT the binding.

CONSENSUS / DISTRIBUTED OPEN (named residual `Prop`s, the partial-synchrony model discharges): CM-liveness/O2-pacemaker (`cm_pacemaker_residual`), CM-dissemination (reliable-broadcast convergence), CM-Stingray (the bandwidth-accounting model; the safety bounds ARE proved), Synchronizer↔operational `World.rand` coupling, `Coordination` mu-recursion projection-progress (the `NoRec` fragment is proved), `Proof.Refine` full abstract forward-simulation (conservation + intra-vat integrity refinements ARE pinned; the missing piece is an abstract small-step relation absent from `Core`), HandlerTransformer upper tiers. These are §8/consensus boundaries, not circuit-soundness holes.

THE MACAROON↔CAP CONVERGENCE ARROW IS PROVEN (no longer a research edge): `theorem chainGateG_implies_capAuthorityG` (`metatheory/Dregg2/Authority/CaveatCapBridge.lean:168`, `#assert_axioms`-pinned at `:606`, plus the non-vacuity twin `chainGateG_implies_capAuthorityG_devac` at `:357`/pin `:592`) — on a coherently-built bridge node, the macaroon caveat-chain narrowing IMPLIES the kernel cap authority `granted ⊆ held`. The four credential aspects (biscuit · macaroon · cap · zk) are the ONE authority seen four ways, and the macaroon→kernel-gate refinement is now a closed Lean theorem, not a `&&`-conjunction hope. The production law is fully proven + in-circuit for the cap aspect (`granted ⊆ held` via `recKDelegateAtten`/`capAuthorityG`/`checkSubset`, witnessed against the authenticated `capability_root`); `CaveatCapBridge` welds the macaroon caveat-chain to it. Source-of-truth doc: `docs/reference/lean-authority.md` §"The convergence arrow". (Earlier memory called this "the honest research edge / joined by `&&` / no theorem `chainGateG → capAuthorityG`" — STALE, the theorem exists and is axiom-clean.)

VK CAVEAT: cap-write/cap-open and supply-mint descriptors are VK-affecting. Drive ALL such artifact work to green + commit (per [[feedback-dont-over-ember-gate]] — the redeploy half is MOOT, the devnet is GONE as of 2026-06-22). The Lean-side fix+proof+registry-swap IS the soundness work. Relates to [[project-perf-kernel-supply-epoch]] (supply Stage 2b), [[project-distributed-houyhnhnm-frontier]] (settlement soundness), [[feedback-named-seam-is-not-a-hole]] (classify each residual: this file's tail is TERMINAL-CRYPTO-FLOOR + small REDUCIBLE-OPEN, not uniform debt), [[feedback-dont-launder-vacuity-as-honest]], [[feedback-conservation-is-not-correctness]].
---
name: project-argus-vision
description: "⚑ ARGUS — the circuit-fidelity vision: the circuit witnesses the protocol's CORRECT EVOLUTION, bound so a LIGHT CLIENT CANNOT BE FOOLED. Argus Panoptes, the hundred-eyed guardian; the inverse of 'the pale ghost' (the projection-proof that deceives). The linchpin (non-amp + production-authority in-circuit) LANDED; the apex + five guarantees are #assert_axioms-clean."
metadata:
  node_type: memory
  type: project
  originSessionId: 3b829648-9d41-4dad-bd2e-1a3eb7f618ab
---

⚑ GROUNDED WHAT-IS: `docs/reference/` (committed, file:line at HEAD) is the source-of-truth for the live state — `lean-circuit.md`, `lean-assurance.md`, `lean-authority.md`. When this vision-memory and `docs/reference/` disagree, the doc wins.

⚑ **ARGUS** = the vision for an assured circuit. Argus Panoptes, the hundred-eyed guardian nothing escapes — the inverse of **the pale ghost** (this codebase's recurring villain: a proof that looks sound but witnesses a PROJECTION, so it fools the verifier; cf [[feedback-conservation-is-not-correctness]]). The bar: **no-malleability + no-forgotten-precondition + refines**, all the way down to a WORTHWHILE semantics — never lossy inherited cruft.

**⚑ THE ACCEPTANCE CRITERION (ember, the operational threat model — THE bar):** the circuit must attest the PRECISE state transition with (1) **NO MALLEABILITY** — everything binding; the witness uniquely pins the transition (pre/post/params); tamper ANY guarantee-relevant field ⇒ UNSAT; the anti-ghost tooth is COMPLETE (every field) or an adversary re-presents the proof for a swapped amount/target/post-state. (2) **NO FORGOTTEN PRECONDITIONS** — EVERY protocol precondition (authorization, attenuation granted⊆held, balance availability, nonce/freshness, no-double-spend non-membership, lifecycle-live, fee coverage, …) is an IN-CIRCUIT CONJUNCT — the deadly bug is a precondition the EXECUTOR checks but the CIRCUIT omits (the light client sees ONLY the proof). (3) **REFINES/BISIMULATES** — `satisfiedVm(descriptor) ⟹ protocol-valid-transition` (soundness = client-safety) + completeness. THE THREAT = a malicious network feeding a light client (a) proofs over bad data or (b) proofs that forgot a precondition. The guarantee: a verifying aggregate ⇒ every turn protocol-valid, no precondition skipped, no field unbound ⇒ the network CANNOT lead the client astray.

**⚑ THE LINCHPIN LANDED (#103).** The crown — non-amplification (granted⊆held) AND production-authority forced IN-CIRCUIT against the openable `capability_root` — is closed, `#assert_axioms`-clean (`capReshapeVmDescriptor` + `capReshape_nonAmp_in_circuit`/`capReshape_production_in_circuit` + rejection teeth; the SDK `verify_full_turn_bound` binds the cap-membership leg to the canonical root). See [[project-cap-reshape-plan]] for the scheme + the one deployed-route residual, and [[project-circuit-soundness-apex]] for the apex.

**⚑ THE CORE THESIS (from a TCB census): the same disease at every layer — a true theorem whose load-bearing premise is discharged OUT-OF-BAND (executor in-memory / host-side check / a shape-AIR), never IN the verified algebra.** It is ONE disease, not N findings ("things being out-of-band = failure to internalize the guarantees", [[feedback-stop-auditing-internalize-guarantees]]). ARGUS internalizes each premise into the circuit's own statement. A key unlock: **a `witnessed` guard and a circuit obligation are THE SAME THING** — caveats, cell-programs, the Bucket-B StateConstraints, intent-preds, AND the sub-circuits `compile` emits are all the ONE `Guard.witnessed` mechanism; routing a silently-ignored constraint through a `witnessed` arm makes it a circuit proof obligation. The guard IS the circuit, at the predicate level.

**⚑ THE WHOLE STACK IS ONE TRANSFORMER ALGEBRA (don't be effect-myopic):** effect = forward transformer `{P}e{Q}`; turn = `seq`; jointturn = `par`/separation-⊗ (tensor non-finality = the binding is irreducible, not recoverable per-cell); **intent = COEFFECT** (a four-faced `offered⟶wanted` TYPED HOLE + `fulfill` = the counit annihilating intent+filler→receipt); receipt = committed postcondition Q; witness = proof of the VC; strand = temporal `seq` of receipts. **EVERYTHING IS Q AND ITS PROJECTIONS:** effect produces Q, intent demands Q, receipt commits Q, witness proves Q, `Dregg2.Verify` consumes Q (app verifies `Q⟹invariant`), the privacy dial (`DiscloseAt` Trusted/Selective/Private) = a PROJECTION of Q. The dregg2 formalization's FINAL FORM = ONE coherent verified theory: one IR (the transformer algebra) over ONE unified guard/predicate language (`Pred ≅ Caveat ≅ Spec.Guard`, proved isomorphic in `Exec/PredAlgebra.lean`) on the Iris resource tier (`StepCamera.lean`), composing by seq/par/the counit, with `interp`(executor) AND `compile`(circuit) BOTH DERIVED from the one term so they can't drift — NOT 52 bespoke circuit proofs. The lever: REIFY the executor as an IR term (`RecStmt`) and prove a generic transformer sound ONCE (`effect_circuit_full_sound`, the v2–v5 manual unrollings collapse under it).

**⚑ THE ONE-CIRCUIT INVARIANT (ember, load-bearing):** there is EXACTLY ONE circuit / ONE VK / ONE algebraic statement, and it is LEAN-DERIVED. That singular statement IS the protocol's identity. A second circuit = a different VK = a DIFFERENT PROTOCOL. What dregg LEGITIMATELY has is diversity at the EXECUTION/WITNESS level: multiple executor/witness-gen impls (dregg2 Lean executor primary, dreggrs Rust diversity, the Rust witness generator) all proving witnesses to the ONE shared Lean-derived circuit. `lean_descriptor_air.rs` is NOT "a Rust AIR" — it's the Rust interpreter/prover of the one Lean descriptor (KEPT). The hand-written Rust AIRs (`effect_vm/air.rs`, `effect_vm_p3_full_air.rs`) must DIE via verified-replacement, not because "Rust is the differential" but because they would be a second circuit. The differential-against-Rust was itself a TRAP (ditch+fix to one worthwhile semantics, don't model the gap).

**⚑ THE FIDELITY COLUMN (the light client's unfoolability = the TOP, exactly as tall as the shortest layer) — current status:**
0. **kernel state models the full worthwhile committed payload** — the RECORD-DIGEST limb realizes `RestHashIffFrame` over the full kernel; the deployed commitment absorbs `record_digest` folding all authority residue (the old narrow-commitment hole is CLOSED; the commitment differentials `CommitDifferential`/`RotatedCommitDifferential` are non-vacuous).
1. **circuit binds that faithful state, welded to recKExec** — per-effect rungs are PROVEN individually; the dominant closure label at HEAD is **CLASS A** (the gate forced from the deployed v3-registry descriptor `= Rfix <tag>`, `Dregg2/Circuit/ClosureAll.lean`). The older labels VALUE_FORCED / RECORD-DIGEST-ANCHORED / MAP-OP-FORCED linger only in a few headers — they name the kind of column forced, not a clean partition. The cap-graph family is forced via the cap-reshape crown. (Source-of-truth: `docs/reference/lean-circuit.md`.)
2. **the Rust interpreter realizes `satisfiedVm`** — the denotational Lean↔Rust eval-agreement differential is BUILT (`circuit/tests/ir2_denotational_differential.rs`: two real oracles — an independent Lean `Satisfied2` re-impl vs what `Ir2Air::eval` enforces — decide accept/reject identically over a generated corpus, driven through the real deployed multi-table batch STARK). The irreducible seam below it is extracting p3 `eval` into Lean's kernel (TERMINAL by design). See [[feedback-byte-identity-differential-is-not-faithfulness]] — the byte-identity FP is DRIFT DETECTION, not faithfulness; the denotational differential is the faithfulness check, and it exists now.
3. **the turn binds the forest** — the per-turn fold (`turnDecodeChain_refines_turnSpec`, kernel seam DERIVED not assumed) + the closed mixed-effect apex (`lightclient_unfoolable_circuit_sound_turn`) + cohort-chain forcing (`chainForcesEveryCohort`); the cross-turn no-replay is closed (`BodyNonceNondecreasing` discharged for the live forest body). OPEN (small, named): the intra-turn receipt-LOG seam is carried not forced (the kernel half is forced); the node verifier iterates only the lead cohort leg (the SDK already chain-checks all legs — a wiring lift).
4. **the aggregate folds the REAL AIR, not the shape AIR** — LIVE: `ivc_turn_chain` (real plonky3 in-circuit FRI recursion) folds N finalized turns into one constant-cost proof, consumed by `lightclient::verify_history`, Lean-proven gap-free above the FRI floor (`RecursiveAggregation.light_client_verifies_whole_history`). dregg ALREADY does the Mina-Pickles-shaped succinct whole-chain thing, with a machine-checked composition Mina lacks. The two named recursion-fork follow-ups (child-circuit VK identity + cross-layer public-value propagation) + the unbounded online accumulator are the depth-axis residuals.
5. **the light client inherits the whole truth, unfoolable** — `theorem lightclient_unfoolable` (`CircuitSoundness.lean:453`, pin `:1058`) + the five guarantee apexes (`unfoolability_guarantee` `:666` etc., `AssuranceCase.lean`) + the whole-history headline `RecursiveAggregation.light_client_verifies_whole_history` are `#assert_axioms`-clean; `tampered_aggregate_cannot_bind` is the anti-ghost at the TOP. The macaroon→cap convergence arrow `chainGateG_implies_capAuthorityG` (`CaveatCapBridge.lean:168`) is now PROVEN — the four credential aspects are no longer joined by a bare `&&`.

**⚑ METHOD (ember):** NO seam-ledger / no sorted-bucket artifact — that labelling reflex is the disease. Forward = empowered dual auditor-doers who find-and-fix as ONE act, iterating in-lane on tests; the understanding regenerates FROM the doing. Argus shared-base Lean edits (EffectVmEmit/RecordKernel) are serial (no Lean agent racing); Rust lanes farm in parallel on persvati; verify-before-push. Docs say what IS, never what WAS. ⚑ Classify every named residual (TERMINAL-CRYPTO-FLOOR / REDUCIBLE-OPEN / CLOSED) per [[feedback-named-seam-is-not-a-hole]] — the remaining ARGUS tail is small REDUCIBLE-OPEN + the terminal crypto floor, NOT uniform debt. See [[project-circuit-soundness-apex]], [[project-cap-reshape-plan]], [[project-distributed-houyhnhnm-frontier]] (the settlement-soundness extension).

The current Lean model still uses a separate `bindingProof`/`ChainBound` hypothesis shape. The theorem you want is a refinement of that: replace “binding leaf says the chain is bound” with a tree-local recursive statement where each verified node’s exposed segment is proven equal to the fold of exactly its descendant executions.
exec
/bin/zsh -lc "sed -n '1,180p' circuit-prove/src/ivc_turn_chain.rs" in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
//! GOLD endgame: a continuous whole-chain IVC accumulator over **finalized turns**.
//!
//! ## What this is
//!
//! [`ivc`](dregg_circuit::ivc) accumulates an *attenuation* fold-chain (delegation
//! depth) into one proof. [`joint_turn_recursive`](crate::joint_turn_recursive)
//! folds the N **per-cell** proofs of a *single* shared turn (the hyperedge
//! apex) into one recursive proof. Neither is the whole-chain accumulator.
//!
//! This module is that accumulator: it folds the sequence of *finalized turn*
//! proofs — in the exact order the node's `tau`/blocklace finality produces
//! (`node::blocklace_sync::poll_finalized_blocks` -> `FinalizedBlock`) — into
//! ONE running recursive proof attesting:
//!
//!   "all turns 1..K executed correctly **and** the finalized state root
//!    advanced correctly from the genesis root to the final root, in that
//!    order."
//!
//! It is the sequential dual of the joint-turn (which is cross-cell at one
//! instant). Here the binding is *temporal*: turn N's post-state root must be
//! turn N+1's pre-state root (`prev.NEW_COMMIT == next.OLD_COMMIT`) — the
//! happened-before chain over the *finalized* order, exactly the property the
//! node's tau ordering establishes.
//!
//! ## The two pieces
//!
//! 1. **[`TurnChainBindingAir`]** (one row per folded position): binds the
//!    sequential chain AND the running ordered-history digest. Each row carries
//!    `[old_root, new_root, acc_in, acc_out, idx, is_real, real_count]` plus the
//!    per-row Poseidon2 permutation aux block, with constraints:
//!      - chain continuity: `new_root[i] == old_root[i+1]` (the temporal tooth);
//!      - first row `old_root == genesis_root` (public input);
//!      - last row `new_root == final_root` (public input);
//!      - **running digest `acc_out == hash_4_to_1([acc_in, old_root, new_root,
//!        idx])` ENFORCED in-circuit** (the genuine round-by-round Poseidon2 of
//!        [`poseidon2_permute_expr`], NOT a free witness column), first row
//!        `acc_in == 0`, last row `acc_out == chain_digest` (public);
//!      - `idx` is a positional counter (`0,1,2,…`) so the digest is positionally
//!        bound;
//!      - `num_turns` (public) is pinned to `real_count[last]`, the cumulative
//!        count of the non-padding (`is_real`) rows.
//!
//!    A trace whose turns are reordered, or that drops/inserts a turn, breaks
//!    continuity and is UNSAT; a forged `chain_digest` has no satisfying Poseidon2
//!    witness; a forged `num_turns` mismatches the real-row count — those are the
//!    load-bearing rejections.
//!
//! 2. **The recursion tree (Gold) — REAL leaves.** Each finalized turn's leaf
//!    is the **Lean-descriptor EffectVM AIR itself** ([`EffectVmDescriptorAir`],
//!    the graduated ONE-circuit cutover constraint set: Poseidon2 state-commit
//!    hash sites, per-row gates, transition continuity, `OLD_COMMIT`/`NEW_COMMIT`
//!    PI bindings, balance range checks), re-proven as a recursion-compatible
//!    uni-STARK over the **same 186-column execution trace** the turn's
//!    production rotated IR-v2 batch proof (the retired v1 `EffectVmP3Proof`)
//!    attests, then wrapped in its own **in-circuit verifier layer**
//!    (uni->batch via `build_and_prove_next_layer`). The chain-binding leaf is
//!    wrapped too, and all batch leaves are pairwise aggregated up a binary tree
//!    (`build_and_prove_aggregation_layer`, chained via [`BatchOnly`]) to ONE
//!    root batch-STARK proof. The verifier checks ONLY the root; its cost is
//!    independent of K.
//!
//! ## What the leaf wrap proves (the statement-equality argument)
//!
//! The production turn artifact is a `p3-batch-stark` proof of
//! `EffectVmDescriptorAir(desc)` over `(extend_vm_trace(base_trace), dpis)`,
//! where `dpis` is the descriptor PI prefix (carrying the chain roots at
//! [`pi::OLD_COMMIT`] / [`pi::NEW_COMMIT`]). The recursion fork's in-circuit
//! verifier consumes uni-STARK proofs under the recursion `StarkConfig`, while
//! the production proof is a batch proof under the audited prover config — two
//! FRI engine instantiations of the SAME constraint set. The fold therefore
//! re-proves the IDENTICAL statement — same AIR (`EffectVmDescriptorAir::eval`,
//! config-agnostic), same extended trace ([`descriptor_recursion_matrix`] =
//! the same `extend_vm_trace` surface `prove_vm_descriptor` uses), same PI
//! prefix — as a recursion-compatible uni-STARK, and THAT proof is verified
//! in-circuit by the wrap layer. A claimed `(old_root, new_root)` with no
//! satisfying execution trace has no satisfying leaf under EITHER config (the
//! descriptor's hash sites force `NEW_COMMIT` to be the genuine Poseidon2
//! post-state commitment), so a prover that skips the host-side gate still
//! CANNOT produce a verifying root for a forged turn — that is the tooth
//! `ungated_prover_with_forged_post_commit_cannot_produce_a_root` bites on.
//!
//! ## What the verifier checks (three teeth, in order)
//!
//! [`verify_turn_chain_recursive`] takes the proof AND a caller-held trust
//! anchor (a [`RecursionVk`] — the root circuit's verifier-key fingerprint,
//! obtained once from an honest setup fold, distributed exactly like any
//! SNARK VK) and refuses unless ALL of:
//!
//!   1. **VK pin** — the root proof's verifier-reconstruction inputs (table
//!      shapes, packing, NPO manifest shape, and the preprocessed Merkle
//!      commitment binding the root verifier circuit's op-list) fingerprint
//!      to the anchor. This closes the from-scratch-prover route through
//!      `verify_recursive_batch_proof`'s reconstruct-from-the-proof
//!      discipline: a root proof of a DIFFERENT circuit no longer verifies
//!      "as if" it were the chain fold. (Guarantee, precisely: under blake3
//!      collision resistance + MMCS binding, the accepted root is a valid
//!      batch-STARK of the SAME root verifier-circuit structure the anchor
//!      was extracted from.)
//!   2. **Claimed-publics attestation** — the carried `genesis_root` /
//!      `final_root` / `num_turns` / `chain_digest` must verify as the public
//!      inputs of the carried chain-binding uni-STARK
//!      (`WholeChainProof::binding_proof`, the same statement the fold wraps
//!      in-circuit). Fiat–Shamir binds all four PIs into that proof, so
//!      relabeling any carried field is refused outright.
//!   3. **The root** — `verify_recursive_batch_proof` on the single root.
//!
//! ## CRITICAL HOLES #1/#2/#6 — CLOSED by the ordered SEGMENT ACCUMULATOR (2026-06-24)
//!
//! A cross-model adversarial review (`docs/CODEX-IVC-SOUNDNESS-REVIEW.md` +
//! `CODEX-IVC-REVIEW-2.md`) found a forged whole-chain claim the verifier ACCEPTS: a
//! root that EXECUTED history A paired with a whole-chain CLAIM for a different history
//! B. The root cause was that the chain claim came from a SEPARATE `TurnChainBindingAir`
//! leaf attesting a hash-chain over CLAIMED roots — never tied in-circuit to the
//! descriptor leaves' ACTUAL roots — so the binding leaf (and its claim) could be swapped
//! or built for a different history than the one the descriptor leaves executed.
//!
//! **THE FIX (codex's ordered segment-accumulator).** The separate binding leaf is GONE
//! from the soundness path. Every DESCRIPTOR leaf carries a constant-size ordered SEGMENT
//! `[first_old, last_new, count, acc]`, exposed through the `expose_claim` table and BOUND
//! IN-CIRCUIT:
//!   - **leaf** ([`prove_descriptor_leaf_rotated_with_segment`]): `first_old`/`last_new`
//!     are the descriptor proof's verified rotated roots (PI `V1_PI_COUNT`/`+1`, read off
//!     the child's `air_public_targets`), `count = 1`, `acc = H(first_old, last_new)`. So
//!     the segment is tied to the ACTUAL execution this leaf re-proves — a prover cannot
//!     expose endpoints that differ from the descriptor it folded.
//!   - **aggregation combine** ([`aggregate_tree`]): both children expose a segment; the
//!     combine constrains STATE CONTINUITY (`L.last_new == R.first_old`), COUNT additivity
//!     (`count = L.count + R.count`), and the ORDERED DIGEST fold (`acc = H(L.acc, R.acc)`,
//!     left≠right ⇒ order-sensitive), then re-exposes the parent segment — up to the root.
//!   - **root + host check** ([`verify_turn_chain_recursive_from_parts`], the SEGMENT
//!     tooth): the root's exposed segment `[first_old, last_new, count, acc]` is the
//!     whole-chain claim derived BY CONSTRUCTION from the real descriptor leaves; the host
//!     checks it equals the carried `[genesis_root, final_root, num_turns, chain_digest]`,
//!     fail-closed. There is NO swappable binding leaf — a root that executed A cannot
//!     expose B's endpoints, so a B-claim against an A-execution is REJECTED.
//!
//! The executable witness `mixed_root_forgery_executes_A_claims_B`
//! (`circuit-prove/tests/ivc_turn_chain_rotated.rs`) asserts the forgery is REJECTED
//! (`is_err`) — the close. The out-of-band swap witness
//! `carried_binding_proof_unlinked_to_root_is_rejected` and the #2 digest/num_turns forge
//! teeth (`binding_air_forged_digest_unsat` / `binding_air_forged_num_turns_unsat`) all
//! still reject. The whole fix is dregg-side — it reuses the EXISTING recursion-fork
//! `expose_claim` channel + the aggregation expose hook (which exposes the
//! `air_public_targets` AND lets the combine add cross-child constraints) + the in-circuit
//! poseidon2 challenger perm; NO fork change was needed.
//!
//! ## The honest residual floor (named, not hidden)
//!
//! - **Engine soundness** (`recursive_sound`): the wrap layer's in-circuit FRI
//!   verifier and the root batch-STARK verifier are the plonky3 recursion
//!   fork's; their soundness is the named crypto carrier, as everywhere else.
//! - **Segment digest — a multi-felt Poseidon2 commitment** ([`seg_poseidon_commit`],
//!   codex re-review #3, CLOSED). The ordered-history `acc` is a genuine
//!   [`SEG_DIGEST_WIDTH`]-felt Poseidon2 sponge over the recursion config's
//!   `BABY_BEAR_D4_W16` challenger permutation (the SAME full-round arithmetization the
//!   FRI challenger uses, CTL-bound against the Poseidon2 AIR), matched host-side by
//!   [`seg_poseidon_commit_host`]. This REPLACED the prior one-felt quadratic fold
//!   `a*M1 + b*M2 + a*b*M3`, which was algebraically broken (a given middle root had a
//!   directly-solvable colliding partner, plus degeneracy roots that made it ignore an
//!   operand). The multi-felt commitment has no algebraic shortcut and ~124-bit collision
//!   resistance, so a same-genesis/same-final/same-count history B with a different middle
//!   now mismatches the root digest. The ONLINE [`crate::accumulator`] is scoped OUT (it
//!   keeps the single-felt binding-leaf carrier, zero-padded to the new lane width — codex
//!   #4 mixed-root weakness for that path is unchanged).
//! - **Child-circuit identity under the VK pin (fork follow-up, precise).** The
//!   harness-level VK pin (tooth 1) pins the ROOT layer's circuit structure; the leaf
//!   circuits' op-list identity is pinned in-band only via the fork's
//!   `into_recursion_input_pinned` path (used by the online [`crate::accumulator`]). For
//!   the balanced-tree K-fold the leaf VK identity rests on the root VK pin + the genuine
//!   same-shape aggregation; baking child preprocessed commitments as checked publics is
//!   the remaining fork follow-up.
//!
//! ## K-fold vs unbounded
//!
//! [`prove_turn_chain_recursive`] folds an arbitrary *finite* K into one proof.
//! This is genuine IVC for a bounded window: the verifier checks one
//! constant-cost root proof for the whole window.
//!
//! The fully *unbounded* online accumulator — where a single running proof is
//! re-folded with each newly-finalized turn forever, with the previous running

exec
/bin/zsh -lc "sed -n '220,330p' circuit-prove/src/ivc_turn_chain.rs && sed -n '832,890p' circuit-prove/src/ivc_turn_chain.rs && sed -n '1150,1235p' circuit-prove/src/ivc_turn_chain.rs" in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
/// The recursion config's challenge (extension) field — the field the verifier
/// circuit (and every expose/combine hook) builds over.
type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

/// **The segment digest width** — the multi-felt Poseidon2 commitment carried as the
/// ordered-history `acc`. Codex re-review #3 replaced the algebraically-broken one-felt
/// quadratic fold with this genuine collision-resistant commitment. Four BabyBear lanes
/// ⇒ ~124-bit collision resistance (the host's tooth-4 check compares all four), and the
/// commitment is a real full-round Poseidon2 permutation — there is no algebraic
/// shortcut and no degeneracy root (the quadratic fold's weakness).
pub const SEG_DIGEST_WIDTH: usize = 4;

/// The number of exposed chain claims: `[first_old, last_new, count, acc_0..acc_{W-1}]`
/// where `W = SEG_DIGEST_WIDTH`. The host verifier's tooth-4 reads these directly,
/// comparing against `[genesis_root, final_root, num_turns, chain_digest_0..]`.
pub const NUM_CHAIN_CLAIMS: usize = SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH;

/// Segment field lanes (the order they are exposed in the `expose_claim` table).
pub const SEG_FIRST_OLD: usize = 0;
pub const SEG_LAST_NEW: usize = 1;
pub const SEG_COUNT: usize = 2;
/// First lane of the multi-felt digest block (`acc_0`); the digest occupies
/// `[SEG_DIGEST_FIRST .. SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]`.
pub const SEG_DIGEST_FIRST: usize = 3;
/// A segment is exactly [`NUM_CHAIN_CLAIMS`] base-field lanes.
pub const SEG_WIDTH: usize = NUM_CHAIN_CLAIMS;

fn to_p3(v: BabyBear) -> P3BabyBear {
    P3BabyBear::from_u64(v.0 as u64)
}

/// The Poseidon2 challenger perm config the segment-digest sponge runs over —
/// `BABY_BEAR_D4_W16`, the SAME permutation the recursion FRI challenger uses (enabled by
/// `prepare_circuit_for_verification`). Reusing it means the sponge is a genuine, already
/// CTL-soundly-arithmetized Poseidon2, not a new gadget.
fn seg_poseidon_config() -> p3_circuit::ops::Poseidon2Config {
    // The ISOLATED segment-digest permutation: `BABY_BEAR_D4_W24` is a DISTINCT op-type
    // (`poseidon2_perm/baby_bear_d4_w24`) from the FRI challenger's `BABY_BEAR_D4_W16`.
    // Sharing nothing — chain-state, CTL bus, op-type — means the digest sponge's perm I/O
    // can never be transitively aliased into the verifier's shared `ExprId::ZERO` witness
    // class (the cross-op connect-DSU collapse that produced the `WitnessId(0)` conflict when
    // the digest reused the challenger's W16 perm). Enabled in
    // `DreggRecursionConfig::prepare_circuit_for_verification`.
    p3_circuit::ops::Poseidon2Config::BABY_BEAR_D4_W24
}

/// Sponge rate (in ext limbs) for the segment digest: `rate_ext` of `BABY_BEAR_D4_W24`
/// = 4. Each absorb adds up to 4 base-field-embedded inputs into the rate limbs; each
/// squeeze reads the 4 CTL-verified rate-output limbs.
const SEG_SPONGE_RATE: usize = 4;

/// Width (in ext limbs) of the sponge state for `BABY_BEAR_D4_W24` = `width_ext` = 6
/// (rate 4 + capacity 2).
const SEG_SPONGE_WIDTH: usize = 6;

/// A base-field domain-separation tag absorbed first, so the digest is a *keyed* sponge
/// (the empty-input / all-zero state cannot be reached by a real chain). Arbitrary fixed
/// nonzero BabyBear; not security-load-bearing on its own, only domain separation.
const SEG_DOMAIN_TAG: u32 = 0x5345_4731 % 0x7800_0001; // "SEG1" mod BabyBear

/// **The in-circuit ordered-segment digest** — a genuine multi-felt Poseidon2
/// commitment (codex re-review #3, replacing the algebraically-broken quadratic fold).
///
/// Runs a duplex sponge over the recursion config's challenger permutation
/// (`BABY_BEAR_D4_W16`, the SAME full-round Poseidon2 the FRI challenger uses, CTL-bound
/// against the Poseidon2 AIR), absorbing `inputs` (each a base-field-embedded ext scalar)
/// two-at-a-time into the rate limbs, then squeezing [`SEG_DIGEST_WIDTH`] base-field
/// lanes from the rate-output limbs. The returned targets are the digest lanes, exposed
/// through the `expose_claim` table (which reads each target's coeff-0) and matched
/// host-side EXACTLY by [`seg_poseidon_commit_host`].
///
/// Because the squeeze outputs are genuine Poseidon2 permutation coordinates, the digest
/// is collision-resistant: there is NO algebraic shortcut (the quadratic fold's `a*b`
/// solvable-collision) and no degeneracy root (the `a=-M2/M3` / `b=-M1/M3` cases that
/// made the old fold ignore an operand). A same-genesis/same-final/same-count history B
/// with a different middle now yields a different digest with ~124-bit security.
///
/// Used (i) at the descriptor leaf to seed `acc = commit([first_old, last_new])`, and
/// (ii) at each aggregation node to fold `parent.acc = commit(L.acc ++ R.acc)` — an
/// order-sensitive tree commitment (left≠right because L.acc is absorbed before R.acc).
///
/// `pub` so the executable witness test (`ivc_turn_chain_rotated.rs`) can mirror the lib's
/// EXACT segment combine when it reconstructs the fold from the public building blocks.
pub fn seg_poseidon_commit(
    cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
    inputs: &[p3_recursion::Target],
) -> [p3_recursion::Target; SEG_DIGEST_WIDTH] {
    let config = seg_poseidon_config();
    // IV/pad constant: a NONZERO domain tag. We deliberately AVOID feeding the shared zero
    // constant (`ExprId::ZERO` == `WitnessId(0)`) into the permutation — in the assembled
    // recursion verifier circuit a perm input/output that touches the shared zero-witness
    // trips a `WitnessConflict { WitnessId(0) }` (the all-zero double-creator class). Seeding
    // every state/pad lane with a nonzero IV keeps the sponge off WitnessId(0) entirely.
    let tag = cb.define_const(RecursionChallenge::from(P3BabyBear::from_u64(
        SEG_DOMAIN_TAG as u64,
    )));

    // Capacity IV seed (the `SEG_SPONGE_WIDTH - SEG_SPONGE_RATE` capacity limbs) for the
    // FIRST permutation; on it the capacity is CTL-bound to this `Const`, keeping the bus
    // balanced. On EVERY SUBSEQUENT permutation the capacity is chained OFF the bus (the
    // perm AIR inherits the previous row's capacity output) — see
    // `add_poseidon2_perm_sponge_step`. This is what makes the digest sponge's
    // `WitnessChecks` global cumulative balance: feeding the full previous state (capacity
    // included) as fresh CTL inputs each perm left every chained perm's capacity RECEIVE
    // unmatched (a perm only sends its rate outputs), so the aggregation child's lookup bus
    // did not balance to zero.
    let cap_seed: Vec<p3_recursion::Target> = vec![tag; SEG_SPONGE_WIDTH - SEG_SPONGE_RATE];

    // The rate lanes carried across permutations (seeded with the nonzero IV). The capacity
    // is held internally by the perm chain, not in this array.
    let mut rate: Vec<p3_recursion::Target> = vec![tag; SEG_SPONGE_RATE];
/// folds these the SAME way the in-circuit combine does so it knows the root segment
/// (hence the chain claims) to carry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct HostSeg {
    pub first_old: BabyBear,
    pub last_new: BabyBear,
    pub count: BabyBear,
    /// The multi-felt Poseidon2 ordered-history digest (codex #3).
    pub acc: [BabyBear; SEG_DIGEST_WIDTH],
}

/// The per-turn (descriptor-leaf) segment: `first_old = old_root`, `last_new =
/// new_root`, `count = 1`, `acc = commit([old_root, new_root])` — the SAME seed
/// [`seg_poseidon_commit`] computes at the leaf wrap.
fn leaf_seg(old_root: BabyBear, new_root: BabyBear) -> HostSeg {
    HostSeg {
        first_old: old_root,
        last_new: new_root,
        count: BabyBear::ONE,
        acc: seg_poseidon_commit_host(&[old_root, new_root]),
    }
}

/// Combine two adjacent segments (the host mirror of the aggregation combine):
/// continuity `l.last_new == r.first_old` (caller-checked upstream as `ChainBreak`),
/// `first_old = l.first_old`, `last_new = r.last_new`, `count = l.count + r.count`,
/// `acc = commit(l.acc ++ r.acc)` (order-sensitive: l before r).
fn combine_seg(l: HostSeg, r: HostSeg) -> HostSeg {
    let mut acc_inputs = Vec::with_capacity(2 * SEG_DIGEST_WIDTH);
    acc_inputs.extend_from_slice(&l.acc);
    acc_inputs.extend_from_slice(&r.acc);
    HostSeg {
        first_old: l.first_old,
        last_new: r.last_new,
        count: l.count + r.count,
        acc: seg_poseidon_commit_host(&acc_inputs),
    }
}

/// Fold the per-turn leaf segments into the ROOT segment using the SAME pairwise
/// left-to-right binary tree (with odd-element carry) that [`aggregate_tree`] runs
/// in-circuit — so the host-computed root `[first_old, last_new, count, acc]`
/// equals what the root proof exposes.
fn compute_root_segment(turns: &[&FinalizedTurn]) -> HostSeg {
    let mut level: Vec<HostSeg> = turns
        .iter()
        .map(|t| {
            let (o, n) = rotated_roots(t);
            leaf_seg(o, n)
        })
        .collect();
    while level.len() > 1 {
        let mut next: Vec<HostSeg> = Vec::with_capacity(level.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < level.len() {
            next.push(combine_seg(level[i], level[i + 1]));
            i += 2;
        }
        if i < level.len() {
/// **THE SEGMENT-ACCUMULATOR DESCRIPTOR LEAF (the soundness-critical replacement for the
/// separate binding leaf).** Wrap one rotated finalized-turn descriptor batch in-circuit
/// AND emit its constant-size ordered SEGMENT through the `expose_claim` table, BOUND
/// in-circuit to the descriptor proof's REAL published chain roots:
///
///   `Seg = [first_old, last_new, count, acc]`
///     first_old := descriptor PI `V1_PI_COUNT`   (the rotated OLD-state commitment)
///     last_new  := descriptor PI `V1_PI_COUNT+1` (the rotated NEW-state commitment)
///     count     := 1
///     acc       := H(first_old, last_new)        (the per-turn ordered-history seed)
///
/// Because `first_old`/`last_new` are READ from the descriptor proof's own verified
/// `air_public_targets` (not free prover scalars), the segment is tied to the ACTUAL
/// execution this leaf re-proves. A prover cannot expose a segment whose endpoints differ
/// from the descriptor it folded. This is what closes the mixed-root hole: there is no
/// separate, swappable binding leaf — the whole-chain endpoints/digest are derived from the
/// real descriptor leaves and combined up the tree.
pub fn prove_descriptor_leaf_rotated_with_segment(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggRecursionConfig>,
    descriptor_pis: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    use dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT;

    let (airs, table_public_inputs, common) =
        dregg_circuit::descriptor_ir2::ir2_airs_and_common_for_config(
            desc,
            proof,
            descriptor_pis,
            config,
        )?;

    let input: RecursionInput<'_, DreggRecursionConfig, dregg_circuit::descriptor_ir2::Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof,
            common_data: &common,
            table_public_inputs,
        };

    let backend = create_recursion_backend();

    // The expose hook: the main instance (instance 0) carries the descriptor PIs, so its
    // `air_public_targets[V1_PI_COUNT] / [V1_PI_COUNT+1]` are the verified rotated OLD/NEW
    // commitments. Build the segment over them and expose it.
    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<p3_recursion::Target>]| {
        let main = apt
            .first()
            .expect("descriptor leaf has a main instance with descriptor PIs");
        debug_assert!(
            main.len() > V1_PI_COUNT + 1,
            "descriptor PI vector must carry the rotated OLD/NEW commitments"
        );
        let first_old = main[V1_PI_COUNT];
        let last_new = main[V1_PI_COUNT + 1];
        let count = cb.define_const(RecursionChallenge::ONE);
        // The per-turn seed: a genuine multi-felt Poseidon2 commitment over the leaf's
        // REAL (descriptor-bound) endpoints (codex #3).
        let acc = seg_poseidon_commit(cb, &[first_old, last_new]);
        let mut seg = Vec::with_capacity(SEG_WIDTH);
        seg.push(first_old);
        seg.push(last_new);
        seg.push(count);
        seg.extend_from_slice(&acc);
        debug_assert_eq!(seg.len(), SEG_WIDTH);
        cb.expose_as_public_output(&seg);
    };

    build_and_prove_next_layer_with_expose::<
        DreggRecursionConfig,
        dregg_circuit::descriptor_ir2::Ir2Air,
        _,
        D,
    >(
        &input,
        config,
        &backend,
        &ProveNextLayerParams::default(),
        Some(&expose),
    )
    .map_err(|e| format!("rotated native-batch segment leaf-wrap failed: {e:?}"))
}

// ============================================================================

exec
/bin/zsh -lc 'rg -n "acc_attests_whole_history|AggregateAttests|tampered_aggregate|leaf_pairing|EngineSound|ChainBound|Acc|Segment|Seg|whole_history" metatheory/Dregg2 metatheory/Metatheory -S' in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
metatheory/Dregg2/Paco/GPaco.lean:185:## Accumulation
metatheory/Metatheory/Open/CrossCellBisim.lean:39:     EXECUTABLE kernel** (`xcell_whole_history_confluent`). Lifting `applyHalfOut_comm_disjoint` from a
metatheory/Metatheory/Open/CrossCellBisim.lean:195:/-- **KEYSTONE — `xcell_whole_history_confluent` — the adversary-stream confluence over
metatheory/Metatheory/Open/CrossCellBisim.lean:203:theorem xcell_whole_history_confluent
metatheory/Metatheory/Open/CrossCellBisim.lean:259:with `xcell_whole_history_confluent` it says the disjoint-commuted history is observationally
metatheory/Metatheory/Open/CrossCellBisim.lean:317:`xcell_whole_history_confluent`'s `hdis` cannot be dropped — off the disjoint fragment the
metatheory/Metatheory/Open/CrossCellBisim.lean:332:#assert_axioms xcell_whole_history_confluent
metatheory/Metatheory/Open/CrossCellBisim.lean:345:  * `xcell_whole_history_confluent` — THE adversary-stream confluence over `inducedSystem`
metatheory/Metatheory/Open/CrossCellBisim.lean:362:--       multiset of pairwise-disjoint debits reach `xeq` ledgers. `xcell_whole_history_confluent`
metatheory/Dregg2/Authority/Predicate.lean:201:`CryptoKernel.verify` oracle, an accepted proof discharges the kind's predicate. Acceptance
metatheory/Dregg2/Authority/Predicate.lean:244:-- Accept: the honest witness `7` discharges the `dfa` predicate at statement `7`.
metatheory/Dregg2/Authority/Predicate.lean:246:-- Accept: `10` discharges the `pedersen` predicate at statement `5` (10 = 2*5).
metatheory/Dregg2/Paco/Basic.lean:302:### Accumulation
metatheory/Dregg2/Paco/Basic.lean:492:### Additional Accumulation Lemmas
metatheory/Dregg2/Paco/Basic.lean:495:/-- Accumulate paco into upaco parameter.
metatheory/Dregg2/Paco/Basic.lean:528:### Coinduction with Accumulation
metatheory/Dregg2/Paco/Compat.lean:28:## Mult Lemmas (Accumulation)
metatheory/Metatheory/EpistemicDial.lean:203:/-- **Acceptance is preserved exactly as one descends.** If it
metatheory/Metatheory/EpistemicDial.lean:331:def PreservesAcceptance {M : Type v} {I P W : Type u} [Preorder I] [Verifiable P W]
metatheory/Metatheory/EpistemicDial.lean:337:theorem preservesAcceptance_of_embed {M : Type v} {I P W : Type u}
metatheory/Metatheory/EpistemicDial.lean:339:    PreservesAcceptance f S :=
metatheory/Metatheory/EpistemicDial.lean:358:    PreservesAcceptance svenvsToDial S ∧
metatheory/Metatheory/EpistemicDial.lean:359:    PreservesAcceptance dregg2ToDial S :=
metatheory/Metatheory/EpistemicDial.lean:361:   preservesAcceptance_of_embed svenvsToDial S,
metatheory/Metatheory/EpistemicDial.lean:362:   preservesAcceptance_of_embed dregg2ToDial S⟩
metatheory/Metatheory/EpistemicDial.lean:446:    PreservesAcceptance svenvsToDial S ∧
metatheory/Metatheory/EpistemicDial.lean:447:    PreservesAcceptance visToDial S :=
metatheory/Metatheory/EpistemicDial.lean:449:   preservesAcceptance_of_embed svenvsToDial S,
metatheory/Metatheory/EpistemicDial.lean:450:   preservesAcceptance_of_embed visToDial S⟩
metatheory/Dregg2/Paco/Tactic.lean:375:## Accumulation Tactics
metatheory/Dregg2/Paco/LICENSE:165:   9. Accepting Warranty or Additional Liability. While redistributing
metatheory/Metatheory/EnergyGame.lean:257:/-- Accumulate `n` cuts from grade `0` via the energy step's `bump`. -/
metatheory/Dregg2/Time/Frame.lean:32:taken as a hypothesis at every point a *physical-time* conclusion is drawn. Acceptance itself (a bit
metatheory/Dregg2/Time/Frame.lean:170:Acceptance is a bit the in-TCB verifier emits; it says nothing physical by itself. To conclude
metatheory/Metatheory/ConstructiveKnowledge.lean:156:Acceptance-inside ⊑ Out-of-band` — the four predicate-kinds, ordered by *how much the
metatheory/Metatheory/ConstructiveKnowledge.lean:160:predicate's verifier learns only **`Acceptance`** — that the statement is true — and
metatheory/Metatheory/ConstructiveKnowledge.lean:195:  /-- Acceptance discloses strictly less than content: `acceptance ⊑ content`. -/
metatheory/Dregg2/Verify/LoadBearingAuditBroad.lean:187:#load_bearing_audit_report Dregg2.Circuit.Spec.AccountGrowth.createCellAdmit
metatheory/Dregg2/Verify/LoadBearingAuditBroad.lean:188:  nonvacuous := Dregg2.Circuit.Spec.AccountGrowth.createCellA_rejects_unauthorized
metatheory/Dregg2/Verify/LoadBearingAuditBroad.lean:189:#load_bearing_audit_report Dregg2.Circuit.Spec.AccountGrowth.CreateCellSpec
metatheory/Dregg2/Verify/LoadBearingAuditBroad.lean:190:  nonvacuous := Dregg2.Circuit.Spec.AccountGrowth.createCellA_rejects_unauthorized
metatheory/Dregg2/Verify/LoadBearingAuditBroad.lean:191:#load_bearing_audit_report Dregg2.Circuit.Spec.AccountGrowth.spawnAdmit
metatheory/Dregg2/Verify/LoadBearingAuditBroad.lean:192:  nonvacuous := Dregg2.Circuit.Spec.AccountGrowth.spawnA_rejects_unauthorized_child
metatheory/Dregg2/Verify/LoadBearingAuditBroad.lean:193:#load_bearing_audit_report Dregg2.Circuit.Spec.AccountGrowth.SpawnFullSpec
metatheory/Dregg2/Verify/LoadBearingAuditBroad.lean:194:  nonvacuous := Dregg2.Circuit.Spec.AccountGrowth.spawnA_rejects_unauthorized_child
metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean:2:# Dregg2.Crypto.DfaAcceptanceAir — the REAL `dregg-dfa-routing-v1` STARK AIR, modeled.
metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean:61:namespace Dregg2.Crypto.DfaAcceptanceAir
metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean:147:def Accumulates : List (Row State Sym Digest) → Prop
metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean:151:      b.running = CryptoPrimitives.compress a.running b.entryHash ∧ Accumulates (b :: rest)
metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean:174:  accum : Accumulates rows
metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean:315:      Accumulates rows →
metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean:353:    (haccum : Accumulates rows)
metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean:745:    -- Accumulates [witRow0, witRow1] : witRow1.running = compress witRow0.running witRow1.entryHash
metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean:803:end Dregg2.Crypto.DfaAcceptanceAir
metatheory/Dregg2/Authority/Intent.lean:54:/-- **`Intent.Accepts i w`** — the *decidable* acceptance check the owning cell runs on a
metatheory/Dregg2/Authority/Intent.lean:58:def Intent.Accepts [Verifiable P W] (i : Intent P W) (w : W) : Prop :=
metatheory/Dregg2/Authority/Intent.lean:63:`Verify`/`Accepts` is tractable; the matcher `find` below carries NO analogous instance,
metatheory/Dregg2/Authority/Intent.lean:65:instance [Verifiable P W] (i : Intent P W) (w : W) : Decidable (Intent.Accepts i w) := by
metatheory/Dregg2/Authority/Intent.lean:66:  unfold Intent.Accepts; infer_instance
metatheory/Dregg2/Authority/Intent.lean:119:content. `Intent.Accepts` is *defined* as `Discharged i.want w` (see §1), so this `Iff` is
metatheory/Dregg2/Authority/Intent.lean:120:`Iff.rfl`: it records, for callers, that `Accepts` is a transparent alias adding nothing
metatheory/Dregg2/Authority/Intent.lean:125:    i.Accepts w ↔ Discharged i.want w := Iff.rfl
metatheory/Dregg2/Authority/Intent.lean:147:VERIFY is decidable: the `Decidable (Intent.Accepts i w)` instance in §1 witnesses this.
metatheory/Dregg2/Authority/Intent.lean:213:(`i.Accepts w`, the decidable local VERIFY) is exactly a witness that admits the *outgoing*
metatheory/Dregg2/Authority/Intent.lean:217:    (owner : Label) (ko ko' : KO) (w : W) (hacc : i.Accepts w) :
metatheory/Dregg2/Authority/Intent.lean:294:#guard (@Intent.Accepts DivBy3 Fill demoVerifiable demoIntent 7 : Bool) == false
metatheory/Dregg2/Authority/Intent.lean:295:#guard (@Intent.Accepts DivBy3 Fill demoVerifiable demoIntent 6 : Bool)
metatheory/Dregg2/Crypto/UCBridge.lean:30:proof in ANOTHER system. Accepting it WIDENS the trust base of dregg2 to include, beyond Lean's
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:198:`conserves` (the ledger total `100` is preserved) and `light_client` (a concrete `EngineSound` over the
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:199:accepting verifier ⇒ `AggregateAttests` ∧ `Run`). Teeth = `tampered_argus_strand_rejected` (a reordered
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:205:open Dregg2.Distributed.HistoryAggregation (ChainStep ChainBound lastStateOf foldedFinalRoot
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:207:open Dregg2.Circuit.RecursiveAggregation (Aggregate EngineSound AggregateAttests
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:208:  light_client_verifies_whole_history)
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:250:    (es : EngineSound RealProof acceptAll zCH zRH zcmb zcompress zcompressN realAggregate teethGenesis [s, s'])
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:283:/-- The accepting `EngineSound` over the honest Argus strand. Each step's `commits` field IS the
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:287:    EngineSound RealProof acceptAll zCH zRH zcmb zcompress zcompressN
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:297:    · rw [hx]; simp [ChainBound]
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:305:argusAggregate.root` over the stepped honest Argus strand obtains `AggregateAttests` (every Argus turn
metatheory/Dregg2/Verify/KeystoneAuditRunnable.lean:310:      ∧ AggregateAttests RealProof zCH zRH zcmb zcompress zcompressN argusAggregate teethGenesis steps
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:120:        leaderSegment B' P wl c l = leaderSegment B P wl c l)
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:126:      (∀ l ∈ L, ∀ c : List BlockId, leaderSegment B' P wl c l = leaderSegment B P wl c l) →
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:147:    (tauStep B P wl acc l).1 = acc.1 ++ leaderSegment B P wl acc.2 l := rfl
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:159:    exact ⟨leaderSegment B P wl acc.2 l ++ r, by
metatheory/Dregg2/Crypto/Ed25519Reduction.lean:117:`AcceptingHandoff` is the minimal interface `CapTPHandoffSound.validateHandoff2` exposes (its §1 leg
metatheory/Dregg2/Crypto/Ed25519Reduction.lean:123:/-- **`AcceptingHandoff K pk m s`** — a handoff certificate whose §1 leg accepted: the ed25519 oracle
metatheory/Dregg2/Crypto/Ed25519Reduction.lean:126:def AcceptingHandoff {PK Msg Sig : Type u} (K : SignatureKernel PK Msg Sig)
metatheory/Dregg2/Crypto/Ed25519Reduction.lean:135:    (haccept : AcceptingHandoff K pk m s) (hnokey : ¬ K.Signed pk m) :
metatheory/Dregg2/Crypto/Ed25519Reduction.lean:144:    (hnokey : ¬ K.Signed pk m) : ¬ AcceptingHandoff K pk m s :=
metatheory/Dregg2/Crypto/Ed25519Reduction.lean:157:/-- **`AcceptedBlock K creatorPK m s`** — a block the honest insert accepted: the creator's ed25519
metatheory/Dregg2/Crypto/Ed25519Reduction.lean:160:def AcceptedBlock {PK Msg Sig : Type u} (K : SignatureKernel PK Msg Sig)
metatheory/Dregg2/Crypto/Ed25519Reduction.lean:171:    (haccept : AcceptedBlock K creatorPK m s) (hnokey : ¬ K.Signed creatorPK m) :
metatheory/Dregg2/Crypto/Ed25519Reduction.lean:180:    (hnokey : ¬ K.Signed creatorPK m) : ¬ AcceptedBlock K creatorPK m s :=
metatheory/Dregg2/Crypto/Ed25519Reduction.lean:192:/-- **`AcceptedAuth K holderPK m s`** — a turn the gate authorized via the ed25519
metatheory/Dregg2/Crypto/Ed25519Reduction.lean:195:def AcceptedAuth {PK Msg Sig : Type u} (K : SignatureKernel PK Msg Sig)
metatheory/Dregg2/Crypto/Ed25519Reduction.lean:204:    (haccept : AcceptedAuth K holderPK m s) (hnokey : ¬ K.Signed holderPK m) :
metatheory/Dregg2/Crypto/Ed25519Reduction.lean:212:    (hnokey : ¬ K.Signed holderPK m) : ¬ AcceptedAuth K holderPK m s :=
metatheory/Dregg2/Crypto/Ed25519Reduction.lean:270:    ¬ AcceptingHandoff instSignatureKernel pk m s :=
metatheory/Dregg2/Consensus/OnDemandFeasibility.lean:100:linearization `tauSeg` and the fast path's causal application order `fastSeg` are
metatheory/Dregg2/Consensus/OnDemandFeasibility.lean:104:theorem tau_agrees_with_fastpath (step : S → T → S) {tauSeg fastSeg : List T}
metatheory/Dregg2/Consensus/OnDemandFeasibility.lean:105:    (hperm : tauSeg.Perm fastSeg) (hcomm : PairwiseCommuting step tauSeg) (s : S) :
metatheory/Dregg2/Consensus/OnDemandFeasibility.lean:106:    tauSeg.foldl step s = fastSeg.foldl step s :=
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:9:    leaf_pairing_defeats_swap}`);
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:10:  • the HISTORY-AGGREGATION tooth (`Distributed.HistoryAggregation.{wellformed_attests_whole_history,
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:23:      bind (`tampered_aggregate_cannot_bind`, concludes `False`), a broken seam is REJECTED
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:24:      (`tooth_rejects_broken_order`, concludes `¬ ChainBound`), and a FOOLING attack breaks the
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:36:  • `LightClientUC.SimAccepts` and the `Reference.refUnfoolable`/`refFoolingBreaksFloor` are themselves
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:55:    teeth := Dregg2.Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind]
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:56:def light_client_verifies_whole_history_KS :=
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:57:  @Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:69:    teeth := Dregg2.Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind]
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:73:-- (4) REAL-ENGINE-SOUND (the EngineSound carrier is inhabited).
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:76:    teeth := Dregg2.Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind]
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:83:    teeth := Dregg2.Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind]
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:84:def leaf_pairing_defeats_swap_KS :=
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:85:  @Dregg2.Circuit.RecursiveAggregation.leaf_pairing_defeats_swap
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:93:def wellformed_attests_whole_history_KS :=
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:94:  @Dregg2.Distributed.HistoryAggregation.wellformed_attests_whole_history
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:142:#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.light_client_verifies_whole_history_KS
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:146:#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.leaf_pairing_defeats_swap_KS
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:147:#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.wellformed_attests_whole_history_KS
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:157:#assert_axioms light_client_verifies_whole_history_KS
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:161:#assert_axioms leaf_pairing_defeats_swap_KS
metatheory/Dregg2/Verify/KeystoneAuditUnfoolability.lean:162:#assert_axioms wellformed_attests_whole_history_KS
metatheory/Dregg2/Authority/TemporalAlgebra2.lean:469:admission. (Acceptance alone concludes nothing physical — exactly as in `Deadline.lean §6` the
metatheory/Dregg2/Crypto/LightClientUC.lean:283:/-- **`SimAccepts` — the simulator's accept decision in the IDEAL world.** Given the floor extractor
metatheory/Dregg2/Crypto/LightClientUC.lean:287:theorem SimAccepts
metatheory/Dregg2/Crypto/LightClientUC.lean:304:  · rintro ⟨π, hacc⟩; exact SimAccepts verify Sat Produced hExt hBind s π hacc
metatheory/Dregg2/Crypto/LightClientUC.lean:389:#assert_axioms SimAccepts
metatheory/Dregg2/Spec/VatBoundary.lean:396:  /-- **Accepting witness exists** (for `preserves_id`): the far side's `Verify` is not the
metatheory/Dregg2/Authority/Positional.lean:5:theorem** (`integrity_obj_atomic`, `proof/access-control/Access.thy`), specialized to
metatheory/Dregg2/Authority/Positional.lean:24:-- l4v reference statements (Access.thy / Syscall_AC.thy), transcribed verbatim in
metatheory/Dregg2/Authority/Positional.lean:91:(`Access.thy:118`):
metatheory/Dregg2/Authority/Positional.lean:126:(`Access.thy:312`) requires, among wellformedness clauses,
metatheory/Dregg2/Lightclient/AttestedQuery.lean:29:    composes it with `RecursiveAggregation.light_client_verifies_whole_history`: a light client
metatheory/Dregg2/Lightclient/AttestedQuery.lean:34:the named `Poseidon2SpongeCR` hypothesis + `RecursiveAggregation.EngineSound`'s named fields (both
metatheory/Dregg2/Lightclient/AttestedQuery.lean:378:`RecursiveAggregation.light_client_verifies_whole_history`: ONE `verify agg.root` check pins every
metatheory/Dregg2/Lightclient/AttestedQuery.lean:413:  * the recursion engine is sound (`EngineSound` — the three named, realizable hypotheses of
metatheory/Dregg2/Lightclient/AttestedQuery.lean:420:and ANY verifying range answer: the whole chain is attested (`AggregateAttests` — every turn
metatheory/Dregg2/Lightclient/AttestedQuery.lean:431:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/Lightclient/AttestedQuery.lean:445:    AggregateAttests Proof CH RH cmb compress compressN agg g steps
metatheory/Dregg2/Lightclient/AttestedQuery.lean:450:  exact ⟨light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
metatheory/Dregg2/Lightclient/MMR.lean:32:    `RecursiveAggregation.light_client_verifies_whole_history` identically. The obligation list
metatheory/Dregg2/Lightclient/MMR.lean:38:the named `Poseidon2SpongeCR` hypothesis (the one floor) + `EngineSound`'s named fields at the
metatheory/Dregg2/Lightclient/MMR.lean:539:  * a sound recursion engine (`EngineSound`) and `verify agg.root = true` (the ONE client check),
metatheory/Dregg2/Lightclient/MMR.lean:544:verifying positional range answer: the whole chain is attested (`AggregateAttests`), the answer is
metatheory/Dregg2/Lightclient/MMR.lean:556:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/Lightclient/MMR.lean:569:    AggregateAttests Proof CH RH cmb compress compressN agg g steps
metatheory/Dregg2/Lightclient/MMR.lean:575:  exact ⟨light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
metatheory/Dregg2/Crypto/Deriv/TableDfa.lean:9:  1. `tableRun_dfaAccepts` — a table run IS a `Dfa.lean` `DfaAccepts` run over the deterministic δ
metatheory/Dregg2/Crypto/Deriv/TableDfa.lean:11:     table FUNCTION (closing the `DfaAcceptanceAir` GAP-A "δ is a deterministic table function"), for
metatheory/Dregg2/Crypto/Deriv/TableDfa.lean:35:open Dregg2.Crypto.Dfa (Step DfaAccepts stepValid chained)
metatheory/Dregg2/Crypto/Deriv/TableDfa.lean:72:closing the `DfaAcceptanceAir` GAP-A. -/
metatheory/Dregg2/Crypto/Deriv/TableDfa.lean:106:/-- **`tableRun_dfaAccepts`** — a table run on a NON-EMPTY word IS a `Dfa.lean` `DfaAccepts` run over
metatheory/Dregg2/Crypto/Deriv/TableDfa.lean:107:the deterministic δ. So the deployed AIR (which certifies `DfaAccepts`) is certifying exactly this
metatheory/Dregg2/Crypto/Deriv/TableDfa.lean:110:theorem tableRun_dfaAccepts (td : TableDfa State Sym) (a : Sym) (as : List Sym) :
metatheory/Dregg2/Crypto/Deriv/TableDfa.lean:111:    DfaAccepts td.δ td.start td.accept (runTrace td td.start (a :: as)) ↔ td.accepts (a :: as) := by
metatheory/Dregg2/Crypto/Deriv/TableDfa.lean:219:  Dregg2.Crypto.Deriv.PredRE.TableDfa.tableRun_dfaAccepts,
metatheory/Dregg2/Firmament/SeL4Abstract.lean:17:      - `cap_rights_to_auth`                — `proof/access-control/Access.thy:107-113`
metatheory/Dregg2/Firmament/SeL4Abstract.lean:18:      - `reply_cap_rights_to_auth`          — `proof/access-control/Access.thy:115-116`
metatheory/Dregg2/Firmament/SeL4Abstract.lean:19:      - `cap_auth_conferred`                — `proof/access-control/Access.thy:118-131`
metatheory/Dregg2/Firmament/SeL4Abstract.lean:166:-- l4v@e2f32e54 proof/access-control/Access.thy:107-113
metatheory/Dregg2/Firmament/SeL4Abstract.lean:190:-- l4v@e2f32e54 proof/access-control/Access.thy:115-116
metatheory/Dregg2/Firmament/SeL4Abstract.lean:199:ported; `Access.thy:131` delegates to the arch-specific `arch_cap_auth_conferred`). Kept an opaque
metatheory/Dregg2/Firmament/SeL4Abstract.lean:205:-- l4v@e2f32e54 proof/access-control/Access.thy:118-131
metatheory/Dregg2/Paco/UpTo/Guarded.lean:134:3. **Accept weaker theorems**: For many applications, `cpn ext (F R) ≤ cpn ext R`
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:103:  RestHashIffFrame AccountsWF)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:519:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:532:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:553:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:566:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:587:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:600:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:861:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:874:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:887:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:900:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:916:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:929:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:945:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:958:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:968:`intentAccountInsert` and pin the accounts-growth (the capability-creation move — a cell brought to
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:975:/-- **`intentAccountInsert accounts cell`** — the INTENT account set after a cell creation: the live
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:978:def intentAccountInsert (accounts : Finset CellId) (cell : CellId) : Finset CellId :=
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:984:open Dregg2.Circuit.Spec.AccountGrowth (CreateCellSpec SpawnFullSpec)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:987:the post-`accounts` to be EXACTLY `intentAccountInsert … newCell` (the new cell brought to life). -/
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:993:    (hRest : Dregg2.Circuit.Inst.CreateCellA.RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:997:    s'.kernel.accounts = intentAccountInsert s.kernel.accounts args.newCell := by
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:1008:    (hRest : Dregg2.Circuit.Inst.CreateCellA.RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:1010:    (hwrong : s'.kernel.accounts ≠ intentAccountInsert s.kernel.accounts args.newCell) :
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:1020:post-`accounts` to be EXACTLY `intentAccountInsert … child` (the spawned child brought to life). -/
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:1032:    s'.kernel.accounts = intentAccountInsert s.kernel.accounts args.child := by
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:1047:    (hwrong : s'.kernel.accounts ≠ intentAccountInsert s.kernel.accounts args.child) :
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:1096:`createFromFactoryE` witness forces the post-`accounts` to be EXACTLY `intentAccountInsert … newCell`
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:1112:    s'.kernel.accounts = intentAccountInsert s.kernel.accounts args.newCell := by
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:1130:    (hwrong : s'.kernel.accounts ≠ intentAccountInsert s.kernel.accounts args.newCell) :
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:1174:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Spec/CircuitSpecTriangle.lean:1195:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Paco/UpTo/GPacoClo.lean:59:- `r`: Accumulator (immediately available facts)
metatheory/Dregg2/Paco/UpTo/GPacoClo.lean:281:## Accumulation in GPaco_clo
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:22:`start = εclosure {nfaStart}`, `accept S = (nfaAccept ∈ S)`, with the flat table laid out as
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:298:def tAccept : (R : PredRE) → TState R
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:302:  | .cat _ r  => Sum.inr (tAccept r)
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:319:            ∪ {t | x = tAccept l ∧ o = none ∧ t = Sum.inl true}
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:322:            ∪ {t | y = tAccept r ∧ o = none ∧ t = Sum.inl true}
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:326:            ∪ {t | x = tAccept l ∧ o = none ∧ t = Sum.inr (tStart r)}
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:333:            ∪ {t | y = tAccept r ∧ o = none ∧ (t = Sum.inr (tStart r) ∨ t = Sum.inl true)}
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:341:  accept := {tAccept R}
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:343:/-- The accept state is a SINK in every sub-machine: no sub-transitions leave `tAccept R`. The crux
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:345:theorem tStep_accept_empty : ∀ (R : PredRE) (o : Option Value), tStep R (tAccept R) o = ∅
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:346:  | .ε, o => by ext t; simp [tStep, tAccept]
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:347:  | .sym _, o => by ext t; simp [tStep, tAccept]
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:350:      show ((fun u => Sum.inr u) '' (tStep r (tAccept r) o)) = ∅
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:358:/-- `thompson R` accepts `w` iff there is a path from `tStart R` to `tAccept R` labelled `w`. -/
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:361:      ∃ x', x'.reduceOption = w ∧ (thompson R).IsPath (tStart R) (tAccept R) x' := by
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:366:    rw [show (thompson R).accept = ({tAccept R} : Set _) from rfl, mem_singleton_iff] at hs₂
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:369:    exact ⟨tStart R, tAccept R, x', rfl, rfl, hr, hp⟩
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:471:        (y = tAccept l ∧ o = none ∧ t ∈ ({Sum.inl true} : Set (TState (.alt l r)))) := by
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:478:        (y = tAccept r ∧ o = none ∧ t ∈ ({Sum.inl true} : Set (TState (.alt l r)))) := by
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:492:        · rcases region_escape (fun u => Sum.inr (Sum.inl u)) (tAccept l)
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:503:        · rcases region_escape (fun u => Sum.inr (Sum.inr u)) (tAccept r)
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:522:        refine ⟨Sum.inr (Sum.inl (tAccept l)),
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:533:        refine ⟨Sum.inr (Sum.inr (tAccept r)),
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:547:        (y = tAccept l ∧ o = none ∧ t ∈ ({Sum.inr (tStart r)} : Set (TState (.cat l r)))) := by
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:557:    rcases region_escape (fun u => Sum.inl u) (tAccept l)
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:559:        (Sum.inr (tAccept r)) hp with
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:563:      obtain ⟨b, hb, hNr⟩ := isPath_from_inr hinr p₂ (tStart r) (Sum.inr (tAccept r)) hM2
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:578:      refine ⟨Sum.inl (tAccept l),
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:580:      refine εNFA.IsPath.cons _ _ _ _ _ (show Sum.inr (tStart r) ∈ M.step (Sum.inl (tAccept l)) none
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:625:      (thompson (.star r)).IsPath (Sum.inr (tStart r)) (Sum.inr (tAccept r)) q
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:638:        refine ⟨Sum.inr (tAccept r),
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:641:          (show Sum.inr (tStart r) ∈ (thompson (.star r)).step (Sum.inr (tAccept r)) none
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:653:        (y = tAccept r ∧ o = none ∧
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:659:  rcases region_escape (fun u => Sum.inr u) (tAccept r)
metatheory/Dregg2/Crypto/Deriv/Thompson.lean:715:        refine ⟨Sum.inr (tAccept r), hqpath, ?_⟩
metatheory/Dregg2/Protocol/Transfer.lean:23:structure Acct where
metatheory/Dregg2/Protocol/Transfer.lean:37:def applyLocal (a : Acct) : LocalOp → Acct
metatheory/Dregg2/Protocol/Transfer.lean:43:public balance; the transition applies a `LocalOp`, landing in another live `Acct` (never
metatheory/Dregg2/Protocol/Transfer.lean:46:  Carrier := Acct
metatheory/Dregg2/Protocol/Transfer.lean:52:def transfer (sender receiver : Acct) (amt : Amount) : Option (Acct × Acct) :=
metatheory/Dregg2/Protocol/Transfer.lean:60:def willSucceed (sender : Acct) (amt : Amount) : Bool := decide (amt ≤ sender.bal)
metatheory/Dregg2/Protocol/Transfer.lean:65:def alice : Acct := ⟨100⟩
metatheory/Dregg2/Protocol/Transfer.lean:67:def bob : Acct := ⟨5⟩
metatheory/Dregg2/Protocol/Transfer.lean:80:theorem transfer_conserves (sender receiver : Acct) (amt : Amount) {s' r' : Acct}
metatheory/Dregg2/Protocol/Transfer.lean:98:theorem transfer_cg5 (sender receiver : Acct) (amt : Amount) {s' r' : Acct}
metatheory/Dregg2/Protocol/Transfer.lean:115:theorem transfer_atomic (sender receiver : Acct) (amt : Amount) :
metatheory/Dregg2/Protocol/Transfer.lean:123:theorem transfer_fail_no_credit (sender receiver : Acct) (amt : Amount)
metatheory/Dregg2/Protocol/Transfer.lean:138:  Config := Acct × Acct
metatheory/Dregg2/Protocol/Transfer.lean:143:def total (s : Acct × Acct) : Nat := s.1.bal + s.2.bal
metatheory/Dregg2/Protocol/Transfer.lean:147:theorem channel_step_conserves {s t : Acct × Acct} (h : channel.Step s t) :
metatheory/Dregg2/Protocol/Transfer.lean:159:theorem channel_run_conserves {s t : Acct × Acct} (hrun : Run channel s t) :
metatheory/Dregg2/Protocol/Transfer.lean:167:def runBatch : Acct × Acct → List (Bool × Amount) → Option (Acct × Acct)
metatheory/Dregg2/Exec/Handlers/StateSupply.lean:193:/-- Account-growth (createCell/spawn) arguments: the privileged `actor` and the FRESH `newCell` id. -/
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:2:# Dregg2.Crypto.Deriv.Determinize — Stage 4: the derivative automaton AS a `DfaAccepts` run.
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:7:Edge C — the in-circuit `Dfa.lean` — consumes a TABLE-OPAQUE automaton: `DfaAccepts δ q₀ accept trace`
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:10:the deployed AIR it suffices to exhibit the DERIVATIVE AUTOMATON in exactly that `DfaAccepts` shape
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:16:    `accept := nullAccept` (`null s = true`);
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:18:  * **`derivativeDfa_correct`**: for a non-empty word, the `Dfa.lean`-shaped run `DfaAccepts derStep R
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:19:    nullAccept (runTrace R w)` holds IFF `derives w R = true` — the SAME `DfaAccepts` predicate the
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:24:(we IMPORT its `DfaAccepts`/`Step`/`dfa_bridge`, we do not edit them).
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:40:open Dregg2.Crypto.Dfa (Step DfaAccepts stepValid chained)
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:51:/-- **`nullAccept`** — the accepting predicate of the derivative automaton: a state accepts iff its
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:53:def nullAccept (s : PredRE) : Prop := null s = true
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:94:            (nullAccept last.next ↔ derives (a :: as) R = true) := by
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:99:    simp only [nullAccept, derives]
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:106:/-! ## `derivativeDfa_correct` — the run is accepted by the `DfaAccepts` predicate iff `derives`. -/
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:109:valid accepting run (the EXACT `Dfa.lean` `DfaAccepts` predicate the deployed AIR certifies, `Dfa.lean:
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:112:because `DfaAccepts` requires a non-empty trace (≥1 transition); the empty-word case is the pure
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:115:    DfaAccepts derStep R nullAccept (runTrace R (a :: as)) ↔ derives (a :: as) R = true := by
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:118:    -- The accept condition `nullAccept last.next` is exactly `derives`, via runTrace_getLast_next.
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:136:    DfaAccepts derStep R nullAccept (runTrace R (a :: as)) ↔ Matches (a :: as) R := by
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:149:-- …and REJECTS `[fr7, fr9]` (so the DfaAccepts run does too, by derivativeDfa_correct).
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:152:-- The run is a GENUINE accepting run for an accepted word (non-vacuous DfaAccepts witness):
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:153:example : DfaAccepts derStep (.sym p7) nullAccept (runTrace (.sym p7) [fr7]) :=
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:157:example : ¬ DfaAccepts derStep (.sym p7) nullAccept (runTrace (.sym p7) [fr9]) := by
metatheory/Dregg2/Crypto/Deriv/Determinize.lean:175:needs: the derivative automaton, presented in the EXACT `Dfa.lean` `DfaAccepts` shape, accepts
metatheory/Dregg2/Apps/ToolAccessDelegation.lean:2:# Dregg2.Apps.ToolAccessDelegation — VERIFIABLE TOOL / MCP-ACCESS DELEGATION (claude usecase #1).
metatheory/Dregg2/Apps/ToolAccessDelegation.lean:77:namespace Dregg2.Apps.ToolAccessDelegation
metatheory/Dregg2/Apps/ToolAccessDelegation.lean:482:end Dregg2.Apps.ToolAccessDelegation
metatheory/Dregg2/Apps/DEVNET-COMPOSITION.md:148:   - *Acceptance:* `docker compose up -d` reaches healthy `node-0` + `gallery`.
metatheory/Dregg2/Apps/DEVNET-COMPOSITION.md:152:   - *Acceptance:* `cargo build --release -p dregg-gallery -p dregg-bounty-board -p compute-exchange -p dregg-privacy-voting` from repo root.
metatheory/Dregg2/Apps/DEVNET-COMPOSITION.md:157:   - *Acceptance:* cluster test starts both without bind error.
metatheory/Dregg2/Apps/DEVNET-COMPOSITION.md:164:   - *Acceptance:* `curl localhost:8400/starbridge-apps/nameservice/manifest.json` returns 200 in compose.
metatheory/Dregg2/Apps/DEVNET-COMPOSITION.md:169:   - *Acceptance:* `teasting` cross-app test can create CWM/SGM cells from factory.
metatheory/Dregg2/Apps/DEVNET-COMPOSITION.md:174:   - *Acceptance:* Starbridge picker shows 6 apps; each loads without 404.
metatheory/Dregg2/Apps/DEVNET-COMPOSITION.md:178:   - *Acceptance:* full browser demo works at `:8400/starbridge.html` without host-side `npm run build`.
metatheory/Dregg2/Apps/DEVNET-COMPOSITION.md:199:    - *Acceptance:* script exits 0 with 3 nodes + 4 apps healthy.
metatheory/Dregg2/Apps/DEVNET-COMPOSITION.md:206:    - *Acceptance:* post-genesis `/api/cells` includes nameservice + identity cells.
metatheory/Dregg2/Apps/DEVNET-COMPOSITION.md:211:    - *Acceptance:* Studio starbridge catalog shows correct badge; no `page: null` without explanation.
metatheory/Dregg2/Apps/DEVNET-COMPOSITION.md:216:    - *Acceptance:* `apps.json` is an accurate deploy manifest for everything that has Rust code.
metatheory/Dregg2/Apps/DEVNET-COMPOSITION.md:223:    - *Acceptance:* `scripts/devnet-smoke.sh` passes against public URL with starbridge assets.
metatheory/Dregg2/Apps/DEVNET-COMPOSITION.md:227:    - *Acceptance:* matches AWS Caddy routing for local parity.
metatheory/Dregg2/Crypto/Dfa.lean:8:    dfa_bridge       : Satisfies dfaCircuit (q₀, accept, trace) ↔ DfaAccepts δ q₀ accept trace
metatheory/Dregg2/Crypto/Dfa.lean:9:    dfa_verify_sound : verify accepts → DfaAccepts …  (derived off the bridge + `extractable`)
metatheory/Dregg2/Crypto/Dfa.lean:62:/-- **`DfaAccepts δ q₀ accept trace`** — the DFA acceptance STATEMENT: the run is NON-EMPTY, every step
metatheory/Dregg2/Crypto/Dfa.lean:66:def DfaAccepts (δ : State → Sym → State → Prop) (q₀ : State) (accept : State → Prop)
metatheory/Dregg2/Crypto/Dfa.lean:95:is the conjunction `dfa_lookup_descriptor` enforces — IDENTICAL in shape to `DfaAccepts` (the IR and
metatheory/Dregg2/Crypto/Dfa.lean:108:/-! ## The bridge — `Satisfies ↔ DfaAccepts`, FULLY proven (NO primitive seam).
metatheory/Dregg2/Crypto/Dfa.lean:116:validity, the chaining, and the boundary conditions are exactly `DfaAccepts`. Fully proved, no
metatheory/Dregg2/Crypto/Dfa.lean:120:    DfaAccepts δ q₀ accept circuit.trace := h
metatheory/Dregg2/Crypto/Dfa.lean:125:    (trace : List (Step State Sym)) (h : DfaAccepts δ q₀ accept trace) :
metatheory/Dregg2/Crypto/Dfa.lean:130:Soundness: per-step `Lookup` validity + chaining + boundaries are `DfaAccepts` (`dfa_sound`).
metatheory/Dregg2/Crypto/Dfa.lean:138:        Satisfies δ q₀ accept circuit → DfaAccepts δ q₀ accept trace)
metatheory/Dregg2/Crypto/Dfa.lean:141:    (DfaAccepts δ q₀ accept trace → ∃ circuit : CircuitIR State Sym, Satisfies δ q₀ accept circuit) :=
metatheory/Dregg2/Crypto/Dfa.lean:189:exists: `verify stmt proof = true  →  ∃ trace, DfaAccepts stmt.δ stmt.q₀ stmt.accept trace`.
metatheory/Dregg2/Crypto/Dfa.lean:194:    ∃ trace : List (Step State Sym), DfaAccepts stmt.δ stmt.q₀ stmt.accept trace := by
metatheory/Dregg2/Crypto/Dfa.lean:282:      ∃ trace : List (Step S Y), DfaAccepts stmt.δ stmt.q₀ stmt.accept trace) := by
metatheory/Dregg2/Crypto/Dfa.lean:297:      ∧ ∃ trace : List (Step S Y), DfaAccepts stmt.δ stmt.q₀ stmt.accept trace := by
metatheory/Dregg2/Crypto/Dfa.lean:347:/-- Non-vacuity of the SOUNDNESS heart: the `"aab"` run is a genuine accepting run (`DfaAccepts`). The
metatheory/Dregg2/Crypto/Dfa.lean:349:theorem aab_accepts : DfaAccepts δ q₀ accept aabTrace := by
metatheory/Dregg2/Crypto/Dfa.lean:369:run), certifies `DfaAccepts`. This exercises the deliverable on a real automaton (the `a⁺b` DFA of
metatheory/Dregg2/Crypto/Dfa.lean:371:example : DfaAccepts δ q₀ accept aabTrace :=
metatheory/Dregg2/Crypto/Dfa.lean:379:acceptance against an arbitrary statement (no `Decidable (DfaAccepts stmt.δ …)` for opaque `Prop`
metatheory/Dregg2/Apps/Compositor.lean:40:## How the rich scene folds into the scalar `AppSpec.admit` boundary (the `ToolAccessDelegation` move)
metatheory/Dregg2/Apps/Compositor.lean:46:`admit : Int → Int → Bool` at scene-snapshot time, EXACTLY as `ToolAccessDelegation.delegAdmit` closes
metatheory/Dregg2/Apps/Compositor.lean:191:folded into the scalar boundary BEFORE it reaches the executor (the `ToolAccessDelegation.delegAdmit`
metatheory/Dregg2/Apps/Compositor.lean:227:`ToolAccessDelegation.mandateSpec` closes `(g, now, tool)`. -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:14:`HistoryAggregation.WellFormedChain` (`aggregate_attests_whole_history`) — so trusting the aggregate
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:30:    tooth `new_root[i] == old_root[i+1]` over the whole chain (`HistoryAggregation.ChainBound`). The
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:102:soundness). They are bundled in `EngineSound` as a hypothesis the headline takes — NOT an axiom. The
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:112:/-- **`EngineSound agg g steps`** — the three named recursion-soundness hypotheses, interpreted
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:115:structure EngineSound (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep) : Prop where
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:131:  tooth over the whole chain (`ChainBound`), AND pins the public genesis/final roots to the chain's
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:134:    ChainBound CH RH cmb compress compressN steps
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:169:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:175:/-- **`AggregateAttests agg g steps`** — the full attestation the light client obtains: every turn
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:179:structure AggregateAttests (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep) : Prop where
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:183:  ordered : ChainBound CH RH cmb compress compressN steps
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:192:/-- **`light_client_verifies_whole_history` (THE MAGNESIUM→GOLD HEADLINE).**
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:195:`AggregateAttests`: every turn executed correctly, the chain is correctly ordered (no reorder/drop/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:200:theorem light_client_verifies_whole_history
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:202:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:204:    AggregateAttests Proof CH RH cmb compress compressN agg g steps := by
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:215:`AggregateAttests` gives the per-step executor transitions + the ordering; composed with state-level
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:258:root tooth (under the standard Poseidon CR set + the preserved `AccountsWF` invariant), and
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:260:follows from `verify agg.root` itself (which delivers the `ChainBound` tooth via `AggregateAttests`),
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:267:`StateChained` hypothesis. The verified root gives `AggregateAttests` (hence the `ChainBound` root
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:269:(matched turns + the preserved `AccountsWF` invariant, both non-cryptographic, neither a
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:281:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:286:  -- the verified root delivers the ordering tooth (ChainBound) — no re-witnessing.
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:287:  have hatt := light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:297:The headline would be hollow if `EngineSound` were unsatisfiable, or if `verify agg.root = true`
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:300:whose root/leaf/binding all verify, and an `EngineSound` proof — so the headline fires on a real
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:301:chain and concludes a real `AggregateAttests`. We ALSO witness the negative: a `verify` that REJECTS
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:302:gives a vacuously-true `EngineSound` (no obligation), and the headline is not invoked — the tooth is
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:338:SATISFIABLE on a real chain: `EngineSound` holds for the accepting verifier, the realizing aggregate,
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:341:the binding soundness yields the singleton `ChainBound` + the genuine root pins. So `EngineSound` is
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:344:    EngineSound RealProof acceptAll zCH zRH zcmb zcompress zcompressN
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:358:    · -- ChainBound on a singleton is `True`.
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:359:      simp [realSteps, ChainBound]
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:366:instance, the light-client headline concludes `AggregateAttests`: verifying the (accepting)
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:367:root attests the honest 1-step history. So `light_client_verifies_whole_history` is non-vacuous — it
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:370:    AggregateAttests RealProof zCH zRH zcmb zcompress zcompressN
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:372:  light_client_verifies_whole_history RealProof acceptAll zCH zRH zcmb zcompress zcompressN
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:390:`ChainBound` is FALSE, so any `EngineSound` whose `binding_sound` fires on such a chain is
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:404:/-- **`tampered_aggregate_cannot_bind` (THE ANTI-GHOST TOOTH).** No sound aggregate can
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:407:whose binding leaf verifies, `binding_sound` would force `ChainBound [s, s']`, which is FALSE for a
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:410:theorem tampered_aggregate_cannot_bind
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:412:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g [s, s'])
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:420:/-- **`leaf_pairing_defeats_swap` (the leg-swap tooth).** A verifying leaf proof attests the
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:426:theorem leaf_pairing_defeats_swap
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:430:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g (s :: ss))
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:456:  `acc_attests_whole_history` — folding `accumulate` from the genesis accumulator over a state-extending
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:462:IVC fixed point) is the SAME named, realizable `EngineSound` boundary §2 already carries; nothing new is
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:467:at its HEAD; for the *root-level* temporal tooth (`ChainBound`) to extend, the new step's `oldRoot` must
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:474:section Accumulator
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:486:which is exactly what the running recursion proof is sound for (`EngineSound`). -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:487:structure Acc (g : RecChainedState) where
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:493:/-- **`Acc.head g acc`** — the state the running accumulator has reached: `lastStateOf` of the folded
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:495:def Acc.head {g : RecChainedState} (acc : Acc CH RH cmb compress compressN g) : RecChainedState :=
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:498:/-- **`genesisAcc g`** — `acc_0`: the empty fold from genesis. Attests the empty (trivially well-formed)
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:500:def genesisAcc (g : RecChainedState) : Acc CH RH cmb compress compressN g where
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:504:/-- `genesisAcc`'s head is genesis (the empty fold has reached nowhere). -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:505:@[simp] theorem genesisAcc_head (g : RecChainedState) :
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:506:    Acc.head CH RH cmb compress compressN (genesisAcc CH RH cmb compress compressN g) = g := rfl
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:524:`accumulate` appends `s` at the END (`steps ++ [s]`). The chain predicates (`StateChained`, `ChainBound`,
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:553:/-- A tail-extended chain stays `ChainBound`, IF the old chain is bound AND the new step continues the
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:558:      ChainBound CH RH cmb compress compressN steps →
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:560:      ChainBound CH RH cmb compress compressN (steps ++ [s])
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:561:  | [], s, _, _ => by simp [ChainBound]
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:563:    -- old chain `[a]`: the new pair is `[a, s]`; the bound is `Continues a s ∧ ChainBound [s]`.
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:588:def accumulate {g : RecChainedState} (acc : Acc CH RH cmb compress compressN g) (s : ChainStep)
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:589:    (hseam : s.pre = Acc.head CH RH cmb compress compressN acc)
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:591:    Acc CH RH cmb compress compressN g where
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:603:            simpa [Acc.head] using (lastStateOf_eq_getLast_post g acc.steps last hlast).symm
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:612:    (acc : Acc CH RH cmb compress compressN g) (s : ChainStep)
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:613:    (hseam : s.pre = Acc.head CH RH cmb compress compressN acc)
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:619:/-- **`acc_attests_whole_history` (THE IVC HEADLINE — by induction from genesis).** The running
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:621:genesis over `acc.steps`, for ANY accumulator reachable from `genesisAcc` by `accumulate` steps. We
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:622:state it as: every `Acc` (which can only be built by `genesisAcc` + `accumulate`, both of which
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:624:`light_client_verifies_whole_history` (§3) — whose `EngineSound` is sound for exactly this
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:628:theorem acc_attests_whole_history {g : RecChainedState}
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:629:    (acc : Acc CH RH cmb compress compressN g) :
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:638:    (acc : Acc CH RH cmb compress compressN g) :
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:639:    Run recChainedSystem g (Acc.head CH RH cmb compress compressN acc) :=
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:647:    (acc : Acc CH RH cmb compress compressN g) :
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:648:    recTotal (Acc.head CH RH cmb compress compressN acc).kernel = recTotal g.kernel :=
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:653:The induction would be hollow if no real `accumulate` step could fire. We build `genesisAcc` over the
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:665:/-- The realizing accumulator: `genesisAcc` over the teeth genesis, then one `accumulate` of the honest
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:666:step. The seam holds because `genesisAcc`'s head IS genesis and the honest step consumes genesis; the
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:668:def ivcRealAcc : Acc zCH zRH zcmb zcompress zcompressN teethGenesis :=
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:669:  accumulate zCH zRH zcmb zcompress zcompressN (genesisAcc zCH zRH zcmb zcompress zcompressN teethGenesis)
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:672:    (by intro last hlast; simp [genesisAcc] at hlast)
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:677:    WellFormedChain zCH zRH zcmb zcompress zcompressN teethGenesis ivcRealAcc.steps :=
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:678:  acc_attests_whole_history zCH zRH zcmb zcompress zcompressN ivcRealAcc
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:684:    recTotal (Acc.head zCH zRH zcmb zcompress zcompressN ivcRealAcc).kernel
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:686:  acc_conserves zCH zRH zcmb zcompress zcompressN ivcRealAcc
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:690:end Accumulator
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:695:#assert_axioms Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:702:#assert_axioms Dregg2.Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:703:#assert_axioms Dregg2.Circuit.RecursiveAggregation.leaf_pairing_defeats_swap
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:711:#assert_axioms Dregg2.Circuit.RecursiveAggregation.acc_attests_whole_history
metatheory/Dregg2/AssuranceCase.lean:39:     recursion obligation `RecursiveAggregation.EngineSound.recursive_sound`.
metatheory/Dregg2/AssuranceCase.lean:79:import Dregg2.Circuit.RecursiveAggregation   -- unfoolability: light_client_verifies_whole_history
metatheory/Dregg2/AssuranceCase.lean:615:  • `Circuit.RecursiveAggregation.light_client_verifies_whole_history` — THE headline:
metatheory/Dregg2/AssuranceCase.lean:620:  • `Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind` — the ANTI-GHOST: a
metatheory/Dregg2/AssuranceCase.lean:621:    reordered chain forces `ChainBound = False`, so no verifying aggregate exists.
metatheory/Dregg2/AssuranceCase.lean:622:  • `Circuit.RecursiveAggregation.leaf_pairing_defeats_swap` — positional pairing means a
metatheory/Dregg2/AssuranceCase.lean:629:    + the preserved `AccountsWF` invariant. This is what `root_tooth_pins_state` (commitment-equality
metatheory/Dregg2/AssuranceCase.lean:632:    conservation across the whole history follows from `verify agg.root` ALONE (the verified `ChainBound`
metatheory/Dregg2/AssuranceCase.lean:640:Floor: FRI / STARK soundness (`EngineSound.recursive_sound`, the ONE recursion obligation),
metatheory/Dregg2/AssuranceCase.lean:657:that checks ONLY `verify agg.root = true` (re-witnessing NOTHING) learns BOTH (1) `AggregateAttests`
metatheory/Dregg2/AssuranceCase.lean:663:`verify agg.root`-only client. This conjoins `light_client_verifies_whole_history` with
metatheory/Dregg2/AssuranceCase.lean:665:anti-ghost teeth (`tampered_aggregate_cannot_bind`) are pinned below. -/
metatheory/Dregg2/AssuranceCase.lean:668:    (es : EngineSound AProof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/AssuranceCase.lean:674:    AggregateAttests AProof CH RH cmb compress compressN agg g steps
metatheory/Dregg2/AssuranceCase.lean:676:  ⟨light_client_verifies_whole_history AProof verify CH RH cmb compress compressN agg g steps es hroot,
metatheory/Dregg2/AssuranceCase.lean:684:#assert_axioms Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history
metatheory/Dregg2/AssuranceCase.lean:686:#assert_axioms Dregg2.Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind
metatheory/Dregg2/AssuranceCase.lean:687:#assert_axioms Dregg2.Circuit.RecursiveAggregation.leaf_pairing_defeats_swap
metatheory/Dregg2/AssuranceCase.lean:689:#assert_axioms Dregg2.Distributed.HistoryAggregation.wellformed_attests_whole_history
metatheory/Dregg2/AssuranceCase.lean:707:#assert_axioms Dregg2.Crypto.LightClientUC.SimAccepts
metatheory/Dregg2/AssuranceCase.lean:817:  * unfoolability (E) is `light_client_verifies_whole_history` + `conserves_from_verification` over a
metatheory/Dregg2/AssuranceCase.lean:876:    executed correctly + is correctly ordered + ends at the genuine fold (`AggregateAttests`), AND
metatheory/Dregg2/AssuranceCase.lean:903:    (es : EngineSound AProof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/AssuranceCase.lean:921:    ∧ AggregateAttests AProof CH RH cmb compress compressN agg g steps
metatheory/Dregg2/AssuranceCase.lean:936:    exact light_client_verifies_whole_history AProof verify CH RH cmb compress compressN
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:58:/-- **`commit_inj_nonce` — the commitment is INJECTIVE in the agent nonce.** Two `AccountsWF` kernels
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:63:    (agent : CellId) (hwf : AccountsWF k) (hwf' : AccountsWF k')
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:69:/-- **`commit_neq_of_nonce_neq` — the contrapositive (the replay teeth).** If two `AccountsWF`
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:73:    (agent : CellId) (hwf : AccountsWF k) (hwf' : AccountsWF k')
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:82:`AccountsWF`, whose agent nonce is STRICTLY INCREASING (the deployed monotone nonce — each turn's
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:87:/-- A turn-chain: indexed live kernels, all `AccountsWF`, with a strictly-monotone agent nonce. -/
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:92:  wf       : ∀ i, AccountsWF (seq i)
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:430:/-! ### Account-set MONOTONICITY (a helper threaded through the `exerciseA` sub-fold).
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:1232:EXACTLY `TurnChain.monotone`. So — provided each reachable state is `AccountsWF` (already
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:1233:`recKExec_preserves_AccountsWF`, threaded as the `wf` field) — the accepted sequence IS a `TurnChain`,
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:1237:indexed kernels `seq i`, each `AccountsWF`, and a per-step witness that `seq (i+1)` is an ACCEPTED
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:1244:    (wf : ∀ i, AccountsWF (seq i).kernel)
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:1252:sequence (strictly nonce-advancing, all `AccountsWF`), a fixed pre-anchor opens the CAS gate at most
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:1257:    (wf : ∀ i, AccountsWF (seq i).kernel)
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:1291:UNCONDITIONAL).** Given indexed states `seq i` (all `AccountsWF`) each produced by an ACCEPTED
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:1300:    (wf : ∀ i, AccountsWF (seq i).kernel)
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:1323:`i`. `AccountsWF` and strict monotonicity hold by construction, so `TurnChain` is INHABITED. -/
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:1325:    (base : RecordKernelState) (hwf : AccountsWF base) (hin : agent ∈ base.accounts) :
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:1346:    (base : RecordKernelState) (hwf : AccountsWF base) (hin : agent ∈ base.accounts) (i : Nat) :
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:1357:    (base : RecordKernelState) (hwf : AccountsWF base) (hin : agent ∈ base.accounts)
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:1415:       `AccountsWF` — already `recKExec_preserves_AccountsWF` — and bumps the nonce) is mechanical
metatheory/Dregg2/Circuit/CrossTurnFreshness.lean:1428:-proved lemmas (`commitPrologue_nonce`, `recKExec_preserves_AccountsWF`, `admissible_links_to_head`).
metatheory/Dregg2/Circuit/RotatedKernelRefinementNotesFresh.lean:150:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementNotesFresh.lean:192:  frAccounts := henc.frAccounts
metatheory/Dregg2/Coord/SharedBudgetDynamics.lean:203:  /-- Accepted: sufficient balance remained at its tau position. -/
metatheory/Dregg2/Circuit/WitnessExtractComposite.lean:49:  RestHashIffFrame AccountsWF)
metatheory/Dregg2/Circuit/WitnessExtractComposite.lean:80:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/WitnessExtractComposite.lean:96:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/WitnessExtractComposite.lean:147:    (hwf : AccountsWF pre.kernel)
metatheory/Dregg2/Circuit/WitnessExtractV1.lean:20:The `AccountsWF` side-conditions on pre/post are the well-formed-accounts hypotheses the executor already
metatheory/Dregg2/Circuit/WitnessExtractV1.lean:35:  RestHashIffFrame AccountsWF)
metatheory/Dregg2/Circuit/WitnessExtractV1.lean:131:Poseidon2 CR (`compressNInjective`/`cellLeafInjective`). The `AccountsWF` pre/post conditions are the
metatheory/Dregg2/Circuit/WitnessExtractV1.lean:138:    (hwf : AccountsWF (E.view.toKernel pre)) (hwf' : AccountsWF (E.view.toKernel post))
metatheory/Dregg2/Circuit/FloorsNonVacuousWaveTransfer.lean:189:  guardAccepts := by decide
metatheory/Dregg2/Circuit/FloorsNonVacuousWaveTransfer.lean:190:  frAccounts := rfl
metatheory/Dregg2/Circuit/CircuitCompletenessLifecycle.lean:74:open Dregg2.Circuit.StateCommit (AccountsWF compressNInjective)
metatheory/Dregg2/Circuit/CircuitCompletenessLifecycle.lean:130:  frAccounts          := hspec.2.2.2.1
metatheory/Dregg2/Circuit/CircuitCompletenessLifecycle.lean:173:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessLifecycle.lean:222:  frAccounts          := hspec.2.2.2.1
metatheory/Dregg2/Circuit/CircuitCompletenessLifecycle.lean:264:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessLifecycle.lean:323:  frAccounts          := hspec.2.2.2.2.1
metatheory/Dregg2/Circuit/CircuitCompletenessLifecycle.lean:380:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessLifecycle.lean:425:    (frAccounts : post.kernel.accounts = pre.kernel.accounts)
metatheory/Dregg2/Circuit/CircuitCompletenessLifecycle.lean:447:  frAccounts := frAccounts
metatheory/Dregg2/Circuit/CircuitCompletenessLifecycle.lean:505:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessLifecycle.lean:568:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/EffectInstances2.lean:176:  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/EffectInstances2.lean:178:    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/EffectInstances2.lean:180:  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/EffectInstances2.lean:182:    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/EffectInstances2.lean:361:  · rintro ⟨hg, hnull, hlog, hAcc, hCell, hCaps, hBal, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/EffectInstances2.lean:364:    exact ⟨hg, hnull, hlog, hAcc, hCell, hCaps, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/EffectInstances2.lean:366:  · rintro ⟨hg, hnull, hlog, hAcc, hCell, hCaps, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/EffectInstances2.lean:368:    exact ⟨hg, hnull, hlog, hAcc, hCell, hCaps, hBal, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Apps/Trustline.lean:89:(`BudgetSlice::debits`); `holderAcct`/`issuerWell` are the bilateral signed-well pair in the
metatheory/Dregg2/Apps/Trustline.lean:103:  holderAcct : Int
metatheory/Dregg2/Apps/Trustline.lean:123:    ∧ t.holderAcct = (t.drawn : Int)
metatheory/Dregg2/Apps/Trustline.lean:137:  { ceiling := n, drawn := 0, draws := [], holderAcct := 0, issuerWell := 0 }
metatheory/Dregg2/Apps/Trustline.lean:148:                , holderAcct := t.holderAcct + (amt : Int)
metatheory/Dregg2/Apps/Trustline.lean:159:                , holderAcct := t.holderAcct - (amt : Int)
metatheory/Dregg2/Apps/Trustline.lean:169:                    , holderAcct := t.holderAcct + (amt : Int)
metatheory/Dregg2/Apps/Trustline.lean:186:                    , holderAcct := t.holderAcct - (amt : Int)
metatheory/Dregg2/Apps/Trustline.lean:254:    t.holderAcct + t.issuerWell = 0 := by
metatheory/Dregg2/Apps/Trustline.lean:278:    t₂.drawn = t.drawn ∧ t₂.holderAcct = t.holderAcct ∧ t₂.issuerWell = t.issuerWell
metatheory/Dregg2/Apps/Trustline.lean:285:  · show t.holderAcct + (a : Int) - (a : Int) = t.holderAcct
metatheory/Dregg2/Apps/Trustline.lean:337:      ∧ (settleAll c).tl.holderAcct = 0
metatheory/Dregg2/Apps/Trustline.lean:347:  · show c.tl.holderAcct - (c.tl.drawn : Int) = 0
metatheory/Dregg2/Apps/Trustline.lean:386:  · show t.holderAcct + (amt : Int) = ((t.drawn + amt : Nat) : Int)
metatheory/Dregg2/Apps/Trustline.lean:402:  · show t.holderAcct - (amt : Int) = ((t.drawn - amt : Nat) : Int)
metatheory/Dregg2/Apps/Trustline.lean:440:    ∀ n, (traj t₀ sched n).holderAcct + (traj t₀ sched n).issuerWell = 0 :=
metatheory/Dregg2/Apps/Trustline.lean:452:    ∀ n, (traj t₀ sched n).holderAcct ≤ ((traj t₀ sched n).ceiling : Int) := by
metatheory/Dregg2/Apps/Trustline.lean:526:#guard demo₁.holderAcct == 30
metatheory/Dregg2/Apps/Trustline.lean:529:#guard demo₁.holderAcct + demo₁.issuerWell == 0
metatheory/Dregg2/Apps/Trustline.lean:546:#guard demo₂.holderAcct == 0
metatheory/Dregg2/Apps/Trustline.lean:815:    ∀ n, (trajS s₀ sched n).tl.holderAcct + (trajS s₀ sched n).tl.issuerWell = 0 :=
metatheory/Dregg2/Apps/Trustline.lean:1029:and DERIVES the bilateral credit view from `drawn` — `holderAcct = +drawn` / `issuerWell =
metatheory/Dregg2/Apps/Trustline.lean:1038:  , holderAcct := (drawn : Int), issuerWell := -(drawn : Int) }
metatheory/Dregg2/Apps/Trustline.lean:1054:registers the deployment stores are EQUAL: deriving `holderAcct`/`issuerWell` from `drawn`
metatheory/Dregg2/Exec/CapTPStoreForward.lean:457:/-! ### §9b.1 — Accounting laws (proved). -/
metatheory/Dregg2/Distributed/HistoryAggregation.lean:15:proof's validity is exactly `AggregateAttests` from this file — so a light client that checks only
metatheory/Dregg2/Distributed/HistoryAggregation.lean:25:**The headline (`wellformed_attests_whole_history`):** a `WellFormedChain` from a genesis state
metatheory/Dregg2/Distributed/HistoryAggregation.lean:42:  compressInjective compressNInjective cellLeafInjective RestHashIffFrame AccountsWF cellDigest)
metatheory/Dregg2/Distributed/HistoryAggregation.lean:108:/-- **`ChainBound steps`** — every adjacent pair satisfies the temporal tooth. The whole sequence is
metatheory/Dregg2/Distributed/HistoryAggregation.lean:110:def ChainBound : List ChainStep → Prop
metatheory/Dregg2/Distributed/HistoryAggregation.lean:113:  | s :: s' :: rest => Continues CH RH cmb compress compressN s s' ∧ ChainBound (s' :: rest)
metatheory/Dregg2/Distributed/HistoryAggregation.lean:139:  bound   : ChainBound CH RH cmb compress compressN steps
metatheory/Dregg2/Distributed/HistoryAggregation.lean:197:FULL standard Poseidon CR set + the PROVED-preserved `AccountsWF` structural invariant on BOTH seam
metatheory/Dregg2/Distributed/HistoryAggregation.lean:209:    (hwf : AccountsWF s.post.kernel) (hwf' : AccountsWF s'.pre.kernel)
metatheory/Dregg2/Distributed/HistoryAggregation.lean:321:adjacent pair the turn-contexts match AND both seam kernels are `AccountsWF`. These are exactly the
metatheory/Dregg2/Distributed/HistoryAggregation.lean:323:holds under the accumulator's NoOp-padding (`ivc_turn_chain.rs:325`), and `AccountsWF` is the
metatheory/Dregg2/Distributed/HistoryAggregation.lean:324:structural invariant every `recKExec` PRESERVES (`StateCommit.recKExec_preserves_AccountsWF`). The
metatheory/Dregg2/Distributed/HistoryAggregation.lean:325:TOOTH itself is NOT here — it comes from `ChainBound`, which a verified `bindingProof` supplies. So
metatheory/Dregg2/Distributed/HistoryAggregation.lean:331:      (s.turn = s'.turn ∧ AccountsWF s.post.kernel ∧ AccountsWF s'.pre.kernel)
metatheory/Dregg2/Distributed/HistoryAggregation.lean:336:verified root tooth `ChainBound` (what a verified `bindingProof` delivers, = `AggregateAttests.ordered`),
metatheory/Dregg2/Distributed/HistoryAggregation.lean:337:and the structural envelope `SeamStruct` (matched turns + `AccountsWF`), the whole chain is
metatheory/Dregg2/Distributed/HistoryAggregation.lean:339:`root_tooth_pins_kernel` from the `ChainBound` tooth — it is no longer the prover-supplied `StateChained`
metatheory/Dregg2/Distributed/HistoryAggregation.lean:349:      ChainBound CH RH cmb compress compressN steps →
metatheory/Dregg2/Distributed/HistoryAggregation.lean:357:    -- the seam `s.post.kernel = s'.pre.kernel` is DERIVED from the verified `ChainBound` tooth.
metatheory/Dregg2/Distributed/HistoryAggregation.lean:368:VERIFIED root tooth `ChainBound` (= `AggregateAttests.ordered`), and the structural envelope
metatheory/Dregg2/Distributed/HistoryAggregation.lean:380:    (hbound : ChainBound CH RH cmb compress compressN steps)
metatheory/Dregg2/Distributed/HistoryAggregation.lean:389:`seam_roots_chain`; whole-list `ChainBound` follows when each seam's turn-contexts agree (the
metatheory/Dregg2/Distributed/HistoryAggregation.lean:400:/-- **`wellformed_attests_whole_history` (THE HEADLINE).** A well-formed chain from genesis
metatheory/Dregg2/Distributed/HistoryAggregation.lean:404:  (2) **the chain is correctly ordered** — the root-level temporal tooth holds (`ChainBound`), so no
metatheory/Dregg2/Distributed/HistoryAggregation.lean:411:theorem wellformed_attests_whole_history (g : RecChainedState) (steps : List ChainStep)
metatheory/Dregg2/Distributed/HistoryAggregation.lean:414:      ∧ ChainBound CH RH cmb compress compressN steps          -- (2) correctly ordered
metatheory/Dregg2/Distributed/HistoryAggregation.lean:427:`ChainBound`). Both witnessed below over the concrete `ConsensusExec.teethGenesis`. -/
metatheory/Dregg2/Distributed/HistoryAggregation.lean:441:not vacuous. (We exhibit `StateChained`; `ChainBound` on a singleton is `True`.) -/
metatheory/Dregg2/Distributed/HistoryAggregation.lean:477:/ spliced chain is NOT `ChainBound`: if the first step's `newRoot` differs from the second's
metatheory/Dregg2/Distributed/HistoryAggregation.lean:478:`oldRoot`, the `Continues` tooth fails, so `ChainBound` is false. We witness this abstractly: for ANY
metatheory/Dregg2/Distributed/HistoryAggregation.lean:479:two steps whose seam roots disagree, `ChainBound [s, s']` is `False` — exactly the
metatheory/Dregg2/Distributed/HistoryAggregation.lean:485:    ¬ ChainBound CH RH cmb compress compressN [s, s'] := by
metatheory/Dregg2/Distributed/HistoryAggregation.lean:497:#assert_axioms Dregg2.Distributed.HistoryAggregation.wellformed_attests_whole_history
metatheory/Dregg2/Circuit/RotatedKernelRefinement.lean:256:  guardAccepts : acceptsEffects pre.kernel tr.dst = true
metatheory/Dregg2/Circuit/RotatedKernelRefinement.lean:259:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinement.lean:393:      henc.guardSrcLifecycleLive, henc.guardAccepts⟩
metatheory/Dregg2/Circuit/RotatedKernelRefinement.lean:397:  · exact henc.frAccounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:116:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:181:   henc.frame.frAccounts, henc.frame.frCell, henc.frame.frNullifiers, henc.frame.frRevoked,
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:268:   henc.frame.frAccounts, henc.frame.frCell, henc.frame.frNullifiers, henc.frame.frRevoked,
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:412:   henc.frame.frAccounts, henc.frame.frCell, henc.frame.frNullifiers, henc.frame.frRevoked,
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:463:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:497:   henc.frAccounts, henc.frCell, henc.frCaps, henc.frNullifiers, henc.frRevoked,
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:556:   henc.frame.frAccounts, henc.frame.frCell, henc.frame.frNullifiers, henc.frame.frRevoked,
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:626:   henc.capRemove.frame.frAccounts, henc.capRemove.frame.frCell, henc.capRemove.frame.frNullifiers,
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:1256:   rd.frame.frAccounts, rd.frame.frCell, rd.frame.frNullifiers, rd.frame.frRevoked,
metatheory/Dregg2/Circuit/StateCommit.lean:40:`cSFrameReuse`+`FrameDigestBindsCells`, dead cells from the PROVED `AccountsWF` invariant, and the 16
metatheory/Dregg2/Circuit/StateCommit.lean:52:  * `AccountsWF k` — NOT crypto: the structural invariant "cells outside `accounts` hold the default".
metatheory/Dregg2/Circuit/StateCommit.lean:53:                     PROVED PRESERVED by `recKExec_preserves_AccountsWF` (a real theorem, not a portal).
metatheory/Dregg2/Circuit/StateCommit.lean:57:PROVED (everything else — crucially THE FRAME): `recKExec_preserves_AccountsWF`, the binding lemmas,
metatheory/Dregg2/Circuit/StateCommit.lean:85:/-! ## §1 — the `AccountsWF` invariant and its PROVED preservation.
metatheory/Dregg2/Circuit/StateCommit.lean:87:`AccountsWF k` says every cell OUTSIDE the live account set holds the default `Value` (`.int 0`).
metatheory/Dregg2/Circuit/StateCommit.lean:92:/-- **`AccountsWF k`** — every cell outside the live account set holds the default `Value`. The
metatheory/Dregg2/Circuit/StateCommit.lean:94:def AccountsWF (k : RecordKernelState) : Prop := ∀ c, c ∉ k.accounts → k.cell c = default
metatheory/Dregg2/Circuit/StateCommit.lean:96:/-- **THEOREM 1 — `recKExec_preserves_AccountsWF` (not portaled).** A committed `recKExec`
metatheory/Dregg2/Circuit/StateCommit.lean:97:step preserves `AccountsWF`: the account set is unchanged (`recKExec_frame`), and `recTransfer`
metatheory/Dregg2/Circuit/StateCommit.lean:99:theorem recKExec_preserves_AccountsWF {k k' : RecordKernelState} {t : Turn}
metatheory/Dregg2/Circuit/StateCommit.lean:100:    (hwf : AccountsWF k) (h : recKExec k t = some k') : AccountsWF k' := by
metatheory/Dregg2/Circuit/StateCommit.lean:109:  -- `recTransfer` leaves `c` untouched; `AccountsWF k` makes it default.
metatheory/Dregg2/Circuit/StateCommit.lean:114:#assert_axioms recKExec_preserves_AccountsWF
metatheory/Dregg2/Circuit/StateCommit.lean:427:post-state frame; the `AccountsWF` invariant closes the dead-cell case. The post `cell` map is
metatheory/Dregg2/Circuit/StateCommit.lean:434:`cellLeafInjective CH`, `RestHashIffFrame RH`) + the `AccountsWF` invariant on both states. The frame
metatheory/Dregg2/Circuit/StateCommit.lean:444:    (hwf : AccountsWF k) (hwf' : AccountsWF k')
metatheory/Dregg2/Circuit/StateCommit.lean:485:  obtain ⟨hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel, hDgs,
metatheory/Dregg2/Circuit/StateCommit.lean:515:        · -- c is a DEAD cell: AccountsWF on both states ⇒ both default; recTransfer leaves it.
metatheory/Dregg2/Circuit/StateCommit.lean:516:          have hk'acc : c ∉ k'.accounts := by rw [hAcc]; exact hcacc
metatheory/Dregg2/Circuit/StateCommit.lean:522:    hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel, hDgs, hDE, hDEA, hHeaps⟩
metatheory/Dregg2/Circuit/StateCommit.lean:552:`FrameDigestBindsCells` recovers every untouched live cell, and `AccountsWF` (on BOTH states) closes
metatheory/Dregg2/Circuit/StateCommit.lean:562:    (hwf : AccountsWF k) (hwf' : AccountsWF k')
metatheory/Dregg2/Circuit/StateCommit.lean:563:    (hAcc : k.accounts = k'.accounts)
metatheory/Dregg2/Circuit/StateCommit.lean:569:  rw [← hAcc] at hcd
metatheory/Dregg2/Circuit/StateCommit.lean:589:      · -- dead cell: AccountsWF on both states ⇒ both default.
metatheory/Dregg2/Circuit/StateCommit.lean:590:        have hk'acc : c ∉ k'.accounts := by rw [← hAcc]; exact hcacc
metatheory/Dregg2/Circuit/StateCommit.lean:602:`cellLeafInjective`, `RestHashIffFrame`) + the PROVED-preserved `AccountsWF` structural invariant. -/
metatheory/Dregg2/Circuit/StateCommit.lean:610:    (hwf : AccountsWF k) (hwf' : AccountsWF k')
metatheory/Dregg2/Circuit/StateCommit.lean:616:  obtain ⟨hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel, hDgs, hDE, hDEA, hHeaps⟩ :=
metatheory/Dregg2/Circuit/StateCommit.lean:621:      hAcc.symm hcd
metatheory/Dregg2/Circuit/StateCommit.lean:641:  obtain ⟨hg, hcell, hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel,
metatheory/Dregg2/Circuit/StateCommit.lean:659:    ⟨hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel, hDgs, hDE, hDEA, hHeaps⟩
metatheory/Dregg2/Circuit/StateCommit.lean:701:      -- `frameCarrier k t = k.accounts \ {src,dst}`. The carriers agree by `hAcc` (accounts frozen).
metatheory/Dregg2/Circuit/StateCommit.lean:703:        recStateCommit, cellDigest, frameCarrier, hAcc]
metatheory/Dregg2/Circuit/StateCommit.lean:928:rest CR set; `compressInjective cmb` only for the root-binding corollary); `AccountsWF` (a STRUCTURAL
metatheory/Dregg2/Circuit/StateCommit.lean:929:invariant, PROVED preserved by `recKExec_preserves_AccountsWF`). The old per-digest binding portals
metatheory/Dregg2/Circuit/StateCommit.lean:934:#assert_axioms recKExec_preserves_AccountsWF
metatheory/Dregg2/Circuit/CircuitCompletenessValue.lean:64:open Dregg2.Circuit.StateCommit (AccountsWF)
metatheory/Dregg2/Circuit/CircuitCompletenessValue.lean:143:  frAccounts          := hspec.2.2.2.1
metatheory/Dregg2/Circuit/CircuitCompletenessValue.lean:199:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessValue.lean:267:  frAccounts          := hspec.2.2.2.1
metatheory/Dregg2/Circuit/CircuitCompletenessValue.lean:319:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessValue.lean:351:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessValue.lean:415:  frAccounts          := hspec.2.2.2.2.1
metatheory/Dregg2/Circuit/CircuitCompletenessValue.lean:456:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Exec/CircuitEmitGadgets.lean:486:        satisfiedEmittedDfa δ q₀ accept emittedDfa circuit → DfaAccepts δ q₀ accept trace)
metatheory/Dregg2/Exec/CircuitEmitGadgets.lean:489:    (DfaAccepts δ q₀ accept trace →
metatheory/Dregg2/Distributed/CellMigration.lean:268:  -- `liveAccept` is the post-ACCEPT live map (insert `c` at the destination `d`); `handoffWorld`
metatheory/Dregg2/Distributed/CellMigration.lean:271:  let liveAccept : FedId → Finset CellId := fun f => if f = d then insert c (w.live f) else w.live f
metatheory/Dregg2/Distributed/CellMigration.lean:272:  { live      := fun f => if f = s then (liveAccept f).erase c else liveAccept f
metatheory/Dregg2/Distributed/CellMigration.lean:307:    -- `w2.live = liveAccept` and `w2.{authAt,locked,tombstone}` match `handoffWorld`'s fields by
metatheory/Dregg2/Circuit/DescriptorIR2.lean:93:  | memAccess
metatheory/Dregg2/Circuit/DescriptorIR2.lean:98:  | umemAccess
metatheory/Dregg2/Circuit/DescriptorIR2.lean:164:def memTableDef : TableDef := ⟨.memory, "memory", 5, .memAccess⟩
metatheory/Dregg2/Circuit/DescriptorIR2.lean:289:Aggregation.EngineSound.recursive_sound`, `circuit/src/joint_turn_recursive.rs`'s leaf verifier,
metatheory/Dregg2/Circuit/DescriptorIR2.lean:863:`RecursiveAggregation.EngineSound.recursive_sound` / the leaf-verifier's soundness — the one FRI
metatheory/Dregg2/Circuit/DescriptorIR2.lean:1310:  | .memAccess       => "memory"
metatheory/Dregg2/Circuit/DescriptorIR2.lean:1312:  | .umemAccess      => "umemory"
metatheory/Dregg2/Circuit/DescriptorIR2.lean:1317:def umemTableDef : TableDef := ⟨.custom UMEM_TID, "umemory", 8, .umemAccess⟩
metatheory/Dregg2/Circuit/CircuitCompleteness.lean:27:its own commitment), with `AccountsWF` the structural side-condition the executor preserves. This is the
metatheory/Dregg2/Circuit/CircuitCompleteness.lean:69:open Dregg2.Circuit.StateCommit (AccountsWF compressInjective compressNInjective cellLeafInjective
metatheory/Dregg2/Circuit/CircuitCompleteness.lean:87:pre post` holds by `rfl` on the binding fields, with `AccountsWF` the structural side-condition (the
metatheory/Dregg2/Circuit/CircuitCompleteness.lean:98:boundary kernels (both `AccountsWF` — the structural side-condition the executor preserves), the
metatheory/Dregg2/Circuit/CircuitCompleteness.lean:102:    (hpre : AccountsWF pre.kernel) (hpost : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompleteness.lean:119:`AccountsWF` boundary kernels) admits a circuit witness — a memory boundary `(minit, mfin, maddrs)` and
metatheory/Dregg2/Circuit/CircuitCompleteness.lean:127:    kstep pre post → AccountsWF pre.kernel → AccountsWF post.kernel →
metatheory/Dregg2/Circuit/CircuitCompleteness.lean:162:`kstep pre post` (with `AccountsWF` boundary kernels), the per-effect satisfiability rung
metatheory/Dregg2/Circuit/CircuitCompleteness.lean:175:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompleteness.lean:307:  guardAccepts  := hspec.1.2.2.2.2.2.2.2
metatheory/Dregg2/Circuit/CircuitCompleteness.lean:309:  frAccounts          := hspec.2.2.2.1
metatheory/Dregg2/Circuit/CircuitCompleteness.lean:412:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/RotatedKernelRefinementPermsVK.lean:121:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementPermsVK.lean:154:  ⟨henc.guard, henc.cellMapMove, henc.logAdv, henc.frAccounts, henc.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementPermsVK.lean:200:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementPermsVK.lean:232:  ⟨henc.guard, henc.cellMapMove, henc.logAdv, henc.frAccounts, henc.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementPermsVK.lean:308:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementPermsVK.lean:364:  exact ⟨rd.guard, hcellMap, rd.logAdv, rd.frAccounts, rd.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementPermsVK.lean:401:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementPermsVK.lean:454:  exact ⟨rd.guard, hcellMap, rd.logAdv, rd.frAccounts, rd.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementPermsVK.lean:490:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementPermsVK.lean:516:  ⟨henc.guard, henc.logAdv, henc.frAccounts, henc.frCell, henc.frCaps,
metatheory/Dregg2/Exec/FFI.lean:207:/-- Accumulate a JSON string body until the closing quote (escapes: `\"`, `\\`). -/
metatheory/Dregg2/Circuit/Witness/CreateCellFromFactoryWitness.lean:27:open Dregg2.Circuit.AccountsCommit
metatheory/Dregg2/Circuit/Witness/CreateCellFromFactoryWitness.lean:148:  , expected := fun s args => accDigConcrete (expectedAccounts s args)
metatheory/Dregg2/Circuit/Witness/CreateCellFromFactoryWitness.lean:149:  , postClause := fun s args post => accDigConcrete post.accounts = accDigConcrete (expectedAccounts s args)
metatheory/Dregg2/Circuit/Witness/SetVKWitness.lean:60:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Distributed/ThresholdAdmission.lean:165:structure CryptoAccepts {PK : Type u} (hc : HostCommittee PK) {msg : ℕ}
metatheory/Dregg2/Distributed/ThresholdAdmission.lean:183:  P.committee commit = some hc ∧ cert.threshold ≥ hc.floorK ∧ CryptoAccepts hc cert
metatheory/Dregg2/Distributed/ThresholdAdmission.lean:195:      (P.committee commit = some hc ∧ cert.threshold ≥ hc.floorK ∧ CryptoAccepts hc cert) :=
metatheory/Dregg2/Distributed/ThresholdAdmission.lean:224:Note the absence of any `CryptoAccepts` hypothesis — refusal holds even for a genuine aggregate. -/
metatheory/Dregg2/Distributed/ThresholdAdmission.lean:251:    (hbad : ¬ CryptoAccepts hc cert) :
metatheory/Dregg2/Distributed/ThresholdAdmission.lean:264:    (hca : CryptoAccepts hc cert) :
metatheory/Dregg2/Distributed/ThresholdAdmission.lean:301:def passingCert_crypto : CryptoAccepts hostFed4 (msg := 99) passingCert where
metatheory/Dregg2/Distributed/ThresholdAdmission.lean:357:theorem forged_not_crypto : ¬ CryptoAccepts hostFed4 (msg := 99) forgedCert := by
metatheory/Dregg2/Distributed/ThresholdAdmission.lean:392:cryptographic content is `Crypto.BlsThreshold`'s NAMED carriers (consumed via `CryptoAccepts`'s
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:7:(`light_client_verifies_whole_history`). But "internally correct" is NOT "finalized": a valid
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:16:  (1) the succinct aggregate verifies  (the recursion engine — `RecursiveAggregation.EngineSound`),
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:35:soundness — carried, exactly as in `RecursiveAggregation`, by the NAMED, REALIZABLE `EngineSound`
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:50:  (ChainStep stateRoot foldedFinalRoot lastStateOf StateChained ChainBound zeroTurn)
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:52:  (Aggregate EngineSound AggregateAttests light_client_verifies_whole_history)
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:160:`AggregateAttests` (every turn executed correctly, correctly ordered, final root is the genuine fold)
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:169:  history : AggregateAttests Proof CH RH cmb compress compressN agg g steps
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:184:ride `light_client_verifies_whole_history` (under the named `EngineSound`); leg 3 is fully proved from
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:190:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:195:  { history := light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:240:   AggregateAttests)
metatheory/Dregg2/Circuit/CircuitCompletenessTransferConstruct.lean:49:open Dregg2.Circuit.StateCommit (AccountsWF compressInjective compressNInjective cellLeafInjective
metatheory/Dregg2/Circuit/CircuitCompletenessTransferConstruct.lean:94:commitment) and `AccountsWF` boundary kernels, there is a circuit witness of `transferV3` whose
metatheory/Dregg2/Circuit/CircuitCompletenessTransferConstruct.lean:107:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel)
metatheory/Dregg2/Circuit/Witness/PipelinedSendWitness.lean:117:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/Witness/MakeSovereignWitness.lean:72:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Distributed/FinalityGate.lean:127:  | [wS, pSeg, bSeg] =>
metatheory/Dregg2/Distributed/FinalityGate.lean:129:      let pS ← stripReq? "P=" pSeg
metatheory/Dregg2/Distributed/FinalityGate.lean:130:      let bS ← stripReq? "B=" bSeg
metatheory/Dregg2/Circuit/Witness/ReceiptArchiveWitness.lean:64:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Distributed/FeeHistory.lean:218:  obtain ⟨hbodyTot, hbodyAcc⟩ := transfer_body_total_frame hbody
metatheory/Dregg2/Distributed/FeeHistory.lean:219:  have hpm' : s.proposer ∈ s'.kernel.accounts := by rw [hbodyAcc]; exact s.hpm
metatheory/Dregg2/Distributed/FeeHistory.lean:220:  have htm' : s.treasury ∈ s'.kernel.accounts := by rw [hbodyAcc]; exact s.htm
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:256:/-- **`leaderSegment B participants wavelength prevCovered l`** — the blocks a final leader `l`
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:261:def leaderSegment (B : Lace) (participants : List AuthorId) (wavelength : Nat)
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:276:  (acc.1 ++ leaderSegment B participants wavelength acc.2 l,
metatheory/Dregg2/Distributed/StrandAdmission.lean:541:  | [nS, mSeg, sSeg, vSeg, boSeg, qSeg] =>
metatheory/Dregg2/Distributed/StrandAdmission.lean:543:      let mS ← stripReq? "m=" mSeg
metatheory/Dregg2/Distributed/StrandAdmission.lean:544:      let sS ← stripReq? "S=" sSeg
metatheory/Dregg2/Distributed/StrandAdmission.lean:545:      let vS ← stripReq? "V=" vSeg
metatheory/Dregg2/Distributed/StrandAdmission.lean:546:      let boS ← stripReq? "Bo=" boSeg
metatheory/Dregg2/Distributed/StrandAdmission.lean:547:      let qS ← stripReq? "q=" qSeg
metatheory/Dregg2/Circuit/Witness/RefreshDelegationWitness.lean:136:all empty. Accounts {0,1}. -/
metatheory/Dregg2/Distributed/StrandIntegrity.lean:248:def StrandAccepts (B : Lace) (p : AuthorId) (b : Block) : Prop :=
metatheory/Dregg2/Distributed/StrandIntegrity.lean:256:    (hff : StrandForkFree B p) (hacc : StrandAccepts B p b) :
metatheory/Dregg2/Circuit/Witness/ExerciseWitness.lean:75:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/Inst/delegate.lean:215:  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/delegate.lean:217:    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/delegate.lean:219:  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/delegate.lean:221:    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/EffectRefinement.lean:59:open Dregg2.Circuit.Spec.AccountGrowth
metatheory/Dregg2/Circuit/EffectRefinement.lean:290:    (hRest : RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
metatheory/Dregg2/Circuit/EffectRefinement.lean:300:    (hRest : RestIffNoAccountsBalBorn S.RH)
metatheory/Dregg2/Circuit/EffectRefinement.lean:313:    (hRest : RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
metatheory/Dregg2/Circuit/EffectRefinement.lean:889:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectRefinement.lean:908:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectRefinement.lean:933:    (hwf : AccountsWF pre.kernel) (hwf' : AccountsWF post.kernel)
metatheory/Dregg2/Circuit/EffectRefinement.lean:945:    (hwf : AccountsWF pre.kernel)
metatheory/Dregg2/Circuit/EffectRefinement.lean:958:    (hwf : AccountsWF pre.kernel)
metatheory/Dregg2/Circuit/Witness/CreateCellWitness.lean:24:open Dregg2.Circuit.AccountsCommit
metatheory/Dregg2/Circuit/Witness/CreateCellWitness.lean:28:open Dregg2.Circuit.Spec.AccountGrowth
metatheory/Dregg2/Circuit/Witness/CreateCellWitness.lean:50:    (hRest : RestIffNoAccountsBalBorn S.RH)
metatheory/Dregg2/Circuit/Witness/CreateCellWitness.lean:61:    (hRest : RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
metatheory/Dregg2/Circuit/Witness/SpawnWitness.lean:32:open Dregg2.Circuit.Spec.AccountGrowth
metatheory/Dregg2/Circuit/Witness/SpawnWitness.lean:134:def withAccounts (k : RecordKernelState) (acc : Finset CellId) : RecordKernelState := { k with accounts := acc }
metatheory/Dregg2/Circuit/Witness/SpawnWitness.lean:141:  , active1      := mkComp accountsDigC (fun s args => accountsDigC (withAccounts s.kernel (expectedAccounts s args)))
metatheory/Dregg2/Circuit/Inst/bridgeMintA.lean:31:digest — the realizable Poseidon-CR bar). NO `AccountsWF` (the touched thing is not the cell map), NO
metatheory/Dregg2/Circuit/Inst/bridgeMintA.lean:170:  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/bridgeMintA.lean:172:    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/bridgeMintA.lean:174:  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/bridgeMintA.lean:176:    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Witness/RevokeDelegationWitness.lean:157:label 1 = `[node 9]`; others empty. Accounts {0,1}. -/
metatheory/Dregg2/Circuit/Witness/RefusalWitness.lean:78:`refusalA_full_sound`; carries the standard Poseidon-CR portals + `AccountsWF` on both states. -/
metatheory/Dregg2/Circuit/Witness/RefusalWitness.lean:84:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/Witness/DelegateWitness.lean:163:caps. Accounts {0,1,2}. -/
metatheory/Dregg2/Circuit/Witness/IncrementNonceWitness.lean:82:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/Witness/EmitEventWitness.lean:82:`emitEventA_full_sound`; carries the standard Poseidon-CR portals + `AccountsWF` on both states. -/
metatheory/Dregg2/Circuit/Witness/EmitEventWitness.lean:88:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/Inst/cellUnsealA.lean:133:  · rintro ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
metatheory/Dregg2/Circuit/Inst/cellUnsealA.lean:135:    exact ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
metatheory/Dregg2/Circuit/Inst/cellUnsealA.lean:137:  · rintro ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
metatheory/Dregg2/Circuit/Inst/cellUnsealA.lean:139:    exact ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
metatheory/Dregg2/Circuit/ClosureFloorReduce.lean:100:  guardAccepts : acceptsEffects pre.kernel tr.dst = true
metatheory/Dregg2/Circuit/ClosureFloorReduce.lean:102:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/ClosureFloorReduce.lean:166:  guardAccepts := r.guardAccepts
metatheory/Dregg2/Circuit/ClosureFloorReduce.lean:167:  frAccounts := r.frAccounts
metatheory/Dregg2/Circuit/Witness/SetPermissionsWitness.lean:64:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/RotatedKernelRefinementNotes.lean:140:digest of the GROWN list `x :: preList`. The committed-column analog of Birth's `gAccountsGrow`: the
metatheory/Dregg2/Circuit/RotatedKernelRefinementNotes.lean:191:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementNotes.lean:228:  refine ⟨⟨henc.proof, henc.freshness⟩, ?_, henc.logAdv, henc.frAccounts, henc.frCell, henc.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementNotes.lean:291:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementNotes.lean:327:  refine ⟨trivial, ?_, henc.logAdv, henc.frAccounts, henc.frCell, henc.frCaps, henc.frNullifiers,
metatheory/Dregg2/Circuit/RotatedKernelRefinementNotes.lean:435:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementNotes.lean:470:  refine ⟨⟨rd.proof, rd.freshness⟩, ?_, rd.logAdv, rd.frAccounts, rd.frCell, rd.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementNotes.lean:501:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementNotes.lean:535:  refine ⟨trivial, ?_, rd.logAdv, rd.frAccounts, rd.frCell, rd.frCaps, rd.frNullifiers,
metatheory/Dregg2/Circuit/ClosureAll.lean:719:      = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log))
metatheory/Dregg2/Circuit/ClosureAll.lean:721:        = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log →
metatheory/Dregg2/Circuit/ClosureAll.lean:726:    (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell) hdec hpub rfl
metatheory/Dregg2/Circuit/ClosureAll.lean:765:      = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log))
metatheory/Dregg2/Circuit/ClosureAll.lean:767:        = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log →
metatheory/Dregg2/Circuit/ClosureAll.lean:772:    (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child) hdec hpub rfl
metatheory/Dregg2/Circuit/ClosureAll.lean:1285:      = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log))
metatheory/Dregg2/Circuit/ClosureAll.lean:1287:        = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log →
metatheory/Dregg2/Circuit/ClosureAll.lean:1292:    (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell) hdec hpub rfl
metatheory/Dregg2/Circuit/ClosureAll.lean:1335:      = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log))
metatheory/Dregg2/Circuit/ClosureAll.lean:1337:        = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log →
metatheory/Dregg2/Circuit/ClosureAll.lean:1342:    (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child) hdec hpub rfl
metatheory/Dregg2/Circuit/ClosureTransfer.lean:36:  3. **Kernel frame** — the 16 non-`bal` frame fields (`frAccounts`/…/`frHeaps`, all unchanged) + the
metatheory/Dregg2/Circuit/ClosureTransfer.lean:37:     side guards (`guardNonNeg`/`guardDistinct`/`guardLiveSrc`/`guardLiveDst`/`guardAccepts`). The frame
metatheory/Dregg2/Circuit/ClosureTransfer.lean:151:  guardAccepts : acceptsEffects pre.kernel tr.dst = true
metatheory/Dregg2/Circuit/ClosureTransfer.lean:153:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/ClosureTransfer.lean:241:  guardAccepts := rd.guardAccepts
metatheory/Dregg2/Circuit/ClosureTransfer.lean:242:  frAccounts := rd.frAccounts
metatheory/Dregg2/Circuit/Inst/cellSealA.lean:133:  · rintro ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
metatheory/Dregg2/Circuit/Inst/cellSealA.lean:135:    exact ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
metatheory/Dregg2/Circuit/Inst/cellSealA.lean:137:  · rintro ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
metatheory/Dregg2/Circuit/Inst/cellSealA.lean:139:    exact ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
metatheory/Dregg2/Circuit/TurnTransferWitness.lean:286:twice; carries the standard Poseidon-CR portals + `AccountsWF` on the three boundary kernels. -/
metatheory/Dregg2/Circuit/TurnTransferWitness.lean:292:    (hwf0 : AccountsWF k₀) (hwf1 : AccountsWF k₁) (hwf2 : AccountsWF k₂)
metatheory/Dregg2/Circuit/ActionDispatch.lean:92:open Dregg2.Circuit.Spec.AccountGrowth
metatheory/Dregg2/Circuit/RotatedKernelRefinementAttenuate.lean:137:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementAttenuate.lean:234:   henc.frAccounts, henc.frCell, henc.frNullifiers, henc.frRevoked, henc.frCommitments,
metatheory/Dregg2/Circuit/TransferDecodeBridge.lean:160:  guardAccepts : acceptsEffects pre.kernel tr.dst = true
metatheory/Dregg2/Circuit/TransferDecodeBridge.lean:163:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/TransferDecodeBridge.lean:238:  guardAccepts := res.guardAccepts
metatheory/Dregg2/Circuit/TransferDecodeBridge.lean:239:  frAccounts := res.frAccounts
metatheory/Dregg2/Circuit/Inst/heapWriteA.lean:177:  · rintro ⟨hg, hcell, hheaps, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/heapWriteA.lean:179:    exact ⟨hg, hcell, hheaps, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/heapWriteA.lean:181:  · rintro ⟨hg, hcell, hheaps, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/heapWriteA.lean:183:    exact ⟨hg, hcell, hheaps, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/WitnessExtract5.lean:33:open Dregg2.Circuit.Spec.AccountGrowth (SpawnFullSpec)
metatheory/Dregg2/Circuit/FloorsNonVacuousWave.lean:123:  frAccounts := rfl
metatheory/Dregg2/Circuit/Inst/receiptArchiveA.lean:160:    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/receiptArchiveA.lean:163:    exact ⟨hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/receiptArchiveA.lean:165:  · rintro ⟨hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/receiptArchiveA.lean:167:    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/receiptArchiveA.lean:180:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/TransferWitness.lean:141:+ `AccountsWF` on both states (the anti-ghost teeth are corollaries, see §4). -/
metatheory/Dregg2/Circuit/TransferWitness.lean:147:    (hwf : StateCommit.AccountsWF k) (hwf' : StateCommit.AccountsWF k')
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:37:    floor (`SetInsertRootProver` / `AccountsInsertRootProver` / `SpawnHandoffInsertProver`), the
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:96:open Dregg2.Circuit.StateCommit (AccountsWF compressNInjective)
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:102:  (AccountsRootRow gAccountsGrow accountsGrowForced
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:112:open Dregg2.Circuit.Spec.AccountGrowth
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:170:  frAccounts := hspec.2.2.2.1
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:225:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:262:  frAccounts := hspec.2.2.2.1
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:302:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:315:/-! ## §3 — createCell: the completeness rung (dual of `createCell_descriptorRefines`). Accounts
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:325:/-- **`AccountsInsertRootProver` — the realizable accounts SET-ROOT FIX-root construction floor (NAMED,
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:332:structure AccountsInsertRootProver (compressN : List FieldElem → FieldElem)
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:336:  hroots : AccountsRootRow compressN preK postK preRoot postRoot
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:337:  gate : gAccountsGrow compressN preK newCell postRoot
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:340:From `CreateCellSpec pre actor newCell post` and the realizable `AccountsInsertRootProver`, ASSEMBLE
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:347:    (prover : AccountsInsertRootProver compressN pre.kernel post.kernel newCell) :
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:385:        AccountsInsertRootProver compressN pre.kernel post.kernel newCell)
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:388:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:402:`createCellFromFactory_descriptorRefines`). Accounts SET-INSERT (child-vk-derived key) + factory
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:414:`AccountsInsertRootProver`, ASSEMBLE `createFromFactoryGenuineEncodes`: the accounts SET-ROOT columns +
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:422:    (prover : AccountsInsertRootProver compressN pre.kernel post.kernel newCell) :
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:478:        AccountsInsertRootProver compressN pre.kernel post.kernel newCell)
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:481:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:495:/-! ## §5 — spawn: the completeness rung (dual of `spawn_descriptorRefines_handoff`). Accounts
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:503:columns (`AccountsInsertRootProver`) AND the child cap-tree sorted-spine INSERT data
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:525:(`AccountsInsertRootProver`), and the realizable cap-handoff sorted-tree INSERT floor
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:534:    (accProver : AccountsInsertRootProver compressN pre.kernel post.kernel child)
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:606:        AccountsInsertRootProver compressN pre.kernel post.kernel child ×'
metatheory/Dregg2/Circuit/CircuitCompletenessSetInsert.lean:610:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/FloorsNonVacuousWavePermsProgram.lean:110:  frAccounts := rfl
metatheory/Dregg2/Circuit/FloorsNonVacuousWavePermsProgram.lean:175:  frAccounts := rfl
metatheory/Dregg2/Circuit/FloorsNonVacuousWavePermsProgram.lean:234:  frAccounts := rfl
metatheory/Dregg2/Circuit/FloorsNonVacuousWavePermsProgram.lean:283:  { frAccounts := rfl, frCell := rfl, frNullifiers := rfl, frRevoked := rfl,
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:65:  (logHashInjective compressNInjective RestHashIffFrame AccountsWF cellLeafInjective)
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:72:open Dregg2.Circuit.Inst.CreateCellA (RestIffNoAccountsBalBorn)
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:203:      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:206:      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:209:      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:212:      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:215:      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:218:      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:228:      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:231:      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:236:      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:335:    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:369:      exact createCell_circuit_refines_spec S LE_cell cN hN hLE_cell DBal hDBal DSide hDSide hRestAccounts hLog
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:443:        DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:516:    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:553:          DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:559:          DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:596:    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:619:      DAuth hDAuth DHeaps hDHeaps hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull hRestCommitments
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:653:    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:676:      DAuth hDAuth DHeaps hDHeaps hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull hRestCommitments
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:706:    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
metatheory/Dregg2/Circuit/TurnEffectRefinement.lean:727:      hDSC DAuth hDAuth DHeaps hDHeaps hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull hRestCommitments
metatheory/Dregg2/Circuit/RotatedKernelRefinementIncNonce.lean:177:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementIncNonce.lean:238:    henc.frAccounts, henc.frCaps, henc.frNullifiers, henc.frRevoked, henc.frCommitments,
metatheory/Dregg2/Circuit/Inst/createCellA.lean:8:ADDITIVE: imports `AccountsCommit`, `BornEmptyCommit`, `EffectCommit3`, `Spec/accountgrowth`.
metatheory/Dregg2/Circuit/Inst/createCellA.lean:10:import Dregg2.Circuit.AccountsCommit
metatheory/Dregg2/Circuit/Inst/createCellA.lean:25:open Dregg2.Circuit.AccountsCommit
metatheory/Dregg2/Circuit/Inst/createCellA.lean:28:open Dregg2.Circuit.Spec.AccountGrowth
metatheory/Dregg2/Circuit/Inst/createCellA.lean:42:/-! ## §1 — the `RestIffNoAccountsBalBorn` portal (global side-tables only). -/
metatheory/Dregg2/Circuit/Inst/createCellA.lean:44:/-- **`RestIffNoAccountsBalBorn RH`** — rest portal: `accounts` + `bal` + born-empty side tables
metatheory/Dregg2/Circuit/Inst/createCellA.lean:46:def RestIffNoAccountsBalBorn (RH : RecordKernelState → ℤ) : Prop :=
metatheory/Dregg2/Circuit/Inst/createCellA.lean:87:def expectedAccounts (s : RecChainedState) (args : CreateCellArgs) : Finset CellId :=
metatheory/Dregg2/Circuit/Inst/createCellA.lean:96:  accountsComponent LE cN hN hLE expectedAccounts
metatheory/Dregg2/Circuit/Inst/createCellA.lean:161:    (hRest : RestIffNoAccountsBalBorn S.RH) :
metatheory/Dregg2/Circuit/Inst/createCellA.lean:171:    (hRest : RestIffNoAccountsBalBorn S.RH) :
metatheory/Dregg2/Circuit/Inst/createCellA.lean:186:    createCellGuardProp, createCellAdmit, expectedAccounts, expectedBal, readBornEmptySide,
metatheory/Dregg2/Circuit/Inst/createCellA.lean:205:    (hRest : RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
metatheory/Dregg2/Circuit/SetFieldCommit.lean:50:dead cells from the PROVED `AccountsWF` invariant, the 16 non-cell fields from `cSFRest`+
metatheory/Dregg2/Circuit/SetFieldCommit.lean:66:  * `AccountsWF k` — NOT crypto: the structural invariant "cells outside `accounts` hold the default",
metatheory/Dregg2/Circuit/SetFieldCommit.lean:67:                     REUSED from `StateCommit` (proved preserved there by `recKExec_preserves_AccountsWF`).
metatheory/Dregg2/Circuit/SetFieldCommit.lean:403:`AccountsWF` invariant), the four guard gates give `SetFieldGuard`; the four frame EQ gates + the
metatheory/Dregg2/Circuit/SetFieldCommit.lean:412:+ the `AccountsWF` invariant on both kernels. The frame binding is PROVED (the binding lemmas are
metatheory/Dregg2/Circuit/SetFieldCommit.lean:423:    (hwf : StateCommit.AccountsWF s.kernel) (hwf' : StateCommit.AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/SetFieldCommit.lean:450:  obtain ⟨hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif, hDC, hDel, hDgs,
metatheory/Dregg2/Circuit/SetFieldCommit.lean:482:      · -- c is a DEAD cell: AccountsWF on both kernels ⇒ both default; setFieldCellMap leaves it.
metatheory/Dregg2/Circuit/SetFieldCommit.lean:483:        have hk'acc : c ∉ s'.kernel.accounts := by rw [hAcc]; exact hcacc
metatheory/Dregg2/Circuit/SetFieldCommit.lean:491:    hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩
metatheory/Dregg2/Circuit/SetFieldCommit.lean:526:  obtain ⟨_hnr, hguard, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/SetFieldCommit.lean:531:    ⟨hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩
metatheory/Dregg2/Circuit/SetFieldCommit.lean:570:        recSetFieldCommit, sfFrameCarrier, hAcc]
metatheory/Dregg2/Circuit/SetFieldCommit.lean:768:new chain piece; `compressInjective cmb` only for the root-binding corollary); `AccountsWF` (a
metatheory/Dregg2/Circuit/FloorsNonVacuousWaveBirth.lean:37:open Dregg2.Circuit.Spec.AccountGrowth
metatheory/Dregg2/Circuit/WitnessExtract3.lean:32:open Dregg2.Circuit.Spec.AccountGrowth (CreateCellSpec)
metatheory/Dregg2/Circuit/WitnessExtract3.lean:193:    (hRest : Inst.CreateCellA.RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
metatheory/Dregg2/Circuit/WitnessExtractV1PerEffect.lean:38:  RestHashIffFrame AccountsWF)
metatheory/Dregg2/Circuit/WitnessExtractV1PerEffect.lean:54:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/WitnessExtractV1PerEffect.lean:84:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/WitnessExtractV1PerEffect.lean:111:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/WitnessExtractV1PerEffect.lean:141:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/WitnessExtractV1PerEffect.lean:169:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/WitnessExtractV1PerEffect.lean:195:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/WitnessExtractV1PerEffect.lean:223:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/WitnessExtractV1PerEffect.lean:246:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/WitnessExtractV1PerEffect.lean:271:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectRefinementBatch2.lean:97:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectRefinementBatch2.lean:110:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectRefinementBatch2.lean:123:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectRefinementBatch2.lean:136:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectRefinementBatch2.lean:150:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectRefinementBatch2.lean:163:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectRefinementBatch2.lean:176:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectRefinementBatch2.lean:189:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectRefinementBatch2.lean:226:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/RotatedKernelRefinementMisc.lean:149:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementMisc.lean:186:  ⟨henc.guard, henc.cellMapMove, henc.logAdv, henc.frAccounts, henc.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementMisc.lean:264:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementMisc.lean:299:  ⟨hnr, henc.guard, henc.cellMapMove, henc.logAdv, henc.frAccounts, henc.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementMisc.lean:387:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementMisc.lean:459:   rd.logAdv, rd.frAccounts, rd.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementMisc.lean:545:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementMisc.lean:605:  ⟨hnr, rd.guard, rd.cellMapMove, rd.logAdv, rd.frAccounts, rd.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementMisc.lean:640:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementMisc.lean:666:  ⟨henc.logAdv, henc.frAccounts, henc.frCell, henc.frCaps,
metatheory/Dregg2/Circuit/AccountsCommit.lean:2:# Dregg2.Circuit.AccountsCommit — the `accounts` growth carrier (sorted-`Finset` list digest).
metatheory/Dregg2/Circuit/AccountsCommit.lean:13:namespace Dregg2.Circuit.AccountsCommit
metatheory/Dregg2/Circuit/AccountsCommit.lean:40:    (expectedAccounts : St → Args → Finset CellId) : ActiveComponent St Args where
metatheory/Dregg2/Circuit/AccountsCommit.lean:42:  expected  := fun pre args => listDigest LE cN ((expectedAccounts pre args).sort (· ≤ ·))
metatheory/Dregg2/Circuit/AccountsCommit.lean:43:  postClause := fun pre args post => post.accounts = expectedAccounts pre args
metatheory/Dregg2/Circuit/AccountsCommit.lean:51:end Dregg2.Circuit.AccountsCommit
metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:249:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:294:  ⟨henc.guard, henc.cellMapMove, henc.heapsSplice, henc.logAdv, henc.frAccounts, henc.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:464:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:493:  ⟨rd.guard, rd.cellMapMove, rd.heapsSplice, rd.logAdv, rd.frAccounts, rd.frCaps,
metatheory/Dregg2/Circuit/Inst/incrementNonceA.lean:161:    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/incrementNonceA.lean:164:    exact ⟨hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/incrementNonceA.lean:166:  · rintro ⟨hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/incrementNonceA.lean:168:    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/incrementNonceA.lean:181:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectInstances.lean:6:realizable Poseidon CR portals + `AccountsWF` + a per-effect `GuardDecodes`. `StateCommit` (Transfer)
metatheory/Dregg2/Circuit/EffectInstances.lean:179:CR portal is consumed but vacuously discharged), + `AccountsWF` on both states.
metatheory/Dregg2/Circuit/EffectInstances.lean:191:    (hwf : AccountsWF k) (hwf' : AccountsWF k')
metatheory/Dregg2/Circuit/EffectInstances.lean:360:    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/EffectInstances.lean:363:    exact ⟨hnr, hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/EffectInstances.lean:365:  · rintro ⟨_hnr, hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/EffectInstances.lean:367:    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/EffectInstances.lean:377:exercises `cELog` non-trivially) — + `AccountsWF` on both kernels. -/
metatheory/Dregg2/Circuit/EffectInstances.lean:387:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/CommitmentCrossBind.lean:75:through-`cellCommit` bridge). `AccountsWF` (structural, PROVED preserved in `StateCommit`).
metatheory/Dregg2/Circuit/Inst/transfer.lean:197:  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/transfer.lean:199:    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/transfer.lean:201:  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/transfer.lean:203:    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/FloorsNonVacuousWaveLifecycle.lean:105:  frAccounts := rfl
metatheory/Dregg2/Circuit/FloorsNonVacuousWaveLifecycle.lean:172:  frAccounts := rfl
metatheory/Dregg2/Circuit/FloorsNonVacuousWaveLifecycle.lean:234:  frAccounts := rfl
metatheory/Dregg2/Circuit/FloorsNonVacuousWaveLifecycle.lean:296:  frAccounts := rfl
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:2:# Dregg2.Circuit.EngineSoundOfApex — THE WELD: discharge `EngineSound.leaf_sound` BY the single-turn apex.
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:5:(`RecursiveAggregation.light_client_verifies_whole_history`,
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:6:`FinalizedLightClient.light_client_accepts_finalized_history`) rides `RecursiveAggregation.EngineSound`,
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:14:This module WELDS them: it builds an `EngineSound` whose `leaf_sound` is DERIVED from the apex — so the
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:61:  * `engineSound_of_apex` — BUILDS `RecursiveAggregation.EngineSound` from a `Forall₂` of
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:67:    into `light_client_verifies_whole_history` / `light_client_accepts_finalized_history`, the multi-turn
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:82:namespace Dregg2.Circuit.EngineSoundOfApex
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:95:open Dregg2.Circuit.RecursiveAggregation (Aggregate EngineSound)
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:103:`Proof`/`verify` are the OPAQUE aggregation-engine carriers (the same the `Aggregate`/`EngineSound`
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:182:/-! ## §4 — `engineSound_of_apex` — BUILD `EngineSound` (discharge `leaf_sound`) FROM the apex.
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:186:`EngineSound` legs (`recursive_sound` = the FRI recursive-verifier soundness, `binding_sound` = the
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:191:/-- **`leafSound_of_bundles`.** The `EngineSound.leaf_sound` field — the positional `Forall₂` that
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:208:/-- **`engineSound_of_apex` — THE WELD.** Builds `RecursiveAggregation.EngineSound` from:
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:215:The resulting `EngineSound` is the one `light_client_verifies_whole_history` /
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:226:      Dregg2.Distributed.HistoryAggregation.ChainBound CH' RH' cmb' compress' compressN' steps
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:233:    EngineSound Proof verify CH' RH' cmb' compress' compressN' agg g steps where
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:244:(`RecursiveAggregation.light_client_verifies_whole_history`) and the finalized-history headline
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:246:per-leaf bundles + the two recursion legs}, with `EngineSound.leaf_sound` discharged by circuit
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:262:(`RecursiveAggregation.AggregateAttests` — every turn executed, correctly ordered, genuine fold)
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:263:obtained WITHOUT carrying `EngineSound` as a free sibling: its `leaf_sound` is the apex
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:273:      Dregg2.Distributed.HistoryAggregation.ChainBound CH RH cmb compress compressN steps
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:281:    Dregg2.Circuit.RecursiveAggregation.AggregateAttests Proof CH RH cmb compress compressN agg g steps :=
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:282:  Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:291:finalization) obtained with `EngineSound.leaf_sound` discharged by the apex. The whole distributed
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:301:      Dregg2.Distributed.HistoryAggregation.ChainBound CH RH cmb compress compressN steps
metatheory/Dregg2/Circuit/EngineSoundOfApex.lean:361:end Dregg2.Circuit.EngineSoundOfApex
metatheory/Dregg2/Circuit/RotatedKernelRefinementMintBurn.lean:179:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementMintBurn.lean:269:  · exact henc.frAccounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementMintBurn.lean:389:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementMintBurn.lean:443:  · exact henc.frAccounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementProgram.lean:88:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementProgram.lean:150:  ⟨rd.guard, rd.cellMapMove, rd.logAdv, rd.frAccounts, rd.frCaps,
metatheory/Dregg2/Circuit/CoordinatedTurnEmit.lean:407:    (hwfA : AccountsWF sA.kernel) (hwfB : AccountsWF sB.kernel)
metatheory/Dregg2/Circuit/CoordinatedTurnEmit.lean:408:    (hwfA' : AccountsWF sA'.kernel) (hwfB' : AccountsWF sB'.kernel)
metatheory/Dregg2/Circuit/CoordinatedTurnEmit.lean:519:    (hwfA : AccountsWF sA.kernel) (hwfB : AccountsWF sB.kernel)
metatheory/Dregg2/Circuit/CoordinatedTurnEmit.lean:520:    (hwfA' : AccountsWF sA'.kernel) (hwfB' : AccountsWF sB'.kernel)
metatheory/Dregg2/Circuit/Refinement.lean:22:`AccountsWF` well-formedness invariant (preserved in `StateCommit`) — NOT the impossible
metatheory/Dregg2/Circuit/Refinement.lean:103:the realizable Poseidon-CR portals + `AccountsWF` on the two endpoints (the reachable-state invariant
metatheory/Dregg2/Circuit/Refinement.lean:109:      (fun k t k' => AccountsWF k ∧ AccountsWF k' ∧ circuitStep CH RH cmb compress compressN k t k')
metatheory/Dregg2/Circuit/Refinement.lean:129:      (fun k t k' => AccountsWF k ∧ AccountsWF k' ∧ circuitStep CH RH cmb compress compressN k t k')
metatheory/Dregg2/Circuit/Refinement.lean:159:    (hwf : AccountsWF k) (hwf' : AccountsWF k')
metatheory/Dregg2/Circuit/Refinement.lean:222:      (fun k t k' => AccountsWF k ∧ AccountsWF k' ∧
metatheory/Dregg2/Circuit/Inst/pipelinedSendA.lean:150:    rintro ⟨_, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/pipelinedSendA.lean:153:    exact ⟨hlog, hAcc, hcell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/pipelinedSendA.lean:155:  · rintro ⟨hlog, hAcc, hcell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/pipelinedSendA.lean:157:    exact ⟨trivial, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/pipelinedSendA.lean:170:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/RotatedKernelRefinementSpawnHandoff.lean:63:open Dregg2.Circuit.Spec.AccountGrowth
metatheory/Dregg2/Circuit/RotatedKernelRefinementSetField.lean:179:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementSetField.lean:246:    henc.frAccounts, henc.frCaps, henc.frNullifiers, henc.frRevoked, henc.frCommitments,
metatheory/Dregg2/Circuit/Inst/setVKA.lean:165:    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/setVKA.lean:168:    exact ⟨hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/setVKA.lean:170:  · rintro ⟨hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/setVKA.lean:172:    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/setVKA.lean:180:exercises `cELog` non-trivially) + `AccountsWF` on both kernels. -/
metatheory/Dregg2/Circuit/Inst/setVKA.lean:186:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/CircuitCompletenessSatFloor.lean:18:`SatFloor S hash d kstep` — "every kernel `kstep pre post` (with `AccountsWF` boundary kernels) admits a
metatheory/Dregg2/Circuit/CircuitCompletenessSatFloor.lean:52:open Dregg2.Circuit.StateCommit (AccountsWF)
metatheory/Dregg2/Circuit/CircuitCompletenessSatFloor.lean:68:step `kstep pre post` (with `AccountsWF` boundary kernels), a memory boundary `(minit, mfin, maddrs)`, a
metatheory/Dregg2/Circuit/CircuitCompletenessSatFloor.lean:77:    kstep pre post → AccountsWF pre.kernel → AccountsWF post.kernel →
metatheory/Dregg2/Circuit/CircuitSoundness.lean:27:   (`CommitSurface`), and that those kernels are `AccountsWF`. Faithfulness is NOT assumed: it is a
metatheory/Dregg2/Circuit/CircuitSoundness.lean:30:   set + the PROVED-preserved `AccountsWF`). It assumes NO kernel admissibility (no authority, no
metatheory/Dregg2/Circuit/CircuitSoundness.lean:93:  (recStateCommit recStateCommit_binds_kernel AccountsWF
metatheory/Dregg2/Circuit/CircuitSoundness.lean:140:the same turn), both `AccountsWF`, are EQUAL. This is `recStateCommit_binds_kernel` repackaged: the
metatheory/Dregg2/Circuit/CircuitSoundness.lean:142:assumption, only collision-resistance + the structural `AccountsWF`. This is exactly the faithfulness
metatheory/Dregg2/Circuit/CircuitSoundness.lean:146:    (hwf : AccountsWF k) (hwf' : AccountsWF k')
metatheory/Dregg2/Circuit/CircuitSoundness.lean:157:are `AccountsWF`, and `pre`/`post` carry the turn the commitment is taken at. It DERIVES the kernel
metatheory/Dregg2/Circuit/CircuitSoundness.lean:194:      preserved by the executor, `recKExec_preserves_AccountsWF` — not a crypto assumption). -/
metatheory/Dregg2/Circuit/CircuitSoundness.lean:195:  preWF     : AccountsWF pre.kernel
metatheory/Dregg2/Circuit/CircuitSoundness.lean:197:  postWF    : AccountsWF post.kernel
metatheory/Dregg2/Circuit/CircuitSoundness.lean:273:pre of `b` are `AccountsWF`, then their kernels COINCIDE — the frame at the seam is forced by the
metatheory/Dregg2/Circuit/CircuitSoundness.lean:299:  * `Accept` — the verdict; `verifyBatch vk pi π` is `accept` exactly when the proof checks.
metatheory/Dregg2/Circuit/SettlementSoundness.lean:77:  RestHashIffFrame logHashInjective recStateCommit recStateCommit_binds_kernel AccountsWF)
metatheory/Dregg2/Circuit/SettlementSoundness.lean:175:    (hwf : AccountsWF k) (hwf' : AccountsWF k')
metatheory/Dregg2/Circuit/BornEmptyCommit.lean:4:Account-growth effects reset every indexed slot at a fresh `CellId` (`bornEmptyCellSlots` in
metatheory/Dregg2/Circuit/BornEmptyCommit.lean:17:open Dregg2.Circuit.Spec.AccountGrowth
metatheory/Dregg2/Circuit/Inst/introduceA.lean:221:  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/introduceA.lean:223:    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/introduceA.lean:225:  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/introduceA.lean:227:    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/EffectEmittedRefinement.lean:66:open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective RestHashIffFrame AccountsWF cellLeafInjective)
metatheory/Dregg2/Circuit/EffectEmittedRefinement.lean:300:    (hRest : RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
metatheory/Dregg2/Circuit/EffectEmittedRefinement.lean:554:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectEmittedRefinement.lean:575:    (hwf : AccountsWF pre.kernel) (hwf' : AccountsWF post.kernel)
metatheory/Dregg2/Circuit/EffectEmittedRefinement.lean:673:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectEmittedRefinement.lean:687:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectEmittedRefinement.lean:701:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectEmittedRefinement.lean:715:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectEmittedRefinement.lean:729:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectEmittedRefinement.lean:856:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectEmittedRefinement.lean:870:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectEmittedRefinement.lean:884:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectEmittedRefinement.lean:900:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectCommit2.lean:6:carrying only realizable Poseidon-CR portals + `AccountsWF` + a per-effect `GuardDecodes`. But ~25 of
metatheory/Dregg2/Circuit/EffectCommit2.lean:42:encoder), exactly the v1 bar. NO `AccountsWF` is needed (the touched thing is not the cell map). NO
metatheory/Dregg2/Circuit/EffectCommit2.lean:361:rest hash. NO `AccountsWF`, NO cell `funext`. -/
metatheory/Dregg2/Circuit/CircuitCompletenessAssembled.lean:42:     `AccountsWF` boundary kernels) ⟹ ∃ an accepting batch proof against `vkOfRegistry Rfix` committing to
metatheory/Dregg2/Circuit/CircuitCompletenessAssembled.lean:87:open Dregg2.Circuit.StateCommit (AccountsWF compressInjective compressNInjective cellLeafInjective
metatheory/Dregg2/Circuit/CircuitCompletenessAssembled.lean:256:      Dregg2.Circuit.Spec.AccountGrowth.CreateCellSpec pre actor newCell post := by
metatheory/Dregg2/Circuit/CircuitCompletenessAssembled.lean:272:      Dregg2.Circuit.Spec.AccountGrowth.SpawnFullSpec pre actor child target post := by
metatheory/Dregg2/Circuit/CircuitCompletenessAssembled.lean:426:    Dregg2.Circuit.Spec.AccountGrowth.CreateCellSpec pre actor newCell post →
metatheory/Dregg2/Circuit/CircuitCompletenessAssembled.lean:666:`spawn_descriptorComplete` rung's `AccountsInsertRootProver` + `SpawnHandoffInsertProver` (the cap-tree
metatheory/Dregg2/Circuit/CircuitCompletenessAssembled.lean:674:      Dregg2.Circuit.Spec.AccountGrowth.SpawnFullSpec pre actor child target post →
metatheory/Dregg2/Circuit/CircuitCompletenessAssembled.lean:720:From a genuine kernel transition `kstepAll e pre post` (with `AccountsWF` boundary kernels), the discharged
metatheory/Dregg2/Circuit/CircuitCompletenessAssembled.lean:732:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessAssembled.lean:756:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessAssembled.lean:775:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessAssembled.lean:837:        kstepAll e pre post → AccountsWF pre.kernel → AccountsWF post.kernel →
metatheory/Dregg2/Circuit/FloorsNonVacuousWaveMiscNotes.lean:96:  frAccounts := rfl
metatheory/Dregg2/Circuit/FloorsNonVacuousWaveMiscNotes.lean:163:  frAccounts := rfl
metatheory/Dregg2/Circuit/FloorsNonVacuousWaveMiscNotes.lean:218:  frAccounts := rfl
metatheory/Dregg2/Circuit/FloorsNonVacuousWaveMiscNotes.lean:270:  frAccounts := rfl
metatheory/Dregg2/Circuit/FloorsNonVacuousWaveMiscNotes.lean:328:  frAccounts := rfl
metatheory/Dregg2/Circuit/Inst/noteSpendA.lean:206:  · rintro ⟨hg, hnull, hlog, hAcc, hCell, hCaps, hBal, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/noteSpendA.lean:208:    exact ⟨hg, hnull, hlog, hAcc, hCell, hCaps, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/noteSpendA.lean:210:  · rintro ⟨hg, hnull, hlog, hAcc, hCell, hCaps, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/noteSpendA.lean:212:    exact ⟨hg, hnull, hlog, hAcc, hCell, hCaps, hBal, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:23:`accounts : Finset CellId` already has an honest commitment carrier: `AccountsCommit` — the Poseidon
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:29:`gAccountsGrow` forces the POST accounts-root to the digest of `insert newCell pre.accounts`.
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:33:> `AccountsCommit` carrier already proven. The Rust realization: `compute_commitment` absorbs an
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:62:(`compressNInjective` + the injective `accountsLeaf`, the SAME carrier `AccountsCommit`/`ListCommit`
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:66:import Dregg2.Circuit.AccountsCommit
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:76:open Dregg2.Circuit.AccountsCommit (accountsSorted accounts_eq_of_sorted_eq accountsSorted_eq_of_eq)
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:77:open Dregg2.Circuit.Spec.AccountGrowth
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:103:index (`accountsSorted = k.accounts.sort (· ≤ ·)`), reusing the `AccountsCommit` carrier. A field
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:107:/-- A field element (the same `ℤ`-carrier `ListCommit`/`AccountsCommit` use for a felt). -/
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:142:POST value the gate `gAccountsGrow` PINS to the GROWN-set digest. -/
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:144:/-- **`AccountsRootRow compressN preK postK preRoot postRoot`** — the decode tying the FIX row's two
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:146:def AccountsRootRow (compressN : List FieldElem → FieldElem)
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:150:/-- **`gAccountsGrow compressN preK newCell postRoot`** — the FIX gate body: the POST accounts-root
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:154:def gAccountsGrow (compressN : List FieldElem → FieldElem)
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:164:    (henc : AccountsRootRow compressN preK postK preRoot postRoot)
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:165:    (hgate : gAccountsGrow compressN preK newCell postRoot) :
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:193:  hroots : AccountsRootRow compressN pre.kernel post.kernel preRoot postRoot
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:195:  gate : gAccountsGrow compressN pre.kernel newCell postRoot
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:273:  hroots : AccountsRootRow compressN pre.kernel post.kernel preRoot postRoot
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:274:  gate : gAccountsGrow compressN pre.kernel newCell postRoot
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:363:  hroots : AccountsRootRow compressN pre.kernel post.kernel preRoot postRoot
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:364:  gate : gAccountsGrow compressN pre.kernel child postRoot
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:426:  rw [Dregg2.Circuit.Spec.AccountGrowth.execFullA_spawnA]
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:427:  exact (Dregg2.Circuit.Spec.AccountGrowth.spawnChainA_iff_spec pre actor child target post).mpr
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:464:-- so `gAccountsGrow` FAILS for it — a no-op birth is rejected.
metatheory/Dregg2/Circuit/RotatedKernelRefinementBirth.lean:479:§2–§4 force the growth from `*GenuineEncodes.gate`, the MODELLED `gAccountsGrow` the decode ASSERTS —
metatheory/Dregg2/Circuit/CircuitCompletenessRecord.lean:80:open Dregg2.Circuit.StateCommit (AccountsWF compressNInjective)
metatheory/Dregg2/Circuit/CircuitCompletenessRecord.lean:158:  frAccounts          := hspec.2.2.2.1
metatheory/Dregg2/Circuit/CircuitCompletenessRecord.lean:199:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessRecord.lean:230:  frAccounts          := hspec.2.2.1
metatheory/Dregg2/Circuit/CircuitCompletenessRecord.lean:270:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessRecord.lean:299:  frAccounts          := hspec.2.1
metatheory/Dregg2/Circuit/CircuitCompletenessRecord.lean:338:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessRecord.lean:391:  frAccounts          := hspec.2.2.2.1
metatheory/Dregg2/Circuit/CircuitCompletenessRecord.lean:435:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessRecord.lean:485:  frAccounts          := hspec.2.2.2.2.1
metatheory/Dregg2/Circuit/CircuitCompletenessRecord.lean:527:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessRecord.lean:572:  frAccounts          := hspec.2.2.2.1
metatheory/Dregg2/Circuit/CircuitCompletenessRecord.lean:612:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/CircuitCompletenessRecord.lean:656:  frAccounts          := hspec.2.2.2.1
metatheory/Dregg2/Circuit/CircuitCompletenessRecord.lean:695:    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
metatheory/Dregg2/Circuit/Argus/Effects/ReceiptArchive.lean:99:`compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`/`logHashInjective` portals + `AccountsWF` on
metatheory/Dregg2/Circuit/Argus/Effects/ReceiptArchive.lean:116:  (AccountsWF compressNInjective cellLeafInjective RestHashIffFrame logHashInjective)
metatheory/Dregg2/Circuit/Argus/Effects/ReceiptArchive.lean:294:    RestHashIffFrame S.RH`, `hLog : logHashInjective S.LH`) and `AccountsWF` on BOTH kernels (`hwf`,
metatheory/Dregg2/Circuit/Argus/Effects/ReceiptArchive.lean:312:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/Inst/setPermissionsA.lean:171:    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/setPermissionsA.lean:174:    exact ⟨hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/setPermissionsA.lean:176:  · rintro ⟨hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/setPermissionsA.lean:178:    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/setPermissionsA.lean:186:`logHashInjective` (the growing log exercises `cELog` non-trivially) + `AccountsWF` on both kernels. -/
metatheory/Dregg2/Circuit/Inst/setPermissionsA.lean:192:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/EffectCommit.lean:44:    `funext` (`c ∈ T` → `expectedLeaf`, `c ∈ accounts\T` → frozen, dead → `AccountsWF`), NEVER
metatheory/Dregg2/Circuit/EffectCommit.lean:45:    asserted. Carries ONLY injectivity portals + `AccountsWF` + a per-effect `GuardDecodes` obligation.
metatheory/Dregg2/Circuit/EffectCommit.lean:402:dst` / `c = cell`. It carries ONLY injectivity portals + `AccountsWF` + a per-effect `GuardDecodes`
metatheory/Dregg2/Circuit/EffectCommit.lean:423:frozen by the frame digest; dead → `AccountsWF`); the log + 16 fields from the rest/log gates. Carries
metatheory/Dregg2/Circuit/EffectCommit.lean:424:only the realizable Poseidon-CR injectivity portals + `AccountsWF` + the per-effect `GuardDecodes`. -/
metatheory/Dregg2/Circuit/EffectCommit.lean:430:    (hwf  : AccountsWF (E.view.toKernel pre)) (hwf' : AccountsWF (E.view.toKernel post))
metatheory/Dregg2/Circuit/Inst/balanceA.lean:184:  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/balanceA.lean:186:    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/balanceA.lean:188:  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/balanceA.lean:190:    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Argus/Effects/SetField.lean:51:    (`compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`/`logHashInjective`) + the `AccountsWF`
metatheory/Dregg2/Circuit/Argus/Effects/SetField.lean:75:`AccountsWF` assumptions enter ONLY inside the reused `setfield_circuit_full_sound` hypotheses, not in
metatheory/Dregg2/Circuit/Argus/Effects/SetField.lean:288:    (`hCompressN`/`hLeaf`/`hRest`/`hLog`, `AccountsWF` on both kernels — the EXACT hypotheses the keystone
metatheory/Dregg2/Circuit/Argus/Effects/SetField.lean:308:    (hwf : StateCommit.AccountsWF s.kernel) (hwf' : StateCommit.AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/CoordinatedTurnRefinement.lean:239:  AccountsWF sA.kernel ∧ AccountsWF sB.kernel ∧
metatheory/Dregg2/Circuit/CoordinatedTurnRefinement.lean:240:  AccountsWF sA'.kernel ∧ AccountsWF sB'.kernel ∧
metatheory/Dregg2/Circuit/Argus/Effects/SetVerificationKey.lean:48:    portals (`compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`/`logHashInjective`) + `AccountsWF`
metatheory/Dregg2/Circuit/Argus/Effects/SetVerificationKey.lean:95:`CommitSurface` cell-leaf/rest/log/compression injectivity portals + `AccountsWF` enter ONLY inside the
metatheory/Dregg2/Circuit/Argus/Effects/SetVerificationKey.lean:115:  (compressNInjective cellLeafInjective RestHashIffFrame logHashInjective AccountsWF)
metatheory/Dregg2/Circuit/Argus/Effects/SetVerificationKey.lean:288:    (`hwf : AccountsWF st.kernel`, `hwf' : AccountsWF st'.kernel`);
metatheory/Dregg2/Circuit/Argus/Effects/SetVerificationKey.lean:304:    (hwf : AccountsWF st.kernel) (hwf' : AccountsWF st'.kernel)
metatheory/Dregg2/Circuit/Argus/Effects/CreateCell.lean:69:open Dregg2.Circuit.Spec.AccountGrowth
metatheory/Dregg2/Circuit/Argus/Effects/CreateCell.lean:72:  (CreateCellArgs createCellE createCellA_full_sound RestIffNoAccountsBalBorn)
metatheory/Dregg2/Circuit/Argus/Effects/CreateCell.lean:241:    (hRest : RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
metatheory/Dregg2/Circuit/Spec/NoteGrowthAbstractBinding.lean:108:    (hspec : AccountGrowth.CreateCellSpec st actor newCell st')
metatheory/Dregg2/Circuit/Spec/NoteGrowthAbstractBinding.lean:116:    (hspec : AccountGrowth.SpawnSpec st actor child target st')
metatheory/Dregg2/Circuit/CouncilCommit.lean:107:the PROVED-preserved `AccountsWF`. The council commitment is a FIELD of one cell of that kernel, so it
metatheory/Dregg2/Circuit/CouncilCommit.lean:125:host's off-circuit `StaticThresholdSigPolicy`. Carries EXACTLY the StateCommit CR set + `AccountsWF`
metatheory/Dregg2/Circuit/CouncilCommit.lean:134:    (hwf : AccountsWF k) (hwf' : AccountsWF k')
metatheory/Dregg2/Circuit/CouncilCommit.lean:178:    (hwf : AccountsWF k) (hwf' : AccountsWF k')
metatheory/Dregg2/Circuit/CouncilCommit.lean:209:    (hwf : AccountsWF k) (hwf' : AccountsWF k')
metatheory/Dregg2/Circuit/Inst/delegateAttenA.lean:225:  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/delegateAttenA.lean:227:    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/delegateAttenA.lean:229:  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/delegateAttenA.lean:231:    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Argus/Effects/SetPermissions.lean:84:`compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`/`logHashInjective` portals + the two `AccountsWF`
metatheory/Dregg2/Circuit/Argus/Effects/SetPermissions.lean:112:-- digest-portal injectivity predicates + `AccountsWF` live in `StateCommit`; the circuit framework names
metatheory/Dregg2/Circuit/Argus/Effects/SetPermissions.lean:115:  (logHashInjective AccountsWF compressNInjective cellLeafInjective RestHashIffFrame)
metatheory/Dregg2/Circuit/Argus/Effects/SetPermissions.lean:287:    (`hwf : AccountsWF s.kernel`, `hwf' : AccountsWF s'.kernel`);
metatheory/Dregg2/Circuit/Argus/Effects/SetPermissions.lean:306:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/Argus/Effects/IncrementNonce.lean:78:`logHashInjective` portal hypotheses + the `AccountsWF` well-formedness side-conditions), not in the
metatheory/Dregg2/Circuit/Argus/Effects/IncrementNonce.lean:100:  (compressNInjective cellLeafInjective RestHashIffFrame logHashInjective AccountsWF)
metatheory/Dregg2/Circuit/Argus/Effects/IncrementNonce.lean:301:    well-formedness side-conditions (`hwf : AccountsWF s.kernel`, `hwf' : AccountsWF s'.kernel`);
metatheory/Dregg2/Circuit/Argus/Effects/IncrementNonce.lean:316:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/ClosureFanoutGenuine.lean:630:        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log)) ×'
metatheory/Dregg2/Circuit/ClosureFanoutGenuine.lean:631:        (post.log = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log →
metatheory/Dregg2/Circuit/ClosureFanoutGenuine.lean:667:        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log)) ×'
metatheory/Dregg2/Circuit/ClosureFanoutGenuine.lean:668:        (post.log = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log →
metatheory/Dregg2/Circuit/ClosureFanoutGenuine.lean:958:      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log)) ×'
metatheory/Dregg2/Circuit/ClosureFanoutGenuine.lean:959:      (post.log = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log →
metatheory/Dregg2/Circuit/ClosureFanoutGenuine.lean:970:      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log)) ×'
metatheory/Dregg2/Circuit/ClosureFanoutGenuine.lean:971:      (post.log = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log →
metatheory/Dregg2/Circuit/RotatedKernelRefinementLifecycle.lean:148:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementLifecycle.lean:179:  refine ⟨henc.guard, ?_, henc.logAdv, henc.frAccounts, henc.frCell, henc.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementLifecycle.lean:278:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementLifecycle.lean:333:  refine ⟨henc.guard, ?_, ?_, henc.logAdv, henc.frAccounts, henc.frCell, henc.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementLifecycle.lean:439:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementLifecycle.lean:472:  ⟨henc.guard, henc.cellMapMove, henc.logAdv, henc.frAccounts, henc.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementLifecycle.lean:495:  ⟨henc.guard, henc.cellMapMove, henc.logAdv, henc.frAccounts, henc.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementLifecycle.lean:572:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementLifecycle.lean:651:  refine ⟨rd.guard, ?_, rd.logAdv, rd.frAccounts, rd.frCell, rd.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementLifecycle.lean:710:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementLifecycle.lean:831:  refine ⟨rd.guard, ?_, ?_, rd.logAdv, rd.frAccounts, rd.frCell, rd.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementLifecycle.lean:921:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementLifecycle.lean:989:  ⟨rd.guard, rd.cellMapMoveDecodes hwrite, rd.logAdv, rd.frAccounts, rd.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementLifecycle.lean:1059:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementLifecycle.lean:1142:  refine ⟨rd.guard, ?_, rd.logAdv, rd.frAccounts, rd.frCell, rd.frCaps,
metatheory/Dregg2/Circuit/Inst/mintA.lean:175:  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/mintA.lean:177:    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/mintA.lean:179:  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/mintA.lean:181:    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Argus/Effects/PipelinedSend.lean:69:`AccountsWF` well-formedness preconditions of the v1 framework), not in the welded conclusion's
metatheory/Dregg2/Circuit/Argus/Effects/PipelinedSend.lean:89:  (compressNInjective cellLeafInjective RestHashIffFrame logHashInjective AccountsWF)
metatheory/Dregg2/Circuit/Argus/Effects/PipelinedSend.lean:214:    cells outside `accounts` hold `default`, the v1 `CommitSurface` `AccountsWF` requirement);
metatheory/Dregg2/Circuit/Argus/Effects/PipelinedSend.lean:229:    (hwf : AccountsWF st.kernel) (hwf' : AccountsWF st'.kernel)
metatheory/Dregg2/Circuit/Argus/Effects/MakeSovereign.lean:88:whole-function-digest path does not — `AccountsWF s.kernel` and `AccountsWF s'.kernel` (off-account
metatheory/Dregg2/Circuit/Argus/Effects/MakeSovereign.lean:117:  (AccountsWF compressNInjective cellLeafInjective RestHashIffFrame logHashInjective)
metatheory/Dregg2/Circuit/Argus/Effects/MakeSovereign.lean:295:    well-formedness preconditions `hwf : AccountsWF s.kernel`, `hwf' : AccountsWF s'.kernel` (the honest
metatheory/Dregg2/Circuit/Argus/Effects/MakeSovereign.lean:314:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/Argus/Effects/Refusal.lean:77:`compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`/`logHashInjective` portals + `AccountsWF` on
metatheory/Dregg2/Circuit/Argus/Effects/Refusal.lean:94:  (AccountsWF compressNInjective cellLeafInjective RestHashIffFrame logHashInjective)
metatheory/Dregg2/Circuit/Argus/Effects/Refusal.lean:265:    `hLog : logHashInjective S.LH`) and `AccountsWF` on BOTH kernels (`hwf`, `hwf'`);
metatheory/Dregg2/Circuit/Argus/Effects/Refusal.lean:282:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/Argus/Effects/EmitEvent.lean:114:  (compressNInjective cellLeafInjective RestHashIffFrame logHashInjective AccountsWF)
metatheory/Dregg2/Circuit/Argus/Effects/EmitEvent.lean:258:    (`hN`/`hL`/`hRest`/`hLog`) + `AccountsWF` on both states (`hwf`/`hwf'`, the descriptor's well-formed
metatheory/Dregg2/Circuit/Argus/Effects/EmitEvent.lean:274:    (hwf : AccountsWF st.kernel) (hwf' : AccountsWF st'.kernel)
metatheory/Dregg2/Circuit/Inst/refusalA.lean:166:    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/refusalA.lean:169:    exact ⟨hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/refusalA.lean:171:  · rintro ⟨hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/refusalA.lean:173:    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/refusalA.lean:181:exercises `cELog` non-trivially) + `AccountsWF` on both kernels. -/
metatheory/Dregg2/Circuit/Inst/refusalA.lean:187:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/RotatedKernelRefinementCellSeal.lean:241:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementCellSeal.lean:290:  refine ⟨henc.guard, ?_, henc.logAdv, henc.frAccounts, henc.frCell, henc.frCaps,
metatheory/Dregg2/Circuit/RotatedKernelRefinementCellSeal.lean:395:  frAccounts : post.kernel.accounts = pre.kernel.accounts
metatheory/Dregg2/Circuit/RotatedKernelRefinementCellSeal.lean:488:  refine ⟨rd.guard, ?_, rd.logAdv, rd.frAccounts, rd.frCell, rd.frCaps,
metatheory/Dregg2/Circuit/Inst/revoke.lean:221:  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/revoke.lean:223:    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/revoke.lean:225:  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/revoke.lean:227:    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Spec/accountgrowth.lean:63:namespace Dregg2.Circuit.Spec.AccountGrowth
metatheory/Dregg2/Circuit/Spec/accountgrowth.lean:644:end Dregg2.Circuit.Spec.AccountGrowth
metatheory/Dregg2/Circuit/Inst/receiptArchiveLifecycleA.lean:146:  · rintro ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSC, hFac,
metatheory/Dregg2/Circuit/Inst/receiptArchiveLifecycleA.lean:148:    exact ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSC, hFac,
metatheory/Dregg2/Circuit/Inst/receiptArchiveLifecycleA.lean:150:  · rintro ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSC, hFac,
metatheory/Dregg2/Circuit/Inst/receiptArchiveLifecycleA.lean:152:    exact ⟨hg, hlif, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSC, hFac,
metatheory/Dregg2/Circuit/TurnEmit.lean:88:  (logHashInjective compressNInjective RestHashIffFrame AccountsWF cellLeafInjective)
metatheory/Dregg2/Circuit/TurnEmit.lean:94:open Dregg2.Circuit.Inst.CreateCellA (RestIffNoAccountsBalBorn)
metatheory/Dregg2/Circuit/TurnEmit.lean:418:    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
metatheory/Dregg2/Circuit/TurnEmit.lean:464:      exact createCell_emitted_refines_spec S LE_cell cN hN hLE_cell DBal hDBal DSide hDSide hRestAccounts
metatheory/Dregg2/Circuit/TurnEmit.lean:549:        DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull
metatheory/Dregg2/Circuit/Inst/exerciseA.lean:147:/-- **`AccountsWF` survives the hold post-state** (kernel frozen). -/
metatheory/Dregg2/Circuit/Inst/exerciseA.lean:149:    (hwf : AccountsWF st.kernel) : AccountsWF (exerciseHoldState st actor).kernel := by
metatheory/Dregg2/Circuit/Inst/exerciseA.lean:187:  · rintro ⟨hguard, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/exerciseA.lean:190:      recordKernel_eq_of_fields hAcc hcell hCaps hNul hRev hCom hBal hSC hFac hLif hDC hDel
metatheory/Dregg2/Circuit/Inst/exerciseA.lean:209:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/Inst/exerciseA.lean:243:    (hwf : AccountsWF pre.kernel) (hwf' : AccountsWF holdPost.kernel)
metatheory/Dregg2/Circuit/Inst/exerciseA.lean:260:    (hwf : AccountsWF pre.kernel)
metatheory/Dregg2/Circuit/Inst/exerciseA.lean:282:    (hwf : AccountsWF pre.kernel)
metatheory/Dregg2/Circuit/Inst/spawnA.lean:8:ADDITIVE: imports `AccountsCommit`, `BornEmptyCommit`, `EffectCommit5`, `Spec/accountgrowth`; edits none.
metatheory/Dregg2/Circuit/Inst/spawnA.lean:10:import Dregg2.Circuit.AccountsCommit
metatheory/Dregg2/Circuit/Inst/spawnA.lean:26:open Dregg2.Circuit.AccountsCommit
metatheory/Dregg2/Circuit/Inst/spawnA.lean:29:open Dregg2.Circuit.Spec.AccountGrowth
metatheory/Dregg2/Circuit/Inst/spawnA.lean:92:def expectedAccounts (s : RecChainedState) (args : SpawnArgs) : Finset CellId :=
metatheory/Dregg2/Circuit/Inst/spawnA.lean:98:  accountsComponent LE cN hN hLE expectedAccounts
metatheory/Dregg2/Circuit/Inst/spawnA.lean:249:    SpawnCircuitSpec, spawnGuardProp, spawnAdmit, expectedAccounts, readSpawnCreateLeg,
metatheory/Dregg2/Circuit/Inst/spawnA.lean:274:    spawnGuardProp, spawnAdmit, expectedAccounts, readSpawnCreateLeg, expectedSpawnCreateLeg,
metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:354:`siteDigestsAcc` produces the list of resolved digests for the sites, in order, each site
metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:358:/-- **`siteDigestsAcc hash env acc sites`** — the head-first accumulator: `acc` holds the digests
metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:363:def siteDigestsAcc (hash : List ℤ → ℤ) (env : VmRowEnv) :
metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:368:    siteDigestsAcc hash env (acc ++ [d]) ss
metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:372:  siteDigestsAcc hash env [] sites
metatheory/Dregg2/Circuit/Inst/refreshDelegationA.lean:156:  · rintro ⟨hg, hprod, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSC, hFac,
metatheory/Dregg2/Circuit/Inst/refreshDelegationA.lean:159:    exact ⟨hg, hprod.1, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSC, hFac,
metatheory/Dregg2/Circuit/Inst/refreshDelegationA.lean:161:  · rintro ⟨hg, hdgs, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hSC, hFac,
metatheory/Dregg2/Circuit/Inst/refreshDelegationA.lean:163:    exact ⟨hg, by rw [Prod.mk.injEq]; exact ⟨hdgs, hstamp⟩, hlog, hAcc, hCell, hCaps, hNul, hRev,
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRefreshDelegation.lean:358:  obtain ⟨_hguard, _hdeleg, _hlog, _hAcc, _hCell, hcaps, _⟩ := hspec
metatheory/Dregg2/Circuit/Inst/burnA.lean:176:  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/burnA.lean:178:    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/burnA.lean:180:  · rintro ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/burnA.lean:182:    exact ⟨hg, hbal, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Emit/EffectVmEmitSpawn.lean:309:open Dregg2.Circuit.Spec.AccountGrowth (SpawnSpec SpawnFullSpec spawnCapsMap execSpawnA_iff_spec)
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBundleFold.lean:101:def firstAccBind : VmConstraint2 :=
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBundleFold.lean:105:def lastAccBind : VmConstraint2 :=
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBundleFold.lean:119:  , firstAccBind
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBundleFold.lean:120:  , lastAccBind
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBundleFold.lean:165:  have hmem : lastAccBind ∈ bundleFoldDescriptor.constraints := by
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBundleFold.lean:169:  -- `lastAccBind` on the last row asserts `loc acc_out = pub final` (the `isLast = true` hyp
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBundleFold.lean:171:  simp only [lastAccBind, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:11:(`light_client_verifies_whole_history`), with an apex anti-ghost (tamper any seam ⇒ reject).
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:38:  * `argus_strand_light_client` — **THE APEX.** Threaded into `light_client_verifies_whole_history`
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:59:   (`RecursiveAggregation`) names `EngineSound.leaf_sound : verify p = true → recCexec s.pre s.turn =
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:81:  (ChainStep StateChained ChainBound Continues lastStateOf foldedFinalRoot stateRoot zeroTurn
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:85:  (Aggregate EngineSound AggregateAttests light_client_verifies_whole_history
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:86:   attested_history_is_run attested_history_conserves tampered_aggregate_cannot_bind
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:87:   leaf_pairing_defeats_swap)
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:216:(`EngineSound`, REUSED) — learns the whole Argus history executed correctly, is correctly
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:221:`AggregateAttests`: EVERY Argus turn executed correctly per the verified executor (`recCexec` — the
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:224:engine-soundness hypotheses (`EngineSound`, REUSED verbatim). The strand the layer's headline talks
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:228:merely some list satisfying `EngineSound`. -/
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:237:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:239:    AggregateAttests Proof CH RH cmb compress compressN agg g steps
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:243:  ⟨light_client_verifies_whole_history Proof verify CH RH cmb compress compressN agg g steps es hroot,
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:258:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:291:      contradictory (`tampered_aggregate_cannot_bind`, REUSED).
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:292:  (b) the leaf↔step PAIRING binds each Argus turn's proof to ITS OWN step (`leaf_pairing_defeats_swap`,
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:299:verifies, the binding soundness would force `ChainBound [s, s']`, which is FALSE. Hence the aggregate
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:301:moves the §8 full-state root) breaks the binding. Rides the layer's `tampered_aggregate_cannot_bind`. -/
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:308:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g [s, s'])
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:313:  tampered_aggregate_cannot_bind Proof verify CH RH cmb compress compressN agg g s s' es hbreak hverify
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:318:turn while exporting this step's roots. Rides the layer's `leaf_pairing_defeats_swap`. -/
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:327:    (es : EngineSound Proof verify CH RH cmb compress compressN agg g (s :: ss))
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:330:  leaf_pairing_defeats_swap Proof verify CH RH cmb compress compressN agg g p ps s ss hagg es hleafverify
metatheory/Dregg2/Circuit/Inst/emitEventA.lean:162:    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/emitEventA.lean:165:    exact ⟨hg, hlog, hAcc, hcell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/emitEventA.lean:167:  · rintro ⟨hg, hlog, hAcc, hcell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/emitEventA.lean:169:    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/emitEventA.lean:181:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCreateCell.lean:60:open Dregg2.Circuit.Spec.AccountGrowth
metatheory/Dregg2/Circuit/Emit/EffectVmEmitPipelinedSend.lean:52:open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective cellLeafInjective RestHashIffFrame AccountsWF)
metatheory/Dregg2/Circuit/Emit/EffectVmEmitPipelinedSend.lean:336:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/Inst/revokeDelegationA.lean:211:  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/revokeDelegationA.lean:213:    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/revokeDelegationA.lean:215:  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/revokeDelegationA.lean:217:    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/revokeDelegationFullA.lean:223:  · rintro ⟨hg, hcaps, hstep, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/revokeDelegationFullA.lean:227:    exact ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/revokeDelegationFullA.lean:229:  · rintro ⟨hg, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/revokeDelegationFullA.lean:231:    refine ⟨hg, hcaps, ?_, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/attenuateA.lean:218:  · rintro ⟨hInb, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/attenuateA.lean:220:    exact ⟨hInb, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/attenuateA.lean:222:  · rintro ⟨hInb, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/attenuateA.lean:224:    exact ⟨hInb, hcaps, hlog, hAcc, hCell, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/noteCreateA.lean:207:  · rintro ⟨hg, hcom, hlog, hAcc, hCell, hCaps, hNul, hRev, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/noteCreateA.lean:209:    exact ⟨hg, hcom, hlog, hAcc, hCell, hCaps, hNul, hRev, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/noteCreateA.lean:211:  · rintro ⟨hg, hcom, hlog, hAcc, hCell, hCaps, hNul, hRev, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/noteCreateA.lean:213:    exact ⟨hg, hcom, hlog, hAcc, hCell, hCaps, hNul, hRev, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/createCellFromFactoryA.lean:10:ADDITIVE: imports `AccountsCommit`, `BornEmptyCommit`, `EffectCommit5`, `Spec/factorycreation`; edits none.
metatheory/Dregg2/Circuit/Inst/createCellFromFactoryA.lean:12:import Dregg2.Circuit.AccountsCommit
metatheory/Dregg2/Circuit/Inst/createCellFromFactoryA.lean:28:open Dregg2.Circuit.AccountsCommit
metatheory/Dregg2/Circuit/Inst/createCellFromFactoryA.lean:119:def expectedAccounts (s : RecChainedState) (args : CreateFromFactoryArgs) : Finset CellId :=
metatheory/Dregg2/Circuit/Inst/createCellFromFactoryA.lean:139:  accountsComponent LE cN hN hLE expectedAccounts
metatheory/Dregg2/Circuit/Inst/createCellFromFactoryA.lean:283:    factoryAdmit, expectedAccounts, expectedBal, expectedCell, expectedSlotCaveats,
metatheory/Dregg2/Circuit/Inst/setProgramA.lean:160:    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/setProgramA.lean:163:    exact ⟨hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/setProgramA.lean:165:  · rintro ⟨hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/setProgramA.lean:167:    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/setProgramA.lean:175:exercises `cELog` non-trivially) + `AccountsWF` on both kernels. -/
metatheory/Dregg2/Circuit/Inst/setProgramA.lean:181:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Circuit/Inst/cellDestroyA.lean:149:  · rintro ⟨hg, hlif, hdc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
metatheory/Dregg2/Circuit/Inst/cellDestroyA.lean:151:    exact ⟨hg, hlif, hdc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
metatheory/Dregg2/Circuit/Inst/cellDestroyA.lean:153:  · rintro ⟨hg, hlif, hdc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
metatheory/Dregg2/Circuit/Inst/cellDestroyA.lean:155:    exact ⟨hg, hlif, hdc, hlog, hAcc, hCell, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac,
metatheory/Dregg2/Circuit/Inst/makeSovereignA.lean:161:    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/makeSovereignA.lean:164:    exact ⟨hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/makeSovereignA.lean:166:  · rintro ⟨hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/makeSovereignA.lean:168:    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
metatheory/Dregg2/Circuit/Inst/makeSovereignA.lean:181:    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
metatheory/Dregg2/Exec/DfaRouting.lean:17:`Crypto.Dfa`'s `Step`/`stepValid`/`chained`/`DfaAccepts` verbatim as the run shape, and add the
metatheory/Dregg2/Exec/DfaRouting.lean:35:    (`Crypto.Dfa.DfaAccepts δ start accepting route`). Fail-closed: the delivery constructor
metatheory/Dregg2/Exec/DfaRouting.lean:85:/-! ## §2 — A route is an accepting run (REUSING `Crypto.Dfa.DfaAccepts`).
metatheory/Dregg2/Exec/DfaRouting.lean:91:`accepting` node (a valid destination). This is **precisely** `Crypto.Dfa.DfaAccepts δ start
metatheory/Dregg2/Exec/DfaRouting.lean:98:/-- **`IsAcceptingRun rd route`** — the route is an *accepting run* of the routing DFA: it starts
metatheory/Dregg2/Exec/DfaRouting.lean:100:valid destination (`rd.accepting`). This IS `Crypto.Dfa.DfaAccepts` — the routing automaton's
metatheory/Dregg2/Exec/DfaRouting.lean:102:def IsAcceptingRun (rd : RoutingDfa Node Hop) (route : Route Node Hop) : Prop :=
metatheory/Dregg2/Exec/DfaRouting.lean:103:  DfaAccepts rd.δ rd.start rd.accepting route
metatheory/Dregg2/Exec/DfaRouting.lean:131:  routes : IsAcceptingRun rd route
metatheory/Dregg2/Exec/DfaRouting.lean:140:    IsAcceptingRun rd d.route ∧ d.route.dest = some d.dest :=
metatheory/Dregg2/Exec/DfaRouting.lean:269:    IsAcceptingRun gr.rd gd.delivery.route ∧
metatheory/Dregg2/Exec/DfaRouting.lean:314:    IsAcceptingRun (commHopDfa a b s) (commHopRoute a b s) := by
metatheory/Dregg2/Exec/DfaRouting.lean:331:    GStep (GlobalType.comm a b s k) k ∧ IsAcceptingRun (commHopDfa a b s) (commHopRoute a b s) :=
metatheory/Dregg2/Exec/DfaRouting.lean:369:theorem goodRoute_accepts : IsAcceptingRun lineDfa goodRoute := by
metatheory/Dregg2/Exec/DfaRouting.lean:390:example : IsAcceptingRun lineDfa goodDelivery.route ∧ goodDelivery.route.dest = some 2 :=
metatheory/Dregg2/Exec/DfaRouting.lean:398:theorem badRoute_rejected : ¬ IsAcceptingRun lineDfa badRoute := by
metatheory/Dregg2/Exec/DfaRouting.lean:445:example : IsAcceptingRun lineGuarded.rd goodGuardedDelivery.delivery.route ∧
metatheory/Dregg2/Exec/DistributedExports.lean:119:  | [hS, gSeg, heSeg, geSeg] =>
metatheory/Dregg2/Exec/DistributedExports.lean:121:      let gS ← stripReq? "g=" gSeg
metatheory/Dregg2/Exec/DistributedExports.lean:122:      let heS ← stripReq? "he=" heSeg
metatheory/Dregg2/Exec/DistributedExports.lean:123:      let geS ← stripReq? "ge=" geSeg
metatheory/Dregg2/Exec/DistributedExports.lean:253:  | [hS, fSeg, sSeg] =>
metatheory/Dregg2/Exec/DistributedExports.lean:255:      let fS ← stripReq? "f=" fSeg
metatheory/Dregg2/Exec/DistributedExports.lean:256:      let sS ← stripReq? "s=" sSeg
metatheory/Dregg2/Exec/DistributedExports.lean:344:  | [qS, eSeg] =>
metatheory/Dregg2/Exec/DistributedExports.lean:346:      let eS ← stripReq? "e=" eSeg
metatheory/Dregg2/Exec/DistributedExports.lean:432:  | [yS, nSeg, nnSeg, tSeg] =>
metatheory/Dregg2/Exec/DistributedExports.lean:434:      let nS ← stripReq? "n=" nSeg
metatheory/Dregg2/Exec/DistributedExports.lean:435:      let nnS ← stripReq? "N=" nnSeg
metatheory/Dregg2/Exec/DistributedExports.lean:436:      let tS ← stripReq? "t=" tSeg
metatheory/Dregg2/Exec/DistributedExports.lean:533:  | [gS, aSeg, bSeg] =>
metatheory/Dregg2/Exec/DistributedExports.lean:535:      let aS ← stripReq? "a=" aSeg
metatheory/Dregg2/Exec/DistributedExports.lean:536:      let bS ← stripReq? "b=" bSeg
metatheory/Dregg2/Exec/DistributedExports.lean:635:  | [bS, dSeg] =>
metatheory/Dregg2/Exec/DistributedExports.lean:637:      let dS ← stripReq? "D=" dSeg
metatheory/Dregg2/Exec/CustodyReceipt.lean:18:nothing anywhere proves an HONEST relay can't be slashed by a fabricated one. Accountability —

The important implementation details are now clear: leaf exposes `[old,new,1,H(old,new)]` from descriptor public targets, combine exposes `[L.first,R.last,L.count+R.count,H(L.acc,R.acc)]` with continuity, and the host compares the root exposed segment to the carried claim. I’m checking the aggregation hook names so the Lean sketch can keep the proof obligations split cleanly.
exec
/bin/zsh -lc 'rg -n "aggregate_tree|combine|last_new|first_old|SEG_FIRST_OLD|SEG_LAST_NEW|SEG_COUNT|expose_as_public_output|root_exposed|NUM_CHAIN_CLAIMS|claim" circuit-prove/src/ivc_turn_chain.rs' in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
75://! in-circuit by the wrap layer. A claimed `(old_root, new_root)` with no
110://! `CODEX-IVC-REVIEW-2.md`) found a forged whole-chain claim the verifier ACCEPTS: a
112://! B. The root cause was that the chain claim came from a SEPARATE `TurnChainBindingAir`
114://! descriptor leaves' ACTUAL roots — so the binding leaf (and its claim) could be swapped
119://! `[first_old, last_new, count, acc]`, exposed through the `expose_claim` table and BOUND
121://!   - **leaf** ([`prove_descriptor_leaf_rotated_with_segment`]): `first_old`/`last_new`
123://!     the child's `air_public_targets`), `count = 1`, `acc = H(first_old, last_new)`. So
126://!   - **aggregation combine** ([`aggregate_tree`]): both children expose a segment; the
127://!     combine constrains STATE CONTINUITY (`L.last_new == R.first_old`), COUNT additivity
131://!     tooth): the root's exposed segment `[first_old, last_new, count, acc]` is the
132://!     whole-chain claim derived BY CONSTRUCTION from the real descriptor leaves; the host
135://!     expose B's endpoints, so a B-claim against an A-execution is REJECTED.
137://! The executable witness `mixed_root_forgery_executes_A_claims_B`
143://! `expose_claim` channel + the aggregation expose hook (which exposes the
144://! `air_public_targets` AND lets the combine add cross-child constraints) + the in-circuit
215:/// The BabyBear prime modulus `2^31 - 2^27 + 1`. The `count` / `num_turns` chain claim is a
221:/// circuit (and every expose/combine hook) builds over.
232:/// The number of exposed chain claims: `[first_old, last_new, count, acc_0..acc_{W-1}]`
235:pub const NUM_CHAIN_CLAIMS: usize = SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH;
237:/// Segment field lanes (the order they are exposed in the `expose_claim` table).
238:pub const SEG_FIRST_OLD: usize = 0;
239:pub const SEG_LAST_NEW: usize = 1;
240:pub const SEG_COUNT: usize = 2;
244:/// A segment is exactly [`NUM_CHAIN_CLAIMS`] base-field lanes.
245:pub const SEG_WIDTH: usize = NUM_CHAIN_CLAIMS;
288:/// through the `expose_claim` table (which reads each target's coeff-0) and matched
297:/// Used (i) at the descriptor leaf to seed `acc = commit([first_old, last_new])`, and
302:/// EXACT segment combine when it reconstructs the fold from the public building blocks.
442:/// Find the instance index of the `expose_claim` non-primitive table in a batch
446:/// Returns `None` if the proof carries no exposed-claim table.
447:pub(crate) fn expose_claim_instance_index(
454:        .position(|e| e.op_type.as_str() == "expose_claim")
458:/// Read the `expose_claim` table's public values from a batch proof (the 4 chain
459:/// claims, host-readable and bus-bound to the verified history). Returns `None`
460:/// if there is no exposed-claim table.
461:fn root_exposed_claims(
467:        .find(|e| e.op_type.as_str() == "expose_claim")?;
535:        /// The root this turn claims to consume.
562:    /// **The claimed chain publics are unattested.** The carried
565:    /// a relabeled (spliced) public claim.
608:                "claimed chain publics are not attested by the carried binding proof \
830:/// (the base-field values it exposes through the `expose_claim` table):
831:/// `[first_old, last_new, count, acc_0..acc_{W-1}]` (`W = SEG_DIGEST_WIDTH`). The prover
832:/// folds these the SAME way the in-circuit combine does so it knows the root segment
833:/// (hence the chain claims) to carry.
836:    pub first_old: BabyBear,
837:    pub last_new: BabyBear,
843:/// The per-turn (descriptor-leaf) segment: `first_old = old_root`, `last_new =
848:        first_old: old_root,
849:        last_new: new_root,
855:/// Combine two adjacent segments (the host mirror of the aggregation combine):
856:/// continuity `l.last_new == r.first_old` (caller-checked upstream as `ChainBreak`),
857:/// `first_old = l.first_old`, `last_new = r.last_new`, `count = l.count + r.count`,
859:fn combine_seg(l: HostSeg, r: HostSeg) -> HostSeg {
864:        first_old: l.first_old,
865:        last_new: r.last_new,
872:/// left-to-right binary tree (with odd-element carry) that [`aggregate_tree`] runs
873:/// in-circuit — so the host-computed root `[first_old, last_new, count, acc]`
887:            next.push(combine_seg(level[i], level[i + 1]));
1055:/// leaf now folds into the SAME `aggregate_tree` / chain machinery.
1152:/// AND emit its constant-size ordered SEGMENT through the `expose_claim` table, BOUND
1155:///   `Seg = [first_old, last_new, count, acc]`
1156:///     first_old := descriptor PI `V1_PI_COUNT`   (the rotated OLD-state commitment)
1157:///     last_new  := descriptor PI `V1_PI_COUNT+1` (the rotated NEW-state commitment)
1159:///     acc       := H(first_old, last_new)        (the per-turn ordered-history seed)
1161:/// Because `first_old`/`last_new` are READ from the descriptor proof's own verified
1166:/// real descriptor leaves and combined up the tree.
1205:        let first_old = main[V1_PI_COUNT];
1206:        let last_new = main[V1_PI_COUNT + 1];
1210:        let acc = seg_poseidon_commit(cb, &[first_old, last_new]);
1212:        seg.push(first_old);
1213:        seg.push(last_new);
1217:        cb.expose_as_public_output(&seg);
1248:    /// claimed publics below AGAINST A PROOF instead of trusting bare fields:
1447:/// envelope (the envelope's `vk_fingerprint_hex` is a discarded claim). A root of a
1575:/// This exists to make the soundness claim falsifiable: the host gate in
1585:    claimed_selectors: &[usize],
1588:    prove_chain_core_rotated(&refs, claimed_selectors)
1641:    // mirrors the in-circuit combine's continuity constraint and fails closed BEFORE any proving.
1658:    // pairwise binary tree `aggregate_tree` runs in-circuit. Its four fields ARE the four chain
1659:    // claims the artifact carries — derived from the REAL descriptor leaves' rotated roots, NOT
1662:    let genesis_root = root_seg.first_old;
1663:    let final_root = root_seg.last_new;
1675:    // the root's exposed segment is what binds the claim now). It is NOT folded into the root.
1682:    // (first_old/last_new bound to the descriptor's real roots, count=1, acc=H(old,new)).
1698:    let root = aggregate_tree(batch_leaves, &config, &backend, &params)?;
1756:fn aggregate_tree(
1773:            // ordered segment `[first_old, last_new, count, acc]` in their `expose_claim`
1774:            // table. Read both, constrain them to combine soundly (state continuity, count
1776:            // separate binding leaf — the whole-chain claim is the fold of the REAL
1778:            let left_idx = expose_claim_instance_index(&proofs[i].0).ok_or_else(|| {
1780:                    reason: "left aggregation child carries no segment (expose_claim) table"
1784:            let right_idx = expose_claim_instance_index(&proofs[i + 1].0).ok_or_else(|| {
1786:                    reason: "right aggregation child carries no segment (expose_claim) table"
1805:                // (1) STATE CONTINUITY: L.last_new == R.first_old. The left subtree's final
1810:                // `ExprId::ZERO` witness (`WitnessId(0)`): when one operand (`l.last_new`, a real
1817:                cb.connect(l[SEG_LAST_NEW], r[SEG_FIRST_OLD]);
1819:                // (2) parent segment: span [L.first_old .. R.last_new], count L+R, ordered
1823:                let first_old = l[SEG_FIRST_OLD];
1824:                let last_new = r[SEG_LAST_NEW];
1825:                let count = cb.add(l[SEG_COUNT], r[SEG_COUNT]);
1833:                parent.push(first_old);
1834:                parent.push(last_new);
1838:                cb.expose_as_public_output(&parent);
1873:///      `[first_old, last_new, count, acc]` (derived by construction from the
1874:///      real descriptor leaves and combined up the tree) must equal the carried
1877:///      endpoints, so a B-claim against an A-execution is refused. (The carried
1910:///   3. **The segment tooth** — the root's exposed ordered segment `[first_old,
1911:///      last_new, count, acc]` (built from the real descriptor leaves, combined up
1925:    // binds the claim to the real descriptor leaves). It is retained in the artifact for byte
1938:    // (2) The root. The root batch proof is produced by `aggregate_tree` at the rotated
1947:    // `expose_claim` non-primitive table whose `public_values` are the root's ORDERED SEGMENT
1948:    // `[first_old, last_new, count, acc]`. That segment is built BY CONSTRUCTION from the real
1949:    // descriptor leaves: each leaf's `first_old`/`last_new` are bound in-circuit to its
1950:    // descriptor proof's verified rotated roots, and the combine at each aggregation node
1951:    // enforces state continuity (`L.last_new == R.first_old`), count additivity, and the
1953:    // root-exposed segment is the WHOLE-CHAIN claim derived from the ACTUAL execution. The
1954:    // carried claim must match it exactly. There is NO separate binding leaf to swap: a root
1955:    // that executed history A cannot expose B's endpoints, so a B-claim against an A-execution
1956:    // FAILS here (`genesis = A.first_old != B.genesis`, etc.).
1957:    let exposed = root_exposed_claims(root_proof).ok_or_else(|| {
1971:                "root-exposed segment {exposed:?} != carried claim {expected:?} \
1972:                 (the carried claim is not the fold of the real descriptor leaves)"
2008:/// [`aggregate_tree`] uses internally). The open work is the *driver*: a

exec
/bin/zsh -lc "sed -n '880,910p' circuit-prove/src/ivc_turn_chain.rs && sed -n '1510,1665p' circuit-prove/src/ivc_turn_chain.rs && sed -n '1710,1795p' circuit-prove/src/ivc_turn_chain.rs" in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
            leaf_seg(o, n)
        })
        .collect();
    while level.len() > 1 {
        let mut next: Vec<HostSeg> = Vec::with_capacity(level.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < level.len() {
            next.push(combine_seg(level[i], level[i + 1]));
            i += 2;
        }
        if i < level.len() {
            next.push(level[i]);
        }
        level = next;
    }
    level[0]
}

/// [`generate_chain_trace`] reading the ROTATED chain roots (PI 34/35) instead of the v1
/// OLD/NEW_COMMIT (PI 0/4). The binding leaf the rotated fold wraps therefore commits to the
/// rotated v9 commitments.
fn generate_chain_trace_rotated(
    turns: &[&FinalizedTurn],
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>, BabyBear), TurnChainError> {
    if turns.len() < 2 {
        return Err(TurnChainError::TooFewTurns { count: turns.len() });
    }
    for i in 1..turns.len() {
        let (_, prev_new) = rotated_roots(turns[i - 1]);
        let (this_old, _) = rotated_roots(turns[i]);
        if prev_new != this_old {
            reason: format!("root BatchStarkProof blob does not decode: {e}"),
        })?;
    root_proof
        .validate()
        .map_err(|e| TurnChainError::EnvelopeDecode {
            reason: format!("root BatchStarkProof failed structural validation: {e:?}"),
        })?;
    let binding_proof: RecursionCompatibleProof =
        postcard::from_bytes(binding_blob).map_err(|e| TurnChainError::EnvelopeDecode {
            reason: format!("binding Proof blob does not decode: {e}"),
        })?;
    verify_turn_chain_recursive_from_parts(
        &root_proof,
        &binding_proof,
        BabyBear::new(genesis_root),
        BabyBear::new(final_root),
        core::array::from_fn(|i| BabyBear::new(chain_digest[i])),
        num_turns,
        &RecursionVk(*vk_anchor),
    )
}

/// Fold K finalized-turn proofs into ONE whole-chain recursive proof.
///
/// `turns` must be in the node's **finalized order** (the `tau`/blocklace order
/// from `node::blocklace_sync::poll_finalized_blocks`). Each turn's `new_root`
/// must be the next turn's `old_root` — the temporal binding the chain leaf
/// enforces both host-side and in-circuit.
///
/// Steps:
///   1. host admission: every turn's production descriptor proof verifies
///      SELECTOR-BOUND through the Lean descriptor verifier
///      ([`verify_descriptor_participant`]) — this also determines each turn's
///      descriptor selector;
///   2. host-side: >= 2 turns, sequential continuity;
///   3. prove the chain-binding leaf (rejects a broken order in-circuit too);
///   4. re-prove each turn's REAL descriptor AIR over its OWN execution trace
///      as a recursion-compatible uni-STARK ([`prove_descriptor_leaf`]);
///   5. wrap every leaf in its own IN-CIRCUIT verifier layer (uni->batch) —
///      per-turn execution soundness is verified inside the recursion, not
///      merely at the host gate;
///   6. pairwise-aggregate all batch leaves up a binary tree to ONE root.
///
/// The host gate (step 1) is an admission discipline, NOT the soundness
/// boundary: a prover that skips it (see
/// [`prove_turn_chain_recursive_without_host_gate`]) still cannot produce a
/// verifying root for a forged turn, because steps 4-5 have no satisfying
/// witness for a forged `(old_root, new_root)`.
pub fn prove_turn_chain_recursive(
    turns: &[FinalizedTurn],
) -> Result<WholeChainProof, TurnChainError> {
    // (1) host admission: descriptor-verify every turn, selector-bound.
    let mut selectors = Vec::with_capacity(turns.len());
    for (i, t) in turns.iter().enumerate() {
        let s = verify_descriptor_participant(&t.participant)
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
        selectors.push(s);
    }
    let refs: Vec<&FinalizedTurn> = turns.iter().collect();
    prove_chain_core_rotated(&refs, &selectors)
}

/// **THE UNGATED PROVER (tamper surface).** Fold a chain WITHOUT the host-side
/// descriptor admission, taking the prover's CLAIMED selectors at face value.
///
/// This exists to make the soundness claim falsifiable: the host gate in
/// [`prove_turn_chain_recursive`] must NOT be load-bearing. A malicious prover
/// that skips it and feeds a forged turn (a post-commit lie in the PIs, a stub
/// trace, an absent/borrowed proof object) still has to satisfy the REAL
/// descriptor AIR in-circuit at the leaf wrap — and a forged statement has no
/// satisfying witness, so the fold fails and no verifying root exists. The
/// tests `ungated_prover_with_forged_post_commit_cannot_produce_a_root` and
/// `ungated_prover_with_stub_leaf_cannot_produce_a_root` drive this path.
pub fn prove_turn_chain_recursive_without_host_gate(
    turns: &[FinalizedTurn],
    claimed_selectors: &[usize],
) -> Result<WholeChainProof, TurnChainError> {
    let refs: Vec<&FinalizedTurn> = turns.iter().collect();
    prove_chain_core_rotated(&refs, claimed_selectors)
}

// ============================================================================
// THE ROTATED whole-chain fold (Bucket-F: the ONLY fold — the v1 `prove_chain_core`
// + v1 leaf are deleted; `prove_turn_chain_recursive` routes straight here).
// ============================================================================

/// Fold K finalized turns into one whole-chain proof through the ROTATED leaf-wrap.
///
/// Identical in shape to [`prove_turn_chain_recursive`], but every per-turn leaf is the
/// rotated multi-table `Ir2BatchProof` (carried on `participant.rotated`), minted in-circuit
/// via [`prove_descriptor_leaf_rotated_with_config`] at [`ir2_leaf_wrap_config`] — NOT the v1
/// uni-STARK `EffectVmDescriptorAir` wrap. The whole tree (binding leaf + aggregation) runs at
/// the ONE wrap config, exactly as the aggregation gate
/// (`rotation_batchstark_leaf_smoke::two_rotated_leaves_aggregate_at_wrap_config`) proves it
/// folds. Every turn MUST carry a rotated leg (`participant.rotated == Some`); a missing leg
/// fails closed.
///
/// The temporal binding is read from the ROTATED commitments (PI 34/35 — the rotated trace's
/// before/after `state_commit` carriers), so the chain continuity tooth
/// (`prev.new_root == next.old_root`) binds the rotated v9 commitment.
pub fn prove_turn_chain_recursive_rotated(
    turns: &[FinalizedTurn],
) -> Result<WholeChainProof, TurnChainError> {
    // Host admission: descriptor-verify every turn, selector-bound (the v1 leg gate; the
    // rotated leaf re-proof is the soundness boundary, this is admission discipline).
    let mut selectors = Vec::with_capacity(turns.len());
    for (i, t) in turns.iter().enumerate() {
        let s = verify_descriptor_participant(&t.participant)
            .map_err(|reason| TurnChainError::TurnProofInvalid { index: i, reason })?;
        selectors.push(s);
    }
    let refs: Vec<&FinalizedTurn> = turns.iter().collect();
    prove_chain_core_rotated(&refs, &selectors)
}

/// The rotated fold core: like [`prove_chain_core`] but mints rotated native-batch leaves and
/// runs the whole tree at [`ir2_leaf_wrap_config`].
fn prove_chain_core_rotated(
    turns: &[&FinalizedTurn],
    selectors: &[usize],
) -> Result<WholeChainProof, TurnChainError> {
    if selectors.len() != turns.len() {
        return Err(TurnChainError::RecursionFailed {
            reason: format!(
                "selector count {} != turn count {}",
                selectors.len(),
                turns.len()
            ),
        });
    }
    // Host-side continuity (the `ChainBreak` tooth: `prev.new_root == next.old_root`). This
    // mirrors the in-circuit combine's continuity constraint and fails closed BEFORE any proving.
    let _ = generate_chain_trace_rotated_continuity(turns)?;

    // CODEX #5 — the count field is a BabyBear (mod p), so `num_turns` must be `< p` for the
    // exposed `count` lane to faithfully equal the real turn count (no modular wrap). A single
    // K-fold window of `>= p ~ 2^31` turns is far past any real finality stream, but we bound it
    // explicitly rather than rely on the implicit ceiling.
    if (turns.len() as u64) >= BABY_BEAR_MODULUS as u64 {
        return Err(TurnChainError::RecursionFailed {
            reason: format!(
                "num_turns {} >= BabyBear modulus {BABY_BEAR_MODULUS} (count lane would wrap mod p)",
                turns.len()
            ),
        });
    }

    // The ROOT SEGMENT the host computes by folding the per-turn leaf segments through the SAME
    // pairwise binary tree `aggregate_tree` runs in-circuit. Its four fields ARE the four chain
    // claims the artifact carries — derived from the REAL descriptor leaves' rotated roots, NOT
    // from a separate (swappable) binding leaf.
    let root_seg = compute_root_segment(turns);
    let genesis_root = root_seg.first_old;
    let final_root = root_seg.last_new;
    let chain_digest = root_seg.acc;

/// Host-side continuity check ONLY (the `ChainBreak` tooth), extracted so the rotated fold no
/// longer needs the full binding-trace generation just to validate ordering. Returns `Ok(())`
/// when `>= 2` turns and every `prev.new_root == next.old_root`.
fn generate_chain_trace_rotated_continuity(turns: &[&FinalizedTurn]) -> Result<(), TurnChainError> {
    if turns.len() < 2 {
        return Err(TurnChainError::TooFewTurns { count: turns.len() });
    }
    for i in 1..turns.len() {
        let (_, prev_new) = rotated_roots(turns[i - 1]);
        let (this_old, _) = rotated_roots(turns[i]);
        if prev_new != this_old {
            return Err(TurnChainError::ChainBreak {
                index: i,
                expected_old_root: prev_new.0,
                found_old_root: this_old.0,
            });
        }
    }
    Ok(())
}

/// Build the chain-binding leaf reading the ROTATED chain roots (PI 34/35), at the wrap config.
///
/// **Bucket-F fix:** the binding-leaf inner proof MUST be minted at [`ir2_leaf_wrap_config`]
/// (log_blowup 6), the SAME FRI engine the whole rotated tree runs at — it is wrapped and
/// aggregated with the rotated descriptor leaves at that config, so proving it at the default
/// `create_recursion_config` (log_blowup 3) and then wrapping at the wrap config raises
/// `InvalidProofShape("Fewer siblings in proof than op_ids provided")` in-circuit.
fn prove_chain_binding_leaf_rotated(
    turns: &[&FinalizedTurn],
) -> Result<(RecursionCompatibleProof, Vec<BabyBear>), TurnChainError> {
    use crate::plonky3_recursion_impl::recursive::{
        prove_inner_for_air_with_config, verify_inner_for_air_with_config,
    };
    let (trace, pis, _digest) = generate_chain_trace_rotated(turns)?;
    let matrix = trace_to_matrix(&trace);
    let air = TurnChainBindingAir;
    let wrap_config = ir2_leaf_wrap_config();
    let proof = prove_inner_for_air_with_config(&air, matrix, &pis, &wrap_config);
    verify_inner_for_air_with_config(&air, &proof, &pis, &wrap_config)
        .map_err(|reason| TurnChainError::RecursionFailed { reason })?;
    Ok((proof, pis))
}

/// Fold a vector of batch-STARK proofs to ONE via 2-to-1 aggregation layers.
/// (Same binary-tree fold as [`joint_turn_recursive`](crate::joint_turn_recursive).)
fn aggregate_tree(
    mut proofs: Vec<RecursionOutput<DreggRecursionConfig>>,
    config: &DreggRecursionConfig,
    backend: &p3_recursion::FriRecursionBackendForExt<D, 16, 8, p3_recursion::ops::Poseidon2Config>,
    params: &ProveNextLayerParams,
) -> Result<RecursionOutput<DreggRecursionConfig>, TurnChainError> {
    if proofs.is_empty() {
        return Err(TurnChainError::RecursionFailed {
            reason: "no leaves to aggregate".to_string(),
        });
    }
    while proofs.len() > 1 {
        let mut next_level: Vec<RecursionOutput<DreggRecursionConfig>> =
            Vec::with_capacity(proofs.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < proofs.len() {
            // THE SEGMENT COMBINE (close of the mixed-root hole): BOTH children carry an
            // ordered segment `[first_old, last_new, count, acc]` in their `expose_claim`
            // table. Read both, constrain them to combine soundly (state continuity, count
            // additivity, ordered-digest fold), and expose the parent segment. There is no
            // separate binding leaf — the whole-chain claim is the fold of the REAL
            // descriptor leaves' segments.
            let left_idx = expose_claim_instance_index(&proofs[i].0).ok_or_else(|| {
                TurnChainError::RecursionFailed {
                    reason: "left aggregation child carries no segment (expose_claim) table"
                        .to_string(),
                }
            })?;
            let right_idx = expose_claim_instance_index(&proofs[i + 1].0).ok_or_else(|| {
                TurnChainError::RecursionFailed {
                    reason: "right aggregation child carries no segment (expose_claim) table"
                        .to_string(),
                }
            })?;

            let left = proofs[i].into_recursion_input::<BatchOnly>();
            let right = proofs[i + 1].into_recursion_input::<BatchOnly>();

            let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                               left_apt: &[Vec<p3_recursion::Target>],

exec
/bin/zsh -lc "sed -n '320,430p' metatheory/Dregg2/Circuit/RecursiveAggregation.lean" in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
def zcompress : ℤ → ℤ → ℤ := fun _ _ => 0
def zcompressN : List ℤ → ℤ := fun _ => 0

/-- The realizing 1-step chain: the honest executor step over the teeth genesis. -/
def realSteps : List ChainStep := [honestStep]

/-- The realizing aggregate: every proof is the accepting `Unit`; the public roots are the genuine
endpoints of `realSteps` (so `binding_sound`'s pin holds by `rfl`). -/
def realAggregate : Aggregate RealProof where
  root := ()
  leafProofs := [()]
  bindingProof := ()
  genesisRoot := ChainStep.oldRoot zCH zRH zcmb zcompress zcompressN honestStep
  finalRoot := foldedFinalRoot zCH zRH zcmb zcompress zcompressN teethGenesis realSteps
  chainDigest := 0
  numTurns := 1

/-- **`real_engine_sound` (non-vacuity, positive).** The named soundness hypotheses are
SATISFIABLE on a real chain: `EngineSound` holds for the accepting verifier, the realizing aggregate,
the teeth genesis, and the honest 1-step chain. Each implication is discharged concretely — the leaf
soundness yields the genuine `recCexec teethGenesis honestTurn = some _` (the honest step's `commits`),
the binding soundness yields the singleton `ChainBound` + the genuine root pins. So `EngineSound` is
INHABITED — the headline is not vacuous. -/
theorem real_engine_sound :
    EngineSound RealProof acceptAll zCH zRH zcmb zcompress zcompressN
      realAggregate teethGenesis realSteps := by
  refine { recursive_sound := ?_, leaf_sound := ?_, binding_sound := ?_ }
  · intro _
    refine ⟨fun p hp => ?_, rfl⟩
    -- every leaf is `()`; `acceptAll _ = true`.
    rfl
  · -- the positional pairing: leaf `()` ↦ step `honestStep`, whose `commits` IS the executor witness.
    show List.Forall₂ _ [()] realSteps
    refine List.Forall₂.cons ?_ (List.Forall₂.nil)
    intro _
    exact honestStep.commits
  · intro _
    refine ⟨?_, ?_, ?_⟩
    · -- ChainBound on a singleton is `True`.
      simp [realSteps, ChainBound]
    · -- genesisRoot is defined as the genuine oldRoot of the head step.
      simp [realAggregate, realSteps]
    · -- finalRoot is defined as the genuine fold.
      rfl

/-- **`light_client_fires_on_real_chain` (the headline is WITNESSED).** On the realizing
instance, the light-client headline concludes `AggregateAttests`: verifying the (accepting)
root attests the honest 1-step history. So `light_client_verifies_whole_history` is non-vacuous — it
fires on a real chain and delivers a real attestation, not an empty implication. -/
theorem light_client_fires_on_real_chain :
    AggregateAttests RealProof zCH zRH zcmb zcompress zcompressN
      realAggregate teethGenesis realSteps :=
  light_client_verifies_whole_history RealProof acceptAll zCH zRH zcmb zcompress zcompressN
    realAggregate teethGenesis realSteps real_engine_sound rfl

/-- **`real_chain_first_turn_executed` (the attestation is REAL).** Reading the conclusion
of the witnessed headline: the first (only) turn of the realizing history executed —
`recCexec teethGenesis honestTurn = some _`. So the light client's attestation is a TRUE fact about a
real executor run, not a formal husk. -/
theorem real_chain_first_turn_executed :
    recCexec teethGenesis honestTurn = some honestStep.post := by
  have h := light_client_fires_on_real_chain.every_turn honestStep (by simp [realSteps])
  simpa [honestStep] using h

end Realize

/-! ## 6. THE ANTI-GHOST TOOTH — the named hypotheses REJECT a tampered aggregate.

Additive attestation is only meaningful if the aggregate cannot attest a BROKEN history. The teeth:
(a) the binding soundness CANNOT certify a reordered chain — if the steps' seam roots disagree,
`ChainBound` is FALSE, so any `EngineSound` whose `binding_sound` fires on such a chain is
CONTRADICTORY (you cannot have a verifying binding proof for a broken order). (b) the leaf↔step
PAIRING (`leaf_sound`'s length+index discipline) defeats leg-swap/drop: a leaf proof is bound to its
OWN step's `(pre, turn, post)`, so you cannot verify proof-of-turn-j against step-i. -/

section AntiGhost

variable (Proof : Type) (verify : Proof → Bool)
variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-- **`tampered_aggregate_cannot_bind` (THE ANTI-GHOST TOOTH).** No sound aggregate can
attest a REORDERED 2-step chain. If the first step's `newRoot` differs from the second's `oldRoot`
(a spliced/reordered/dropped turn — the `TurnChainError::ChainBreak` condition), then for ANY engine
whose binding leaf verifies, `binding_sound` would force `ChainBound [s, s']`, which is FALSE for a
broken order. Hence the engine cannot have a verifying binding proof over a tampered chain — the
aggregate REJECTS reorder/drop/insert. -/
theorem tampered_aggregate_cannot_bind
    (agg : Aggregate Proof) (g : RecChainedState) (s s' : ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g [s, s'])
    (hbreak : ChainStep.newRoot CH RH cmb compress compressN s
                ≠ ChainStep.oldRoot CH RH cmb compress compressN s')
    (hverify : verify agg.bindingProof = true) :
    False := by
  obtain ⟨hbound, _, _⟩ := es.binding_sound hverify
  exact tooth_rejects_broken_order CH RH cmb compress compressN s s' hbreak hbound

/-- **`leaf_pairing_defeats_swap` (the leg-swap tooth).** A verifying leaf proof attests the
transition of ITS OWN POSITIONALLY-PAIRED step, not some other turn's. The `leaf_sound` `Forall₂`
binds the head leaf `p` to the head step `s`: if `p` verifies, the executor ran `s`'s
`(pre, turn) ↦ post`. An adversary cannot satisfy the head leaf by supplying a proof of a DIFFERENT
turn while exporting `s`'s roots — the leaf is bound to `s` by the positional pairing, not re-pointable.
This is the recursion analog of the per-effect anti-ghost. -/
theorem leaf_pairing_defeats_swap
    (agg : Aggregate Proof) (g : RecChainedState) (p : Proof) (ps : List Proof)
    (s : ChainStep) (ss : List ChainStep)
    (hagg : agg.leafProofs = p :: ps)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g (s :: ss))

One subtlety to carry into Lean: the count lane is a field element, so the formal theorem either needs `leaves.length < p` or should model `count : Nat` and add a separate representation lemma for the field encoding. The Rust path already has the `< BabyBear modulus` admission check.
exec
/bin/zsh -lc "sed -n '1795,1845p' circuit-prove/src/ivc_turn_chain.rs && sed -n '1865,1985p' circuit-prove/src/ivc_turn_chain.rs" in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
                               left_apt: &[Vec<p3_recursion::Target>],
                               right_apt: &[Vec<p3_recursion::Target>]| {
                let l = left_apt
                    .get(left_idx)
                    .expect("left segment instance present");
                let r = right_apt
                    .get(right_idx)
                    .expect("right segment instance present");
                debug_assert!(l.len() >= SEG_WIDTH && r.len() >= SEG_WIDTH);

                // (1) STATE CONTINUITY: L.last_new == R.first_old. The left subtree's final
                // root must be the right subtree's first root — the temporal tooth, in-circuit.
                //
                // Enforce equality by DIRECT `connect`, NOT `assert_zero(sub(..))`. The
                // `sub`+`assert_zero` idiom lowers to a backward-add whose `out` is the shared
                // `ExprId::ZERO` witness (`WitnessId(0)`): when one operand (`l.last_new`, a real
                // child-exposed root) is transitively unioned into the zero class by the verifier's
                // in-circuit challenger machinery, witness generation OVERWRITES `WitnessId(0)` with
                // a non-zero root — a `WitnessConflict { WitnessId(0) }`. `connect` unions the two
                // operands directly (no zero involved): equal on the honest path, and a mismatch
                // (a tampered/discontinuous chain) is rejected as a conflict — the same temporal
                // tooth, fail-closed, without touching the zero slot.
                cb.connect(l[SEG_LAST_NEW], r[SEG_FIRST_OLD]);

                // (2) parent segment: span [L.first_old .. R.last_new], count L+R, ordered
                // multi-felt digest acc = commit(L.acc ++ R.acc) (L absorbed before R ⇒
                // order-sensitive). The digest occupies SEG_DIGEST_WIDTH lanes from
                // SEG_DIGEST_FIRST.
                let first_old = l[SEG_FIRST_OLD];
                let last_new = r[SEG_LAST_NEW];
                let count = cb.add(l[SEG_COUNT], r[SEG_COUNT]);
                let mut acc_inputs = Vec::with_capacity(2 * SEG_DIGEST_WIDTH);
                acc_inputs
                    .extend_from_slice(&l[SEG_DIGEST_FIRST..SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
                acc_inputs
                    .extend_from_slice(&r[SEG_DIGEST_FIRST..SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
                let acc = seg_poseidon_commit(cb, &acc_inputs);
                let mut parent = Vec::with_capacity(SEG_WIDTH);
                parent.push(first_old);
                parent.push(last_new);
                parent.push(count);
                parent.extend_from_slice(&acc);
                debug_assert_eq!(parent.len(), SEG_WIDTH);
                cb.expose_as_public_output(&parent);
            };

            let out = build_and_prove_aggregation_layer_with_expose::<
                DreggRecursionConfig,
                BatchOnly,
                BatchOnly,
                _,
///
///   1. **VK pin** — recompute the presented root's verifier-key fingerprint
///      and compare it to `expected_vk` (the anchor an honest setup
///      distributed). A root proof of a different circuit — the from-scratch
///      aggregation route — is refused here, BEFORE any cryptographic check
///      trusts the proof's self-described circuit data.
///   2. **The root** — the single root batch-STARK proof verifies.
///   3. **The segment tooth** — the root's exposed ORDERED SEGMENT
///      `[first_old, last_new, count, acc]` (derived by construction from the
///      real descriptor leaves and combined up the tree) must equal the carried
///      `[genesis_root, final_root, num_turns, chain_digest]`. This closes the
///      mixed-root hole: a root that executed history A cannot expose B's
///      endpoints, so a B-claim against an A-execution is refused. (The carried
///      binding proof is NO LONGER a soundness dependency.)
pub fn verify_turn_chain_recursive(
    proof: &WholeChainProof,
    expected_vk: &RecursionVk,
) -> Result<(), TurnChainError> {
    verify_turn_chain_recursive_from_parts(
        &proof.root.0,
        &proof.binding_proof,
        proof.genesis_root,
        proof.final_root,
        proof.chain_digest,
        proof.num_turns,
        expected_vk,
    )
}

/// The verify core, taking the VERIFY-SUFFICIENT PARTS directly instead of a whole
/// [`WholeChainProof`] value.
///
/// This is the byte-path's verifier: a [`WholeChainProof`] cannot be reconstructed
/// from bytes because its `root.1` (`Rc<CircuitProverData>`) is prover-only and not
/// serde — but the verifier never reads `root.1`. The three teeth use only
/// `root.0` (the root [`BatchStarkProof`]), the chain-binding `Proof`, and the four
/// public scalars, which is exactly this signature. [`verify_turn_chain_recursive`]
/// is a thin wrapper that forwards a whole value's parts here, and
/// [`verify_whole_chain_proof_bytes`] decodes a [`WholeChainProofBytes`] envelope and
/// calls this — so the in-memory and over-wire paths share ONE verifier body.
///
/// The teeth, in order (identical to [`verify_turn_chain_recursive`]):
///   1. **VK pin** — recompute the root's verifier-key fingerprint and compare to
///      `expected_vk` (a foreign-circuit root is refused before any check trusts it).
///   2. **The root** — the single root batch-STARK proof verifies.
///   3. **The segment tooth** — the root's exposed ordered segment `[first_old,
///      last_new, count, acc]` (built from the real descriptor leaves, combined up
///      the tree) must equal the carried `[genesis_root, final_root, num_turns,
///      chain_digest]`. (The carried binding proof is NOT a soundness dependency.)
#[allow(clippy::too_many_arguments)]
pub fn verify_turn_chain_recursive_from_parts(
    root_proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
    binding_proof: &RecursionCompatibleProof,
    genesis_root: BabyBear,
    final_root: BabyBear,
    chain_digest: [BabyBear; SEG_DIGEST_WIDTH],
    num_turns: usize,
    expected_vk: &RecursionVk,
) -> Result<(), TurnChainError> {
    // The carried binding proof is NO LONGER a soundness dependency (the SEGMENT tooth below
    // binds the claim to the real descriptor leaves). It is retained in the artifact for byte
    // API compatibility and host-side defense-in-depth only; deliberately not re-verified here.
    let _ = binding_proof;

    // (1) VK pin.
    let found = recursion_vk_fingerprint(root_proof);
    if found != *expected_vk {
        return Err(TurnChainError::VkFingerprintMismatch {
            expected: expected_vk.to_hex(),
            found: found.to_hex(),
        });
    }

    // (2) The root. The root batch proof is produced by `aggregate_tree` at the rotated
    // leaf-wrap config (`ir2_leaf_wrap_config`, log_blowup 6 / 19 queries — the SAME FRI engine
    // the whole rotated tree runs at), NOT the default `create_recursion_config` (log_blowup 3 /
    // 38 queries). It MUST be verified under that same config, else FRI reconstruction expects
    // the wrong query count (`QueryProofCountMismatch { expected: 38, got: 19 }`).
    verify_recursive_batch_proof_with_config(root_proof, &ir2_leaf_wrap_config())
        .map_err(|reason| TurnChainError::RecursionFailed { reason })?;

    // (3) THE SEGMENT TOOTH (the close of the IVC mixed-root hole). The root proof carries an
    // `expose_claim` non-primitive table whose `public_values` are the root's ORDERED SEGMENT
    // `[first_old, last_new, count, acc]`. That segment is built BY CONSTRUCTION from the real
    // descriptor leaves: each leaf's `first_old`/`last_new` are bound in-circuit to its
    // descriptor proof's verified rotated roots, and the combine at each aggregation node
    // enforces state continuity (`L.last_new == R.first_old`), count additivity, and the
    // ordered-digest fold (`acc = H(L.acc, R.acc)`) — re-exposed up to the root. So the
    // root-exposed segment is the WHOLE-CHAIN claim derived from the ACTUAL execution. The
    // carried claim must match it exactly. There is NO separate binding leaf to swap: a root
    // that executed history A cannot expose B's endpoints, so a B-claim against an A-execution
    // FAILS here (`genesis = A.first_old != B.genesis`, etc.).
    let exposed = root_exposed_claims(root_proof).ok_or_else(|| {
        TurnChainError::ClaimedPublicsUnattested {
            reason: "root proof carries no exposed segment table (segment channel absent)"
                .to_string(),
        }
    })?;
    let mut expected = Vec::with_capacity(SEG_WIDTH);
    expected.push(genesis_root);
    expected.push(final_root);
    expected.push(BabyBear::new(num_turns as u32));
    expected.extend_from_slice(&chain_digest);
    if exposed != expected {
        return Err(TurnChainError::ClaimedPublicsUnattested {
            reason: format!(
                "root-exposed segment {exposed:?} != carried claim {expected:?} \
                 (the carried claim is not the fold of the real descriptor leaves)"
            ),
        });
    }

    Ok(())
}

// ============================================================================
// The 2-step inductive core of the UNBOUNDED accumulator.
// ============================================================================

/// The inductive core of a continuous (unbounded) accumulator:
/// `fold_two_turns(running, next) -> new_running`.

I didn’t find a Lean declaration named `acc_attests_whole_history` in the checked-in metatheory; the name appears in Rust comments for the online accumulator. So I’ll phrase this as the Lean theorem schema to add, reusing `EngineSound`’s boundary style but replacing its binding-field projection with a structural tree induction.
exec
/bin/zsh -lc "sed -n '110,150p' circuit-prove/src/accumulator.rs && sed -n '1,220p' metatheory/Dregg2/Distributed/HistoryAggregation.lean" in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
//! point + a structural idempotence argument, not a proof of `∀N, VK_N == VK_4`.
//!
//! **THE PRECISE REMAINING CRYPTO (the structural half of the wrap — named exactly, with the localized
//! delta).** The fixed point is reached at depth 4, NOT depth 2 — a finite 2-step transient. The
//! ROOT-CAUSED structural reason: the AGG∘LEAF verifier op-list depends on the STRUCTURE of the running
//! (left) input proof — specifically the per-instance opened-column widths / public-value counts of its
//! `non_primitives` and its `rows` (see `verify_p3_batch_proof_circuit` in the fork: it iterates the
//! input proof's `non_primitives` and allocates per-instance targets from their `public_values.len()`
//! and opened-value widths). A LEAF input, an `AGG(LEAF,LEAF)` input, and an `AGG(AGG,LEAF)` input each
//! carry a DIFFERENT such structure — and that structure propagates exactly ONE level into the parent's
//! op-list (measured: `rows` Const 269→277, recompose 19112→19093; `prep_commit` ddaa…→830a…), so the
//! parent op-list stabilizes only once the input has been `AGG(AGG,LEAF)`-shaped for one full fold.
//! To make EVERY fold from depth 2 carry the ONE anchor, the running input must have the steady
//! `AGG(AGG,LEAF)` structure from the FIRST aggregation — which requires a CANONICAL agg-shaped SEED
//! whose own left is already agg-shaped (a recursive fixpoint seed). That is the genuine Pickles
//! step∘wrap circuit: a fixed wrap circuit whose output shape equals its input shape, seeded once. The
//! fork exposes no such canonical-shape / re-prove primitive today (no identity/normalize fold), so
//! building the fixpoint seed is genuinely multi-pass — the precise outstanding fork work. The
//! `min_trace_height` ceiling pins the FRI trace heights (the easy half, empirically a near-no-op since
//! heights were already constant) but NOT the op-list. Lever (a)+(b), the tracked-pin fail-closed tooth,
//! and the measured-plus-idempotent fixed point are its foundation.
//!
//! The soundness SKELETON of the unbounded loop is PROVEN in Lean
//! (`Dregg2.Circuit.RecursiveAggregation.accumulate_preserves_wellformed` /
//! `acc_attests_whole_history`, `#assert_axioms`-clean): the running fold preserves whole-history
//! attestation by induction from genesis, carrying the SAME named `EngineSound` recursion boundary.

use p3_commit::Pcs;
use p3_recursion::{
    BatchOnly, ProveNextLayerParams, RecursionInput, RecursionOutput,
    build_and_prove_aggregation_layer, build_and_prove_aggregation_layer_with_expose,
    build_and_prove_next_layer_with_expose,
};
use p3_uni_stark::StarkGenericConfig;

/// The runtime preprocessed-commitment value type for the recursion config — the child proof's
/// VK-identity core (a Merkle cap). This is what the VK-identity pin (lever (a)) constrains in-band.
type RecursionCommit = <<DreggRecursionConfig as StarkGenericConfig>::Pcs as Pcs<
    <DreggRecursionConfig as StarkGenericConfig>::Challenge,
    <DreggRecursionConfig as StarkGenericConfig>::Challenger,
>>::Commitment;
/-
# Dregg2.Distributed.HistoryAggregation — the FOLD model under the IVC accumulator.

**What this is.** The whole-chain IVC accumulator (`circuit/src/ivc_turn_chain.rs`) folds a
sequence of finalized-turn proofs into ONE recursive proof attesting "all turns `1..K` executed
correctly AND the finalized state root advanced correctly from genesis to final, in that order."
This module is the EXECUTABLE/DECLARATIVE model that fold is supposed to attest — stated over the
VERIFIED executor (`Exec.RecordKernel.recCexec`, the same machine `BlocklaceFinality.executeTau`
drives) and the GENUINE per-turn state commitment (`Circuit.StateCommit.recStateCommit`, the
injective §8 full-state root the whole-turn triangle pins — `whole_turn_circuit_pins_intent_fold`).

It is the *meaning* of the chain. `RecursiveAggregation.lean` adds the SNARK recursion layer on top:
it names the inner-proof-soundness + recursive-verifier-soundness hypotheses (the part you cannot
prove in Lean — plonky3/pickles FRI), and shows that, UNDER those named hypotheses, an aggregate
proof's validity is exactly `AggregateAttests` from this file — so a light client that checks only
the succinct aggregate learns the whole history is correct.

**The two binding facts modeled here** (the `TurnChainBindingAir` of `ivc_turn_chain.rs:188`):
  1. **Per-step correctness** — each fold step `(pre, turn, post)` is a GENUINE `recCexec` step
     (its `commits` field), so the step proof, when sound, attests the verified executor actually
     ran that turn.
  2. **The temporal tooth** — `new_root[i] == old_root[i+1]` (`ivc_turn_chain.rs:246`): step `i`'s
     post-root is step `i+1`'s pre-root. Reorder / drop / insert ⇒ the chain breaks (UNSAT).

**The headline (`wellformed_attests_whole_history`):** a `WellFormedChain` from a genesis state
yields — for EVERY turn in the chain — a real `recCexec` step (the turn executed correctly per the
verified executor), the chain is correctly ordered (each post-root = next pre-root), and the whole
chain is a `Run recChainedSystem` from genesis whose final state is the genuine fold of the history,
so `recChained_run_conserves` (no mint/burn over the entire history) applies.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Distributed.HistoryAggregation`.
-/
import Dregg2.Circuit.StateCommit
import Dregg2.Exec.ConsensusExec

namespace Dregg2.Distributed.HistoryAggregation

open Dregg2.Exec (RecChainedState recCexec recChainedSystem recChained_run_conserves recTotal)
open Dregg2.Execution (System Run)
open Dregg2.Circuit.StateCommit (recStateCommit recStateCommit_binds recStateCommit_binds_kernel
  compressInjective compressNInjective cellLeafInjective RestHashIffFrame AccountsWF cellDigest)

/-- The all-zero turn — `Turn` has no `Inhabited` instance, so we name the canonical default
turn-context used to commit the genesis/empty-chain root. -/
def zeroTurn : Dregg2.Exec.Turn := ⟨0, 0, 0, 0⟩

/-! ## 0. The §8 state-commitment portal (the genuine per-turn root).

`recStateCommit k t` is the injective full-state commitment from the whole-turn triangle — the ONE
authenticated per-turn state root the running prover folds (`StateCommit.lean:196`). It is
parametric in the Poseidon portal functions; we carry them as section variables exactly as
`StateCommit`/`WholeTurnTriangle` do, plus the single collision-resistance carrier
`compressInjective cmb` the binding lemma needs (REALIZABLE — Poseidon 2-to-1 CR). -/

section Portal

variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-- **`stateRoot k t`** — the genuine §8 full-state commitment of kernel `k` under the turn-context
`t` (the prover-folded per-turn root). `recStateCommit` with the portal fixed. A turn `t` advances
`(stateRoot k t) ↦ (stateRoot k' t')`; the chain binds these roots. -/
def stateRoot (k : Dregg2.Exec.RecordKernelState) (t : Dregg2.Exec.Turn) : ℤ :=
  recStateCommit CH RH cmb compress compressN k t

/-! ## 1. One fold step — a finalized turn + the roots it advances.

The Rust `FinalizedTurn` (`ivc_turn_chain.rs:100`) carries a whole-turn proof whose PI exposes
`(OLD_COMMIT, NEW_COMMIT)`. Here a `ChainStep` carries the pre-state chained record, the turn, and
the post-state chained record, together with the EXECUTOR WITNESS `recCexec pre turn = some post` —
so this is a real verified step, not an asserted one. Its roots are the GENUINE `stateRoot` of the
pre/post kernels. -/

/-- A single fold step: a genuine `recCexec` transition `(pre, turn) ↦ post`, plus the receipt logs
the chained state carries. Modeled directly over the verified executor so the step's roots are the
real commitments of states the executor reached — what an honest inner step proof, when
sound, attests. -/
structure ChainStep where
  /-- The pre-state chained record (kernel + receipt log). -/
  pre  : RecChainedState
  /-- The turn applied this step. -/
  turn : Dregg2.Exec.Turn
  /-- The post-state chained record. -/
  post : RecChainedState
  /-- **The executor witness**: `recCexec pre turn = some post`. -/
  commits : recCexec pre turn = some post

/-- The step's pre-state root (the §8 commitment of the pre-kernel). The Rust `old_root`. -/
def ChainStep.oldRoot (s : ChainStep) : ℤ := stateRoot CH RH cmb compress compressN s.pre.kernel s.turn

/-- The step's post-state root (the §8 commitment of the post-kernel). The Rust `new_root`. -/
def ChainStep.newRoot (s : ChainStep) : ℤ := stateRoot CH RH cmb compress compressN s.post.kernel s.turn

/-! ## 2. The temporal tooth — `new_root[i] == old_root[i+1]`.

`TurnChainBindingAir` constraint 1 (`ivc_turn_chain.rs:246`): each step's `new_root` must be the
NEXT step's `old_root`. A reordered/dropped/inserted turn breaks this and is UNSAT. -/

/-- **`Continues s s'`** — the temporal tooth between adjacent steps: `s.newRoot = s'.oldRoot`
(`new_root[i] == old_root[i+1]`). Its failure is the `TurnChainError::ChainBreak` rejection. -/
def Continues (s s' : ChainStep) : Prop :=
  ChainStep.newRoot CH RH cmb compress compressN s = ChainStep.oldRoot CH RH cmb compress compressN s'

/-- **`ChainBound steps`** — every adjacent pair satisfies the temporal tooth. The whole sequence is
the genuine finalized order (no reorder/drop/insert at the root level). -/
def ChainBound : List ChainStep → Prop
  | []            => True
  | [_]           => True
  | s :: s' :: rest => Continues CH RH cmb compress compressN s s' ∧ ChainBound (s' :: rest)

/-! ## 3. State-level continuity + the well-formed chain.

The Rust chain binding is over ROOTS; the executor model adds the underlying STATE continuity (step
`i`'s post-state IS step `i+1`'s pre-state — `RecChainedState` equality), which §5 shows the
root-level tooth recovers under CR. `lastStateOf` is the state the chain reaches from genesis. -/

/-- **`StateChained g steps`** — the steps form a contiguous executor run from genesis `g`: the first
step's pre-state is `g`, and each step's post-state is the next step's pre-state. -/
def StateChained (g : RecChainedState) : List ChainStep → Prop
  | []        => True
  | s :: rest => s.pre = g ∧ StateChained s.post rest

/-- **`lastStateOf g steps`** — the state the chain reaches from genesis `g`: genesis if empty,
else the last step's `post`. (Defined structurally so the run keystone can name the endpoint.) -/
def lastStateOf (g : RecChainedState) : List ChainStep → RecChainedState
  | []        => g
  | s :: rest => lastStateOf s.post rest

/-- **`WellFormedChain g steps`** — the steps are a genuine executor chain from genesis `g` AND the
root-level temporal tooth holds. -/
structure WellFormedChain (g : RecChainedState) (steps : List ChainStep) : Prop where
  /-- State-level continuity from genesis (each `recCexec` post is the next pre). -/
  chained : StateChained g steps
  /-- Root-level temporal tooth (the `TurnChainBindingAir` continuity constraint). -/
  bound   : ChainBound CH RH cmb compress compressN steps

/-! ## 4. The genuine final root of the whole history.

The accumulator's final claim is "`final_root` = the genuine fold of the whole history"
(`ivc_turn_chain.rs:18`): the §8 commitment of the kernel reached by folding `recCexec` over all the
turns. `lastStateOf g steps` IS that folded state; its commitment is the genuine final root. -/

/-- **`foldedFinalRoot g steps`** — the genuine §8 final root: commit the folded post-kernel
(`lastStateOf`) under the last step's turn-context (the `NEW_COMMIT` the accumulator exposes; the
empty chain commits genesis under `default`). -/
def foldedFinalRoot (g : RecChainedState) (steps : List ChainStep) : ℤ :=
  match steps.getLast? with
  | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
  | some s => stateRoot CH RH cmb compress compressN (lastStateOf g steps).kernel s.turn

/-! ## 5. The CR recovery — the ROOT tooth recovers STATE continuity.

The accumulator's verifier only sees ROOTS, not states. Under collision-resistance of the commitment
(`compressInjective cmb`, via `recStateCommit_binds`), the root-level tooth recovers the underlying
kernel continuity. This is why the LIGHT CLIENT, seeing only roots, learns state
continuity — the §8 root is an injective full-state commitment. -/

/-- **`seam_roots_chain` (the easy direction).** State-level continuity at a seam ENTAILS
the root-level tooth: if `s.post = s'.pre` and the turn-contexts agree at the seam, their roots
chain. So an honest accumulator never asserts the tooth separately — it is free from execution. -/
theorem seam_roots_chain (s s' : ChainStep)
    (hstate : s.post = s'.pre) (hturn : s.turn = s'.turn) :
    ChainStep.newRoot CH RH cmb compress compressN s
      = ChainStep.oldRoot CH RH cmb compress compressN s' := by
  unfold ChainStep.newRoot ChainStep.oldRoot
  rw [hstate, hturn]

/-- **`root_tooth_pins_state` (THE CR RECOVERY).** Under collision-resistance of the
commitment combiner, the ROOT-level tooth pins the underlying full-state COMMITMENT: if two steps
share a turn-context and their seam roots agree, then their cell-digests AND rest-hashes agree
(`cellDigest s.post = cellDigest s'.pre ∧ RH s.post = RH s'.pre`). That is exactly the binding
`recStateCommit_binds` provides — the §8 root is an injective commitment to (live-cell digest, rest
hash), i.e. to the WHOLE kernel (every cell binds via `cellLeafInjective`; the 16 non-cell fields via
`RestHashIffFrame`). So a light client that sees only the matching roots GENUINELY learns the states
chained, up to CR. This is the load-bearing fact that makes "verify the succinct aggregate"
sufficient: the root IS the full-state commitment. -/
theorem root_tooth_pins_state (hCmb : compressInjective cmb) (s s' : ChainStep)
    (hturn : s.turn = s'.turn)
    (htooth : ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s') :
    cellDigest CH compress compressN s.post.kernel s'.turn
        = cellDigest CH compress compressN s'.pre.kernel s'.turn
      ∧ RH s.post.kernel = RH s'.pre.kernel := by
  unfold ChainStep.newRoot ChainStep.oldRoot stateRoot at htooth
  rw [hturn] at htooth
  exact recStateCommit_binds CH RH cmb compress compressN hCmb
          s.post.kernel s'.pre.kernel s'.turn htooth

/-- **`root_tooth_pins_kernel` (THE STRENGTHENED CR RECOVERY — state-equality, not just commitment).**
The critique's precise gap: `root_tooth_pins_state` recovers only `cellDigest`+`RH` EQUALITY
(commitment-level), not the `s.post.kernel = s'.pre.kernel` STATE equality `StateChained` needs — so
the headline still took state continuity as a separate prover hypothesis. This closes it: under the
FULL standard Poseidon CR set + the PROVED-preserved `AccountsWF` structural invariant on BOTH seam
kernels, an agreeing root-tooth at a matched turn-context forces the WHOLE kernel equal
(`recStateCommit_binds_kernel`: `RH` recovers the 15 non-cell fields incl. `accounts`, then the cell
digest recovers `cell` over the now-common carrier). So a light client seeing only the matching roots
GENUINELY learns the adjacent KERNELS coincide — up to CR — not merely their commitments. (The
receipt LOG is the one `RecChainedState` component the §8 state root does NOT bind; see
`KernelChained` below — conservation rides on the kernel alone, so the log is conservation-irrelevant,
and that is the exact, named residual rather than a hidden hypothesis.) -/
theorem root_tooth_pins_kernel
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH) (s s' : ChainStep)
    (hwf : AccountsWF s.post.kernel) (hwf' : AccountsWF s'.pre.kernel)
    (hturn : s.turn = s'.turn)
    (htooth : ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s') :
    s.post.kernel = s'.pre.kernel := by
  unfold ChainStep.newRoot ChainStep.oldRoot stateRoot at htooth
  rw [hturn] at htooth
  exact recStateCommit_binds_kernel CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
          s.post.kernel s'.pre.kernel s'.turn hwf hwf' htooth

/-! ## 6. THE HEADLINE — a well-formed chain attests the WHOLE history. -/


exec
/bin/zsh -lc 'rg -n "acc_attests_whole_history|accumulator|Segment|segment|HostSeg|chain_digest|mixed-root|mixed root" metatheory docs circuit-prove/src/accumulator.rs circuit-prove/tests -S' in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
circuit-prove/src/accumulator.rs:10://! This module is the SEQUENTIAL DUAL: a running accumulator that holds ONE `RecursionOutput` (the
circuit-prove/src/accumulator.rs:27://!      `num_turns += 1`, `chain_digest = H(prev_digest, old, new, idx)`;
circuit-prove/src/accumulator.rs:32://! the consumed turns (proofs) are dropped. The accumulator ALSO retains a small per-turn scalar
circuit-prove/src/accumulator.rs:35://! leaf so its digest reproduces the running `chain_digest`. So the running STATE is O(num_turns)
circuit-prove/src/accumulator.rs:39://! ## ⚠ SEGMENT-ACCUMULATOR FOLLOW-UP (the mixed-root analog, named)
circuit-prove/src/accumulator.rs:41://! The K-fold tree (`ivc_turn_chain`) closed the mixed-root hole by carrying an ordered
circuit-prove/src/accumulator.rs:42://! SEGMENT on every DESCRIPTOR leaf and combining segments in-circuit (so the whole-chain
circuit-prove/src/accumulator.rs:44://! accumulator STILL uses the separate `TurnChainBindingAir` leaf at `finalize` (its claim
circuit-prove/src/accumulator.rs:49://! segment tooth's by-construction binding. The follow-up is to port the segment model here:
circuit-prove/src/accumulator.rs:50://! each `accumulate` step's descriptor leaf carries its segment, and the running fold combines
circuit-prove/src/accumulator.rs:51://! `running.segment` with the new leaf's segment (the left-linear analog of the K-fold combine —
circuit-prove/src/accumulator.rs:53://! K-fold bar (the mixed-root witness) is the one that landed.
circuit-prove/src/accumulator.rs:134://! `acc_attests_whole_history`, `#assert_axioms`-clean): the running fold preserves whole-history
circuit-prove/src/accumulator.rs:171:/// Expose the accumulator's binding-leaf claims `[genesis, final, num_turns, chain_digest]`
circuit-prove/src/accumulator.rs:172:/// as a `SEG_WIDTH`-lane segment, ZERO-PADDING the single-felt binding digest to the K-fold
circuit-prove/src/accumulator.rs:174:/// `[genesis, final, num_turns, chain_digest, 0, …, 0]`.
circuit-prove/src/accumulator.rs:176:/// This keeps the ONLINE accumulator's artifact structurally uniform with the K-fold's
circuit-prove/src/accumulator.rs:177:/// multi-felt segment (so `verify_turn_chain_recursive`'s tooth (4) reads a consistent
circuit-prove/src/accumulator.rs:178:/// layout) WITHOUT strengthening its digest — the accumulator path is scoped OUT of the
circuit-prove/src/accumulator.rs:179:/// codex #3 mixed-root close (its binding leaf is the separate, swappable single-felt
circuit-prove/src/accumulator.rs:181:fn accumulator_expose_padded_segment(
circuit-prove/src/accumulator.rs:186:    // Binding-leaf PI order: [genesis, final, num_turns, chain_digest] — i.e. the first
circuit-prove/src/accumulator.rs:192:        "binding leaf must expose [genesis, final, num_turns, chain_digest]"
circuit-prove/src/accumulator.rs:253:    /// **The temporal tooth.** The next turn does not consume the accumulator's head root: its
circuit-prove/src/accumulator.rs:257:        /// The accumulator's current head root (what the next turn must consume).
circuit-prove/src/accumulator.rs:277:    /// point. The fold is REJECTED (never folded unpinned). The accumulator is left UNCHANGED.
circuit-prove/src/accumulator.rs:286:    /// `finalize` on an empty accumulator (no turns folded — there is nothing to attest).
circuit-prove/src/accumulator.rs:299:                 accumulator head_root {expected_old_root}"
circuit-prove/src/accumulator.rs:315:            AccError::Empty => write!(f, "cannot finalize an empty accumulator (no turns folded)"),
circuit-prove/src/accumulator.rs:332:    pub chain_digest: BabyBear,
circuit-prove/src/accumulator.rs:335:    /// The running Poseidon2 accumulator carrier (`acc_out` of the binding AIR; `chain_digest` IS
circuit-prove/src/accumulator.rs:340:/// The running accumulator: a single running recursion proof (O(1) PROOF memory) + the O(1) chain
circuit-prove/src/accumulator.rs:349:/// the per-turn `TurnChainBindingAir` leaf so its last-row digest reproduces `summary.chain_digest`
circuit-prove/src/accumulator.rs:350:/// EXACTLY (the AIR's `acc_out == chain_digest` constraint). This is precisely the component prereq
circuit-prove/src/accumulator.rs:408:    /// `acc_0`: the empty accumulator (no running proof, no summary). The base of the IVC fold.
circuit-prove/src/accumulator.rs:508:    /// got the accumulator into a state where the running proof and the pinned VK disagree; the driver
circuit-prove/src/accumulator.rs:531:    /// circuit is refused IN-CIRCUIT, not host-side. Does NOT mutate the accumulator.
circuit-prove/src/accumulator.rs:585:    ///   5. advance the running summary (`head_root`, `chain_digest`, `num_turns`).
circuit-prove/src/accumulator.rs:656:                //      accumulator UNCHANGED. (The previous behaviour silently fell through to the
circuit-prove/src/accumulator.rs:671:                        // Restore the running proof we `take()`-d so the accumulator is unchanged on
circuit-prove/src/accumulator.rs:732:        //     constraint (`acc_out == chain_digest`) holds — see `finalize_binding_leaf`'s note.
circuit-prove/src/accumulator.rs:740:                    chain_digest: acc_out,
circuit-prove/src/accumulator.rs:755:                    chain_digest: acc_out,
circuit-prove/src/accumulator.rs:768:    /// **Read the running accumulator out into a [`WholeChainProof`]** a light client verifies.
circuit-prove/src/accumulator.rs:776:    /// `finalize` consumes the accumulator (the running proof is moved into the artifact).
circuit-prove/src/accumulator.rs:781:    /// last-row digest reproduces `summary.chain_digest` EXACTLY and tooth 2 of
circuit-prove/src/accumulator.rs:783:    /// head_root, num_turns, chain_digest]`) passes. The per-pair ordering is attested BOTH by this
circuit-prove/src/accumulator.rs:805:        // running `chain_digest` exactly.
circuit-prove/src/accumulator.rs:821:            // chain_digest]`, so the accumulator's root carries the host-readable,
circuit-prove/src/accumulator.rs:825:            // (`SEG_DIGEST_WIDTH`-lane) Poseidon2 segment digest. The ONLINE accumulator
circuit-prove/src/accumulator.rs:826:            // (scoped OUT of the mixed-root close — its binding leaf is still the separate,
circuit-prove/src/accumulator.rs:830:            // does NOT strengthen the accumulator's digest — its collision-resistance is
circuit-prove/src/accumulator.rs:831:            // unchanged from the 1-felt binding leaf; the structural mixed-root weakness
circuit-prove/src/accumulator.rs:836:                    accumulator_expose_padded_segment(cb, claims);
circuit-prove/src/accumulator.rs:894:                accumulator_expose_padded_segment(cb, claims);
circuit-prove/src/accumulator.rs:917:        // the single-felt online-accumulator carrier — ZERO-PADDED to the K-fold path's multi-felt
circuit-prove/src/accumulator.rs:918:        // digest lane width (codex #3). The accumulator is scoped OUT of the mixed-root close; the
circuit-prove/src/accumulator.rs:921:        // (`summary.chain_digest` is the UNPADDED running carrier — a different, internal quantity.)
circuit-prove/src/accumulator.rs:922:        let mut chain_digest = [BabyBear::ZERO; crate::ivc_turn_chain::SEG_DIGEST_WIDTH];
circuit-prove/src/accumulator.rs:923:        chain_digest[0] = binding_pis[3];
circuit-prove/src/accumulator.rs:930:            chain_digest,
circuit-prove/src/accumulator.rs:952:/// hash_4_to_1([acc_in, old, new, idx])` (the SAME fold `accumulate` ran into `summary.chain_digest`),
circuit-prove/src/accumulator.rs:955:/// head_root, num_turns, chain_digest]`. The first/last-row + continuity constraints hold by
circuit-prove/src/accumulator.rs:956:/// construction; the last-row `acc_out == chain_digest` reproduces the running digest exactly. Tooth 2
circuit-prove/src/accumulator.rs:995:    let chain_digest = trace.last().unwrap()[crate::ivc_turn_chain::COL_ACC_OUT];
circuit-prove/src/accumulator.rs:1001:        chain_digest,
circuit-prove/tests/accumulator.rs:3://! `dregg_circuit_prove::accumulator::Accumulator` extends a running recursion proof ONE finalized
circuit-prove/tests/accumulator.rs:8://!     (`AccError::ChainBreak`); an empty accumulator refuses to finalize.
circuit-prove/tests/accumulator.rs:24:use dregg_circuit_prove::accumulator::{AccError, Accumulator};
circuit-prove/tests/accumulator.rs:136:    // The turns already link by construction (make_chain asserts it); the accumulator's continuity
circuit-prove/tests/accumulator.rs:147:    // A fresh accumulator has no summary and 0 turns.
circuit-prove/tests/accumulator.rs:153:/// An empty accumulator refuses to finalize (nothing to attest).
circuit-prove/tests/accumulator.rs:155:fn empty_accumulator_refuses_finalize() {
circuit-prove/tests/accumulator.rs:159:        Ok(_) => panic!("an empty accumulator must not finalize"),
circuit-prove/tests/accumulator.rs:189:    // The rejected step did NOT advance the accumulator.
circuit-prove/tests/accumulator.rs:223:        .expect("the accumulator has a summary after 3 turns");
circuit-prove/tests/accumulator.rs:246:    // mixed-root hole) — each descriptor leaf carries `[first_old, last_new, count, acc]` and the
circuit-prove/tests/accumulator.rs:247:    // BALANCED-TREE combine folds `acc = H(L.acc, R.acc)`. The online accumulator instead carries
circuit-prove/tests/accumulator.rs:252:    // to its own root-exposed value (the segment tooth), which is what soundness requires.
circuit-prove/tests/accumulator.rs:333:/// fold, leaving the accumulator UNCHANGED (still 2 turns).
circuit-prove/tests/accumulator.rs:381:    // The rejected step did NOT advance the accumulator.
circuit-prove/tests/accumulator.rs:385:        "a rejected fold leaves the accumulator unchanged"
circuit-prove/tests/accumulator.rs:430:/// work. See the accumulator module header for the full statement.
metatheory/Dregg2.lean:207:import Dregg2.Apps.SwarmSignal         -- THE NOTIFY DEMO: verified async swarm-signal coordinator (NOTIFY-CASCADE.md §demo-app-design) — a coordinator NOTIFIES workers under ATTENUATED badge-masked notify caps (the async --wake the metatheory lacked; AgentOrchestration's async sibling). Runs on Step-1 NotifyAuthority ALONE (no core Auth.notify, no felt, no VK). 6 teeth both polarities, all reusing Step-1's signalGated/attenuateNotify: coordinator_wakes_worker_commits (OR's exactly the held badge) + worker_cannot_widen_mask (no-amplify, REFUSE) + worker_cannot_poke_peer (no cap targets the peer, structural) + worker_cannot_signal_back (no cap targets the coordinator + notify-cap NEVER confers Reply/Call) + out_of_mask_signal_refused (fail-closed) + attenuation_shrinks_admitted (the keystone signalAdmissible_attenuate_no_amplify); wake_is_balance_neutral (writes a badge accumulator, not the ledger). HONEST: the teeth demonstrate AUTHORITY containment, NOT information containment — the carried badge-OR covert-channel risk (a notify cap is never info-free) is flagged in the module doc, not laundered. #assert_all_clean, #guard non-vacuity both polarities
metatheory/Dregg2.lean:342:import Dregg2.Circuit.Emit.EffectVmEmitNoteSpendCompose  -- TURN-LEVEL COMPOSITION for the NOT-per-row noteSpend: per-row root-bound descriptor (binds the nullifier-set INSERT into state_commit, anti-ghost) ⊗ turn-level NON-MEMBERSHIP gadget (sorted-tree Merkle, dsl/revocation.rs, the `non-revocation` turn sub-proof — supplies FRESHNESS nf∉nullifiers) ⊗ turn-level §8 proof gadget ⟹ FULL NoteSpendSpec (all 17 fields). compose_perRow_and_turnGadget_suffices (sufficiency) + stale_nullifier_does_not_commit (turn gadget LOAD-BEARING, fail-closed) + compose_commits_iff_turn_gadgets_accept (IFF). #assert_axioms clean. The layering: every leg graduates at the per-row OR the turn/accumulator layer with a named gadget.
metatheory/Dregg2.lean:605:import Dregg2.Circuit.Emit.EffectVmEmitBundleFold -- THE PROOF-OF-PROOFS FOLD, emitted from Lean (law #1; retires `BundleTreeFoldAir`): folds child-bundle DIGESTS (Poseidon2(child.outer_pi) — NOT inner STARKs, which verify classically in verify_aggregated_tree, so NO genuine recursion / no named seam) into the root accumulator; width 3, PI 2, 4 constraints (1 window gate + 1 arity-2 compress chip lookup — the compress is now an IN-circuit constraint, was a verifier-side recompute, retiring the hand-AIR's named residual). Teeth fold_rejects_tampered_final/fold_compress_is_hashed, axiom-clean.
metatheory/Dregg2.lean:610:import Dregg2.Circuit.RotatedKernelRefinementAttenuate -- THE capability/attenuation VALUE leg, closed HONESTLY for attenuate against the GENUINE non-amp descriptor (attenuateVmDescriptorGenuineNonAmp, EffectVmEmitAttenuateA, width 186 — recompute + submask). CLASS = VALUE_PARTIAL. THE LOAD-BEARING FINDING: the genuine recompute does NOT pin the exact attenuateSlotF Caps-function update — it forces a SINGLE-EDGE PREPEND-ACCUMULATOR ADVANCE over a cap_root FELT (post.capRoot = hash[hash[holder,target,rights,op], pre.capRoot], capAdvanceOf/edgeLeafOf), anti-ghosted (tamper any edge field ⇒ root moves ⇒ UNSAT, attenuateGenuine_binds_edge), with the bound rights felt gated granted⊑held bitwise (attenuateGenuineNonAmp_in_circuit). There is NO theorem (structurally cannot be from THIS descriptor) relating that felt accumulator to a sorted-Merkle commitment of the Caps function. So the circuit FORCES the NON-AMPLIFICATION AXIS (the security crux) + the genuine recompute-bound per-cell post (CapCellSpecGenuine, frame frozen), and the EXACT Caps move (attenuateSlotF) + the receipt-log + the 16-field frame are carried as NAMED decode residuals in attenuateEncodes (the cap-tree Caps↔felt residual the per-edge recompute cannot certify). attenuate_descriptorRefines: attenuateEncodes ⟹ AttenuateSpec pre actor idx keep post (= the .attenuateA arm of fullActionStep). attenuate_nonAmp_forced: the in-circuit granted⊑held per bit, FORCED. Tooth: attenuate_descriptorRefines_rejects_amplify (an over-grant row — granted bit set, held bit clear — is UNSAT, reusing attenuateGenuineNonAmp_rejects_amplify). attenuate_spec_non_amplifying: confRights(attenuate keep c)≤confRights c off the forced spec. NAMED RESIDUALS: (a) the Caps↔felt-accumulator lift (capsMove); (b) the registry cutover — the genuine descriptor is v1-level (teeth at per-row constraint satisfaction), so swapping the live v3Registry entry attenuateVmDescriptor2R24 (=attenuateV3) requires FIRST a rotateV3/v3OfWith lift of the genuine-non-amp descriptor + a Satisfied2⟹per-row bridge (its own strand) + the Rust JSON re-emit/V3_STAGED_REGISTRY_FP re-pin — NOT done; the registry was NOT swapped. #assert_axioms-clean on every theorem.
metatheory/Dregg2.lean:627:import Dregg2.Circuit.RotatedKernelRefinementCapFamily -- THE CAPABILITY-FAMILY refinements, FORCING the exact sorted-tree cap-table move via CapTreeUpdate (the #103 cap-reshape payoff). Per effect a DATA-bearing <Effect>CapsTreeEncodes decode bundles (1) the sorted-tree update DATA (SpineCommits old/new + present/fresh) from which the gadget FORCES the exact key-set move, and (2) the kernel-side Caps-FUNCTION residual (the faithful cap-tree↔kernel-caps ENCODING the commitment cannot certify — a HYPOTHESIS, exactly as attenuateEncodes.capsMove / NullifierTreeEncodes). INSERT (delegate/introduce/grantCap): delegate_forces_insert (keysOf grows by exactly the fresh edge key) + delegate_descriptorRefines ⟹ DelegateSpec + delegate_execFullA + delegate_rejects_ungrounded (the Granovetter gate bites). UPGRADE — attenuate goes PAST the felt-accumulator VALUE_PARTIAL: attenuate_forces_keyset_preserved (capUpdateAt_sound — the key set is PRESERVED, the in-place slot narrow's sorted-tree shadow, FORCED against the real deployed binary-Merkle commitment) + attenuate_descriptorRefines_exact ⟹ AttenuateSpec (SET-EXACT, not just non-amp) + attenuate_execFullA. delegateAtten (insert of an attenuated cap): delegateAtten_forces_insert + delegateAtten_descriptorRefines ⟹ DelegateAttenSpec + delegateAtten_non_amplifying (granted⊑held off the forced spec). refreshDelegation (update-at-key over the DELEGATIONS tree): refreshDelegation_forces_keyset_preserved + refreshDelegation_descriptorRefines ⟹ RefreshDelegationSpec. REMOVE (revoke/revokeDelegation/revokeCapability): revoke_forces_remove (keysOf loses exactly remKey + remKey absent) + revoke_descriptorRefines ⟹ RevokeSpec + revoke_execFullA + revokeDelegation_execFullA + revoke_drops_edge (holder confers no t-edge after). The exact Caps-function move is FORCED per effect (recDelegateCaps/attenuateSlotF/grant-attenuated/refreshDelegationsMap/removeEdgeCaps), with the SET move now forced by the gadget — the Caps↔tree encoding is the named carrier. #assert_axioms-clean.
metatheory/Dregg2.lean:629:import Dregg2.Circuit.RotatedKernelRefinementSpawnHandoff -- THE PHASE-D PAYOFF for spawn: the parent→child CAPABILITY HANDOFF, FORCED in-circuit via the deployed sorted cap-tree INSERT (CapTreeUpdate.capInsert_sound) — replacing the FROZEN cap_root (gCapPass) of the live spawn descriptor that RotatedKernelRefinementBirth carried as the NAMED capHandoff/delegateHandoff/delegationsHandoff residual. spawnHandoffEncodes bundles the EXISTING accounts-growth decode (spawnGenuineEncodes — accounts insert FORCED) + the sorted-tree INSERT data for the CHILD cap_root (SpineCommits old binds spine, childKey FRESH, new binds sortedInsert childKey spine). spawn_handoff_forces_insert: capInsert_sound FORCES keysOf newRoot = insert childKey (keysOf oldRoot) against the REAL deployed binary-Merkle commitment (the SET move, NOT frozen, NOT a felt accumulator) — the cap-family delegate_descriptorRefines template. spawn_handoff_key_present: the conferred cap key IS committed after the handoff. spawn_descriptorRefines_handoff ⟹ SpawnSpec (accounts FORCED via spawn_descriptorRefines + the cap-tree insert FORCED at the SET level; the spawnCapsMap/spawnDelegateMap/spawnDelegationsMap Caps-FUNCTION moves ride birth's named faithful-encoding residual, NOW backed by the forced insert — the SOLE remaining carrier, exactly the cap-family class) + _execFullA. NEGATIVE TEST (the upgrade's point): spawn_handoff_rejects_frozen_root — a spawn that FREEZES the child cap_root (newRoot = oldRoot, no handoff) while claiming the handoff is UNSAT (the fresh childKey would be BOTH absent (hfresh) AND present (forced insert) — contradiction), EXACTLY what the live gCapPass freeze could NOT catch. spawn_handoff_rejects_wrong_accounts (the accounts tooth inherited). NON-VACUITY: spawn_handoff_nonvacuous — the forced insert STRICTLY grows the child's committed cap key set (childKey ∈ new ∧ ∉ old). #assert_axioms-clean (carriers = CapHashScheme.chipCR/SpineCommits via CapTreeUpdate + compressNInjective via Birth, all HYPOTHESES).
metatheory/Dregg2.lean:635:import Dregg2.Consensus.TauPrefixMonotone -- T5 RESOLVED with a SOUNDNESS FINDING: tauOrder finalized-prefix monotonicity is REFUTED unconditionally (honest-laggard counterexample lagBase→lagGrown: a lagging validator's late wave-end ratifier grows an ALREADY-FINAL wave's coverage and xsorts MID-PREFIX; insert-valid, equivocation-free — the node's executed_up_to index slicing at blocklace_sync.rs::poll_finalized_blocks would re-execute block 32 and PERMANENTLY skip block 41) + PROVED conditional: tau_finalized_prefix_monotone under FinalizedRegionStable (leaders_extend + fold_agrees = the finalized region undisturbed; executable mirror stableCheck = the check the node is MISSING; pointwise sufficient condition fold_agrees_of_pointwise; node-shaped corollary tau_executed_prefix_fixed = the executed region is bit-identical under take) + structural foldl_tauStep_fst_extend (tau's loop only APPENDS — reorder risk lives entirely in the leader list + segments); POS tooth trace3→trace6 (full second wave: stableCheck holds, 9→18 prefix) + NEG teeth isolate the failing field (leaders_extend holds, fold_agrees fails); #assert_axioms-clean
circuit-prove/tests/ivc_turn_chain_rotated.rs:181:/// and RELABELED carried publics (final_root / chain_digest / num_turns /
circuit-prove/tests/ivc_turn_chain_rotated.rs:219:    // REFUSED: relabeled chain_digest (claiming a different ordered history) — the digest
circuit-prove/tests/ivc_turn_chain_rotated.rs:221:    let honest_digest = whole.chain_digest;
circuit-prove/tests/ivc_turn_chain_rotated.rs:222:    whole.chain_digest[0] = honest_digest[0] + BabyBear::ONE;
circuit-prove/tests/ivc_turn_chain_rotated.rs:225:        other => panic!("a relabeled chain_digest must be refused; got {other:?}"),
circuit-prove/tests/ivc_turn_chain_rotated.rs:227:    whole.chain_digest = honest_digest;
circuit-prove/tests/ivc_turn_chain_rotated.rs:296:        &env.chain_digest,
circuit-prove/tests/ivc_turn_chain_rotated.rs:619:        whole_a.chain_digest, whole_b.chain_digest,
circuit-prove/tests/ivc_turn_chain_rotated.rs:630:    forged.chain_digest = whole_b.chain_digest;
circuit-prove/tests/ivc_turn_chain_rotated.rs:700:    let chain_digest = h1;
circuit-prove/tests/ivc_turn_chain_rotated.rs:701:    let pis = vec![genesis, final_root, BabyBear::new(2), chain_digest];
circuit-prove/tests/ivc_turn_chain_rotated.rs:718:/// `acc_out == hash_4_to_1([acc_in, old, new, idx])`, so a forged `chain_digest` (a
circuit-prove/tests/ivc_turn_chain_rotated.rs:740:    // FORGERY: claim a different chain_digest than the real hash chain. We move the
circuit-prove/tests/ivc_turn_chain_rotated.rs:749:    forged_pis[3] = forged_digest; // chain_digest public
circuit-prove/tests/ivc_turn_chain_rotated.rs:770:        "FINDING #2 CLOSED: a forged chain_digest must be REJECTED by the in-AIR \
circuit-prove/tests/ivc_turn_chain_rotated.rs:854:// THE FIX (codex's ordered segment-accumulator). The separate binding leaf is GONE
circuit-prove/tests/ivc_turn_chain_rotated.rs:858:// the segments (state continuity `L.last_new == R.first_old`, count additivity, ordered
circuit-prove/tests/ivc_turn_chain_rotated.rs:859:// digest `acc = H(L.acc, R.acc)`) up to the root. The root's exposed segment is thus
circuit-prove/tests/ivc_turn_chain_rotated.rs:865:// segment table at the root is the descriptor-derived one. The strongest remaining
circuit-prove/tests/ivc_turn_chain_rotated.rs:871:// the PUBLIC building blocks (`prove_descriptor_leaf_rotated_with_segment` + the segment
circuit-prove/tests/ivc_turn_chain_rotated.rs:874:// THIS is the close of the mixed-root hole.
circuit-prove/tests/ivc_turn_chain_rotated.rs:877:/// Find the instance index of the `expose_claim` (segment) non-primitive table in a
circuit-prove/tests/ivc_turn_chain_rotated.rs:894:// The in-circuit segment digest is the lib's `pub seg_poseidon_commit` (a multi-felt
circuit-prove/tests/ivc_turn_chain_rotated.rs:899:/// Fold history A's GENUINE segment-bearing descriptor leaves into ONE root (the real
circuit-prove/tests/ivc_turn_chain_rotated.rs:900:/// segment-accumulator fold), then carry B's claims to the verifier. The whole-chain
circuit-prove/tests/ivc_turn_chain_rotated.rs:901:/// claim for B must FAIL against a root that executed A — the segment tooth fires because
circuit-prove/tests/ivc_turn_chain_rotated.rs:905:#[ignore = "SLOW: a real segment fold (~minutes); run with --ignored — codex re-review #2 CLOSE"]
circuit-prove/tests/ivc_turn_chain_rotated.rs:910:        ir2_leaf_wrap_config, prove_descriptor_leaf_rotated_with_segment, seg_poseidon_commit,
circuit-prove/tests/ivc_turn_chain_rotated.rs:937:    // (which is no longer a soundness dependency). B's `chain_digest` here is irrelevant to
circuit-prove/tests/ivc_turn_chain_rotated.rs:938:    // the rejection — the segment tooth fails on B's genesis/final/count already — but we
circuit-prove/tests/ivc_turn_chain_rotated.rs:958:    // B's carried multi-felt digest (irrelevant to the rejection — the segment tooth fails on
circuit-prove/tests/ivc_turn_chain_rotated.rs:960:    let mut b_chain_digest = [BabyBear::ZERO; SEG_DIGEST_WIDTH];
circuit-prove/tests/ivc_turn_chain_rotated.rs:961:    b_chain_digest[0] = b_pis[3];
circuit-prove/tests/ivc_turn_chain_rotated.rs:963:    // ----- The fold: A's REAL segment-bearing descriptor leaves -> one root. -----
circuit-prove/tests/ivc_turn_chain_rotated.rs:967:        let wrapped = prove_descriptor_leaf_rotated_with_segment(
circuit-prove/tests/ivc_turn_chain_rotated.rs:973:        .expect("A's rotated descriptor leaf wraps with its segment");
circuit-prove/tests/ivc_turn_chain_rotated.rs:977:    // Aggregate the segment leaves to ONE root (mirror the lib `aggregate_tree` combine:
circuit-prove/tests/ivc_turn_chain_rotated.rs:978:    // continuity + count additivity + ordered-digest fold, re-exposing the parent segment).
circuit-prove/tests/ivc_turn_chain_rotated.rs:985:            let left_idx = expose_claim_idx(&proofs[i].0).expect("left segment");
circuit-prove/tests/ivc_turn_chain_rotated.rs:986:            let right_idx = expose_claim_idx(&proofs[i + 1].0).expect("right segment");
circuit-prove/tests/ivc_turn_chain_rotated.rs:1029:            .expect("segment aggregation layer");
circuit-prove/tests/ivc_turn_chain_rotated.rs:1045:    // segment tooth reads A's root-exposed segment (= A's genesis/final/count/digest) and
circuit-prove/tests/ivc_turn_chain_rotated.rs:1052:        b_chain_digest,
circuit-prove/tests/ivc_turn_chain_rotated.rs:1057:    eprintln!("[codex-#2 mixed-root] verdict = {verdict:?}  (is_err = CLOSED; is_ok = STILL OPEN)");
circuit-prove/tests/ivc_turn_chain_rotated.rs:1060:    // ordered segment-accumulator binds the root-exposed [genesis, final, num_turns,
circuit-prove/tests/ivc_turn_chain_rotated.rs:1065:         leaves carrying a B whole-chain claim MUST be REJECTED by the segment tooth — A's \
docs/reference/circuit.md:139:   turn breaks continuity (UNSAT); a forged `chain_digest` has no satisfying
docs/reference/circuit.md:163:scalars `genesis_root`/`final_root`/`chain_digest`/`num_turns`
docs/reference/circuit.md:235:  `genesis_root`/`final_root`/`chain_digest`/`num_turns`. `expected_vk` is the
docs/reference/wasm-web.md:163:`AttestedHistory` — `attested`, genesis/final root, `chain_digest`, `num_turns`,
docs/design-frontiers/AGENT-SWARM-UX.md:323:expressivity. The cockpit's inbox is exactly the badge-OR accumulator made
docs/reference/firmament.md:111:- **Notification** — a badge-OR accumulator: `signal` ORs a badge and wakes
docs/deos/DOCUMENT-LANGUAGE.md:393:  first-class `ConflictRegion` (`Segment::{Clean,Conflict}`, an antichain of ≥2 live
docs/deos/UMEM-PRIMITIVE.md:350:a merge failure"* (`lib.rs:7`; `ConflictRegion`/`Segment::Conflict`, each `Alternative` tagged
metatheory/Dregg2/Paco/UpTo.lean:32:- `gupaco_clo F clo r`: Symmetric version (guard = accumulator)
metatheory/Dregg2/Paco/Coind.lean:42:/-- Coinduction with accumulator.
metatheory/Dregg2/Paco/Coind.lean:45:The step function can use both the witness R and the accumulator r.
metatheory/Dregg2/Paco/Coind.lean:145:When the accumulator and guard are both ⊥.
metatheory/Dregg2/Paco/Coind.lean:150:Simplified interface when no accumulator or guard is needed. -/
metatheory/Dregg2/Paco/Coind.lean:163:/-- Companion coinduction with ⊥ accumulator/guard. -/
docs/desktop-os-research/SEL4-RENDER-PATH.md:317:new seL4 capability: the `aarch64-sel4-roottask-musl` target links `--no-rosegment`,
docs/desktop-os-research/SEL4-RENDER-PATH.md:326:[render-pd] JIT W->X arena: 16384 KiB static RWX (--no-rosegment image)
docs/desktop-os-research/SEL4-RENDER-PATH.md:472:  success on the `--no-rosegment` already-X image). This is the one genuinely-new OS
metatheory/Dregg2/Paco/Tactic.lean:21:| `pbase` | `⊢ upaco F r x y` | Go right (use accumulator `r`) |
metatheory/Dregg2/Paco/Tactic.lean:37:    · pbase; ...      -- Base case: use accumulator
metatheory/Dregg2/Paco/Tactic.lean:227:- `pbase`: for using the accumulator instead
metatheory/Dregg2/Paco/Tactic.lean:235:/-- Use the accumulator relation (go into the r side of upaco).
metatheory/Dregg2/Paco/Tactic.lean:431:Apply monotonicity to weaken/strengthen the accumulator parameter.
metatheory/Dregg2/Paco/Tactic.lean:434:/-- Apply monotonicity of paco in the accumulator.
metatheory/Dregg2/Paco/Tactic.lean:453:/-- Apply monotonicity of upaco in the accumulator.
docs/desktop-os-research/SEL4-INTERACTIVE-COCKPIT.md:118:accumulator, no warp — which is exactly what a click-target hit-test wants. This
docs/deos/DOC-CELL-COMPOSITION.md:207:embed-atom, instead of pushing `Segment::Clean(text)` it pushes a
docs/deos/DOC-CELL-COMPOSITION.md:208:`Segment::Embedded(resolved)` where `resolved` is the **child cell rendered
docs/deos/DOC-CELL-COMPOSITION.md:219:    emit Segment::Embedded { role: E.role, provenance: E.provenance, child }
docs/deos/DOC-CELL-COMPOSITION.md:535:   emits `Segment::Embedded` for embed-atoms. *(prototype)*
docs/desktop-os-research/patches/gpui-offscreen.patch:88: unicode-segmentation.workspace = true
metatheory/docs/CODEX-IVC-SEGMENT-ACCUMULATOR-DESIGN.md:1:# Codex design — the ordered segment-accumulator fix for the IVC mixed-root hole (2026-06-24)
metatheory/docs/CODEX-IVC-SEGMENT-ACCUMULATOR-DESIGN.md:3:Codex's recommended construction (gigabrain advice, not a review): close the mixed-root forgery by making the whole-chain claim sound-BY-CONSTRUCTION — a constant-size ordered segment accumulator carried by every descriptor leaf + each aggregation node, replacing the separate binding leaf in the soundness-critical path.
metatheory/docs/DREGG-CALCULUS.md:459:surfaces antichains as `Segment::Conflict` for prose resolution.
metatheory/Metatheory/EnergyGame.lean:6:`Grade` is a capped budget-accumulator (`ℕ`, accumulated with the `PolisGrade` max-plus quantale's
metatheory/Metatheory/EnergyGame.lean:23:    failure modes the Boolean composition `combineFloor` had to catch on two axes are now one accumulator.
metatheory/Metatheory/EnergyGame.lean:72:cap is reached only at or above the budget). The accumulator is monotone — you cannot un-spend. -/
metatheory/Metatheory/EnergyGame.lean:221:both with ONE accumulator:
metatheory/Metatheory/EnergyGame.lean:307:single big jump are BOTH out of the energy floor. One accumulator, both failure modes — the two-axis
metatheory/Metatheory/EnergyGame.lean:372:     `combineFloor` catch unified into a single accumulator.
metatheory/docs/HARVEST-KEEPERS.md:36:- **LogUp migration (perf + soundness)** — replace bit-decomposition range checks (32 cols/wire) with shared range-table + one aux + 3 constraints; replace nullifier polynomial accumulator `∏(α−eᵢ)` with a sorted-neighbor / multiplicity-bounded LogUp bus (a clean algebraic statement of set semantics). Lean adds a `LookupKind` discriminator (localTable/globalBus/permBus); feature-gate behind `recursion`. (from: rebuild/DESIGN-lookups-plonky3-perf.md)
metatheory/docs/HARVEST-KEEPERS.md:96:- **The abstract-spec ≠ concrete-row gap is REAL and load-bearing** — `CircuitSpecTriangle` proves over an abstract witness; the EffectVM emitter proves over the concrete 186-col layout; NO proof bridges them (the row's `state_commit = H4(...)` is not yet proven equal to the spec's `compressN(...)`). Group-B passthrough effects have WEAK row-intent (only "frozen except nonce") while their abstract specs are strong — honest amplification must STATE the weak row-intent and explicitly defer real semantics; never overclaim per-row for turn/accumulator properties (nullifier non-membership, queue FIFO, handoff membership are CROSS-AIR, conditional on "the PI root is genuine"). (from: rebuild/_EMITTER-AMPLIFICATION-WORKLIST.md)
metatheory/docs/HARVEST-KEEPERS.md:132:- **Interpreter GAP #2** — `transition` constraints only read `next.state_before[hi]`; GROUP-7 custom-count accumulator needs a generalized next-column read form. (from: rebuild/_EMITTER-AMPLIFICATION-WORKLIST.md)
metatheory/docs/guides/circuit.md:100:new_root    = hash[record_leaf, old_root]                              -- a prepend-accumulator advance
metatheory/docs/guides/circuit.md:107:turn-level accumulator, the same boundary transfer's two-sided conservation has).
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:25:The strongest, most current strand is the **whole-chain IVC accumulator**:
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:69:  accumulator. `prove_turn_chain_recursive` folds a finite K-turn window into ONE root
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:77:  of N, reads off the genuine `genesis_root → final_root` + `chain_digest`. This IS
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:142:| Is the per-turn proof recursive (turn-proof attests prior turn-proof)? | **NO** at the per-turn layer — proofs are independent per-turn; the receipt chain threads a `previous_receipt_hash` ([u8;32] HASH, not a proof). Recursion lives in the SEPARATE `ivc_turn_chain` accumulator layer that folds N already-finalized turns. | `turn/src/witnessed_receipt.rs` (hash link), `turn/src/verify.rs` (hash-chain verify), vs `circuit-prove/src/ivc_turn_chain.rs` (the recursive fold) |
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:144:| Attenuation/delegation-depth IVC | **ALIVE** but DIFFERENT scope — `circuit/src/ivc.rs` folds an *attenuation* fold-chain (delegation depth), hash-chain accumulation with a real STARK backend (`StateTransitionAir`). NOT the whole-turn-chain accumulator. | `circuit/src/ivc.rs` |
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:147:accumulator** (`ivc_turn_chain`), Lean-proven in `RecursiveAggregation.lean`. It is NOT
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:207:| Unbounded online accumulator (single running proof, O(1) memory, re-folded forever) | `fold_two_turns` 2-step inductive core exists; the unbounded driver needs the fork's `into_recursion_input::<BatchOnly>` chaining driven as a fold not a tree | **GAP** (bounded-K today; unbounded is fork work) |
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:214:online accumulator (Mina is unbounded; dregg's `fold_two_turns` core exists but the
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:241:3. **(Larger) the unbounded online accumulator** — drive `fold_two_turns` as a running
metatheory/docs/CODEX-BUS-BALANCE-FIX.md:3:ROOT CAUSE (codex, the expose_claim bus designer): the W24 segment-digest expose_claim READS (mult=-1) have NO matching WRITES (mult=+1) in the aggregation child proof, because the W24 poseidon2_perm/baby_bear_d4_w24 table (whose output CTL emits the +1 writes) is registered at the LEAF layer but MISSING from the AGGREGATION layer's proof construction (only the W16 challenger + expose_claim are registered there). -> WitnessChecks global cumulative != 0 -> native verify_all_tables rejects GlobalCumulativeMismatch.
metatheory/docs/CODEX-BUS-BALANCE-FIX.md:8:## The invariant (per proof carrying the segment)
metatheory/docs/CODEX-BUS-BALANCE-FIX.md:9:- child segment values: PublicAir +1, expose_claim -1
metatheory/docs/CODEX-BUS-BALANCE-FIX.md:13:The bus does NOT carry upward — each aggregation layer re-exposes a new segment (new readers) needing new same-proof writers.
metatheory/docs/STALE-CRATE-DRIFT-CENSUS.md:63:`PolynomialAccumulator` (constant-size revocation accumulator).
metatheory/docs/STALE-CRATE-DRIFT-CENSUS.md:82:`hash` (4), `accumulator` (2). The `PolynomialAccumulator` is the live
metatheory/docs/STALE-CRATE-DRIFT-CENSUS.md:83:revocation accumulator used at `node/src/state.rs:16,295` (`NodeState.revocation_accumulator`,
metatheory/docs/STALE-CRATE-DRIFT-CENSUS.md:84:"O(1) polynomial accumulator over all revoked token hashes") and documented at
metatheory/docs/CODEX-IVC-REVIEW-3.md:1:# Codex re-review #3 — the segment-accumulator close + the weak-digest deviation (2026-06-24)
metatheory/docs/CODEX-IVC-REVIEW-3.md:3:VERDICT: PARTIAL CLOSE. Distinct-endpoint mixed-root forgery genuinely REJECTED (structural). But the digest deviation (base-field fold instead of codex's specified collision-resistant commitment) is a REAL soundness downgrade for same-endpoint/same-count histories — and it's ALGEBRAICALLY broken, not merely 31-bit.
metatheory/docs/CODEX-IVC-REVIEW-3.md:5:**Verdict: partial close.** The original mixed-root forgery with different genesis/final/count is closed in the K-fold path. The root proof exposes the descriptor-derived segment, and the verifier compares it to the carried claim at [ivc_turn_chain.rs:1757](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1757). So if A and B differ in genesis, final, or count, the rejection does not depend on the digest.
metatheory/docs/CODEX-IVC-REVIEW-3.md:12:   Leaf segments expose only `[old, new, 1, H(old,new)]` from PI 42/43 at [ivc_turn_chain.rs:1059](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1059). Aggregation exposes only `[first_old, last_new, count, acc]` at [ivc_turn_chain.rs:1632](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1632). The verifier does not pin intermediate roots independently; it checks only the folded root segment. The carried binding proof is explicitly ignored at [ivc_turn_chain.rs:1724](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1724).
metatheory/docs/CODEX-IVC-REVIEW-3.md:19:   Removing the swappable binding leaf from the soundness path was necessary. But now the only K-fold ordered-history commitment is the weak segment `acc`. The old Poseidon `TurnChainBindingAir` still exists and really constrains its digest at [ivc_turn_chain.rs:613](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:613), but it is no longer verified in the K-fold verifier.
metatheory/docs/CODEX-IVC-REVIEW-3.md:21:4. **Medium: the online accumulator is not closed by this fix.**  
metatheory/docs/CODEX-IVC-REVIEW-3.md:22:   [accumulator.rs:39](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:39) explicitly says the online accumulator still uses a separate binding leaf and retains the mixed-root structural weakness. Scope the close to the balanced K-fold path only.
metatheory/docs/CODEX-IVC-REVIEW-3.md:27:**Bottom line:** distinct-endpoint mixed-root forgery is genuinely rejected. Full ordered-history soundness is not achieved. Same-endpoint/same-count histories rely on a one-felt, algebraically weak digest; if an attacker can realize colliding intermediate roots as valid executions, a proof of A can stand in for B’s middle history. The fix should replace `seg_hash2_*` with an in-circuit collision-resistant multi-felt commitment, and the root claim should carry that wider digest.
metatheory/docs/CODEX-IVC-REVIEW-3.md:29:**Verdict: partial close.** The original mixed-root forgery with different genesis/final/count is closed in the K-fold path. The root proof exposes the descriptor-derived segment, and the verifier compares it to the carried claim at [ivc_turn_chain.rs:1757](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1757). So if A and B differ in genesis, final, or count, the rejection does not depend on the digest.
metatheory/docs/CODEX-IVC-REVIEW-3.md:36:   Leaf segments expose only `[old, new, 1, H(old,new)]` from PI 42/43 at [ivc_turn_chain.rs:1059](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1059). Aggregation exposes only `[first_old, last_new, count, acc]` at [ivc_turn_chain.rs:1632](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1632). The verifier does not pin intermediate roots independently; it checks only the folded root segment. The carried binding proof is explicitly ignored at [ivc_turn_chain.rs:1724](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1724).
metatheory/docs/CODEX-IVC-REVIEW-3.md:43:   Removing the swappable binding leaf from the soundness path was necessary. But now the only K-fold ordered-history commitment is the weak segment `acc`. The old Poseidon `TurnChainBindingAir` still exists and really constrains its digest at [ivc_turn_chain.rs:613](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:613), but it is no longer verified in the K-fold verifier.
metatheory/docs/CODEX-IVC-REVIEW-3.md:45:4. **Medium: the online accumulator is not closed by this fix.**  
metatheory/docs/CODEX-IVC-REVIEW-3.md:46:   [accumulator.rs:39](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:39) explicitly says the online accumulator still uses a separate binding leaf and retains the mixed-root structural weakness. Scope the close to the balanced K-fold path only.
metatheory/docs/CODEX-IVC-REVIEW-2.md:3:VERDICT: the exposed-claim channel is SOUND (the old forgery rejects), but #1 NOT fully closed — a DEEPER mixed-root hole remains.
metatheory/docs/CODEX-IVC-REVIEW-2.md:25:- tooth 3: mixed root verifies: [ivc_turn_chain.rs:1537](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1537)
metatheory/docs/CODEX-IVC-REVIEW-2.md:41:The flipped test at [ivc_turn_chain_rotated.rs:595](/Users/ember/dev/breadstuffs/circuit-prove/tests/ivc_turn_chain_rotated.rs:595) covers only the old external cross-pairing shape. It does not cover the mixed-root attack above. I would add a test that constructs descriptor leaves from A, binding leaf from B, aggregates them into one root, carries B’s binding proof/claims, and asserts rejection. I expect current code to accept unless there is another cross-leaf equality constraint outside the reviewed paths.
metatheory/docs/CODEX-IVC-REVIEW-2.md:64:- tooth 3: mixed root verifies: [ivc_turn_chain.rs:1537](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1537)
metatheory/docs/COMPOSITION-SOUNDNESS-CENSUS.md:66:| 2 | Intra-turn accumulator (two noteSpend / two mint in one turn) | **HANDLED — definitionally threaded** | `turnSpec` `ActionDispatch.lean:243–246` (`fullActionStep st a st1 ∧ turnSpec st1 rest st'`); per-step kernel forced by seam #1 | low |
metatheory/docs/COMPOSITION-SOUNDNESS-CENSUS.md:98:### Seam #2 — Intra-turn accumulator (double noteSpend / double mint): HANDLED
metatheory/docs/COMPOSITION-SOUNDNESS-CENSUS.md:104:double-spend. The accumulator is threaded by the *recursive structure* of `turnSpec`, and each `st1`
metatheory/docs/COMPOSITION-SOUNDNESS-CENSUS.md:105:kernel is pinned by seam #1. **No accumulator double-count forgery** — the two-spend-in-one-turn case
metatheory/docs/COMPOSITION-SOUNDNESS-CENSUS.md:267:(intermediate kernels forced, accumulators threaded, joint/forest binding carried). It does NOT yet
metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md:12:   [ivc_turn_chain.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:375) enforces seam continuity, first root, final root, and accumulator carry-forward, but never enforces `acc_out = H(acc_in, old_root, new_root, idx)`. It explicitly says `numTurns` is unconstrained at [ivc_turn_chain.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:378). The honest trace generator computes the hash at [ivc_turn_chain.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:457), but that is prover-side discipline, not verifier soundness.  
metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md:13:   **Attack:** produce a binding proof for arbitrary `chain_digest` and arbitrary `num_turns` by choosing accumulator columns that satisfy only the carry constraints. This breaks the claimed ordered-history commitment even before considering recursion.
metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md:15:3. **Critical/High: the real accumulator silently disables VK pinning on mismatch.**  
metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md:16:   [accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:529) sets `pin_this_fold` only if the current running preprocessed commitment equals the saved pin. If it differs, the code falls through to `running.into_recursion_input::<BatchOnly>()` at [accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:535), meaning the fold proceeds unpinned instead of rejecting. The test at [accumulator.rs test](/Users/ember/dev/breadstuffs/circuit-prove/tests/accumulator.rs:296) uses `probe_pinned_fold`, which always calls the pinned path, so it does not test this branch.  
metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md:20:   The claim is made in [accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:67), while the test only samples depth 4 and 5 at [tests/accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/tests/accumulator.rs:370). One equality measurement is not an induction. To prove fixed point, the code needs a structural argument that the wrapped input proof shape, rows, non-primitive manifest, preprocessed metadata, and verifier op-list are identical under another fold. The file itself still says the structural half is residual at [accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:129).  
metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md:24:   [accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:648) folds the running proof with the binding leaf using `into_recursion_input`, not the pinned path, and [accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:651) uses `ProveNextLayerParams::default()` instead of the wrap params.  
metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md:25:   **Gap:** even if the running accumulator stabilizes, the terminal proof may have a depth/shape-dependent root VK. That weakens the “constant verifier forever” story unless separately anchored and measured for every relevant finalization shape.
metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md:35:8. **Medium: the accumulator is not O(1) state as implemented.**  
metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md:36:   The code stores all seam pairs in `seam_pairs` at [accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:256), and finalization rebuilds the binding proof from them. The comment at [accumulator.rs](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:241) admits `O(num_turns)` scalar witness state.  
metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md:37:   **Impact:** proof memory may be bounded, but the running accumulator state is not strictly constant-size.
metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md:40:   `EngineSound` assumes recursive soundness, positional leaf-to-step pairing, and binding soundness at [RecursiveAggregation.lean](/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/RecursiveAggregation.lean:115). The unbounded accumulator stores a `leanWitness` directly at [RecursiveAggregation.lean](/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/RecursiveAggregation.lean:487), and `acc_attests_whole_history` is just projection at [RecursiveAggregation.lean](/Users/ember/dev/breadstuffs/metatheory/Dregg2/Circuit/RecursiveAggregation.lean:628).  
metatheory/docs/CODEX-IVC-FINAL-REVIEW.md:3:VERDICT: for the K-fold segment path, NO critical soundness hole — the same-endpoint mixed-root forgery is GENUINELY CLOSED under the Poseidon2 truncated-output commitment assumption.
metatheory/docs/CODEX-IVC-FINAL-REVIEW.md:7:- THE DIGEST IS NOT ~31-bit coeff-0-only: dregg compares a 7-felt segment claim — genesis, final, count, + FOUR BabyBear digest lanes (ivc_turn_chain.rs:224 + :1963). ~124-bit digest collision resistance.
metatheory/docs/CODEX-IVC-FINAL-REVIEW.md:11:- MEDIUM (scope): the ONLINE ACCUMULATOR path (accumulator.rs:171/819/916) is still single-felt/zero-padded, explicitly scoped out — do NOT generalize the K-fold close to it. The named separate follow-up.
metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md:68:| **ring_closure** | **ASPIRATIONAL (Silver)** `cell/src/ring_closure.rs:1`, `silver` (`:280`) BLAKE3 commitment, no STARK; `RingClosureAttestation` has ZERO live callers | Attest that N parallel transfers form a closed cycle (coequalizer of the bilateral binding) — composable rings for apps | The bilateral binding is wired (`turn/src/bilateral_schedule.rs` `ExpectedBilateral` is consumed in `executor/proof_verify.rs`); ring_closure is its N-ary Silver sibling, BLAKE3-only ("Golden = STARK" deferred in-module). Weld = lift the cycle-closure into the accumulator the way bilateral is. **Medium-large, VK-affecting** (Golden). Low priority — Silver is a witness commitment, not yet a verified move |
metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md:70:| **unilateral** | **ALIVE-WIRED (data + PI), accumulator-orphaned** `cell/src/unilateral.rs:1`; `turn/src/bilateral_schedule.rs:333` `unilateral_pi_tag`/`unilateral_salt` project into the circuit's `UNILATERAL_ATTESTATION_KIND_*` PI lanes (`circuit/src/effect_vm/pi.rs:538`); `cross_fed_cite.rs:43` builds attestations | A cell binding a property over its OWN transition without a counterparty (the 1-arity sibling of bilateral Transfer/Grant and trilateral Introduce) | The PI-tag/salt/build path is live and tested; the **accumulator** functions (`bilateral_schedule.rs:458` `push_unilateral`, `:470` `unilateral_root_for`) have NO live consumer — the bilateral path IS driven (`extract_from_pi` in proof_verify), the unilateral sibling is not folded into a turn yet. Weld = drive `push_unilateral` from the executor the way bilateral is. **Small, not VK-affecting** (PI lanes reserved) |
metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md:115:4. **unilateral accumulator drive** — *small.* PI lanes + tag/salt + builder are live; only
metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md:127:   Golden (STARK, accumulator-lifted) is the real weld and is module-deferred.
metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md:132:- **unilateral** is ALIVE on its data + PI-projection path (only the accumulator fold is
metatheory/Dregg2/Resource.lean:39:    (`Laws.lean`) — succinctly checkable (a field sum, sum-`≤`-1, a sorted-id accumulator,
metatheory/docs/PROGRAM-NOTIFY-WELD.md:49:firmament's notify object. The badge-OR accumulator and the cap-gating stay in
metatheory/Dregg2/Spec/Lifecycle.lean:327:recursive accumulator `accum`, into the single checkpoint digest `h`. This is the SAME
metatheory/Dregg2/Spec/Lifecycle.lean:338:recursive accumulator. Given the prefix and that `checkpointHash = foldl accum seed
metatheory/Dregg2/Crypto/NonMembership.lean:32:a sorted/accumulator structure; the sorted-tree neighbor-bracketing is the canonical realization).
metatheory/Dregg2/Paco/UpTo/GPacoClo.lean:13:- `gupaco_clo F clo r`: Symmetric version (guard = accumulator)
metatheory/Dregg2/Paco/UpTo/GPacoClo.lean:66:/-- Symmetric version: guard equals accumulator -/
metatheory/Dregg2/Paco/UpTo/GPacoClo.lean:353:When you have a gpaco predicate and use it as the accumulator for gupaco,
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:16:tree; the proof attempt refutes the unconditional statement. A wave's segment is its
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:41:  (2) `fold_agrees` — replaying the OLD leaders' segment computation in the GROWN lace
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:42:      reproduces the same segments and coverages (no late ratifier grew an old wave's
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:85:  splices a segment mid-order);
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:86:* `fold_agrees` — replaying the OLD leaders through `B'`'s segment computation
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:87:  (`tauStep B'`) reproduces the `B` fold exactly: same emitted segments AND same coverage
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:120:        leaderSegment B' P wl c l = leaderSegment B P wl c l)
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:126:      (∀ l ∈ L, ∀ c : List BlockId, leaderSegment B' P wl c l = leaderSegment B P wl c l) →
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:144:/-- One `tauStep` extends the accumulated order by the leader's segment (definitional). -/
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:147:    (tauStep B P wl acc l).1 = acc.1 ++ leaderSegment B P wl acc.2 l := rfl
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:149:/-- **`foldl_tauStep_fst_extend`** — folding ANY further leader list onto an accumulator
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:152:per-leader segments — exactly the two fields of `FinalizedRegionStable`. -/
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:159:    exact ⟨leaderSegment B P wl acc.2 l ++ r, by
metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:272:round-4 block 23) is super-ratified at round 6, its segment — the nine new blocks — is
metatheory/Dregg2/Crypto/DfaAcceptanceAir.lean:114:/-- One **AIR row**: public `state`/`sym`/`next` and the two `Digest` accumulator columns
metatheory/Dregg2/Consensus/OnDemandFeasibility.lean:86:segment, one permutation = the verified `tauOrder` restriction, the other = the causal
metatheory/Dregg2/Crypto/SchnorrCurveField.lean:304:the witnessed accumulator to be the genuine scalar product. Abstracting `smul` as opaque hides exactly
metatheory/Dregg2/Crypto/SchnorrCurveField.lean:318:accumulator (the trace's `ACC` column), `base` the running `2^i·G` (the `BASE` column). -/
metatheory/Dregg2/Crypto/SchnorrCurveField.lean:328:accumulator `acc` and running base `base`, yields `acc + (value of the bits)·base`. Proven by
metatheory/Dregg2/Crypto/SchnorrCurveField.lean:329:induction generalizing the running base (= `2^k·G`) and accumulator — the loop invariant the AIR's
metatheory/Dregg2/Crypto/SchnorrCurveField.lean:330:accumulator/base transitions encode. -/
metatheory/Dregg2/Crypto/SchnorrCurveField.lean:348:which is what `scan_computes_scalar_products` asserts (`phase-0 final accumulator == s·G`). -/
metatheory/Dregg2/Crypto/SchnorrCurveField.lean:357:result — so the accumulator is NOT bit-independent; a tampered bit yields a different scalar product,
metatheory/Dregg2/Crypto/SchnorrCurveField.lean:364:accumulator depends on every bit, so a stale/flipped bit produces a wrong scalar product. Mirror of
metatheory/Dregg2/Distributed/HistoryAggregation.lean:2:# Dregg2.Distributed.HistoryAggregation — the FOLD model under the IVC accumulator.
metatheory/Dregg2/Distributed/HistoryAggregation.lean:4:**What this is.** The whole-chain IVC accumulator (`circuit/src/ivc_turn_chain.rs`) folds a
metatheory/Dregg2/Distributed/HistoryAggregation.lean:143:The accumulator's final claim is "`final_root` = the genuine fold of the whole history"
metatheory/Dregg2/Distributed/HistoryAggregation.lean:148:(`lastStateOf`) under the last step's turn-context (the `NEW_COMMIT` the accumulator exposes; the
metatheory/Dregg2/Distributed/HistoryAggregation.lean:157:The accumulator's verifier only sees ROOTS, not states. Under collision-resistance of the commitment
metatheory/Dregg2/Distributed/HistoryAggregation.lean:164:chain. So an honest accumulator never asserts the tooth separately — it is free from execution. -/
metatheory/Dregg2/Distributed/HistoryAggregation.lean:323:holds under the accumulator's NoOp-padding (`ivc_turn_chain.rs:325`), and `AccountsWF` is the
metatheory/Dregg2/Distributed/HistoryAggregation.lean:390:configuration the accumulator's NoOp-padding establishes — see `ivc_turn_chain.rs:325`). This makes
metatheory/Dregg2/Distributed/HistoryAggregation.lean:409:This is the meaning the IVC accumulator's `WholeChainProof` claims; `RecursiveAggregation.lean`
metatheory/Dregg2/Distributed/Consensus.lean:72:* `OPEN-CM-XSORT` — the intra-segment `tau` linearization tie-break is still open in
metatheory/Dregg2/Distributed/Consensus.lean:449:round-robin ANCHOR LABEL (which block a segment is named after), not a process whose proposal must
metatheory/Dregg2/Distributed/Consensus.lean:486:metadata (which segment a block anchors), not a liveness-critical authority.
metatheory/Dregg2/Proof/CordialMiners.lean:37:  super-ratified leader **anchors** a segment of the total order (`tau`).
metatheory/Dregg2/Proof/CordialMiners.lean:78:  * **OPEN-CM-XSORT.** The deterministic intra-segment `xsort` total order (`ordering.rs::xsort`,
metatheory/Dregg2/Proof/CordialMiners.lean:81:    safety question, not the within-segment tie-break.
metatheory/Dregg2/Proof/CordialMiners.lean:341:*single* segment of `tau` — recovered as a theorem about the protocol dregg1 runs. -/
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:18:     (union of causal pasts of ratifying wave-end blocks), take the blocks NEW to this segment
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:49:* `xsort` intra-segment tie-break is the OPEN-CM-XSORT residual (named in `ConsensusExec`); here we
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:50:  linearize a segment by `(round, id)` — deterministic, causal-respecting on the traces we exhibit;
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:235:append. The intra-segment linearization is the OPEN-CM-XSORT residual; here we sort by `(round, id)`
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:249:/-- Deterministic intra-segment linearization by `(round, id)` — the OPEN-CM-XSORT stand-in. A
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:256:/-- **`leaderSegment B participants wavelength prevCovered l`** — the blocks a final leader `l`
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:258:from the leader, linearized by `xsortBy`. The per-leader segment of `ordering.rs::tau`'s loop
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:261:def leaderSegment (B : Lace) (participants : List AuthorId) (wavelength : Nat)
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:271:segment to the order accumulated so far, and replace `prevCovered` with this leader's coverage
metatheory/Dregg2/Distributed/BlocklaceFinality.lean:276:  (acc.1 ++ leaderSegment B participants wavelength acc.2 l,
metatheory/Dregg2/Distributed/ThresholdDecrypt.lean:74:of `b`, conditionally XOR `a` into the accumulator, then shift `a` left with the `0x1b` reduction when the
metatheory/Dregg2/Distributed/FinalityGate.lean:108:/-- Parse the `B=` lace segment (a `|`-separated list of `BLOCKW`, or empty). -/
metatheory/Dregg2/Distributed/FinalityGate.lean:125:  -- split into the three `;`-separated segments: "<w>", "P=<...>", "B=<...>".
metatheory/Dregg2/Privacy.lean:402:  (the witness is a Merkle/accumulator opening; hides which element). -/
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:14:depth-16 binary-Merkle fold the cap-tree REALLY commits, NOT a felt accumulator):
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:36:     against the REAL deployed commitment, not a felt accumulator.
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:165:accumulator). The exact sorted-tree move for delegate / introduce / grantCap. -/
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:212:of `attenuateSlotF`. This UPGRADES `attenuate` from the felt-accumulator VALUE_PARTIAL: the sorted-tree
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:245:against the REAL deployed commitment. THIS is the upgrade past the felt-accumulator VALUE_PARTIAL: the
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:262:felt-accumulator VALUE_PARTIAL: the sorted-tree set move is forced against the real commitment. -/
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:1052:column, so the rotated cap-root limb is free to carry the DELEG accumulator). `refreshDelegationWriteV3_forces_write`
metatheory/Dregg2/Circuit/RotatedKernelRefinementCapFamily.lean:1069:  -- limbs (the rotated cap-root limb 25 carries the DELEG accumulator on a refresh row; refresh freezes caps).
metatheory/Dregg2/Circuit/StateCommit.lean:219:`LH xs = LH ys ⇒ xs = ys`. The standard collision-resistance of a Poseidon log/Merkle accumulator
metatheory/Dregg2/Firmament/SeL4Kernel.lean:9:spec calls for: a synchronous **Endpoint** (rendezvous), a **Notification** (badge-OR accumulator),
metatheory/Dregg2/Firmament/SeL4Kernel.lean:228:/-! ## §2 — The Notification: the badge-OR accumulator.
metatheory/Dregg2/Firmament/SeL4Kernel.lean:230:Mirrors `Notification` (`emulated_kernel.rs:138`): one `badge : u64` accumulator. `Signal` ORs the
metatheory/Dregg2/Firmament/SeL4Kernel.lean:232:wait, resets to zero). We model the accumulator as a `Nat` and the badge-OR as `Nat`-bitwise-or
metatheory/Dregg2/Firmament/SeL4Kernel.lean:236:/-- A Notification object — the badge-OR accumulator (`badge : u64`). Mirrors `Notification`
metatheory/Dregg2/Firmament/SeL4Kernel.lean:248:/-- **`signal n badge`** — `seL4_Signal`: OR `badge` into the accumulator. Non-blocking (a signal
metatheory/Dregg2/Firmament/SeL4Kernel.lean:260:in `badges` in order (what the accumulator holds when a `Wait` finally runs). -/
metatheory/Dregg2/Firmament/SeL4Kernel.lean:724:the accumulator), then resets. The seL4 accumulation: the returned badge is the OR of every signal
metatheory/Dregg2/Circuit/DescriptorIR2.lean:275:/-! ### The accumulator / recursive-proof-binding op (`docs/EPOCH-DESIGN.md` — the Custom leg).
metatheory/Dregg2/Circuit/DescriptorIR2.lean:298:/-- An accumulator / recursive-proof-binding op: the row's `custom_proof_commitment` column
metatheory/Dregg2/Circuit/DescriptorIR2.lean:369:op (`umemOp`, additive: no shipped descriptor emits it until the rotation), the accumulator /
metatheory/Dregg2/Circuit/DescriptorIR2.lean:824:/-! ## §6c — `Satisfied2Custom`: the accumulator / recursive-proof-binding denotation (the Custom leg).
metatheory/Dregg2/Circuit/DescriptorIR2.lean:882:/-- **The custom-binding denotation** — `Satisfied2` PLUS the accumulator leg: every declared
metatheory/Dregg2/Circuit/DescriptorIR2.lean:1364:/-- Render one proof-binding op (the accumulator / recursive-proof binding: the row's
metatheory/Dregg2/Circuit/DescriptorIR2.lean:1638:/-! ### §10c — the PROOF-BINDING (Custom accumulator) demo: wire golden + non-vacuity + the
metatheory/Dregg2/Firmament/NotifyOrgans.lean:24:  * `Dregg2.Firmament.SeL4Kernel.Notification` — the badge-OR accumulator (the canonical model §3.1 says
metatheory/Dregg2/Firmament/NotifyOrgans.lean:25:    "the others refine"). Each organ's wake accumulator is modelled as THIS one object (a pubsub head, an
metatheory/Dregg2/Firmament/NotifyOrgans.lean:33:membership / nothing at all — becomes "hold a `NotifyCap` over the organ's accumulator", and the
metatheory/Dregg2/Firmament/NotifyOrgans.lean:41:  | **PUBSUB / channels** | YES (`Apps/PubsubFactory.lean`) | publish-wake as `signalGated` (§1): a publisher holds a `NotifyCap` to the topic's Notification accumulator; publishing a badge is `signalGated`; an ATTENUATED subscriber cap = "may receive badge X only"; a publisher can't signal a badge it doesn't hold + an attenuated subscriber receives a SUBSET. |
metatheory/Dregg2/Firmament/NotifyOrgans.lean:50:over ANY organ wake (any `(cap, accumulator, badge)`) and shows every one obeys the SAME three laws
metatheory/Dregg2/Firmament/NotifyOrgans.lean:83:wake), the badge-OR accumulator (the organ's wake surface — a pubsub head, an inbox head, an event log),
metatheory/Dregg2/Firmament/NotifyOrgans.lean:90:wake" authority), the `Notification` badge-OR accumulator (the wake surface — the same object for every
metatheory/Dregg2/Firmament/NotifyOrgans.lean:94:  /-- The held capability to wake this organ's accumulator (the §2.0 "may poke" authority). -/
metatheory/Dregg2/Firmament/NotifyOrgans.lean:103:accumulator. This is the SINGLE definition every organ's wake reduces to — the WELD made one function.
metatheory/Dregg2/Firmament/NotifyOrgans.lean:112:accumulator; publishing topic-kind `b` is `signalGated` — it commits iff `b` is within the publisher's
metatheory/Dregg2/Firmament/NotifyOrgans.lean:119:(object `publisher`'s reach is the topic's badge-OR accumulator, scoped to topic-kinds within
metatheory/Dregg2/Firmament/NotifyOrgans.lean:126:`topicKind` into the topic's accumulator is `signalGated` under the publisher's cap. Commits (OR's the
metatheory/Dregg2/Firmament/NotifyOrgans.lean:127:topic-kind into the accumulator, waking every subscriber) iff `topicKind ⊑ topicMask`; refuses
metatheory/Dregg2/Firmament/NotifyOrgans.lean:144:accumulator — the weld is that this organ's publish IS that gate. -/
metatheory/Dregg2/Firmament/NotifyOrgans.lean:152:COMMITS, OR'ing exactly that kind into the topic's accumulator (waking subscribers). The non-vacuity
metatheory/Dregg2/Firmament/NotifyOrgans.lean:177:the inbox's Notification accumulator (the deliver surface); delivering a message tagged `senderTag` is
metatheory/Dregg2/Firmament/NotifyOrgans.lean:183:`inbox`'s accumulator, scoped to sender-tags within `senderMask`). The held replacement for sender-set
metatheory/Dregg2/Firmament/NotifyOrgans.lean:189:tagged `senderTag` into the inbox's accumulator is `signalGated` under the sender's cap. Commits (OR's
metatheory/Dregg2/Firmament/NotifyOrgans.lean:201:accumulator. -/
metatheory/Dregg2/Firmament/NotifyOrgans.lean:209:COMMITS, OR'ing the tag into the inbox accumulator (the owner's wake). Non-vacuity partner. -/
metatheory/Dregg2/Firmament/NotifyOrgans.lean:276:`(cap, accumulator, badge)` — i.e. as an `OrganWake.fire`. The unification: EVERY organ wake obeys the
metatheory/Dregg2/Firmament/NotifyOrgans.lean:284:(any organ's `(cap, accumulator, badge)`), its wake obeys the three notify laws:
metatheory/Dregg2/Firmament/NotifyOrgans.lean:353:publish, inbox deliver, and event emit, on the SAME cap / accumulator / badge, are the IDENTICAL
metatheory/Dregg2/Firmament/NotifyOrgans.lean:427:-- The three gated wakes, on one cap/accumulator/badge, agree exactly (the weld, witnessed): a held badge.
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:8:that the IVC accumulator (`circuit/src/ivc_turn_chain.rs::prove_turn_chain_recursive` →
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:94:  /-- Public: the running digest of the ordered (old,new) pairs (`WholeChainProof.chain_digest`). -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:446:This section proves the part Mina LACKS: that the accumulator can be driven as a CONTINUOUS LEFT-FOLD
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:448:memory (keep only `acc_{n-1}`), and that the running accumulator's attestation is PRESERVED at every
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:456:  `acc_attests_whole_history` — folding `accumulate` from the genesis accumulator over a state-extending
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:457:  stream yields an accumulator attesting `WellFormedChain g (the whole stream)`. The base case is the
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:460:This is the SOUNDNESS SKELETON of the unbounded online accumulator. The CRYPTO carrier (the running
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:469:via `seam_roots_chain` (state-chaining ENTAILS the root tooth, the "honest accumulator never asserts the
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:482:/-- **The running accumulator state.** It carries the genesis it folds from, the ordered list of steps
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:493:/-- **`Acc.head g acc`** — the state the running accumulator has reached: `lastStateOf` of the folded
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:578:/-- **`accumulate acc s hseam hturn`** — the running left-fold step. Given the running accumulator
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:607:/-- **`accumulate_preserves_wellformed` (THE IVC INVARIANT).** The running accumulator's attestation is
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:609:the inductive heart of the unbounded accumulator — `acc_{n-1} ⊢ 0..n-1` and `turn_n` extends ⟹
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:619:/-- **`acc_attests_whole_history` (THE IVC HEADLINE — by induction from genesis).** The running
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:620:accumulator attests the WHOLE history it has folded: `acc.leanWitness` IS a `WellFormedChain` from
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:621:genesis over `acc.steps`, for ANY accumulator reachable from `genesisAcc` by `accumulate` steps. We
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:628:theorem acc_attests_whole_history {g : RecChainedState}
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:633:/-- **`acc_attests_run` (the run the accumulator inherits).** The accumulated history is a genuine
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:634:`Run recChainedSystem` from genesis to the accumulator's head — so EVERY run-level theorem of the
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:643:entire history the running accumulator folded: the ledger total at the head equals the genesis total. A
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:651:/-! ### IVC non-vacuity — the accumulator FIRES on a real chain (genesis → one accumulate step).
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:654:teeth genesis and `accumulate` the honest step into it, getting a length-1 accumulator whose witness is
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:665:/-- The realizing accumulator: `genesisAcc` over the teeth genesis, then one `accumulate` of the honest
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:674:/-- **`ivc_accumulate_fires` (IVC non-vacuity).** The realizing accumulator attests a REAL well-formed
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:678:  acc_attests_whole_history zCH zRH zcmb zcompress zcompressN ivcRealAcc
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:681:realizing accumulator's folded history conserves the ledger total: head total = genesis total. So the
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:704:-- the UNBOUNDED IVC accumulator: the running left-fold preserves whole-history attestation, by
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:711:#assert_axioms Dregg2.Circuit.RecursiveAggregation.acc_attests_whole_history
metatheory/Dregg2/Firmament/NotifyAuthority.lean:25:  * `Dregg2.Firmament.SeL4Kernel.Notification` — the badge-OR accumulator (`signal n badge :=
metatheory/Dregg2/Firmament/NotifyAuthority.lean:29:    this exact `Notification.signal` — it does not re-implement the accumulator.
metatheory/Dregg2/Firmament/NotifyAuthority.lean:58:     accumulator) iff the signalled badge is within the held mask, and REFUSES (`none`) a badge with a
metatheory/Dregg2/Firmament/NotifyAuthority.lean:202:(`badge &&& badgeMask`, which equals `badge` exactly when admissible, §1) into the accumulator via the
metatheory/Dregg2/Firmament/NotifyAuthority.lean:284:badge is admissible, `signalGated` returns `some` and the accumulator gains precisely `badge` (the
metatheory/Dregg2/Firmament/NotifyAuthority.lean:425:-- The committed badge OR's into the accumulator EXACTLY (no truncation): signalling 0b001 then 0b100
metatheory/Dregg2/Circuit/RotatedKernelRefinementNotesFresh.lean:24:nullifier accumulator). `NullifierTreeEncodes S root pre` says: the tree at `root` commits a key set
metatheory/Dregg2/Circuit/RotatedKernelRefinementNotesFresh.lean:82:nullifier-accumulator commitment), never an axiom. -/
metatheory/Dregg2/Deos/ReplayMembrane.lean:112:  -- induction on the trace, threading the accumulator; agreement on members carries through `foldl`.
metatheory/Dregg2/Proof/CoinductiveAdversary.lean:401:  --     Use the coinduction principle for gpaco_clo with accumulator/guard ⊥.
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:16:  1. **OPEN-CM-XSORT — the deterministic intra-segment total order (`ordering.rs::xsort`).**
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:17:     `ordering.rs` orders the blocks *within* a super-ratified segment deterministically, tie-broken
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:20:     segment (a `List Block`), i.e. a genuine total preorder — and define `Block.xsort` (the
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:22:     `xsort_perm`/`xsort_length` (it permutes the segment, losing nothing), `xsort_idem`
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:23:     (determinism: re-sorting is a no-op), and `xsort_segment_total_order` (the output is a
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:24:     **linear extension**: any two distinct segment blocks are strictly comparable by id). This is
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:25:     the within-segment determinism `cordial_agreement` deliberately scoped out — now a theorem.
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:87:/-! ## 1. OPEN-CM-XSORT closed: the deterministic intra-segment total order.
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:89:`ordering.rs::xsort` deterministically orders the blocks *within* a super-ratified segment, tie-
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:90:broken by block id so two honest nodes computing `tau` over the same segment agree on the order.
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:92:transitive, total — over an arbitrary segment, then build the sort and prove it is a genuine
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:93:linear extension (sorted + a permutation of the segment + idempotent). -/
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:102:/-! ### 1a. `xsort_consistency`: reflexive, transitive, total over a segment.
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:104:These are the three laws the task asks for. Stated *over a segment* `seg : List Block` (the
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:105:super-ratified segment `xsort` orders) — though `xleq` is in fact a total preorder on ALL blocks,
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:124:is a genuine total preorder over any segment `seg`: reflexive, transitive, and total on the segment's
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:126:the same segment get the same order. Packaged as one statement over an explicit segment. -/
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:141:/-- **`Block.xsort seg`** (`ordering.rs::xsort`): the deterministic ordering of a segment, sorting
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:142:by block id via insertion sort over `xleq`. The within-segment total order `cordial_agreement`
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:151:/-- **`xsort_perm`** — `xsort` only *reorders*: it is a permutation of the segment, so the
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:152:total order loses no block and invents none (the `tau` segment is exactly the super-ratified blocks,
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:161:/-- **`xsort_mem`** — membership is preserved both ways: a block is in the sorted segment
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:162:iff it was in the segment. -/
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:166:/-- **`xsort_idem` (DETERMINISM).** Re-sorting an already-sorted segment is a no-op:
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:173:/-- **`xsort_segment_total_order` (the linear-extension keystone).** On a *canonical*
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:174:segment (distinct blocks have distinct ids — the content-addressing invariant, exactly
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:175:`Lace.Canonical` restricted to the segment), `xsort` realizes a genuine **linear order**: any two
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:176:DISTINCT blocks of the segment are *strictly* id-comparable (`a.id < b.id ∨ b.id < a.id`), and the
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:177:sorted output puts them in that strict order. So `tau` is a total order on the segment, not merely a
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:178:preorder — the deterministic within-segment ranking `ordering.rs::xsort` guarantees. This closes
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:180:theorem xsort_segment_total_order (seg : List Block)
metatheory/Dregg2/Proof/CordialMinersLiveness.lean:517:#assert_axioms xsort_segment_total_order
metatheory/Dregg2/Exec/FieldsMap.lean:12:single `fields_root` = `ListCommit.listDigest` — the SAME injective accumulator the side-table
metatheory/Dregg2/Exec/FieldsMap.lean:27:name-keyed `Value`/`scalar`) and `Circuit.ListCommit` (the injective accumulator portal).
metatheory/Dregg2/Circuit/Argus/InterpGolden.lean:36:    `HashInput` form (`col`/`digest`/`zero`), arity 2 AND 4, the ORDERED digest-accumulator
metatheory/Dregg2/Circuit/Argus/InterpGolden.lean:47:SEMANTICS (binding equation, accumulator order, input resolution), not the Poseidon2 instance;
metatheory/Dregg2/Exec/TriDomain.lean:149:`atomic.rs` carries an `excess` accumulator per domain. We read a `RecChainedState` into three
metatheory/Dregg2/Exec/TriDomain.lean:156:These are the executable shadows of `atomic.rs`'s three per-domain `excess` accumulators. -/
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:58:2. **The shape-AIR vs real-AIR CENSUS GAP remains the named carried hypothesis.** The IVC accumulator
metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:62:    `CanonicalHeapTree`/`update_witness`, BUILT + differential-tested). The accumulator advance
metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:64:    `newRoot` is now bound to the sorted-tree SPLICE, not merely a prepend-accumulator advance: a root
metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:65:    that is the right accumulator but the WRONG sorted-tree update is REJECTED. The Rust deployed-level
metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:215:14-field frame ride the named decode residual. NOTE the forced recompute is the prepend-accumulator
metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:223:prepend-accumulator advance over `leafOf(addrOf coll key, value)` and `oldRoot` (`EffectVmEmitHeapRoot`
metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:289:prepend-accumulator advance; the sorted-Merkle splice binding is the named Phase-E residual.) -/
metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:352:sorted leaf list (`MapMerkleRoot.mapRoot (Heap.set h addr v)`), not the one-leaf accumulator. The
metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:355:content-binding the accumulator could not give.
metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:360:accumulator but the WRONG sorted-tree update is now REJECTED (`writesTo_functional`). This makes
metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:382:sorted-tree update (`writesTo`), not the prepend accumulator. -/
metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:533:prepend accumulator. The Phase-E residual is CLOSED: the published root is now bound to the sorted-tree
metatheory/Dregg2/Circuit/RotatedKernelRefinementExercise.lean:534:SPLICE, not merely an accumulator advance. -/
metatheory/Dregg2/Circuit/Poseidon2Surface.lean:123:/-- A Horner accumulator from a non-negative seed and digit list `< refBase` is `≥ acc * refBase^|xs|`
metatheory/Dregg2/Circuit/RotatedKernelRefinementAttenuate.lean:29:from THIS descriptor — relating that felt accumulator to a sorted-Merkle commitment of the `Caps`
metatheory/Dregg2/Circuit/RotatedKernelRefinementAttenuate.lean:31:cap-root accumulator with non-amplifying rights*; it does NOT pin *the resulting `Caps` function equals
metatheory/Dregg2/Circuit/RotatedKernelRefinementAttenuate.lean:41:    `Caps`↔felt-accumulator residual the per-edge recompute cannot certify;
metatheory/Dregg2/Circuit/RotatedKernelRefinementAttenuate.lean:111:    felt accumulator (`capAdvanceOf`) the circuit recomputes pins WHICH edge mutated the cap-root, but
metatheory/Dregg2/Circuit/RotatedKernelRefinementAttenuate.lean:115:    level, only at the recompute-accumulator level — stated plainly in the module header).
metatheory/Dregg2/Circuit/RotatedKernelRefinementAttenuate.lean:131:  -- THE NAMED `Caps`-FUNCTION RESIDUAL: the exact in-place slot narrowing (the felt accumulator the
metatheory/Dregg2/Circuit/Argus/InterpCore.lean:41:    the site evaluator `decideSites` mirrors `siteHoldsAll`'s ordered `go` accumulator EXACTLY
metatheory/Dregg2/Circuit/Argus/InterpCore.lean:228:ordered site list with an accumulator `acc` of already-resolved digests, asserting
metatheory/Dregg2/Circuit/Argus/InterpCore.lean:232:`decideSites` mirrors `siteHoldsAll.go` EXACTLY: same accumulator, same `++ [d]` append, deciding
metatheory/Dregg2/Circuit/Argus/InterpCore.lean:250:/-- The site-walk decision agrees with `siteHoldsAll.go` at EVERY accumulator state. Generalised
metatheory/Dregg2/Circuit/Argus/InterpCore.lean:251:over `acc` so the induction threads the digest accumulator (the order-sensitive part). -/
metatheory/Dregg2/Circuit/Argus/InterpCore.lean:261:siteHoldsAll …`. The site ORDER is realized faithfully (both recursions thread the same accumulator
metatheory/Dregg2/Circuit/Argus/Policy.lean:369:accumulator). `colSumExpr [] = const 0`; `colSumExpr (c :: cs) = var c + colSumExpr cs`. -/
metatheory/Dregg2/Circuit/Argus/EmitRoundtrip.lean:41:banned). We prove it from scratch: `tdc_append` (the accumulator threads as a tail append),
metatheory/Dregg2/Circuit/Argus/EmitRoundtrip.lean:89:/-- The `toDigitsCore` accumulator threads as a tail append: producing `n`'s digits onto `ds`
metatheory/Dregg2/Circuit/Argus/Effects/NoteSpend.lean:937:   `gNullifierRootUpdate` accumulator gate (`EffectVmEmitNoteSpend §B`); this freshness gate composes
metatheory/Dregg2/Circuit/TurnCircuitCompose.lean:51:/-- Append one emitted step's decoded constraints to an accumulator (wire indices unchanged). -/
metatheory/Dregg2/Circuit/ClosureLog.lean:14:REALIZABLE Poseidon log-accumulator CR carrier, beside `compressInjective`/…). So the log IS published
metatheory/Dregg2/Circuit/RotatedKernelRefinementSpawnHandoff.lean:109:accumulator). This is the PHASE-D payoff: the spawn handoff is now circuit-forced at the set level. -/
metatheory/Dregg2/Exec/Program.lean:85:  prefix over the record substrate (each path segment is a named scalar). Fail-closed: a missing segment
metatheory/Dregg2/Exec/Program.lean:418:/-- Read the ordered scalar path from a list of segment field-names (`none` if ANY segment is
metatheory/Dregg2/Exec/Program.lean:730:/-- **`prefixOf` admit-char.** Admits IFF the path reads (all segments present) AND the
metatheory/Dregg2/Exec/Program.lean:932:-- prefixOf: a 2-segment path must register UNDER the namespace [10, 20] (owned by the actor).
metatheory/Dregg2/Exec/Program.lean:938:-- REJECT: a segment missing ⇒ fail-closed.
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapRoot.lean:34:runtime's cap-table digest is an APPEND/PREPEND accumulator over edge-mutations: the new root is
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapRoot.lean:35:`hash_2_to_1(edge_leaf, old_root)` — the canonical prepend-accumulator advance (the SAME shape escrow uses
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapRoot.lean:47:     `new_cap_root = hash[ edge_leaf, old_cap_root ]` — the genuine prepend-accumulator advance, reading
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapRoot.lean:90:    pins the executor's computed new root (the `hash[edge_leaf, old_root]` prepend-accumulator
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapRoot.lean:108:    (delegate / delegateAtten / revokeDelegation / introduce) reuses it. So the prepend-accumulator
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapRoot.lean:113:prepend-accumulator advance + its anti-ghost (`capRoot_binds_edge`) are the Phase-A digest pin; the
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapRoot.lean:174:/-- The OLD `cap_root` carrier (the pre-image of the accumulator advance): the `state_before` cap-root
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapRoot.lean:193:`new_cap_root = hash[ edge_leaf, old_cap_root ]` — the genuine prepend-accumulator advance, reading the
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBundleFold.lean:12:with `acc_in[0]` pinned to the public `initial` accumulator and `acc_out[last]` to the public
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBundleFold.lean:13:`final` accumulator.
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBundleFold.lean:46:accumulator is UNSAT — the Rust `tree_fold_rejects_tampered_final_acc` rejection) and
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBundleFold.lean:63:/-- Chain accumulator before absorbing this child. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBundleFold.lean:67:/-- Chain accumulator after absorbing this child (`Poseidon2(acc_in, digest)` = out0). -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBundleFold.lean:76:/-- Public input: the initial (seed) accumulator. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBundleFold.lean:78:/-- Public input: the final accumulator (the outer attestation). -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBundleFold.lean:139:-- Two public inputs: initial + final accumulator.
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBundleFold.lean:158:accumulator cannot satisfy the descriptor — exactly the boundary that binds the fold output to the
metatheory/Dregg2/Circuit/Emit/EffectVmEmitMintRunnable.lean:36:(the global supply total, a turn-level cross-cell accumulator) is unchanged and unaffected by this lift.
metatheory/Dregg2/Circuit/Emit/EffectVmEmitMintRunnable.lean:88:gates of `mintVmDescriptor` (a constraint-list segment), on a mint row decoded by `RowEncodes`, force
metatheory/Dregg2/Circuit/Emit/EffectVmEmitReceiptArchiveWide.lean:78:gate segment. NEITHER reads the hash sites, so the runnable per-cell soundness depends ONLY on the gates
metatheory/Dregg2/Circuit/Emit/EffectVmEmitReceiptArchiveWide.lean:83:gates (a constraint-list segment), on an audit-write row decoded by `ArchiveRowEncodes`, force
metatheory/Dregg2/Exec/CodecRoundtrip/Leaves.lean:36:/-- `toDigitsCore` threads its accumulator as a pure SUFFIX. -/
metatheory/Dregg2/Exec/CodecRoundtrip/Leaves.lean:347:/-- `toHex32.go` threads its accumulator as a pure SUFFIX (low nibbles prepended). -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitV2.lean:247:onto the accumulator preserves the result-column invariant. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitV2.lean:274:lookups (against a sound chip table) realize the v1 site walk from the current accumulator. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitV2.lean:1250:row's commitment to a verifying external sub-proof (the accumulator constraint the per-row IR
metatheory/Dregg2/Circuit/Emit/EffectVmEmitExerciseWide.lean:79:gates (a constraint-list segment), on an exercise row decoded by `RowEncodesExercise`, force
metatheory/Dregg2/Exec/CodecRoundtrip/Auth.lean:217:`encodeAuthListW`'s tail is a left-`foldl` accumulator (FFI.lean:1384), which does NOT syntactically
metatheory/Dregg2/Exec/CodecRoundtrip/Auth.lean:220:accumulator-pull-out lemma (`foldl_authtail`) turns it into the clean `',' :: enc b ++ tail` shape. This
metatheory/Dregg2/Exec/CodecRoundtrip/Auth.lean:245:/-- **The accumulator pulls OUT of the tail fold** (the standard `foldl`-with-`++` factoring) — proved
metatheory/Dregg2/Exec/CodecRoundtrip/SideTables.lean:26:/-- The accumulator pulls OUT of the tail fold (`List Char`-level, mirroring `foldl_authtail`). -/
metatheory/Dregg2/Exec/CodecRoundtrip/Forest.lean:83:/-- The accumulator pulls OUT of the tail fold (`List Char`-level, mirroring `foldl_authtail`). -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitMint.lean:502:CROSS-CELL / TURN-LEVEL accumulator (mint by definition changes the total supply, which no single cell
metatheory/Dregg2/Apps/ComputeMarketDesk.lean:72:    the notification object's badge accumulator; the gate/attenuation laws are proved here and in
metatheory/Dregg2/Apps/ComputeMarketDesk.lean:355:accumulator gains exactly the settlement badge — the provider is woken, not polled. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:30:The actual effect — `nullifiers := nf :: nullifiers` — is a SET-INSERT into the nullifier accumulator.
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:35:  ⇒ **needs IR extension: a nullifiers-accumulator-root column in the EffectVM state block absorbed by
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:43:WHOLE accumulated nullifier SET, an inter-row / turn-accumulator property. A SINGLE EffectVM row, even
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:48:no-double-spend (that lives at universe-A's nullifier-set guard and the turn-accumulator layer).
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:448:turn/accumulator layer. We extract the freshness from the spec's guard to NAME the boundary exactly
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:529:(the `nullifiers` accumulator). BEFORE this stage the nullifier-set insert `nf :: nullifiers` was the
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:531:descriptor to FULL: a per-row root-UPDATE gate binds the `nullifiers`-accumulator step into the row, the
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:550:/-- The committed `system_roots` digest carrier of the BEFORE state (the pre-image of the accumulator
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:555:/-- The `nullifiers`-accumulator STEP param: the field-element delta the consumed `nf` contributes to
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:560:/-- The accumulator-step expression (param column 2). -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:566:the before/after `system_roots` digest carriers and the `param2` accumulator step. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:605:digest ADVANCES by the `param2` accumulator step (`sa_digest = sb_digest + step`). This is the per-row
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:611:accumulator step — the gate pins EXACTLY the `nullifiers`-root update. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:620:/-- **Anti-ghost (root tamper).** A row whose after-digest is NOT the advanced accumulator
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:766:-- The accumulator-step param is param2 (param0 = nf, param1 = value), in-range of the 8 param cols.
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:822:the accumulator step, every OTHER side-table root FROZEN). So a satisfying wide-descriptor witness pins
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:847:(186/187) and the `param2` accumulator step. The wide analog of `gNullifierRootUpdate`. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:858:digest advances by the accumulator step. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpend.lean:978:root committed-digest advance by the accumulator step, and every OTHER side-table root frozen. This is the
metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:110:/-- `nullifiers` accumulator digest (noteSpend append; non-membership via spend-proof PI). -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:112:/-- `commitments` accumulator digest (noteCreate append). -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:171:`system_roots` digest (the pre-image of the per-effect root-update accumulator step). One past the
metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:352:/-! ### Walking the ordered site list (the Rust `digests` accumulator).
metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:358:/-- **`siteDigestsAcc hash env acc sites`** — the head-first accumulator: `acc` holds the digests
metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:370:/-- The resolved digests for the whole ordered site list (starting from an empty accumulator). -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmit.lean:591:/-- The selector-binding gate, as a one-element constraint list (the descriptor segment). -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoopWide.lean:108:gates (a constraint-list segment), on a row decoded by `RowEncodes`, force `CellFreezeSpec` (the whole
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpendCompose.lean:17:over the sorted accumulator), composed into the turn proof as the `non-revocation` sub-proof of
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteSpendCompose.lean:30:(turn/accumulator) layer with a named gadget, and the two together are SUFFICIENT.
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:34:accumulator. The EffectVM 14-column block has NO commitment-root column, and the GROUP-4 hash-sites
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:38:  ⇒ **needs IR extension: a commitments-accumulator-root column in the EffectVM state block (a 15th
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:418:into the commitment accumulator, and it is the LOAD-BEARING content of the effect (the per-cell FREEZE
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:438:universe-A's accumulator / the turn layer, NEVER by the per-row circuit. We extract it from the spec to
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:514:(the `commitments` accumulator). BEFORE this stage the commitment-set insert `cm :: commitments` was
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:516:descriptor to FULL: a per-row root-UPDATE gate binds the `commitments`-accumulator step into the row,
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:530:/-- The committed `system_roots` digest carrier of the BEFORE state (the pre-image of the accumulator
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:536:/-- The `commitments`-accumulator STEP param: the field-element delta the published `cm` contributes to
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:542:/-- The accumulator-step expression (param column 2). -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:548:digest ADVANCES by the accumulator step the appended `cm` contributes (the runtime hand-AIR's
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:555:the before/after `system_roots` digest carriers and the `param2` accumulator step. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:595:digest ADVANCES by the `param2` accumulator step (`sa_digest = sb_digest + step`). This is the per-row
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:601:accumulator step — the gate pins EXACTLY the `commitments`-root update. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:610:/-- **Anti-ghost (root tamper).** A row whose after-digest is NOT the advanced accumulator
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:753:-- The accumulator-step param is param2 (param0 = cm, param1 = value), in-range of the 8 param cols.
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:810:accumulator step, every OTHER side-table root FROZEN), so a satisfying wide-descriptor witness pins
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:829:(186/187) and the `param2` accumulator step. The wide analog of `gCommitRootUpdate`. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:840:digest advances by the accumulator step. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:905:DIGEST advanced by the accumulator `step` (the bound update of field 6), and EVERY OTHER side-table root
metatheory/Dregg2/Circuit/Emit/EffectVmEmitNoteCreate.lean:974:digest advance by the accumulator step, and every OTHER side-table root frozen. This is the generic
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:57:    the last; it GRADUATED via the new accumulator / recursive-proof-binding constraint kind
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:266:-- graduates to the EXACT wire JSON of its DIGEST-chained twin (the running accumulator referenced
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:413:/-- A hash-site input that never reads the digest accumulator. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:419:/-- A site whose inputs are all accumulator-free. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:422:/-- A col-only site resolves identically under EVERY accumulator. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:436:ANY accumulator — a col-only site's equation holds in its accumulator-free form. THIS is what
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:1062:The note-spend grow-gate ESCAPES this exactly: its nullifier accumulator lives on the rotated-block limb 26
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:1065:input (site `base+47` absorbs limbs 25/26/27). MIRROR that for the cap-root: place the WRITE accumulator on
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:1072:cap accumulator's PRE root the membership-open + write-gate open against — note-spend-shaped, NOT col 65. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:1076:deployed cap accumulator's POST root — the write-gate's `newRoot`, witness-carried (no v1-state continuity). -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:1113:cap-root (limb 25). `writesTo` is FUNCTIONAL under CR — a forged after-root is UNSAT. The accumulator lives
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:1145:The accumulator lives on a witness-carried rotated limb (note-spend-shaped), so the v1-state continuity
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:1307:This op CLOSES that, mirroring the cap-tree write: the deleg accumulator rides the ROTATED before/after
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:1319:refresh freezes `caps` on the v1 column, so the rotated limb is free to carry the deleg accumulator. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:1342:accumulator folds into the committed rotated state-commit, no v1-state continuity collision. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:1369:`custom_proof_commitment` to a verifying external sub-proof — the accumulator constraint the
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:1458:`base = traceWidth`). The deployed nullifier accumulator's PRE root — the openable
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:1463:`base = traceWidth + 51`). The deployed nullifier accumulator's POST root — the grow-gate's
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:1680:`base = traceWidth`). The deployed commitments accumulator's PRE root. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:1684:`base = traceWidth + 51`). The deployed commitments accumulator's POST root — the grow-gate's
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:1791:`base = traceWidth`). The deployed accounts accumulator's PRE root — the openable
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean:1796:`base = traceWidth + 51`). The deployed accounts accumulator's POST root — the grow-gate's
metatheory/Dregg2/Intent/Ring.lean:202:This is the Rust `sent_per_asset[asset]` accumulator: one `+= s.amount` per leg, indexed by the SEND
metatheory/Dregg2/Circuit/Emit/EffectVmEmitDelegate.lean:43:    in-row sorted-TREE update vs the prepend-accumulator digest advance — see `EffectVmEmitAttenuateA`).
metatheory/Dregg2/Exec/ConsensusExec.lean:15:super-ratified leader (`Proof.CordialMiners.Committed`) *anchors* a segment, and the segment's
metatheory/Dregg2/Exec/ConsensusExec.lean:16:blocks are linearized (the intra-segment `xsort` tie-break, OPEN-CM-XSORT). The node then
metatheory/Dregg2/Exec/ConsensusExec.lean:55:  (`OPEN-CM-XSORT`, the intra-segment tie-break) — `cordial_agreement` is about *which leader
metatheory/Dregg2/Exec/ConsensusExec.lean:102:maps each finalized block to its segment's leader; `anchor_committed` is the finality evidence
metatheory/Dregg2/Exec/ConsensusExec.lean:108:  /-- Each finalized block's segment-anchoring committed leader. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationCaveat.lean:375:prefix of the combined walk, so its accumulator is untouched by the caveat sites). -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitPipelinedSendWide.lean:87:per-row gates (a constraint-list segment), on a pipelined-send row decoded by `RowEncodesSend`, force
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRecordRoot.lean:8:user-field-map root (`Exec.FieldsMap.fieldsRoot`, the unbounded `key ≥ 8` overflow accumulator) into
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRecordRoot.lean:199:accumulator `digs`). Record's 4th input is `fields_root` (col 89), transfer's is `record_digest`
metatheory/Dregg2/Circuit/Emit/EffectVmEmitHeapRoot.lean:19:     `new_heap_root = hash[ leaf, old_heap_root ]` — the SAME prepend-accumulator advance the cap
metatheory/Dregg2/Circuit/Emit/EffectVmEmitHeapRoot.lean:103:accumulator advance, identical to the cap-root advance with the generic leaf). -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitHeapRoot.lean:142:The accumulator advance (`siteHeapRootAdvance`, `new_root = hash[leaf, old_root]`) BINDS the new
metatheory/Dregg2/Circuit/Emit/EffectVmEmitHeapRoot.lean:160:not the prepend accumulator. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitHeapRoot.lean:166:splice (`DescriptorIR2.writesTo`), not the prepend accumulator. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotation.lean:274:`STATE_COMMIT = wireCommit` of its OWN limbs and iroot. (The walk's accumulator recomputes
metatheory/Dregg2/Exec/CircuitEmit.lean:637:  -- Generalize the accumulator: foldl over `cols` of `.mul acc (.var c)` evaluates to the
metatheory/Dregg2/Exec/CircuitEmit.lean:638:  -- `Int` fold from the same accumulator value; then pull the init `coeff` out via `termFold_init`.
metatheory/Dregg2/Exec/CircuitEmit.lean:659:    -- Generalize accumulator over the tail fold.
metatheory/Dregg2/Exec/AdmissionWire.lean:29:/-- Fold `addUnique` over a cell list into accumulator `xs`. -/
metatheory/Dregg2/Intent/SealedAuction.lean:287:  -- General fold invariant: the accumulator, if `some`, is always a member of the consumed prefix,
metatheory/Dregg2/Intent/SealedAuction.lean:288:  -- and members of the prefix carry through. Proven over an arbitrary starting accumulator.
metatheory/Dregg2/Circuit/Emit/EffectVmEmitAttenuateA.lean:64:prepend-accumulator DIGEST advance, not yet the in-row sorted-TREE update (membership-open + sorted-key
metatheory/Dregg2/Circuit/Emit/EffectVmEmitAttenuateA.lean:595:into the commitment — NOT bound a SECOND, incompatible way by the prepend-accumulator `siteCapRootAdvance`.
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationWide.lean:74:there is no `.digest k` accumulator to resolve — the rotation emission supplies `ins` directly.) -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationWide.lean:93:inputs explicitly, no cross-site accumulator, so the family is the pointwise conjunction). -/
metatheory/Dregg2/Apps/AgentOrchestrationBudget.lean:461:wide mask): `signalGated` is `some`, OR'ing the badge into the queue accumulator. The wake is
metatheory/Dregg2/Apps/AgentOrchestrationBudget.lean:484:balance-neutrality (the async edge writes a badge accumulator, not the ledger). -/
metatheory/Dregg2/Apps/AgentOrchestrationBudget.lean:487:the prior OR the signalled badge — and nothing else. The async edge touches the badge accumulator
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBurn.lean:568:accumulator (burn changes total supply, carried by no single cell), the exact analogue of transfer's
metatheory/Dregg2/Circuit/Emit/EffectVmEmitEmitEventWide.lean:78:gates (a constraint-list segment), on an emit row decoded by `RowEncodesEmit` with `s_noop = 0`, force
metatheory/Dregg2/Exec/SystemRoots.lean:50:`compressNInjective` (the already-built injective accumulator portal) — never a new axiom.
metatheory/Dregg2/Exec/SystemRoots.lean:79:/-- `nullifiers` accumulator digest (noteSpend append; non-membership via spend-proof PI). -/
metatheory/Dregg2/Exec/SystemRoots.lean:81:/-- `commitments` accumulator digest (noteCreate append). -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBilateralAgg.lean:85:/-! ## §2 — The aggregation MAIN-trace layout (schedule block + expected cols + accumulators). -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBilateralAgg.lean:256:-- The main width: schedule 49 + expected 35 + 3 accumulators = 87.
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapReshape.lean:19:`EffectVmEmitCapRoot` advances `cap_root` as a prepend-accumulator DIGEST (Phase A) and explicitly
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapReshape.lean:496:/-! ### §4.1 — the descriptor's constraint segments. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapReshape.lean:648:/-- The non-amp segment has `3·MASK_BITS + 2` gates (held-bool + granted-bool + submask + 2 recon), and
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapReshape.lean:649:the production segment has 2 (the PI binding + the control gate). The descriptor is non-trivial. -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitCapReshape.lean:783:/-- The delegation non-amp segment has `3·MASK_BITS + 2` gates (held-bool + granted-bool + submask + 2
metatheory/Dregg2/Exec/RecordCommit.lean:7:user-field MAP: keys `≥ 8` live in a `fields_root = ListCommit.listDigest (userTail v)` accumulator
metatheory/Dregg2/Circuit/Emit/EffectVmFullStateRunnable.lean:359:The per-row gates of the transfer descriptor (a constraint-list segment), on a transfer row decoded by
metatheory/Dregg2/Circuit/Emit/EffectVmFullStateRunnable.lean:529:     `sysRootsDigestCol = sysRootsDigestColBefore + step` (the accumulator step the prepended/removed
metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationR.lean:240:The 1-felt chain above (`chainFrom`/`wireCommitR`) threads a SINGLE ℤ accumulator — ~31-bit,
metatheory/Dregg2/Circuit/Emit/EffectVmEmitBurnRunnable.lean:92:gates of `burnVmDescriptor` (a constraint-list segment), on a burn row decoded by `RowEncodes`, force
metatheory/Dregg2/Circuit/Emit/EffectVmEmitEscrowRoot.lean:24:of the per-record leaves). The runtime's escrow side-table is an APPEND/PREPEND accumulator: the new root
metatheory/Dregg2/Circuit/Emit/EffectVmEmitEscrowRoot.lean:25:is `hash_2_to_1(record_leaf, old_root)` — the canonical prepend-accumulator advance (the SAME shape the
metatheory/Dregg2/Circuit/Emit/EffectVmEmitEscrowRoot.lean:36:     `new_root = hash[ record_leaf, old_root ]` — the genuine prepend-accumulator advance, reading the
metatheory/Dregg2/Circuit/Emit/EffectVmEmitEscrowRoot.lean:109:/-- The OLD escrow-list root carrier (the pre-image of the accumulator advance). -/
metatheory/Dregg2/Circuit/Emit/EffectVmEmitEscrowRoot.lean:128:`new_root = hash[ record_leaf, old_root ]` — the genuine prepend-accumulator advance, reading the
metatheory/Dregg2/Circuit/Emit/EffectVmEmitTransfer.lean:415:  -- the accumulator at site 3 is [d0, d1, d2]; its getD 0/1/2 are d0/d1/d2.
metatheory/Dregg2/Projection.lean:14:     (`JointTurn.lean`, CG-2 ⊗ CG-5, tier ≥ 3). The classifier is Whittaker's segmented
metatheory/Dregg2/Apps/SwarmSignal.lean:31:do **NOT** claim *information* containment. A badge-OR accumulator is a classic covert channel
metatheory/Dregg2/Apps/SwarmSignal.lean:34:`watch` on its OWN accumulator can still infer, from the wake's timing and badge, facts about the
metatheory/Dregg2/Apps/SwarmSignal.lean:57:  * **`workerA`, `workerB`** (cells 1, 2) — each a `Notification` object (a badge-OR accumulator)
metatheory/Dregg2/Apps/SwarmSignal.lean:58:    the coordinator may `signal`. Each holds, at most, a `watch` on its OWN accumulator (the
metatheory/Dregg2/Apps/SwarmSignal.lean:65:/-- Worker A's cell id — a `Notification` badge-OR accumulator the coordinator may wake. -/
metatheory/Dregg2/Apps/SwarmSignal.lean:67:/-- Worker B's cell id — a second `Notification` accumulator. -/
metatheory/Dregg2/Apps/SwarmSignal.lean:107:accumulator, which needs no `NotifyCap`). This finite, enumerated cap-set is the structural ground
metatheory/Dregg2/Apps/SwarmSignal.lean:138:`signalGated coordToA n kindTest` is `some` and the accumulator gains precisely `kindTest` (the mask
metatheory/Dregg2/Apps/SwarmSignal.lean:145:/-- **① (the observation half)** — after the committed wake, a `wait` on the (empty) accumulator
metatheory/Dregg2/Apps/SwarmSignal.lean:147:for, OR'd into its badge accumulator. Reuses Step-1 `Notification.signal`/`wait`. -/
metatheory/Dregg2/Apps/SwarmSignal.lean:225:/-! ## §4 — Conservation: every wake is balance-NEUTRAL (it writes a badge accumulator, not the
metatheory/Dregg2/Apps/SwarmSignal.lean:228:object only. We pin it as: a committed wake yields a `Notification` (a pure badge accumulator), and
metatheory/Dregg2/Apps/SwarmSignal.lean:234:`Notification`. (The §demo-app-design "conservation" point: a wake writes a badge accumulator, not
metatheory/Dregg2/Apps/SwarmSignal.lean:235:the ledger — here, definitionally, because the wake's codomain IS the accumulator.) -/
metatheory/Dregg2/Authority/CaveatCapBridge.lean:505:  -- Generalize the accumulator `held` to make the induction go through, then specialize to `⊤`.
metatheory/Dregg2/Authority/Positional.lean:44:(`Firmament/SeL4Kernel.Notification`, the badge-OR accumulator). With `notify`, α is total on

exec
/bin/zsh -lc 'rg -n "CODEX-IVC|IVC|mixed-root|mixed root|segment-accumulator|ordered segment|WholeChainProof" docs metatheory -S' in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
metatheory/Dregg2.lean:118:import Dregg2.Spec.Lifecycle          -- lifecycle as the attested dual of creation: creation_and_death_are_dual + archival_is_fold(IVC) + reclaim_by_lease + creation_provable_death_temporal; co-witnessability OPEN
metatheory/Dregg2.lean:430:import Dregg2.Distributed.HistoryAggregation -- IVC FOLD MODEL under circuit/src/ivc_turn_chain.rs (the magnesium→gold meaning layer): a chain of ChainSteps = genuine recCexec transitions over RecChainedState whose roots are the §8 recStateCommit; the TurnChainBindingAir temporal tooth new_root[i]==old_root[i+1] (Continues/ChainBound); HEADLINE wellformed_attests_whole_history (every turn recCexec-correct + ChainBound ordered + the whole chain is Run recChainedSystem ⇒ wellformed_history_conserves no-mint/burn over ALL history); root_tooth_pins_state = the CR RECOVERY (recStateCommit_binds: matching seam roots ⇒ equal cellDigest+RH = the root IS the full-state commitment, so a light client seeing only roots learns state continuity); non-vacuity BOTH ways (honest_chain_wellformed positive over teethGenesis + tooth_rejects_broken_order = reordered chain is NOT ChainBound); #assert_axioms-clean
metatheory/Dregg2.lean:525:import Dregg2.Circuit.RecursiveAggregation -- RECURSIVE-AGGREGATION SOUNDNESS (THE magnesium→gold bridge over circuit/src/ivc_turn_chain.rs prove_turn_chain_recursive→WholeChainProof): the SNARK recursion layer over HistoryAggregation. Opaque (Proof,verify) = plonky3 RecursionCompatibleProof/verify_recursive_batch_proof; EngineSound bundles the 3 NAMED, REALIZABLE soundness hypotheses you cannot prove in Lean — recursive_sound (root verifies ⇒ all child leaves verify; the ONE FRI obligation §H1), leaf_sound (POSITIONAL Forall₂ pairing leaf↔step ⇒ verifying leaf attests its recCexec step; the EffectVm circuit⟺executor soundness), binding_sound (TurnChainBindingAir leaf ⇒ ChainBound + genesis/final root pins). HEADLINE light_client_verifies_whole_history: checking ONLY verify agg.root (re-witnessing NOTHING) ⇒ AggregateAttests (every turn executed correctly + correctly ordered + final root = genuine fold) = proofs-as-additive-attestation, the verification IS the trust + attested_history_conserves inherited. NON-VACUITY both ways: real_engine_sound/light_client_fires_on_real_chain/real_chain_first_turn_executed (witnessed over the honest teethGenesis step) + ANTI-GHOST tampered_aggregate_cannot_bind (reordered chain ⇒ binding_sound forces ChainBound = FALSE ⇒ no verifying aggregate) + leaf_pairing_defeats_swap (positional pairing ⇒ leaf not re-pointable). #assert_axioms-clean; the named hyps are structure FIELDS not axioms
docs/reference/circuit.md:17:  `p3-recursion` tower (IVC turn chain, joint-turn recursive aggregation,
docs/reference/circuit.md:22:- **`dregg-lightclient`** (`lightclient/`) — verify ONE succinct IVC aggregate
docs/reference/circuit.md:23:  (`WholeChainProof`) and obtain the verdict, re-witnessing nothing
docs/reference/circuit.md:118:## The whole-chain IVC fold
docs/reference/circuit.md:162:`WholeChainProof` carrying the root, the chain-binding proof, and the four public
docs/reference/circuit.md:215:A whole `WholeChainProof` is NOT byte-encodable (its `root.1` is prover-only
docs/reference/circuit.md:216:`Rc<CircuitProverData>`); `WholeChainProofBytes`
docs/reference/sdk.md:54:  (`receipt_chain`), an optional IVC builder, stealth keys, and local sovereign
docs/reference/lean-distributed.md:248:- **HistoryAggregation** (`HistoryAggregation.lean`) — the IVC fold: a chain of
metatheory/docs/CODEX-IVC-FINAL-REVIEW.md:1:# Codex FINAL re-review — IVC #1 same-endpoint close (2026-06-25): NO CRITICAL HOLE
metatheory/docs/CODEX-IVC-FINAL-REVIEW.md:3:VERDICT: for the K-fold segment path, NO critical soundness hole — the same-endpoint mixed-root forgery is GENUINELY CLOSED under the Poseidon2 truncated-output commitment assumption.
metatheory/docs/HARVEST-KEEPERS.md:135:- **H1 recursion trust boundary** — re-prove the plonky3 FRI verifier sound in Lean (huge) OR trust the engine audit + model only public-input-binding (H2) + differential-test? (current lean: portal + H2). One engine for both intra-block aggregation AND inter-block IVC, or plonky3-tree + arrabbiata-folding? (current lean: one engine until H1 solid). (from: rebuild/DESIGN-recursion-aggregation-private-joint-turns.md)
metatheory/docs/CODEX-IVC-REVIEW-3.md:1:# Codex re-review #3 — the segment-accumulator close + the weak-digest deviation (2026-06-24)
metatheory/docs/CODEX-IVC-REVIEW-3.md:3:VERDICT: PARTIAL CLOSE. Distinct-endpoint mixed-root forgery genuinely REJECTED (structural). But the digest deviation (base-field fold instead of codex's specified collision-resistant commitment) is a REAL soundness downgrade for same-endpoint/same-count histories — and it's ALGEBRAICALLY broken, not merely 31-bit.
metatheory/docs/CODEX-IVC-REVIEW-3.md:5:**Verdict: partial close.** The original mixed-root forgery with different genesis/final/count is closed in the K-fold path. The root proof exposes the descriptor-derived segment, and the verifier compares it to the carried claim at [ivc_turn_chain.rs:1757](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1757). So if A and B differ in genesis, final, or count, the rejection does not depend on the digest.
metatheory/docs/CODEX-IVC-REVIEW-3.md:22:   [accumulator.rs:39](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:39) explicitly says the online accumulator still uses a separate binding leaf and retains the mixed-root structural weakness. Scope the close to the balanced K-fold path only.
metatheory/docs/CODEX-IVC-REVIEW-3.md:27:**Bottom line:** distinct-endpoint mixed-root forgery is genuinely rejected. Full ordered-history soundness is not achieved. Same-endpoint/same-count histories rely on a one-felt, algebraically weak digest; if an attacker can realize colliding intermediate roots as valid executions, a proof of A can stand in for B’s middle history. The fix should replace `seg_hash2_*` with an in-circuit collision-resistant multi-felt commitment, and the root claim should carry that wider digest.
metatheory/docs/CODEX-IVC-REVIEW-3.md:29:**Verdict: partial close.** The original mixed-root forgery with different genesis/final/count is closed in the K-fold path. The root proof exposes the descriptor-derived segment, and the verifier compares it to the carried claim at [ivc_turn_chain.rs:1757](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1757). So if A and B differ in genesis, final, or count, the rejection does not depend on the digest.
metatheory/docs/CODEX-IVC-REVIEW-3.md:46:   [accumulator.rs:39](/Users/ember/dev/breadstuffs/circuit-prove/src/accumulator.rs:39) explicitly says the online accumulator still uses a separate binding leaf and retains the mixed-root structural weakness. Scope the close to the balanced K-fold path only.
metatheory/docs/CODEX-HEIGHT1-FRI-FIX.md:3:The precise math for the IVC same-endpoint residual: a height-1 (base-domain-size-1) Poseidon2 table's nonzero FRI reduced-opening asserted-zero in the recursive aggregation verifier.
metatheory/Dregg2/Spec/Lifecycle.lean:32:  * **archival is the IVC/recursive-fold reused as history-compression** — an
metatheory/Dregg2/Spec/Lifecycle.lean:34:    `checkpointHash` (`archival_is_fold`): the same fold that powers IVC, here
metatheory/Dregg2/Spec/Lifecycle.lean:125:IVC-style *fold* of the prefix (`§3`). -/
metatheory/Dregg2/Spec/Lifecycle.lean:265:/-! ## §4 — The creation ⊣ termination duality, and archival-as-IVC-fold.
metatheory/Dregg2/Spec/Lifecycle.lean:325:/-- **`FoldsTo prefix h`** — the abstract IVC/recursive-fold relation: the
metatheory/Dregg2/Spec/Lifecycle.lean:328:fold that drives IVC (verify a chain by folding step proofs); here it is reused as
metatheory/Dregg2/Spec/Lifecycle.lean:339:prefix`, we obtain `FoldsTo accum seed prefix att.checkpointHash`. This is the IVC fold
metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md:66:| **derived** | **ORPHANED** `cell/src/derived.rs:1`, `verify_derivation` (`:356`) has ZERO live callers (the `verify_derivation` hits in `circuit/` are a NAME COLLISION — the STARK IVC `cell::derivation`, not this materialized-view `cell::derived`) | Publish a cell whose committed state IS a verifiable function of other cells (`sum(balances)`, join/filter/count) — a light-client-checkable materialized view | This is a *read/query* face, not a value move. Weld is a cross-state binding in the circuit (the `cross_state_derivation` AIR exists) + a `DerivationSpec`-bound `SetField` whose value is constrained `== eval(spec)` via a new `StateConstraint::DerivedEquals`. **Medium, likely VK-affecting** (new cross-cell constraint in the AIR). Lower priority (read-only, not an agent-held authority) |
metatheory/docs/CODEX-IVC-REVIEW-2.md:1:# Codex re-review #2 — IVC #1 fix (2026-06-24)
metatheory/docs/CODEX-IVC-REVIEW-2.md:3:VERDICT: the exposed-claim channel is SOUND (the old forgery rejects), but #1 NOT fully closed — a DEEPER mixed-root hole remains.
metatheory/docs/CODEX-IVC-REVIEW-2.md:25:- tooth 3: mixed root verifies: [ivc_turn_chain.rs:1537](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1537)
metatheory/docs/CODEX-IVC-REVIEW-2.md:41:The flipped test at [ivc_turn_chain_rotated.rs:595](/Users/ember/dev/breadstuffs/circuit-prove/tests/ivc_turn_chain_rotated.rs:595) covers only the old external cross-pairing shape. It does not cover the mixed-root attack above. I would add a test that constructs descriptor leaves from A, binding leaf from B, aggregates them into one root, carries B’s binding proof/claims, and asserts rejection. I expect current code to accept unless there is another cross-leaf equality constraint outside the reviewed paths.
metatheory/docs/CODEX-IVC-REVIEW-2.md:64:- tooth 3: mixed root verifies: [ivc_turn_chain.rs:1537](/Users/ember/dev/breadstuffs/circuit-prove/src/ivc_turn_chain.rs:1537)
metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md:1:# Codex cross-model soundness review — dregg unbounded IVC (2026-06-24)
metatheory/docs/CODEX-IVC-SOUNDNESS-REVIEW.md:3:Adversarial review by codex-cli 0.131.0 (cross-model). Found GENUINE soundness holes — the IVC VERIFIES the honest prover's proof but a FORGED whole-chain claim can verify. 'Test passes' != 'sound'. Every file:line below was spot-checked accurate.
docs/design-frontiers/PG-DREGG-DX.md:151:soundness over a *range* is the whole-chain IVC light client's job
docs/design-frontiers/PG-DREGG-DX.md:434:  STARK re-proof. Proof attestation is range-level IVC (`circuit::ivc_turn_chain`,
docs/design-frontiers/PG-DREGG-DX.md:437:  but a consumer who wants "this row is proof-attested" must walk the IVC range, not
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:25:The strongest, most current strand is the **whole-chain IVC accumulator**:
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:29:  proof** (`WholeChainProof`) using **real plonky3 in-circuit FRI recursion** (the
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:51:— a different axis (cross-cell width) from the whole-chain depth the IVC folds.
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:137:## 2. RECURSIVE PROOF / IVC / proof-carrying-proof
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:144:| Attenuation/delegation-depth IVC | **ALIVE** but DIFFERENT scope — `circuit/src/ivc.rs` folds an *attenuation* fold-chain (delegation depth), hash-chain accumulation with a real STARK backend (`StateTransitionAir`). NOT the whole-turn-chain accumulator. | `circuit/src/ivc.rs` |
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:204:| Succinct proof of the whole chain, verified by a light client in constant work | `lightclient::verify_history` over `WholeChainProof` | **MATCHED, LIVE** |
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:232:   not research. This converts `WholeChainProof` from "sound under VK-pin + carried binding"
metatheory/docs/RECURSION-AGGREGATION-CENSUS.md:315:| Attenuation/delegation-depth IVC | `circuit/src/ivc.rs` | ALIVE-WIRED (different scope) |
docs/design-frontiers/WEB-FORWARD.md:62:   checks ONE recursive `WholeChainProof` against a VK trust-anchor and reads off
docs/design-frontiers/WEB-FORWARD.md:441:*Byte path CLOSED (§7).* The over-wire seam — a `WholeChainProof` had no serde
docs/design-frontiers/WEB-FORWARD.md:444:versioned `WholeChainProofBytes` envelope (`WholeChainProof::to_bytes()`), and
metatheory/docs/CODEX-IVC-SEGMENT-ACCUMULATOR-DESIGN.md:1:# Codex design — the ordered segment-accumulator fix for the IVC mixed-root hole (2026-06-24)
metatheory/docs/CODEX-IVC-SEGMENT-ACCUMULATOR-DESIGN.md:3:Codex's recommended construction (gigabrain advice, not a review): close the mixed-root forgery by making the whole-chain claim sound-BY-CONSTRUCTION — a constant-size ordered segment accumulator carried by every descriptor leaf + each aggregation node, replacing the separate binding leaf in the soundness-critical path.
metatheory/docs/CODEX-IVC-SEGMENT-ACCUMULATOR-DESIGN.md:26:HORIZONLOG.md:4596:- ⚑ THE MISSING WELD (the single highest-leverage edit on the board): the multi-turn IVC / finalized-history /
metatheory/docs/CODEX-IVC-SEGMENT-ACCUMULATOR-DESIGN.md:27:HORIZONLOG.md:4601:  stack. Likely ~one bridging theorem (modulo the IVC recursion shape).
metatheory/docs/CODEX-IVC-SEGMENT-ACCUMULATOR-DESIGN.md:29:HORIZONLOG.md:4633:  axiom (multi-turn/IVC/joint/promises all proven-but-parallel).
metatheory/Dregg2/Await.lean:348:linear chain folds into one IVC proof; here we capture the graph shape: nodes plus a
metatheory/CLAIMS.md:86:| 7 | `…creation_and_death_are_dual`, `…archival_is_fold`, `…reclaim_by_lease`, `…terminal_rejects_{effects,transition}`, `…{migrated,destroyed}_terminal`, `…acceptsEffects_iff`, `…isTerminal_iff`, `…birthProvable`, `…archived_still_live` | `Spec.Lifecycle` | lifecycle = attested dual of creation; archival as IVC fold; lease reclamation |
docs/deos/DREGG-DATA-STORE.md:270:  unwired by the circuit crate-split (the `prover` feature retired; the IVC
metatheory/Dregg2/Lightclient/AttestedQuery.lean:373:itself is the rotation's): the per-turn state commitment that the IVC chain folds
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:8:that the IVC accumulator (`circuit/src/ivc_turn_chain.rs::prove_turn_chain_recursive` →
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:9:`WholeChainProof`) realizes; `verify_turn_chain_recursive` checks only the root, cost independent of N.
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:73:`Aggregate` is the `WholeChainProof` (`ivc_turn_chain.rs:430`): the single root recursion proof, plus
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:81:the four public commitments are exactly the `WholeChainProof` fields. The `leafProofs` are the per-turn
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:84:  /-- The single root recursion proof (the whole tree folded to one — `WholeChainProof.root`). -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:90:  /-- Public: the genesis root the chain starts from (`WholeChainProof.genesis_root`). -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:92:  /-- Public: the final root the chain reaches (`WholeChainProof.final_root`). -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:94:  /-- Public: the running digest of the ordered (old,new) pairs (`WholeChainProof.chain_digest`). -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:96:  /-- Public: the number of finalized turns folded (`WholeChainProof.num_turns`). -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:440:/-! ## 7. THE UNBOUNDED IVC ACCUMULATOR — the running left-fold, proven by induction from genesis.
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:442:§§1–6 prove the FLAT statement: given a `WholeChainProof` over a *finite* K-turn window, verifying its
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:449:step — so by induction from genesis, `acc_n` attests the WHOLE history `0..n`. This is the IVC soundness
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:462:IVC fixed point) is the SAME named, realizable `EngineSound` boundary §2 already carries; nothing new is
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:499:chain. Its head is genesis itself. This is the base of the IVC induction. -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:527:IVC step: dropping/reordering at the tail would break exactly one of them. -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:576:/-! ### `accumulate` — the IVC step (extend one leaf at a time). -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:607:/-- **`accumulate_preserves_wellformed` (THE IVC INVARIANT).** The running accumulator's attestation is
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:619:/-- **`acc_attests_whole_history` (THE IVC HEADLINE — by induction from genesis).** The running
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:626:correct, ordered, and genuinely folded. This is the unbounded IVC soundness, by induction from genesis,
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:651:/-! ### IVC non-vacuity — the accumulator FIRES on a real chain (genesis → one accumulate step).
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:655:a REAL `WellFormedChain`, and read off its conservation (the `100` supply). So the IVC step is inhabited
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:674:/-- **`ivc_accumulate_fires` (IVC non-vacuity).** The realizing accumulator attests a REAL well-formed
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:675:1-step history from genesis — the IVC step genuinely fired and preserved the invariant. -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:682:unbounded-IVC conservation corollary delivers a real conservation fact on a real executor run. -/
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:704:-- the UNBOUNDED IVC accumulator: the running left-fold preserves whole-history attestation, by
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:705:-- induction from genesis (the part Mina lacks — a machine-checked IVC soundness induction):
metatheory/Dregg2/Circuit/RecursiveAggregation.lean:714:-- IVC non-vacuity (the accumulate step FIRES on a real executor run from genesis):
metatheory/Dregg2/Circuit/DescriptorIR2.lean:288:This is the recursion/IVC boundary the rest of the stack already names (`Dregg2.Circuit.Recursive-
metatheory/Dregg2/Distributed/HistoryAggregation.lean:2:# Dregg2.Distributed.HistoryAggregation — the FOLD model under the IVC accumulator.
metatheory/Dregg2/Distributed/HistoryAggregation.lean:4:**What this is.** The whole-chain IVC accumulator (`circuit/src/ivc_turn_chain.rs`) folds a
metatheory/Dregg2/Distributed/HistoryAggregation.lean:409:This is the meaning the IVC accumulator's `WholeChainProof` claims; `RecursiveAggregation.lean`
metatheory/Dregg2/Distributed/FinalizedLightClient.lean:5:light client that verifies ONE succinct IVC aggregate (re-witnessing nothing) learns the whole chain
metatheory/Dregg2/Circuit/Argus/Aggregate.lean:58:2. **The shape-AIR vs real-AIR CENSUS GAP remains the named carried hypothesis.** The IVC accumulator

I found the existing `acc_attests_whole_history` section. It proves the running left-fold invariant for the online accumulator shape, but that’s still a flat proof over an `Acc` record with a carried `WellFormedChain`; it is not yet the balanced segment-tree binding theorem you’re asking for.
exec
/bin/zsh -lc "sed -n '440,710p' metatheory/Dregg2/Circuit/RecursiveAggregation.lean && sed -n '1,180p' metatheory/docs/CODEX-IVC-SEGMENT-ACCUMULATOR-DESIGN.md && sed -n '1,120p' metatheory/docs/CODEX-IVC-FINAL-REVIEW.md" in /Users/ember/dev/breadstuffs
 succeeded in 0ms:
/-! ## 7. THE UNBOUNDED IVC ACCUMULATOR — the running left-fold, proven by induction from genesis.

§§1–6 prove the FLAT statement: given a `WholeChainProof` over a *finite* K-turn window, verifying its
root attests `WellFormedChain` for that window. That is the BOUNDED-K light client (`ivc_turn_chain.rs::
prove_turn_chain_recursive`, a balanced binary tree over K leaves).

This section proves the part Mina LACKS: that the accumulator can be driven as a CONTINUOUS LEFT-FOLD
(`acc_n = accumulate(acc_{n-1}, turn_n)`), extending the attested history ONE step at a time, with O(1)
memory (keep only `acc_{n-1}`), and that the running accumulator's attestation is PRESERVED at every
step — so by induction from genesis, `acc_n` attests the WHOLE history `0..n`. This is the IVC soundness
INDUCTION as a Lean theorem:

  `accumulate_preserves_wellformed` — IF `acc` attests `WellFormedChain g steps` AND the next turn `s`
  is executor-sound (a `ChainStep`, so `s.commits` is built in) and STATE-EXTENDS the head
  (`s.pre = lastStateOf g steps`), THEN `accumulate acc s` attests `WellFormedChain g (steps ++ [s])`.

  `acc_attests_whole_history` — folding `accumulate` from the genesis accumulator over a state-extending
  stream yields an accumulator attesting `WellFormedChain g (the whole stream)`. The base case is the
  empty chain (trivially well-formed); the step is `accumulate_preserves_wellformed`.

This is the SOUNDNESS SKELETON of the unbounded online accumulator. The CRYPTO carrier (the running
recursion proof re-verified in-circuit so `acc_n.proof` has the SAME shape `acc_{n+1}` can verify — the
IVC fixed point) is the SAME named, realizable `EngineSound` boundary §2 already carries; nothing new is
axiomatized. What this section adds OVER §§1–6 is the INDUCTIVE characterization: the flat headline is
re-derived as the n-th unfolding of a one-step-at-a-time fold from genesis.

NOTE on the seam (the genuinely-load-bearing hypothesis, named not hidden). `accumulate` extends a chain
at its HEAD; for the *root-level* temporal tooth (`ChainBound`) to extend, the new step's `oldRoot` must
equal the previous last step's `newRoot`. We DERIVE that from state continuity (`s.pre = lastStateOf …`)
via `seam_roots_chain` (state-chaining ENTAILS the root tooth, the "honest accumulator never asserts the
tooth separately" direction) under the seam turn-context match — the same `hturn` the §5 CR recovery
carries. State continuity is the producer's witness (exactly as `StateChained` is everywhere here); the
tooth is then FREE, not a second assumption. -/

section Accumulator

variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-- **The running accumulator state.** It carries the genesis it folds from, the ordered list of steps
folded so far (the prover's O(1) view keeps only the *witness* of these — the running proof — not the
list; the list is the SPECIFICATION the proof attests), and the live `WellFormedChain` attestation. The
`leanWitness` field IS the inductive invariant: at every fold step it stays a real `WellFormedChain`,
which is exactly what the running recursion proof is sound for (`EngineSound`). -/
structure Acc (g : RecChainedState) where
  /-- The steps folded so far, in chain order (the history the running proof attests). -/
  steps      : List ChainStep
  /-- The inductive invariant: the folded steps are a well-formed chain from genesis. -/
  leanWitness : WellFormedChain CH RH cmb compress compressN g steps

/-- **`Acc.head g acc`** — the state the running accumulator has reached: `lastStateOf` of the folded
steps. The next turn must consume THIS state (`s.pre = acc.head`). -/
def Acc.head {g : RecChainedState} (acc : Acc CH RH cmb compress compressN g) : RecChainedState :=
  lastStateOf g acc.steps

/-- **`genesisAcc g`** — `acc_0`: the empty fold from genesis. Attests the empty (trivially well-formed)
chain. Its head is genesis itself. This is the base of the IVC induction. -/
def genesisAcc (g : RecChainedState) : Acc CH RH cmb compress compressN g where
  steps := []
  leanWitness := { chained := trivial, bound := trivial }

/-- `genesisAcc`'s head is genesis (the empty fold has reached nowhere). -/
@[simp] theorem genesisAcc_head (g : RecChainedState) :
    Acc.head CH RH cmb compress compressN (genesisAcc CH RH cmb compress compressN g) = g := rfl

/-- For a NONEMPTY chain, `lastStateOf` is the last step's `post` (purely structural — it is the state
the fold reaches). Used to identify the join seam in `accumulate`. -/
theorem lastStateOf_eq_getLast_post (g : RecChainedState) (steps : List ChainStep) (last : ChainStep)
    (hlast : steps.getLast? = some last) :
    lastStateOf g steps = last.post := by
  induction steps generalizing g with
  | nil => simp at hlast
  | cons a rest ih =>
    cases rest with
    | nil => simp only [List.getLast?_singleton, Option.some.injEq] at hlast; subst hlast; rfl
    | cons b rest' =>
      have hlast' : (b :: rest').getLast? = some last := by simpa using hlast
      simpa [lastStateOf] using ih a.post hlast'

/-! ### Snoc lemmas — extending each chain predicate by one step at the TAIL.

`accumulate` appends `s` at the END (`steps ++ [s]`). The chain predicates (`StateChained`, `ChainBound`,
`lastStateOf`) are defined by recursion on the HEAD, so extending at the tail needs these three snoc
lemmas, each a straightforward list induction. They are the load-bearing combinatorial content of the
IVC step: dropping/reordering at the tail would break exactly one of them. -/

/-- `lastStateOf` of a tail-extended chain is the new step's `post`, provided the new step extends the
old head (`s.pre = lastStateOf g steps`). -/
theorem lastStateOf_snoc (g : RecChainedState) (steps : List ChainStep) (s : ChainStep) :
    lastStateOf g (steps ++ [s]) = lastStateOf s.pre [s] := by
  induction steps generalizing g with
  | nil => rfl
  | cons a rest ih => simpa [lastStateOf] using ih a.post

/-- A tail-extended chain stays state-chained, IF the old chain is state-chained AND the new step
consumes the old head's state (`s.pre = lastStateOf g steps`). The seam at the join is exactly that
hypothesis. -/
theorem stateChained_snoc (g : RecChainedState) (steps : List ChainStep) (s : ChainStep)
    (hch : StateChained g steps) (hseam : s.pre = lastStateOf g steps) :
    StateChained g (steps ++ [s]) := by
  induction steps generalizing g with
  | nil =>
    -- empty: `s.pre = g` (hseam at the base), and the tail `[]` is `StateChained s.post []` = True.
    refine ⟨?_, trivial⟩
    simpa [lastStateOf] using hseam
  | cons a rest ih =>
    obtain ⟨hpre, hrest⟩ := hch
    subst hpre
    exact ⟨rfl, ih a.post hrest (by simpa [lastStateOf] using hseam)⟩

/-- A tail-extended chain stays `ChainBound`, IF the old chain is bound AND the new step continues the
old LAST step at the root level (`Continues last s`). For the empty/singleton old chain the join has no
predecessor, so it is vacuous; for a longer chain we thread the bound and discharge the final seam. -/
theorem chainBound_snoc :
    ∀ (steps : List ChainStep) (s : ChainStep),
      ChainBound CH RH cmb compress compressN steps →
      (∀ last, steps.getLast? = some last → Continues CH RH cmb compress compressN last s) →
      ChainBound CH RH cmb compress compressN (steps ++ [s])
  | [], s, _, _ => by simp [ChainBound]
  | [a], s, _, hcont => by
    -- old chain `[a]`: the new pair is `[a, s]`; the bound is `Continues a s ∧ ChainBound [s]`.
    refine ⟨?_, trivial⟩
    exact hcont a (by simp)
  | a :: b :: rest, s, hbound, hcont => by
    obtain ⟨hab, htail⟩ := hbound
    refine ⟨hab, ?_⟩
    -- recurse on `b :: rest`; its getLast? is the same as `(a::b::rest).getLast?`.
    have := chainBound_snoc (b :: rest) s htail (by
      intro last hlast
      apply hcont last
      simpa using hlast)
    simpa using this

/-! ### `accumulate` — the IVC step (extend one leaf at a time). -/

/-- **`accumulate acc s hseam hturn`** — the running left-fold step. Given the running accumulator
`acc` (attesting `WellFormedChain g acc.steps`) and the next executor-sound turn `s` (a `ChainStep`, so
`s.commits` is built in) that STATE-EXTENDS the head (`hseam : s.pre = acc.head`) under a matched seam
turn-context (`hturn`), produce `acc'` attesting `WellFormedChain g (acc.steps ++ [s])`. O(1) view: the
prover keeps only `acc` (its running proof); `acc.steps` is the SPEC the proof attests, extended by one.

The two invariants are re-established by the snoc lemmas:
  * STATE continuity (`stateChained_snoc`) from `hseam`;
  * the ROOT temporal tooth (`chainBound_snoc`) — and the NEW seam `Continues last s` is DERIVED from
    `hseam` (state continuity) via `seam_roots_chain`, so the tooth is FREE, never a second assumption. -/
def accumulate {g : RecChainedState} (acc : Acc CH RH cmb compress compressN g) (s : ChainStep)
    (hseam : s.pre = Acc.head CH RH cmb compress compressN acc)
    (hturn : ∀ last, acc.steps.getLast? = some last → last.turn = s.turn) :
    Acc CH RH cmb compress compressN g where
  steps := acc.steps ++ [s]
  leanWitness :=
    { chained := stateChained_snoc g acc.steps s acc.leanWitness.chained hseam
    , bound := chainBound_snoc CH RH cmb compress compressN acc.steps s acc.leanWitness.bound
        (by
          intro last hlast
          -- the root tooth at the join, DERIVED from state continuity (seam_roots_chain).
          -- `last` is the old last step; its post is the old head (`lastStateOf`), which `s.pre` equals.
          have hpost : last.post = s.pre := by
            rw [hseam]
            -- old head = last step's post when the chain is nonempty (getLast? = some last).
            simpa [Acc.head] using (lastStateOf_eq_getLast_post g acc.steps last hlast).symm
          exact seam_roots_chain CH RH cmb compress compressN last s hpost
            (hturn last hlast)) }

/-- **`accumulate_preserves_wellformed` (THE IVC INVARIANT).** The running accumulator's attestation is
PRESERVED by one fold step: `accumulate acc s …` attests `WellFormedChain g (acc.steps ++ [s])`. This is
the inductive heart of the unbounded accumulator — `acc_{n-1} ⊢ 0..n-1` and `turn_n` extends ⟹
`acc_n ⊢ 0..n`. -/
theorem accumulate_preserves_wellformed {g : RecChainedState}
    (acc : Acc CH RH cmb compress compressN g) (s : ChainStep)
    (hseam : s.pre = Acc.head CH RH cmb compress compressN acc)
    (hturn : ∀ last, acc.steps.getLast? = some last → last.turn = s.turn) :
    WellFormedChain CH RH cmb compress compressN g
      (accumulate CH RH cmb compress compressN acc s hseam hturn).steps :=
  (accumulate CH RH cmb compress compressN acc s hseam hturn).leanWitness

/-- **`acc_attests_whole_history` (THE IVC HEADLINE — by induction from genesis).** The running
accumulator attests the WHOLE history it has folded: `acc.leanWitness` IS a `WellFormedChain` from
genesis over `acc.steps`, for ANY accumulator reachable from `genesisAcc` by `accumulate` steps. We
state it as: every `Acc` (which can only be built by `genesisAcc` + `accumulate`, both of which
maintain the invariant) carries the whole-history attestation in its `leanWitness`. Composed with
`light_client_verifies_whole_history` (§3) — whose `EngineSound` is sound for exactly this
`WellFormedChain` — a light client verifying the running root learns the whole accumulated history is
correct, ordered, and genuinely folded. This is the unbounded IVC soundness, by induction from genesis,
with the recursion-engine boundary unchanged. -/
theorem acc_attests_whole_history {g : RecChainedState}
    (acc : Acc CH RH cmb compress compressN g) :
    WellFormedChain CH RH cmb compress compressN g acc.steps :=
  acc.leanWitness

/-- **`acc_attests_run` (the run the accumulator inherits).** The accumulated history is a genuine
`Run recChainedSystem` from genesis to the accumulator's head — so EVERY run-level theorem of the
verified record cell (incl. conservation) applies to the whole O(1)-memory-folded history, with NO
re-execution. -/
theorem acc_attests_run {g : RecChainedState}
    (acc : Acc CH RH cmb compress compressN g) :
    Run recChainedSystem g (Acc.head CH RH cmb compress compressN acc) :=
  wellformed_is_run g acc.steps acc.leanWitness.chained

/-- **`acc_conserves` (conservation over the whole accumulated history).** Value is conserved across the
entire history the running accumulator folded: the ledger total at the head equals the genesis total. A
light client trusting the running aggregate trusts a no-mint/no-burn history of UNBOUNDED length, having
re-executed nothing and held O(1) memory. -/
theorem acc_conserves {g : RecChainedState}
    (acc : Acc CH RH cmb compress compressN g) :
    recTotal (Acc.head CH RH cmb compress compressN acc).kernel = recTotal g.kernel :=
  wellformed_history_conserves g acc.steps acc.leanWitness.chained

/-! ### IVC non-vacuity — the accumulator FIRES on a real chain (genesis → one accumulate step).

The induction would be hollow if no real `accumulate` step could fire. We build `genesisAcc` over the
teeth genesis and `accumulate` the honest step into it, getting a length-1 accumulator whose witness is
a REAL `WellFormedChain`, and read off its conservation (the `100` supply). So the IVC step is inhabited
on a genuine executor run, not an empty implication. -/

section IvcRealize

open Dregg2.Exec.ConsensusExec (teethGenesis honestTurn)

/-- The honest step as a `ChainStep` over the teeth genesis (reusing `HistoryAggregation.honestStep`). -/
abbrev ivcHonestStep : ChainStep := honestStep

/-- The realizing accumulator: `genesisAcc` over the teeth genesis, then one `accumulate` of the honest
step. The seam holds because `genesisAcc`'s head IS genesis and the honest step consumes genesis; the
turn-context match is vacuous (the genesis fold has no last step). -/
def ivcRealAcc : Acc zCH zRH zcmb zcompress zcompressN teethGenesis :=
  accumulate zCH zRH zcmb zcompress zcompressN (genesisAcc zCH zRH zcmb zcompress zcompressN teethGenesis)
    ivcHonestStep
    (by simp [ivcHonestStep, honestStep])
    (by intro last hlast; simp [genesisAcc] at hlast)

/-- **`ivc_accumulate_fires` (IVC non-vacuity).** The realizing accumulator attests a REAL well-formed
1-step history from genesis — the IVC step genuinely fired and preserved the invariant. -/
theorem ivc_accumulate_fires :
    WellFormedChain zCH zRH zcmb zcompress zcompressN teethGenesis ivcRealAcc.steps :=
  acc_attests_whole_history zCH zRH zcmb zcompress zcompressN ivcRealAcc

/-- **`ivc_acc_conserves_real` (the accumulated history conserves — a TRUE arithmetic fact).** The
realizing accumulator's folded history conserves the ledger total: head total = genesis total. So the
unbounded-IVC conservation corollary delivers a real conservation fact on a real executor run. -/
theorem ivc_acc_conserves_real :
    recTotal (Acc.head zCH zRH zcmb zcompress zcompressN ivcRealAcc).kernel
      = recTotal teethGenesis.kernel :=
  acc_conserves zCH zRH zcmb zcompress zcompressN ivcRealAcc

end IvcRealize

end Accumulator

/-! ## 8. Axiom hygiene. -/

#assert_axioms Dregg2.Circuit.RecursiveAggregation.every_leaf_verifies_implies_executed
#assert_axioms Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history
#assert_axioms Dregg2.Circuit.RecursiveAggregation.attested_history_conserves
-- the CRITICAL-3 closure: conservation-over-history DERIVED from `verify agg.root`, no StateChained:
#assert_axioms Dregg2.Circuit.RecursiveAggregation.conserves_from_verification
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_engine_sound
#assert_axioms Dregg2.Circuit.RecursiveAggregation.light_client_fires_on_real_chain
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_chain_first_turn_executed
#assert_axioms Dregg2.Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind
#assert_axioms Dregg2.Circuit.RecursiveAggregation.leaf_pairing_defeats_swap
-- the UNBOUNDED IVC accumulator: the running left-fold preserves whole-history attestation, by
-- induction from genesis (the part Mina lacks — a machine-checked IVC soundness induction):
#assert_axioms Dregg2.Circuit.RecursiveAggregation.lastStateOf_snoc
#assert_axioms Dregg2.Circuit.RecursiveAggregation.stateChained_snoc
#assert_axioms Dregg2.Circuit.RecursiveAggregation.chainBound_snoc
#assert_axioms Dregg2.Circuit.RecursiveAggregation.lastStateOf_eq_getLast_post
#assert_axioms Dregg2.Circuit.RecursiveAggregation.accumulate_preserves_wellformed
# Codex design — the ordered segment-accumulator fix for the IVC mixed-root hole (2026-06-24)

Codex's recommended construction (gigabrain advice, not a review): close the mixed-root forgery by making the whole-chain claim sound-BY-CONSTRUCTION — a constant-size ordered segment accumulator carried by every descriptor leaf + each aggregation node, replacing the separate binding leaf in the soundness-critical path.

HORIZONLOG.md:4198:- **#103 cap-crown Phase-D — the 4-ary c-list `membership` leg vs. the sorted `cap-membership` leg (retire-or-keep).** `sdk/src/full_turn_proof.rs` attaches TWO distinct membership sub-proofs to a cap-gated turn, proving DIFFERENT claims: (a) the **4-ary c-list `membership` leg** (`:978-1012`, witness `MembershipWitness` `:177`, `prove_membership_p3` over the generic positions-indexed `P3MerklePoseidon2Air`, PI `[leaf_hash, root]`, vk `merkle_poseidon2_descriptor`) proves "an opaque capability `leaf_hash` is present in A Merkle tree at the witnessed positions" — a GENERIC membership statement; its root is not structurally pinned to the authenticated `cap_root`, and the leaf is an opaque hash (not the typed 7-field cap preimage). (b) the **sorted `cap-membership` leg** ("cap Phase D", `:1075-1100`, witness `CapMembershipWitness` `:212` ← `ConsumedCapWitness`, `prove_cap_membership_p3` over the SORTED `CanonicalCapTree`, directional path, vk `cap_membership_circuit_descriptor`, expectation `CapMembershipExpectation` `:239` pins `pi[CAP_ROOT]` to the trusted root `:248`) proves "the SPECIFIC CONSUMED capability's full 7-field leaf preimage opens against THE holder's real sorted `cap_root` tree" — the authority leg that ties the acting/consumed cap to the authenticated cap-state, with sorted single-leaf-per-slot semantics. **The two are not redundant:** the sorted leg gives the strictly stronger, structurally-pinned, typed-leaf guarantee; the 4-ary leg gives a weaker generic membership over an unpinned root with an opaque leaf. **Retire-vs-keep tradeoff:** for a cap-gated turn the sorted `cap-membership` leg SUBSUMES the authority claim the 4-ary leg makes (consumed-cap-in-the-real-cap_root ⊃ opaque-leaf-in-some-4-ary-tree), so the 4-ary leg is retireable FOR CAP-GATED TURNS on the claim alone. **Live-producer evidence (the deciding fact):** there is currently NO live producer that sets `membership: Some(MembershipWitness{..})` — the only two build sites (`full_turn_proof.rs:2303`, `:2774`) are both inside `#[cfg(test)] mod tests` (`:2107`) using `merkle_test_witness`; the only LIVE membership-leg producer is `cap_membership` (`node/src/turn_proving.rs:518`, `CapMembershipWitness::from_consumed`). So today the 4-ary `membership` leg is dead on the live path — its `Option`/`P3MerklePoseidon2Air`/`merkle_poseidon2_descriptor` plumbing is wired + SDK-tested but unfed. **The keep argument** is therefore forward-looking, not current: the 4-ary leg is the GENERIC credential/c-list membership primitive (opaque leaf, witnessed root, no sorted `cap_root` to open against) that a NON-cap predicate-credential turn-shape WOULD use — retiring it removes that future affordance and the `merkle_poseidon2` descriptor's only full-turn consumer. **Recommendation (ember to ratify):** keep the 4-ary leg as the general-membership primitive but DO NOT couple it to cap-gated turns (the sorted leg is the cap authority leg of record); OR, if no near-term non-cap credential turn-shape is planned, demote the 4-ary leg + its descriptor to a clearly-labelled "general membership, no live producer" status (Research tier) so it stops reading as a live cap-authority alternative. Before any removal, confirm no in-flight feature wires a live `membership: Some(..)`. Named: cap-crown #103 Phase-D map, 2026-06-13. (Left intact — characterization only, per the brief.)
HORIZONLOG.md:4212:`builder.when_transition()` (`descriptor_ir2.rs:1763-1772`) — every row BUT the last. So **Lean-Satisfied2 is
HORIZONLOG.md:4213:STRICTER than Rust-accept on the last row**, and the byte-identity descriptor differential does NOT catch it (the
HORIZONLOG.md:4224:when_transition) across the rotated descriptor; (2) trace which row feeds the published 8-felt commit + whether
HORIZONLOG.md:4240:   tooth) closes it. CONFIRM-AT-SETTLE: are multi-asset atomic turns reachable? If yes → live hole, not nicety.
HORIZONLOG.md:4279:- IR-v2 deployed path: `descriptor_ir2.rs:1763` puts Gate + Transition under `builder.when_transition()`.
HORIZONLOG.md:4295:precedent exists (`effect_vm_descriptor_exhaustive_differential.rs` = generator-driven differential vs the REAL
HORIZONLOG.md:4321:   descriptor_ir2.rs:1744) + the every-row Poseidon2 hash-site lookups over the last row's own state_after
HORIZONLOG.md:4322:   (descriptor_ir2.rs:1797). NO commitment-malleability hole. (Tightening, not a hole: the NoOp pad's
HORIZONLOG.md:4336:   degree bound is enforced symbolically by verify_batch. check_descriptor2 bounds-checks every producer index
HORIZONLOG.md:4337:   FIRST (descriptor_ir2.rs:4445/1172). One cheap defense-in-depth tightening: proof_verify.rs:357/359/391/393
HORIZONLOG.md:4341:Poseidon2, out-lanes assert_zero descriptor_ir2.rs:2039) · mem/map ops (committed sub-AIRs + zero-summed buses).
HORIZONLOG.md:4356:`Satisfied2` is NOT a faithful denotation of the deployed Rust `verify_vm_descriptor2`. The byte-identity
HORIZONLOG.md:4465:  + fields WITH provenance into the document commitment. The anti-forge tooth is TESTED — forging or
HORIZONLOG.md:4470:  `compute_heap_root` — the anti-forge tooth RE-PROVEN against the REAL root, not the `DefaultHasher`
HORIZONLOG.md:4534:  local arms via the actual Ir2Air::eval (96/216, no drift), bus arms via the actual prove/verify_vm_descriptor2
HORIZONLOG.md:4542:HYGIENE: --features verifier (light-client build) un-broken; wide-descriptor width-skew (188-col) regen IN FLIGHT.
HORIZONLOG.md:4572:ClosureFanoutGenuine.lean:828 is a 36-way split, every slot a proven <e>_descriptorRefines concluding the real
HORIZONLOG.md:4575:- CLASS A (circuit-descriptor-bound, edit propagates RED): 6 effects — transfer, mint, burn, setField,
HORIZONLOG.md:4582:  circuit denotation. Spec-edit still reds them (they refine real Spec); circuit-descriptor-edit does NOT.
HORIZONLOG.md:4583:  Worst: heapWrite(56) Rfix 56 = the WRONG descriptor (transfer fallback), descriptor-abstract by design.
HORIZONLOG.md:4596:- ⚑ THE MISSING WELD (the single highest-leverage edit on the board): the multi-turn IVC / finalized-history /
HORIZONLOG.md:4601:  stack. Likely ~one bridging theorem (modulo the IVC recursion shape).
HORIZONLOG.md:4603:  mint descriptor, rides kstepAll. Argus/Effects/BridgeMint.lean clean (the memory's "breakage" flag is STALE).
HORIZONLOG.md:4633:  axiom (multi-turn/IVC/joint/promises all proven-but-parallel).
HORIZONLOG.md:4647:PROVEN-BUT-UNJOINED weld, and the descriptor (VK-affecting) work is ALREADY DEPLOYED.
HORIZONLOG.md:4654:  never joined -> descriptor edit doesn't propagate red.
HORIZONLOG.md:4655:- THE FIX = non-VK-affecting PROOF-COMPLETION (not descriptor-completion): a cellSeal_forced extraction (transfer's
HORIZONLOG.md:4661:  active-row satisfiedVm -> *_forces -> decode -> root_binds -> kernel field; (4) rewire e_descriptorRefines +
HORIZONLOG.md:4663:- ⚑ THE (b)-GAP DISCRIMINATOR: a slot is a REAL descriptor gap (VK-affecting) iff its committed limb has NO
HORIZONLOG.md:4698:  DELEGATEATTEN, REVOKEDELEGATION, REFRESHDELEGATION. Root cause: the cap-open descriptor forces the authority
HORIZONLOG.md:4703:  false-but-hidden at the deployed descriptor: a prover can publish a wrong post-cap-root and the circuit won't
HORIZONLOG.md:4714:descriptor gaps [VK, mirror attenuate's keepWriteOp + _non_amp]; (c) revokeCapability force-lemma; (d) heapWrite
HORIZONLOG.md:4732:## ⚑ LIFECYCLE LAZY-fan landed (a6ef3b7c) — 3 Class-A + a 6th REAL GAP found (receiptArchive spec↔descriptor divergence)
HORIZONLOG.md:4734:banked, tree red from parallel CapFamily/PermsVK mid-edit): cellUnseal_descriptorRefines_sat (disc gate
HORIZONLOG.md:4735:forces lifecycle=lcLive), cellDestroy_descriptorRefines_sat (BOTH legs: lifecycle=lcDestroyed + deathCert via the
HORIZONLOG.md:4736:record-pin folded in the disc gate), refusal_descriptorRefines_sat (record-pin forces fieldOf refusalField = 1).
HORIZONLOG.md:4738:⚑ receiptArchive = a 6th REAL GAP (different kind: spec↔descriptor DIVERGENCE, not a missing write): deployed
HORIZONLOG.md:4741:(post.lifecycle = pre.lifecycle) — they CONTRADICT. Class-A unreachable from the deployed descriptor without a
HORIZONLOG.md:4742:descriptor change (bind the audit record slot) OR reconciling the spec to the deployed Archived side-table
HORIZONLOG.md:4743:semantics. = an EMBER/descriptor decision, not Lean wiring. Documented at RotatedKernelRefinementLifecycleDisc §6.
HORIZONLOG.md:4756:  the insertWriteOp descriptor + _forces_write keystones) + revokeCapability (removeWriteOp deployed)
HORIZONLOG.md:4761:  …Genuine face (a VK cutover, the …Genuine descriptors EXIST but aren't deployed). Cleanly Class-B-pending.
HORIZONLOG.md:4762:- receiptArchive: spec↔descriptor CONTRADICTION (spec writes record-slot+freezes lifecycle; descriptor forces
HORIZONLOG.md:4763:  lifecycle=Archived) — ember/descriptor decision.
HORIZONLOG.md:4766:NEXT: (a) wire the new *_descriptorRefines_sat into the apex fanout (ClosureFanoutGenuine — MAIN LOOP owns, serial);
HORIZONLOG.md:4767:(b) the VK JSON descriptor regen + drift-gate for the cap-write changes; (c) the 3 frozen-face cutover; (d)
HORIZONLOG.md:4812:  sealed Snapshot (reuses snapshot.rs:80 fail-closed root tooth) + ImageAttestation.
HORIZONLOG.md:4814:  reconstruct tooth, conservation Σ=0, factory provenance, program-for-life binding so a cell can't be smuggled
HORIZONLOG.md:4825:Guarantee A (Authority) circuit-FORCED (a circuit-descriptor edit reds the rung, mutation-confirmed) status by effect:
HORIZONLOG.md:4835:  deleg-tree map-op + runtime column (delegRoot_runtime_column_pending). The one genuine descriptor-architecture
HORIZONLOG.md:4838:SERIAL TAIL (main-loop owned, queued): (a) wire the new _descriptorRefines_sat + the capOpenSat rungs into the apex
HORIZONLOG.md:4840:descriptor regen for the new/changed descriptors (introduceWriteV3/CapOpen wrappers/heapWriteV3 — widths recorded);
HORIZONLOG.md:4853:FOLLOW-UPS (named, VK-free-driveable): (a) SetProgram's OWN circuit descriptor witness (reuses
HORIZONLOG.md:4854:EFFECT_SET_VERIFICATION_KEY's tag today, executor-sound; the descriptor rung is the VK follow-up); (b) wire the
HORIZONLOG.md:4860:After the soundness waves: (1) wire the new _descriptorRefines_sat + capOpenSat rungs (receiptArchive, heapWrite,
HORIZONLOG.md:4861:the 5 cap slots) into the apex fanout ClosureFanoutGenuine (13 wired, ~7-9 to add); (2) the JSON descriptor regen
HORIZONLOG.md:4862:for the new/changed descriptors (introduceWriteV3/CapOpen wrappers/heapWriteV3) + drift re-pin; (3) compact
HORIZONLOG.md:4865:## ⚑ JSON-EMIT FOLLOW-UP (2026-06-20) — the new apex descriptors aren't in emit_descriptors.py's list yet
HORIZONLOG.md:4867:revokeDelegationWriteCapOpenV3) + heapWriteV3 — the apex now PROVES about them. But scripts/emit_descriptors.py
HORIZONLOG.md:4868:emits from a FIXED descriptor-name list that does NOT include them (verified: grep -c WriteCapOpen|heapWrite in
HORIZONLOG.md:4869:emit_descriptors.py = 0), so the checked-in deployed JSON doesn't yet carry these descriptors (drift gate PASSES
HORIZONLOG.md:4873:edit): add the new descriptor names to the emitter so the deployed JSON carries exactly what the apex proves about,
HORIZONLOG.md:4876:## ⚑⚑⚑ AUTHORITY FLOOR — LAST MILE, the light-client forge CLOSED via the verifier tooth (2026-06-20, base 99cf43412, UNCOMMITTED)
HORIZONLOG.md:4879:under its PLAIN cohort descriptor. New `is_forbidden_plain_cap_descriptor` forbids the 5 plain cap-effect
HORIZONLOG.md:4880:descriptors (introduce/revoke/attenuate/grantCap/revokeCapability VmDescriptor2R24) as the uniquely-accepting
HORIZONLOG.md:4881:descriptor — a cap effect MUST bind a `…CapOpen…VmDescriptor2R24` (the depth-16 capOpenConstraintsEff membership
HORIZONLOG.md:4882:crown is IN that descriptor and ONLY there). So a malicious producer that strips the cap-open route to launder
HORIZONLOG.md:4884:- WHY the verifier tooth (not a blind producer resolver re-point): the deployed wire shares NO single resolver
HORIZONLOG.md:4885:  the way the verdict assumed. (1) The SDK light-client verifier iterates ALL cohort descriptors and binds the
HORIZONLOG.md:4886:  unique acceptor (it does NOT call `rotated_descriptor_name`) — so the FORCING had to be a forbidden-name tooth
HORIZONLOG.md:4890:  full_turn_proof.rs:1096/1687) — the verifier tooth makes that route MANDATORY (a producer can't get a cap
HORIZONLOG.md:4892:- NEW forge-rejection test `light_client_rejects_cap_effect_under_plain_descriptor`: proves a RevokeDelegation
HORIZONLOG.md:4895:  tooth: plain cap-effect ⇒ reject, cap-open ⇒ accept.
HORIZONLOG.md:4896:- NO VK/descriptor drift (verifier-behavior change only; no .tsv/.json touched — the cap-open descriptors forced
HORIZONLOG.md:4899:- RESIDUE (named, NOT in scope of this fix): (a) refreshDelegation stays on its plain descriptor — its deleg-tree
HORIZONLOG.md:4901:  authority — named, not a silent forge). (b) The …WriteCapOpen descriptors (introduceWrite/delegateWrite/
HORIZONLOG.md:4904:  (already wired). The write-op binding into the commitment (the ~17-effect descriptor-fix terrain in
HORIZONLOG.md:4914:- LIGHT-CLIENT GAP: the deployed producer selects the PLAIN cohort descriptors for cap effects
HORIZONLOG.md:4920:  from "host asserted it" — a malicious producer proves the cap effect via the non-cap path -> plain descriptor ->
# Codex FINAL re-review — IVC #1 same-endpoint close (2026-06-25): NO CRITICAL HOLE

VERDICT: for the K-fold segment path, NO critical soundness hole — the same-endpoint mixed-root forgery is GENUINELY CLOSED under the Poseidon2 truncated-output commitment assumption.

## Why sound
- Bug A (dropped v_j==0): NOT reopened. expose_claim reads the FULL ext tuple [idx,c0,c1,c2,c3] on the WitnessChecks bus (bus-bound to the W24 output, so c1/c2/c3 can't be freely chosen), exposes only c0 as the public. A forgery requires a collision in the exposed digest.
- THE DIGEST IS NOT ~31-bit coeff-0-only: dregg compares a 7-felt segment claim — genesis, final, count, + FOUR BabyBear digest lanes (ivc_turn_chain.rs:224 + :1963). ~124-bit digest collision resistance.
- Bug B (off-bus capacity): AIR-constrained (noncompact Poseidon2 AIR ties absent next-row inputs to the prior row output; executor mirrors). Sound.

## Residuals (codex, NONE critical)
- MEDIUM (scope): the ONLINE ACCUMULATOR path (accumulator.rs:171/819/916) is still single-felt/zero-padded, explicitly scoped out — do NOT generalize the K-fold close to it. The named separate follow-up.
- LOW (doc drift): comments at expose_claim_air.rs:23 + circuit_builder.rs:486 still describe the old scalar-only expose — fix them (they now contradict the soundness-critical design).
- LOW (margin): the checked digest is 4 BabyBear lanes (~124 bit), not the full D-coeff tuple. Avoids the old one-felt hole; widening beyond 4 lanes would give a conservative 128-bit story.

Do it as a theorem over the **aggregation proof tree**, not over an `Acc`/witness record.

```lean
structure Seg where
  first_old : Root
  last_new  : Root
  count     : Nat      -- or F plus count < p
  acc       : Digest

def LeafSeg (e : ExecLeaf) : Seg :=
  { first_old := e.old, last_new := e.new, count := 1, acc := Hleaf e.old e.new }

def CombineOk (L R P : Seg) : Prop :=
  L.last_new = R.first_old ∧
  P.first_old = L.first_old ∧
  P.last_new = R.last_new ∧
  P.count = L.count + R.count ∧
  P.acc = Hnode L.acc R.acc
```

Key invariant:

```lean
inductive GenuineSeg : Seg -> List ExecLeaf -> Prop
| leaf :
    Executed e ->
    GenuineSeg (LeafSeg e) [e]
| node :
    GenuineSeg Lseg Ls ->
    GenuineSeg Rseg Rs ->
    CombineOk Lseg Rseg Pseg ->
    GenuineSeg Pseg (Ls ++ Rs)
```

Then prove:

```lean
theorem subtree_binding
    (es : EngineSound)
    (t : AggTree)
    (hverify : verify t.proof = true) :
    GenuineSeg t.exposedSeg t.executedLeaves
```

Base case:

```lean
case leaf p stmt exposed =>
  -- EngineSound gives the verified descriptor statement, not whole-chain binding.
  have hleaf := es.leaf_sound hverify
  -- hleaf includes:
  --   Executed e
  --   exposed.first_old = e.old
  --   exposed.last_new = e.new
  --   exposed.count = 1
  --   exposed.acc = Hleaf e.old e.new
  simpa [LeafSeg] using GenuineSeg.leaf hleaf.executed
```

Step case:

```lean
case node p L R Pseg =>
  have hnode := es.combine_sound hverify
  -- hnode gives only local facts:
  --   verify L.proof = true
  --   verify R.proof = true
  --   CombineOk L.exposedSeg R.exposedSeg Pseg

  have hL : GenuineSeg L.exposedSeg L.executedLeaves :=
    subtree_binding es L hnode.left_verified

  have hR : GenuineSeg R.exposedSeg R.executedLeaves :=
    subtree_binding es R hnode.right_verified

  exact GenuineSeg.node hL hR hnode.combine_ok
```

`EngineSound` must provide only **local statement soundness**:

```lean
structure EngineSound where
  leaf_sound :
    verify leafProof = true ->
      Executed e ∧ exposed = LeafSeg e

  combine_sound :
    verify nodeProof = true ->
      verify leftProof = true ∧
      verify rightProof = true ∧
      CombineOk leftExposed rightExposed parentExposed
```

It must **not** provide `GenuineSeg`, `ChainBound`, `foldedFinalRoot`, or “whole history”. Those are derived by the induction.

Final root theorem:

```lean
theorem root_binds_carried_claim
    (es : EngineSound)
    (hroot : verify root.proof = true)
    (hhost : root.exposedSeg = carriedClaim.toSeg) :
    GenuineSeg carriedClaim.toSeg root.executedLeaves := by
  simpa [hhost] using subtree_binding es root hroot
```

Corollaries from `GenuineSeg`:

```lean
theorem genuine_count :
  GenuineSeg s leaves -> s.count = leaves.length

theorem genuine_ordered :
  GenuineSeg s leaves -> ChainBound leaves

theorem genuine_endpoints :
  GenuineSeg s leaves ->
    s.first_old = firstOld leaves ∧ s.last_new = lastNew leaves

theorem genuine_digest :
  GenuineSeg s leaves -> s.acc = treeDigest leaves
```

Mixed-root rejection:

```lean
theorem no_mixed_root
    (hrootA : verify rootA.proof = true)
    (hhostB : rootA.exposedSeg = claimB.toSeg)
    (hneq : claimB.toSeg ≠ genuineTreeSeg rootA.executedLeaves) :
    False := by
  have h := root_binds_carried_claim es hrootA hhostB
  have heq := GenuineSeg_unique_summary h
  exact hneq heq.symm
```

For same endpoints/count, the final “B’s history differs from A’s history” step needs the Poseidon2 binding assumption:

```lean
PoseidonSegBinding :
  treeDigest leavesA = treeDigest leavesB ->
  same ordered leaf segments leavesA leavesB
```

Without that, Lean can prove “the carried claim equals the genuine segment summary of A’s executed leaves”; it cannot prove “no different B exists with the same segment” except by reducing it to a Poseidon2 collision. That is the right boundary: EngineSound gives local proof/constraint soundness; the induction gives ordered-chain binding; Poseidon2 CR gives semantic uniqueness of the ordered digest.
140,804
Do it as a theorem over the **aggregation proof tree**, not over an `Acc`/witness record.

```lean
structure Seg where
  first_old : Root
  last_new  : Root
  count     : Nat      -- or F plus count < p
  acc       : Digest

def LeafSeg (e : ExecLeaf) : Seg :=
  { first_old := e.old, last_new := e.new, count := 1, acc := Hleaf e.old e.new }

def CombineOk (L R P : Seg) : Prop :=
  L.last_new = R.first_old ∧
  P.first_old = L.first_old ∧
  P.last_new = R.last_new ∧
  P.count = L.count + R.count ∧
  P.acc = Hnode L.acc R.acc
```

Key invariant:

```lean
inductive GenuineSeg : Seg -> List ExecLeaf -> Prop
| leaf :
    Executed e ->
    GenuineSeg (LeafSeg e) [e]
| node :
    GenuineSeg Lseg Ls ->
    GenuineSeg Rseg Rs ->
    CombineOk Lseg Rseg Pseg ->
    GenuineSeg Pseg (Ls ++ Rs)
```

Then prove:

```lean
theorem subtree_binding
    (es : EngineSound)
    (t : AggTree)
    (hverify : verify t.proof = true) :
    GenuineSeg t.exposedSeg t.executedLeaves
```

Base case:

```lean
case leaf p stmt exposed =>
  -- EngineSound gives the verified descriptor statement, not whole-chain binding.
  have hleaf := es.leaf_sound hverify
  -- hleaf includes:
  --   Executed e
  --   exposed.first_old = e.old
  --   exposed.last_new = e.new
  --   exposed.count = 1
  --   exposed.acc = Hleaf e.old e.new
  simpa [LeafSeg] using GenuineSeg.leaf hleaf.executed
```

Step case:

```lean
case node p L R Pseg =>
  have hnode := es.combine_sound hverify
  -- hnode gives only local facts:
  --   verify L.proof = true
  --   verify R.proof = true
  --   CombineOk L.exposedSeg R.exposedSeg Pseg

  have hL : GenuineSeg L.exposedSeg L.executedLeaves :=
    subtree_binding es L hnode.left_verified

  have hR : GenuineSeg R.exposedSeg R.executedLeaves :=
    subtree_binding es R hnode.right_verified

  exact GenuineSeg.node hL hR hnode.combine_ok
```

`EngineSound` must provide only **local statement soundness**:

```lean
structure EngineSound where
  leaf_sound :
    verify leafProof = true ->
      Executed e ∧ exposed = LeafSeg e

  combine_sound :
    verify nodeProof = true ->
      verify leftProof = true ∧
      verify rightProof = true ∧
      CombineOk leftExposed rightExposed parentExposed
```

It must **not** provide `GenuineSeg`, `ChainBound`, `foldedFinalRoot`, or “whole history”. Those are derived by the induction.

Final root theorem:

```lean
theorem root_binds_carried_claim
    (es : EngineSound)
    (hroot : verify root.proof = true)
    (hhost : root.exposedSeg = carriedClaim.toSeg) :
    GenuineSeg carriedClaim.toSeg root.executedLeaves := by
  simpa [hhost] using subtree_binding es root hroot
```

Corollaries from `GenuineSeg`:

```lean
theorem genuine_count :
  GenuineSeg s leaves -> s.count = leaves.length

theorem genuine_ordered :
  GenuineSeg s leaves -> ChainBound leaves

theorem genuine_endpoints :
  GenuineSeg s leaves ->
    s.first_old = firstOld leaves ∧ s.last_new = lastNew leaves

theorem genuine_digest :
  GenuineSeg s leaves -> s.acc = treeDigest leaves
```

Mixed-root rejection:

```lean
theorem no_mixed_root
    (hrootA : verify rootA.proof = true)
    (hhostB : rootA.exposedSeg = claimB.toSeg)
    (hneq : claimB.toSeg ≠ genuineTreeSeg rootA.executedLeaves) :
    False := by
  have h := root_binds_carried_claim es hrootA hhostB
  have heq := GenuineSeg_unique_summary h
  exact hneq heq.symm
```

For same endpoints/count, the final “B’s history differs from A’s history” step needs the Poseidon2 binding assumption:

```lean
PoseidonSegBinding :
  treeDigest leavesA = treeDigest leavesB ->
  same ordered leaf segments leavesA leavesB
```

Without that, Lean can prove “the carried claim equals the genuine segment summary of A’s executed leaves”; it cannot prove “no different B exists with the same segment” except by reducing it to a Poseidon2 collision. That is the right boundary: EngineSound gives local proof/constraint soundness; the induction gives ordered-chain binding; Poseidon2 CR gives semantic uniqueness of the ordered digest.
