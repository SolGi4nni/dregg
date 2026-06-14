# NEXT-WAVE — the ready-to-fire forward work (each item: the lever + why it's held)

*(Capture doc, 2026-06-14. THE FLIP is in progress; the overnight wide-safe wave is banked.
This file holds the work that is READY to launch but was deliberately held — so nothing good
is lost at compaction. It is NOT a status board (that is `REORIENT.md`) and NOT the named-
follow-up burn-down (that is `HORIZONLOG.md`, which carries the fine-grained seams). Each item
here names: WHAT, the CLOSURE LEVER, and WHY IT WAS HELD. Present-tense, no trajectory
narrative. Sweep items into git history as they land; demote to Research with a reason if they
sit unscheduled.)*

---

## A. THE FLIP completion + the held push (the one held milestone)

**What.** Finish the cutover flag-day: C5 (the v3Registry→default regen + re-pin ~58 artifacts/11
drift-guards + FFI reseed via `dregg-lean-ffi/scripts/rebuild-dregg2-closure.sh`), the #103 sovereign-
path graduation (ember-DECIDED shape (i): cut `cipherclerk.execute_sovereign_turn_with_proof` +
`turn/src/executor/proof_verify.rs::verify_and_commit_proof` off the bespoke `EffectVmAir` onto the
rotated `Ir2BatchProof`, retiring the `air.rs:1365-1374` legacy cap arm so in-circuit non-amplification
holds EVERYWHERE), the notify Step-2 VK-batch (`docs/NOTIFY-CASCADE.md` + `docs/NOTIFY-STEP2-VK-CHECKLIST.md`
felt-encoders folded into the SAME VK bump), then C7 = DELETE v1 (`effect_vm_p3_full_air.rs`,
`effect_vm/air.rs`, the 186-col `generate_effect_vm_trace`, `ACTIVE_BASE_COUNT`, `CutoverFallback`,
`lean_descriptor_air.rs` v1) + grep-zero per `docs/ROTATION-CUTOVER.md` §EXEC grep_zero_checklist. End
state = ONE proof path.

**Closure lever.** A flip-executor agent is running C5/C7 (the main loop drives it across relaunches).
Then the **persvati workspace gauntlet** (the full cross-crate validation: sdk e2e + node + producer +
circuit harness, 24 cores) on the converged tree, then the **held push (~30 commits)**, then the
**devnet redeploy** (`deploy/aws/update.sh`, fresh genesis — graviton i-0540e3a, EIP 34.224.208.52).

**Why held.** The VK epoch is the one irreversible, coordinated act (it bumps the verifying key + cell
commitment + descriptor SHA registry together). The **redeploy is ember's act** — it is the point-of-no-
return for the live devnet (fresh genesis discards the current chain). Everything is one-command-ready
per ROTATION-CUTOVER §EXEC.3; we wait for ember at the redeploy boundary.

---

## B. The l4v BINARY BRIDGE (the diamond gap)

**What.** Close the distance from the strong Lean composition (`deployed_system_secure` apex; unfoolability
derives conservation) to l4v-grade assurance. The gap is the **binary bridge** — the proofs cover the
abstract kernel, not the deployed binary. Two named obligations (`docs/ASSURANCE-CRITIQUE.md` §5,
HORIZONLOG "Metatheory closures" CRITICAL-2):

1. **Translation-validation of `dregg-lean-ffi/src/marshal.rs` as a THEOREM** — the 2231-line hand-rolled
   byte-for-byte mirror of the Lean wire grammar (`marshal_turn_hosted` emit at `marshal.rs:617`;
   `unmarshal_result` decode at `:1710`) is the codec-in-TCB seam. Today it is upheld only by
   `marshal_roundtrip.rs` differential vs the real FFI symbol. The obligation is
   `marshal_turn_hosted(w) = encodeWWire(lift w)` as a theorem (generate the Rust from Lean, or a verified-
   Rust mirror), NOT a test corpus. (The Lean half is CLOSED — `Dregg2/Exec/FFI/Refine.lean` proves the
   `@[export]`ed body refines the model; this is the Rust half.)
2. **The Lean→C / `libdregg_lean.a` link correspondence** — no binary-correspondence statement that the
   linked `.a` IS the `@[export]`ed Lean (the seL4 C-to-binary analogue).

**Closure lever.** **Stage 0 = make the verified executor authoritative**: invert `turn/src/lean_apply.rs:
~1143` so Lean is the source of truth, not a shadow ("no new mathematics" — a wiring inversion, not a new
proof). Then Stages 1-6 in ASSURANCE-CRITIQUE.md §5 (spec→binary refinement / discharge `leaf_sound` / tie
the apex to one turn / native UC / n>1 consensus / config-pin the crypto floor). Obligation #1 is the
sharper, more tractable one.

**Why held.** Post-cutover by design — it touches the FFI boundary, disjoint from the proof-wire flip, and
Stage 0 wants the rotated path settled first so the authoritative executor is the graduated one.

---

## C. The faucet / finalized-execution hardening (running)

**What.** A production-hardening pass on the faucet + `execute_finalized_turn` cell-provisioning semantics.
S5-1 closed the n≥2 commit with four defect fixes; the faucet currently scratch-clones in multi-party mode
and `execute_finalized_turn` materializes a missing Transfer dest as a remote stub — devnet-correct, but the
provisioning semantics want a deliberate pass (who provisions a cell first-seen-at-finality; the faucet's
eager-exec vs finalized-exec interaction).

**Closure lever.** A lane is running (→ `node/api` + `execute_finalized`). NOT blocking the flip or the
redeploy (the devnet is correct today).

**Why held.** Surfaced by S5-1; it is a refinement of a working path, sequenced after the flip's irreversible
core so it doesn't churn the cutover tree.

---

## D. STARBRIDGE-V2 / DESKTOP deepenings (the cockpit goes LIVE)

*(The native master interface embeds the real verified executor + runs a local dregg world; the headless
heart is gpui-free + `cargo test`-able. `docs/STARBRIDGE-V2.md` is the coverage matrix; HORIZONLOG
"STARBRIDGE-V2" carries the per-panel seams.)*

- **The live-node connection panel** — move reads to gpui's async executor; wire `/api/events/stream` SSE
  into `ReceiptInspector` with `cx.notify()` (snapshot today). **Lever:** connect the cockpit to the now-
  COMMITTING n>1 node → the channel/mailbox/court organs become **LIVE reflections** (today they are
  surfaced honestly as remote-path kind·seam·route, never faked). **Held:** waited on S5 (the node commits
  at n>1 NOW — this is unblocked).
- **The native federation / remote-node panel** — `NodeClient::Http` exists but `reqwest` is gated to
  sel4-thin. **Lever:** un-gate the HTTP client for native-full; the remote organs light up with the live
  panel above. **Held:** rides the live-node connection.
- **Single-source wire types** — replace `starbridge-v2/src/model/` hand-mirrors with a shared
  `dregg-wire-types` crate depended on by both node + shell. **Lever:** extract the crate, depend both
  sides. **Held:** a refactor best done once the wire shapes settle past the flip.
- **The seL4 framebuffer backend** — a gpui renderer targeting a framebuffer cap (the SEL4-EMBEDDING end
  state) + a `NodeClient::Channel` over an seL4 endpoint (same contract over IPC not TCP). **Lever:** the
  rust-sel4 toolchain + Microkit SDK (absent here). **Held:** gated on the seL4 cross-build toolchain.

---

## E. EMBEDDED-SERVO + DISTRIBUTED-SERVO (the browser as a cap-confined guest)

**What.** Implement the design corpus: `docs/EMBEDDED-WEB-SURFACE.md` (a Servo `WebView` opened as a dregg
`SurfaceCapability` cell — its fetches/navigation/new-window/permission/auth become mediated effects gated
by held caps; the trusted-path origin chrome drawn by the shell from the live ledger, never the page) and
`docs/DISTRIBUTED-SERVO.md` (the same, slid apart across the federation by relaxing the firmament `Bounds{n}`
— a link is a sturdy ref, a fetch resolves over CapTP through a netlayer).

**Closure lever.** The **libservo `WebViewDelegate` cap-gate build** — the embedder's impl of the delegate
IS the cap gate. The surface/shell discipline + the cap model + the netlayer + the attestation primitive all
ship today; the build is the libservo embed behind the gate (single-node first = EMBEDDED, then the per-DOM-
node mediation + the seL4 renderer PD = DISTRIBUTED).

**Why held.** A frontier build (libservo is a large dependency; the seL4-PD renderer is research). The design
is settled and present-tense-grounded; the implementation is the next deliberate lane.

---

## F. pg-dregg (the proof-gate + the executor-in-postgres north star)

*(pg-dregg is a standalone workspace `pg-dregg/`, own target — no `./target` contention. M2 mirror +
Tier-C chain-gate + the §11 write outbox + the submit-queue drainer are LIVE on pg17/pg18. `docs/PG-DREGG.md`
is the master.)*

- **The proof-gate S1-S3** (`PG-DREGG.md` §10.2.1): **S1** serialize `circuit::ivc_turn_chain::WholeChainProof`
  (it holds plonky3 proof objects, NOT serde today — needs a versioned envelope); **S2** a node-side proof
  PRODUCER (fold finalized turns via `prove_turn_chain_recursive`/`fold_two_turns` → write a
  `dregg.turn_proofs(lo,hi,genesis_root,final_root,proof bytea,vk)` table the SRF reads); **S3** flip
  `attest::verify_serialized_proof` from the fail-closed stub to the real `verify_turn_chain_recursive`
  (the `tier-c` feature's `dregg-circuit` dep, `--features verifier`, **Lean-FREE**). Until S1-S3 the SRF
  attests NOTHING (the safe direction). **Lever:** S1 is the **WholeChainProof recursion-proof SERDE** (item
  G below) — the shared unblock. **Held:** serde-blocked on the fork-side recursion-proof serialization.
- **Tier-D = the executor in postgres** (the north star): run the verified executor in-backend. **Lever:** a
  pg/Lean process-model spike (can `libdregg_lean.a` link + run inside the postgres backend process?). **Held:**
  process-model-gated — the spike decides full-D vs a D-sidecar (`PG-DREGG.md` §13.1).
- The outbox drainer §11.4 is LANDED (`eaef6a214`, N8); the range-attest SRF shape + federation re-validation
  are BUILT (the pg-dregg wide-safe lane). What remains is S1-S3 + Tier-D above.

---

## G. The WholeChainProof recursion-proof SERDE (the shared unblock)

**What.** Serialize the whole-history recursion proof. `WholeChainProof.root` is an `Rc`-backed
`RecursionOutput` with NO serde, so anything that ships a fetched/stored whole-history proof is placeholdered
behind a versioned envelope.

**Closure lever.** Fork-side serialization in the **plonky3-recursion fork** (the same follow-up
`circuit/src/ivc_turn_chain.rs` already names) — add the derives + a versioned envelope so a
`RecursionOutput` round-trips.

**Why held / why it matters.** It is the SHARED unblock for **(1)** the web over-wire byte-verify (N13's
fetched-proof-verified-in-tab seam — `docs/design-frontiers/WEB-FORWARD.md`) and **(2)** pg-dregg proof-gate
S1 (item F). One fork-side serde fix releases both. Held because it lives in the fork (a separate workspace),
sequenced with the fork push the starbridge-v2 A2 swarm surface also waits on (`72ffc56` retarget + drop the
local `[patch]`).

---

## H. The browser-extension at-rest key encryption

**What.** Harden the MV3 browser-extension front door's key storage. The extension (`8a8ab52ba`) keeps the
key in `chrome.storage.local` for the demo; the PROVEN property is trusted-path mediation (the key never
reaches the page), NOT at-rest encryption.

**Closure lever.** The shape the sibling wasm cipherclerk already ships: BIP39 + PBKDF2 + AES-256-GCM +
auto-lock. → `sdk-ts/extension`.

**Why held.** The trusted-path property (the load-bearing security claim) is proven; at-rest encryption is the
production-hardening follow-on, not a demo blocker.

---

## I. The ADOS narration → effect compiler (R1 — the deeper join)

**What.** Build the tool-call → effect compiler (R1) for the ADOS narration-vs-truth panel. The panel
(`eeb5655f2`) correlates an agent's NARRATION against its TRUTH at the FEED level
(`Correlation::FeedLevelOnly`); claim-to-a-SPECIFIC-turn is the deeper join.

**Closure lever.** The R1 tool-call→effect compiler (`docs/design-frontiers/ADOS.md`): map each narrated
tool-call to the specific protocol effect(s) it claims to have caused, so a narration line binds to a receipt
hash. → starbridge-v2 + the R1 compiler.

**Why held.** The feed-level divergence panel ships now (the useful 80%); the per-turn compiler is the
research-deeper join, scheduled after the cockpit goes live (item D).

---

## J. The numbered standing backlog (filed, sequenced after the flip)

- **#170 quorum unification** — consumer migration: `BlsQuorumCert.lean` / `EpochReconfig.lean` still
  transcribe the historical `n−⌊n/3⌋` + carry `StrictBft`; `MembershipSafety.lean` still has the `n=0↦0`
  guard. The unified `supermajorityThreshold` Lean twin LANDED (`QuorumThreshold.lean`). **Lever:** migrate
  the consumers onto it (`bls_quorum_diff.rs` / `epoch_diff.rs` / `membership_safety_differential.rs` pin
  the relations until migration). Also the S5-3 quorum-consumer-migration leg.
- **#171 remote `.turn()`** — the pg-dregg outbox drainer (`§11.4`) is the first consumer: a node-side task
  drains `dregg.submit_queue` as `dregg_kernel`, runs the submit gates + `execute_via_producer`, resolves +
  mirrors back. **Lever:** the drainer landed (N8); generalize to a remote-`.turn()` ingress.
- **#155 census debts** — the residual census burn-down (the named-but-unscheduled items from the coherence
  census). **Lever:** schedule or demote-to-Research each, per WE-DO-NOT-NAME-WE-SHIP.
- **#150 non-revocation depth** — does the umem `absent` + sorted-gap boundary fully retire
  `DslRevocationTree` (TREE_DEPTH=4)? **Lever:** one read-pass at cutover (it rides the rotation — confirm
  the boundary subsumes the tree, then retire it). Also the Argus apex non-revocation-depth leg (#149/#150).

---

*Cross-refs: `REORIENT.md` (current state) · `HORIZONLOG.md` (fine-grained seam burn-down) ·
`docs/ROTATION-CUTOVER.md` §EXEC (the flip recipe) · `docs/ASSURANCE-CRITIQUE.md` §5 (the l4v roadmap) ·
`docs/PG-DREGG.md` (pg) · `docs/EMBEDDED-WEB-SURFACE.md` + `docs/DISTRIBUTED-SERVO.md` (Servo) ·
`docs/STARBRIDGE-V2.md` (the cockpit).*
