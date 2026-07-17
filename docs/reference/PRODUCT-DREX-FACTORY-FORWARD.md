# PRODUCT-DREX-FACTORY-FORWARD — DrEX terminal + AI-token-factory: state + forward plan

**What this is.** An honest, file:line-cited state assessment of the two app-layer product
surfaces — the **DrEX terminal** (the trading/viewing interface) and the **AI-token-factory**
(spec → proven-safe token → gate) — plus a prioritized forward-moves plan toward shippable
surfaces. Written as a parallel product lane while the main thread works FRI soundness. It does
**not** touch soundness/kernel, and it proposes **no deploys**.

**Bar (from the launch-readiness memory):** shippable = off-laptop, reproducible, not "green on
ember's laptop." That bar is the lens for every "wound" below.

**Companion surfaces (not re-assessed here):** `launchpad-web/` (the factory's downstream deploy
target — a real node-driven / EVM-contract-driven launch UI); `deploy/node/dregg-node.service`
(the durable solo devnet node both DrEX and launchpad settle on).

---

## Part 1 — DrEX terminal (the trading surface)

Two web frontends over a **real** matching/clearing engine and STARK provers:

- **`drex-web/`** (`:8781`) — the feature-complete "live" demo. Real endpoints, real settle.
- **`drex-web-v2/`** (`:8782`) — a cleaner Preact rebuild **seed** (Phase-1 Open-tier only).

### 1a. What is REAL

**The engine wiring is genuine — endpoints shell out to real compiled Rust bins, with honest
"not built" fallbacks (no mock-as-real in the happy path).**

- `drex-web/serve.mjs:330-348` `runClear` spawns the **real** `drex_clear` matcher
  (`intent/src/bin/drex_clear.rs`, 16 KB of real solver→verified_settle). Local-first
  (`serve.mjs:317-327`), else ssh to the prebuilt binary on `persvati`.
- `drex-web/serve.mjs:365-389` `runShieldedClear` spawns the **real** `fhegg_clear`
  (`fhegg-solver/src/bin/fhegg_clear.rs`); returns an honest "not built — run: cargo build …"
  error if absent (`serve.mjs:368-372`) rather than faking a result.
- `drex-web/serve.mjs:408-432` `runCertFProve` spawns the **real** reveal-nothing STARK
  (`circuit-prove/src/bin/cert_f_prove.rs`); same honest not-built fallback.
- `drex-web/serve.mjs:484-535` `/prove-shielded` is a genuinely-structured privacy boundary:
  the solver cert (holding `f/π/s`) stays server-side (`:497`), the browser response is built
  **only** from world-visible scalars (`:506-531`) — the redaction is structural (it explicitly
  does not spread `cleared`), not cosmetic. Honest residuals named inline (`:527-530`:
  input-privacy note-commitment matching + the HidingFriPcs ZK floor).

**The settle path is genuinely real — cleared batches land as real turns on a live node.**

- `drex-web/serve.mjs:139-299` `settleOnNode`: unlocks a node (`:106`), faucets destination
  cells (`:198`), builds **per-trader Transfer effects** off the verified post-ledger
  (`:168-205`), submits a real turn (`:221-225`), polls for the async STARK proof + committed
  receipt (`:242-264`), and reads each trader's balance **back from the node** (`:270-278`).
  This is faithful per-trader value delivery, not a lump pool-move.
- The **Transfer-not-SetField** choice is investigated + documented (`serve.mjs:154-167`):
  per-trader `SetField` **commits but is unattested at the deployed VK** (rotated proof verifies
  under all 8 cohort descriptors → SDK uniqueness gate rejects). Fixing it is a VK-epoch flip,
  which is **ember-gated** and correctly not fired here. This is a labeled inadequacy, not a fake.

**v2 is a disciplined seed.** `drex-web-v2/src/api.js` has one source-of-truth `endpoints` map
with honest `live:` flags; `src/app.js:148,158,176` renders `!live` controls as explicit
`PREVIEW — not live with real money` with deploy-deps. Build is clean (esbuild → `dist/app.js`).
The wallet is extension-central (`window.dregg` = identity + signer; nothing signed in page).

### 1b. WOUNDS (mock-where-real-needed / green-on-the-laptop)

1. **Nothing is deployed or running.** No process on `:8420`/`:8781` (verified: `lsof` empty).
   Every surface requires standing up a **local** dregg node + a **build host** (`persvati`) for
   the un-built matcher bins (locally only `fhegg-solver/target/release/fhegg_clear` exists;
   `drex_clear` and `cert_f_prove` are **not built** → `/clear` ssh's off-box, `/prove-shielded`
   returns "not built"). This is the core "green on the laptop" reality.

2. **The durable node exists but is not installed.** `deploy/node/dregg-node.service` closes the
   "ledger-lost-on-reboot" gap (persistent `--data-dir`, `enable-linger`, idempotent genesis) —
   but it is a solo committee-of-one, loopback-only, requires the **Lean-linked node built on
   hbox** (linux/amd64), and is not running. Installing it is an ember-gated deploy.

3. **v2 flag inconsistency (FIXED, see Part 3).** `drex-web-v2/src/api.js` marked
   `clearShielded`/`proveShielded` as `live:true`, but v2's `serve.mjs` serves only `/clear`,
   `/settle`, `/node/status` (`serve.mjs:141,145,149`) — contradicting the map's own stated
   invariant ("`live` reflects what serve.mjs actually serves TODAY"). Corrected to `live:false`.

4. **Two frontends, no cutover.** v1 (`:8781`) is the feature-complete one; v2 (`:8782`) is a
   Phase-1-only seed (Open-tier ring clear + solo settle; no shielded routes on its server yet).
   v2 has not superseded v1 — a fork risk (two divergent surfaces to maintain).

5. **Input privacy is still revealed-orders.** `/prove-shielded` hides the OUTPUT flows, but the
   INPUT is still revealed orders; matching over hidden note commitments (the shielded pool) is a
   named lane (`serve.mjs:528`), not built into the click path.

### 1c. DrEX frontier (most-blocking gap)

**No hosted, public, durable end-to-end surface.** Today a stranger cannot complete a trade:
the matcher needs a build host, the node is a hand-run local instance with no durable data, and
there is no public signed-data RPC or deployed contract. The single highest-leverage unblock is
**standing up the durable node + hosting one frontend behind the existing tailscale-funnel
pattern** (the games/launchpad units already demonstrate reboot-surviving funnels) — an
ember-gated deploy, but the artifacts exist.

---

## Part 2 — AI-token-factory (spec → proven-safe token → gate)

Three tools in `tools/`: `token-factory/` (orchestrator), `dregg-audit/` (9-door + Halmos), and
`deployer-gate/` (macaroon capability gate + Opus-interview + on-chain gate).

### 2a. What is REAL

- **The pipeline genuinely runs** (no faked/cached verdicts). `token-factory:98` shells
  `emit_token.py`; `:110` shells the real `dregg-audit`; `:114-115` reads the **freshly written**
  report and parses machine verdicts (`parse_audit_report`, `:60-73`). The GATE is real and
  strict (`:119-124`: `fv_proven ∧ ¬counterexample ∧ ¬dangerous_door ∧ latch_detected`).
- **Both polarities demonstrably ran with real Halmos** (refreshed 2026-07-17 on the
  derived emit + 4 invariant families): `artifacts/GOOD/GOOD.halmos.log` = "5 passed;
  0 failed"; `artifacts/RMOON/RMOON.halmos.log` = "3 passed; 2 failed" with concrete
  symbolic INV-CAP counterexamples. "Proven-safe or caught" holds end-to-end on these runs.
- **Stage A (9-door grep) is real deterministic forensics** (`dregg-audit:102-130`, one ERE per
  door, comment-filtered). **Stage B (Halmos) is real** (`dregg-audit:186` invokes
  `uvx --from halmos halmos`, maps each `[PASS]/[FAIL]` to a door).
- **The emitted "safe" contract is a genuine cap-safe token** — `constant cap` literal, one-shot
  mint latch, no owner/seize/pause/blacklist/selfdestruct/proxy/fee door (verified
  `artifacts/GOOD/GOOD.sol:31,52`). Halmos proves the cap over its real bytecode.
- **deployer-gate's macaroon gate is real** — composes the real `dregg_macaroon` crate
  (`Cargo.toml:15`), mints an HMAC-chained capability with 3 caveats (`lib.rs:367-370`), verifies
  the chain + clears caveats against a live snapshot (`lib.rs:394-400`), fails-closed on unknown
  caveats (`lib.rs:431-437`). **14 substantive tests** (`tools/deployer-gate/tests/gate_poc.rs`) cover all arms +
  forgery/wrong-operator/slash-after-issue/expiry/scope/revocation.
- **The AI front is honestly a structured spec-builder, no LLM** (`emit_token.py:24-27,252-263`;
  no HTTP client anywhere). This is the explicitly-named wire-later — honest, not a wound.

### 2b. WOUNDS (mock-where-real-needed / overclaims)

1. **"Parameterizes the FV'd template" — was an overstatement; FIXED (2026-07-17, code
   reconciled).** The old `emit_safe` emitted a hardcoded inline f-string and never read
   `chain/contracts/launchpad/DreggLaunchToken.sol` — a separate, hand-maintained cap-safe
   reimplementation in the same shape. Now `emit_safe` **reads the FV'd template at emit
   time** and derives the contract by exactly five **count-checked substitutions**
   (`emit_token.py: safe_substitutions`); every function body (the one-shot `mint` latch +
   the ERC-20 surface) is carried **byte-for-byte** and re-verified on every emit
   (`verify_derivation`), and a template whose anchors drift makes the emit **fail loudly**.
   Tested: `test_emit_token.py` (byte-identity per pedigree function, the drift tooth, the
   divergence tooth — 10 tests). "Proven-safe carries the FV pedigree" is now true both
   ways: provenance by derivation, plus Halmos still proving the emitted contract's own
   bytecode downstream.

2. **Safe/unsafe determination is a 2-point whitelist.** `emit_token.py:266` — a single string
   equality: `mint_authority == "launchpad-oneshot"` → safe; **everything else** → one hardcoded
   unsafe variant (`:268-269`). "A rug-y spec is caught" is proven over a 2-element input space,
   not general specs.

3. **"5 of 9 doors proven" was NOT supported by code — evidence now committed at the honest
   3/9 (2026-07-17).** `gen_fv_harness.py` generates harnesses for **3 of the 9 taxonomy
   doors** — INV-CAP (#2), INV-NODRAIN (#8), INV-ACCESS-CONTROL (#1) — plus INV-REENTRANCY
   (outside the taxonomy). The other 6 doors (#3 proxy, #4 selfdestruct, #5 honeypot,
   #6 blacklist, #7 pause, #9 fee) remain **grep-only, no proof** (now stated in both
   READMEs; extending harnesses is P6). The evidence gap is CLOSED: committed `.halmos.log`
   runs now cover all four invariant families in both polarities — GOOD 5/5 PASS on the
   derived contract; RMOON INV-CAP 2× COUNTEREXAMPLE (+3 honest PASS); MoonRugToken
   INV-CAP 2× + **INV-NODRAIN COUNTEREXAMPLE** (the owner-drain door disproven by proof);
   UnguardedMintToken (new committed sample run) INV-CAP PASS + **INV-ACCESS-CONTROL
   COUNTEREXAMPLE** — the two-invariants-two-doors contrast case. (INV-REENTRANCY has
   PASS-only evidence; its FAIL polarity lives in the hand-written
   `chain/formal-verification/test/DreggReentrancyFV.t.sol`.)

4. **The Opus "interview" is not live — now LABELED honestly (2026-07-17); wiring it is P7.**
   `deployer-gate/src/interview.rs` is a **text parser only** (`InterviewVerdict::parse`) —
   no Anthropic client, no HTTP. The "two real runs" are **frozen static transcripts**
   (`interview/runs/verdict-{legit,rug}.txt`) of real Opus-4.8 output produced **once,
   offline**; the automated gate replays them forever, and the zkTLS/DECO attestation is
   doc-and-type-shape only. The overclaim is corrected in place: `interview.rs` carries an
   "Honest scope: the transcripts are FROZEN — the interview arm is not live" module note,
   the README's "Real (this PoC)" list now says "captured once, offline" with a dedicated
   honest-scope paragraph, and `lib.rs`'s marquee bullet points at both. What runs today is
   the parser + captured evidence; the live per-applicant interview remains the named
   wire-later (ember-gated on provider choice).

5. **Door-number label bug (FIXED, see Part 3).** `gen_fv_harness.py` labeled owner-drain/seize as
   "door #5" in 4 comments; the DOORS array has it as **#8** (honeypot is #5). Cosmetic; the
   orchestrator's `inv_label` was already correct. Fixed.

### 2c. Factory frontier (most-blocking gap)

**Was: three disconnected PoCs. Now (2026-07-17): ONE wired flow, deploy still deliberately
absent.** The audit-report-hash → gate `audit_registry` wire is BUILT: `token-factory`'s
GATE-WIRE stage shells the new `deploy-gate` CLI (`tools/deployer-gate/src/bin/deploy-gate.rs`
— file-backed operator state over the real macaroon lib): a VERIFIED-SAFE report's sha256 is
registered, a real capability (Audit arm, launch-params-scoped, expiring) is **issued and
authorized**; a REJECTED token's unregistered hash is demonstrably **refused** (`NotGated`).
Both polarities recorded in the committed artifacts (GOOD/RMOON). Still open, correctly:
(a) an actual deploy execution — the artifact now carries the exact `forge create` +
`registerLaunch` invocation as a **proposed, ember-gated** step (the factory NEVER
deploys); (b) live interview automation (P7, labeled); (c) the file-backed PoC registry vs
the on-chain `audit_registry` (the landed `DreggLaunchpad` hook is the on-chain twin —
feeding it from the factory is the remaining seam).

---

## Part 3 — EXECUTED (safe, verified) this lane

Two clear-cut, self-contained, non-settlement/non-deploy fixes, both verified:

1. **`drex-web-v2/src/api.js`** — corrected `clearShielded`/`proveShielded` from `live:true` to
   `live:false` (they are wired in v1's `:8781` server but **not** served by v2's `serve.mjs`),
   restoring the map's own stated invariant. Rebuilt `dist/` (gitignored); `serve.mjs` `--check`
   passes.
2. **`tools/dregg-audit/gen_fv_harness.py`** — corrected 4 comment/docstring mislabels of
   owner-drain/seize from "door #5" to the correct "door #8" (honeypot is #5). Comment-only;
   `python3 -m ast` parses OK; no logic touched.

### Executed 2026-07-17 (the factory honesty-repair lane)

3. **P2 (code-reconciled):** `emit_safe` now genuinely derives from the FV'd
   `DreggLaunchToken.sol` — read at emit time, five count-checked substitutions, every
   function body byte-for-byte + `verify_derivation` on every emit + the drift tooth;
   10 tests in `test_emit_token.py`. README/docstrings updated to the (now true) claim.
4. **P4:** all four Halmos invariant families now have committed run evidence, both
   polarities across GOOD / RMOON / MoonRugToken / UnguardedMintToken (see Part 2b#3);
   `reports/UnguardedMintToken.{audit.md,halmos.log}` newly committed.
5. **P3 (off-chain leg):** GATE-WIRE stage + `deploy-gate` CLI — report-hash registry →
   real macaroon capability issued+authorized / refused NotGated; deploy invocation
   emitted as **proposed, ember-gated** (see Part 2c).
6. **Bug found+fixed by the wiring:** `token-factory`'s `parse_audit_report` matched the
   literal `"HALMOS FOUND A COUNTEREXAMPLE"` while the multi-invariant dregg-audit writes
   `"HALMOS FOUND <n> COUNTEREXAMPLE(S)"` — rejections cited the weaker "not proven"
   instead of the machine counterexample. Regex now matches both formats; RMOON's fresh
   artifact cites the counterexample again.
7. **Interview overclaim labeled** (Part 2b#4): honest-scope notes in `interview.rs`,
   `lib.rs`, and the deployer-gate README; live automation remains P7.

## Part 4 — PROPOSED (ranked; not executed — bigger / ember-gated / judgment / settlement-touching)

Ranked by leverage toward a shippable surface. Effort = rough; Risk = to soundness/settlement.

| # | Move | Why | Effort | Risk | Gate |
|---|------|-----|--------|------|------|
| P1 | **Stand up the durable node + host ONE DrEX frontend** behind the existing tailscale-funnel pattern | The #1 frontier: turns "green on my laptop" into a stranger-completable surface; artifacts (`deploy/node/dregg-node.service`, funnel units) already exist | M | Deploy — **ember-gated** | ember |
| P2 | ~~Reconcile the emit ↔ FV'd template divergence~~ **DONE 2026-07-17** — option (a) executed: `emit_safe` derives from the real `DreggLaunchToken.sol` (count-checked substitutions + byte-for-byte bodies + drift tooth + tests) | Closes the top factory overclaim; "proven-safe carries the FV pedigree" is now true | S–M | Low | done |
| P3 | ~~Wire token-factory → deployer-gate~~ **DONE (off-chain leg) 2026-07-17** — GATE-WIRE stage + `deploy-gate` CLI; remaining seam: feed the ON-CHAIN `audit_registry` (the landed `DreggLaunchpad` hook) | 3 PoCs → one pipeline; the audit is a real gate arm | M | Low (off-chain) | done (off-chain) |
| P4 | ~~Run + commit the 3 newer Halmos invariants~~ **DONE 2026-07-17** — committed PASS/FAIL evidence for all 4 families across GOOD/RMOON/MoonRugToken/UnguardedMintToken | Substantiates door coverage beyond INV-CAP | S | Low | done |
| P5 | **v1→v2 cutover plan** — port v1's shielded/prove/settle routes onto v2's server (or retire v2 seed) to kill the two-frontend fork | Removes divergent-surface maintenance risk; v2 is the cleaner base | M | Low (app-layer) | — |
| P6 | **Extend Halmos harnesses toward the remaining 6 grep-only doors** (proxy/selfdestruct/blacklist/pause/fee) | Moves "caught by proof" from 3/9 toward the full taxonomy | L | Low | — |
| P7 | **Live interview automation** — wire a real LLM call (grain-jail / hosted) behind the deployer-gate interview arm, replacing the frozen transcripts | Makes the marquee anti-scam arm a live gate, not a canned replay | M | Low (off-chain) | ember (LLM provider) |
| P8 | **Broaden the factory spec space** beyond the 2-point whitelist — real spec→variant mapping over more mint-authority / tokenomics shapes | "Rug-y spec caught" over a real input space, not 2 points | M | Low | — |

**Sequencing note.** P1 is the single unblock that most changes the product's posture (off-laptop);
it is ember-gated. P2/P3(off-chain)/P4 were executed 2026-07-17 (see Part 3) — P2 took the code
route (derivation), which proved landable in a day. The live factory frontier is now: P1 (deploy,
ember-gated), the on-chain `audit_registry` seam, P6 (harnesses toward the 6 grep-only doors),
P7 (live interview), P8 (spec space beyond the 2-point whitelist).
