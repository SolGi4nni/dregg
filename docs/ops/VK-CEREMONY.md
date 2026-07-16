# VK-CEREMONY — the multi-party Groth16 trusted-setup ceremony (Track D freeze, highest stakes)

> # ⚠⚠⚠ DO NOT EXECUTE ANY STEP IN §4–§9 UNTIL BOTH GATES OPEN ⚠⚠⚠
>
> This runbook mints the **production settlement VK** that every light client, every
> on-chain verifier, and the frozen hex-KAT pin will trust forever. It is the least
> forgiving procedure in the repo: a mistake bakes toxic waste into the protocol, or
> wastes a multi-GB, multi-participant setup that cannot be quietly re-run.
>
> **GATE 1 — Track B FRI cutover must have landed.** The ceremony MUST operate on the
> **proven-120 `d=8` circuit** (`d=8, lb=6, q=36, pow=16, WRAP_LOG_CEIL=15` → λ=122.60,
> `docs/reference/FRI-CUTOVER-PLAN.md:3-4`), **never** the deployed `d=4` 57.98-bit
> calculator config (`docs/reference/REPRODUCIBLE-BUILD-AND-FREEZE.md:20-22,130-138`).
> Concretely: `FRI-CUTOVER-PLAN.md` **Phases 0–3 complete and gate G3 green** — a *real*
> `d=8` apex-shrink proof from `circuit-prove` verifies inside the gnark circuit
> (`FRI-CUTOVER-PLAN.md:220-223`). Run the ceremony at `d=4` and the frozen KAT pins the
> 57.98-bit config; the `d=8` cutover then throws that ceremony away and demands a second
> multi-GB setup, a second re-key, and a re-publish of the "frozen" genesis
> (`REPRODUCIBLE-BUILD-AND-FREEZE.md:136-138,257-258`). **This ceremony runs ONCE, at `d=8`.**
>
> **GATE 2 — ember's explicit go.** Every publish here is an irreversibly-public push
> (circuit commitment, per-contribution transcripts, final VK, the consumer flip).
> Deployment flips are **not lane-autonomous** (`REPRODUCIBLE-BUILD-AND-FREEZE.md:248,298`;
> `FRI-CUTOVER-PLAN.md:260`). This is a governance gate, not an engineering step.
>
> Until both gates open, the only executable content here is the **§3 rehearsal** (tooling
> dry-run on the current circuit, output **discarded**) and the §2 baseline reads. Each
> step below is labelled **[EXECUTABLE TODAY]** or **[PENDING: needs <X>]**. Do not narrate
> a pending step as if it runs.

---

## 0. What this is, and what it supersedes

This is Rung **D4** of `docs/reference/REPRODUCIBLE-BUILD-AND-FREEZE.md:223-248`, which is
identically **Phases 4–5** of `docs/reference/FRI-CUTOVER-PLAN.md:225-264`. The apex Groth16
VK and the FRI-cutover re-key are the **same artifact** — this runbook is the choreography
for producing it multi-party instead of single-party.

**It supersedes the single-party dev ceremony.** Today the deployed settlement VK comes from
a *known-toxic-waste* single-party setup:

- **gnark side:** `groth16LoadOrSetup` (`chain/gnark/groth16_cache.go:65-98`) runs bare
  `groth16.Setup(ccs)` (`:86`) — "whoever ran Setup … knows the toxic waste and can forge
  proofs for this VK" (`groth16_cache.go:18-25`). The cache **reuses that same waste** across
  runs by design (dev speed), and the file itself says "a real deployment needs an MPC
  ceremony, and its output would NOT live here" (`:24-25`).
- **on-chain identifier:** `docs/ops/DEPLOY-SOLANA-COSMOS-TESTNET.md:12-14,177-184` pins
  `vk_hash = dregg_solana_settlement::dev_ceremony_vk_hash() = keccak256("dregg-settlement-vk-dev-setup")
  = 0x18f57474785bdd93ff7feb573dfadff69516035997115f2854c93f0f31e1ff76` across EVM/Solana/
  Cosmos. That doc names this the standing caveat: "a production settlement needs the
  MPC-ceremony VK re-pinned at `Init`/`instantiate`" (`:434-437`).

After this ceremony, the `groth16.Setup` path is dead for production: the VK comes from the
transcript-verified MPC output, and the single-party cache holds only dev/rehearsal params.

---

## 1. Roles, artifacts, and the box topology

### 1.1 Participants (≥ 3 recommended; ≥ 1-honest is the trust floor)

Groth16 MPC is trustless iff **at least one contributor's randomness is unknown to the
adversary** AND the transcript is publicly verifiable (`REPRODUCIBLE-BUILD-AND-FREEZE.md:286-289`).
Each participant needs only: the published circuit commitment (§4), the previous participant's
transcript, a private entropy source, and the ceremony binary (§ pending). Participants do
**not** need the full source tree or a build box — they operate on serialized SRS blobs.

- **Coordinator** (ember or delegate): publishes the circuit commitment, sequences
  contributions, publishes each transcript, runs the final verifier, performs the pin cutover.
- **Contributors** (≥ 2 besides the coordinator, ideally geographically/organizationally
  disjoint): each runs exactly one `Contribute()` and publishes its transcript + attestation.
- **Public verifiers** (anyone): re-run §7 against the published transcripts.

### 1.2 The box topology — where each step runs (respect the two-tailnet split)

`deploy/README.md:17-36` — **there are TWO tailnets and they are not connected.** The edge
(`100.64.0.x`) and hbox (`skunk-emperor.ts.net`) **cannot reach each other**. `persvati` is the
only box on both. **NEVER** route any ceremony artifact through "the edge's Caddy over the
tailnet" — that path is *false at the network layer* (`deploy/README.md:34-37`).

| step | box | why |
|---|---|---|
| circuit compile + R1CS fingerprint (§4) | **hbox** under `swarm-build` | multi-million-R1CS compile; hbox is the build/prove box (`deploy/README.md:14`); `swarm-build` enforces `MemoryMax=96G` (a bare setup OOM'd + power-cycled the box) |
| Phase-1 / Phase-2 contributions (§5) | each **contributor's own box** | contribution is CPU + entropy, not a dregg build; serialized SRS moves as files |
| Groth16 setup memory peak (§5.3 extract) | **hbox** under `swarm-build` | ~15–25 GB estimated at `d=8` (`FRI-CUTOVER-PLAN.md:291`); the exact peak is measured at that plan's gate G1 (`:179-182`) |
| transcript publication + VK release (§6) | **public git remote / `gh release`** | same pattern as the Lean-seed publish (`REPRODUCIBLE-BUILD-AND-FREEZE.md:177-182`); the ONLY verified public path is a public remote or `tailscale funnel`, never gateway-over-tailnet (`deploy/games/RUNBOOK-FUNNEL.md:20-25`) |

### 1.3 The artifacts a ceremony produces / re-keys

| artifact | path (@ HEAD) | current value → after |
|---|---|---|
| gnark settlement VK | `chain/gnark/fixtures/settlement_groth16.vk` (written by `settlement_snark_test.go:113-123` via `vk.WriteRawTo`) | dev → MPC |
| Solidity verifier | `chain/contracts/DreggGroth16Verifier25.sol` (`settlement_snark_test.go:39,174` `vk.ExportSolidity`), `…Upgradeable.sol`, `chain/codegen/out/…vk.sol` | dev → MPC |
| apex VK pin (Rust) | `DREGG_APEX_RECURSION_VK` = `3ad1c9c6…5503` (`circuit-prove/src/apex_shrink_gnark_export.rs:216-217`) | re-derive |
| apex VK pin (Go mirror) | `DreggApexRecursionVk` = `3ad1c9c6…5503` (`chain/gnark/settlement_circuit.go:122`) | re-derive |
| apex identity fixture | `chain/gnark/fixtures/apex_vk_identity.json` (`FRI-CUTOVER-PLAN.md:125,233`) | regen |
| on-chain `vk_hash` | `keccak256("dregg-settlement-vk-dev-setup")` (`DEPLOY-SOLANA-COSMOS-TESTNET.md:180-184`) | keccak of MPC VK |
| recursion VK pin (KAT) | **none yet** — tautology (`recursive_witness_bundle.rs:180-186`, §6.1) | frozen hex constant |
| audit row | `docs/VK-REGEN-LOG.md` (append-only) | +1 row, `source dirty = no` |

---

## 2. Baseline reads — establish the "before" state  **[EXECUTABLE TODAY]**

Run before the ceremony to record what the ceremony will replace, and to confirm the teeth
that will guard the flip are armed *now* (so a green after the flip means something).

```bash
cd /Users/ember/dev/breadstuffs

# (a) The current dev VK identity + the pin it must satisfy. This exercises the
#     fail-closed tooth that will guard the re-key (check_apex_vk_identity_pin).
cargo test -p circuit-prove derive_deployed_apex_vk_identity_and_check_fixture -- --nocapture

# (b) The recursion-VK tautology as it stands today (the thing §6.1 kills):
#     lookup_recursive_vk accepts iff hash == compute_recursive_vk_hash().
sed -n '180,186p' circuit-prove/src/recursive_witness_bundle.rs

# (c) The RECURSION_P3_REV embedded id (":111") vs the real dep rev (Cargo.toml:236).
#     These are DECOUPLED today and must be reconciled in the same cutover edit (§6.1).
grep -n 'RECURSION_P3_REV' circuit-prove/src/recursive_witness_bundle.rs   # c14b5fc0…
grep -n 'plonky3-recursion' Cargo.toml                                     # rev 0a4a554

# (d) The append-only regen log the ceremony inherits (last row = the "before").
tail -3 docs/VK-REGEN-LOG.md
```

Record: the printed apex fingerprint (`3ad1c9c6…5503` today), the R1CS constraint count
if you also run §3, and the current `origin/main` HEAD.

---

## 3. Ceremony-tooling REHEARSAL (on the current circuit; output DISCARDED)  **[EXECUTABLE TODAY]**

**Purpose:** exercise the gnark MPC primitives end-to-end so the real run (§5) is not the
first time the tooling has been driven. **The output of this rehearsal is `d=4` (or whatever
is deployed) and MUST be thrown away — it is NEVER pinned, published, or copied into a
fixture.** This is a tooling test, not a ceremony.

The gnark MPC primitives are present in the pinned `github.com/consensys/gnark v0.11.0`
(`chain/gnark/go.mod:13`) at `backend/groth16/bn254/mpcsetup`:

- `InitPhase1(power int) Phase1` — fresh powers-of-tau of size `2^power` (universal,
  circuit-independent). `power = ceil(log2(paddedConstraintDomain))`; for ~12M R1CS,
  `power ≈ 24`.
- `(*Phase1).Contribute()` — one participant folds in private randomness.
- `VerifyPhase1(c0, c1 *Phase1, c ...*Phase1) error` — verify the phase-1 chain.
- `InitPhase2(r1cs *cs.R1CS, srs1 *Phase1) (Phase2, Phase2Evaluations)` — bind phase-1 to
  the compiled circuit.
- `(*Phase2).Contribute()`, `VerifyPhase2(c0, c1 *Phase2, c ...*Phase2) error`.
- `ExtractKeys(srs1 *Phase1, srs2 *Phase2, evals *Phase2Evaluations, nConstraints int) (pk, vk)`.
- `WriteTo`/`ReadFrom` on each phase for the serialized transcript blobs.

Get the circuit + its content-fingerprint (the same fingerprint that becomes the §4
commitment). This compiles the R1CS; it is heavy (skip-gated by `DREGG_SNARK`,
`settlement_snark_test.go:73-77`):

```bash
# ON hbox (build box), under swarm-build for the MemoryMax cgroup:
ssh hbox
cd ~/dev/breadstuffs/chain/gnark
# The end-to-end test compiles the SettlementCircuit to R1CS (settlement_snark_test.go:85)
# and logs "R1CS: N constraints …" (:91) plus the circuit fingerprint (groth16_cache.go:72).
DREGG_SNARK=1 swarm-build go test ./... -run TestSettlementGroth16EndToEnd -v \
  2>&1 | tee /tmp/rehearsal-compile.log | grep -E 'R1CS:|circuit fingerprint'
```

**[PENDING: needs the MPC driver written]** — the loop that calls `InitPhase1 → Contribute →
InitPhase2 → Contribute → VerifyPhase{1,2} → ExtractKeys` **does not exist in the tree**:
`chain/gnark` has no `cmd/`, no `main`, and no `mpcsetup` import — the only setup path is the
single-party `groth16LoadOrSetup` (`grep -rn mpcsetup chain/gnark` → nothing; only
`groth16_cache.go` and `settlement_snark_test.go` call setup). Before §3 can actually run the
MPC primitives, that driver + a `Makefile`/`go test` harness must be authored (see §10). Until
then, §3 rehearses only the **compile + fingerprint** legs; the contribute/verify/extract legs
are pending the driver.

---

## 4. Step 1 — publish the circuit commitment  **[PENDING: needs Gate 1 (d=8 circuit) + Gate 2 (ember go)]**

Every participant must sign over the **exact same circuit**. The commitment is the content
hash of the compiled constraint system — `groth16CircuitFingerprint` already computes exactly
this: `sha256(ccs.WriteTo(·))` (CBOR), 128-bit hex (`chain/gnark/groth16_cache.go:50-58`). It
is "stable for the same circuit + gnark version on any machine" (`groth16_cache.go:12-16`), so
any participant can independently recompute it from source and confirm the coordinator did not
substitute a weaker circuit.

Choreography:

1. Freeze the source at a **committed, pushed** rev (a fresh clone must reproduce it —
   `REPRODUCIBLE-BUILD-AND-FREEZE.md:88-90,161`). Record `git rev-parse HEAD`.
2. On hbox: compile the `d=8` SettlementCircuit, capture the R1CS fingerprint (§3 command,
   now at `d=8` because Gate 1 landed).
3. Publish `CEREMONY-COMMITMENT.md` to the public remote: the repo rev, the gnark version
   (`v0.11.0`), the `power` for Phase 1, `nbConstraints`, and the `sha256` circuit
   fingerprint. This is the object every contributor and every public verifier pins.

**Attestation:** the commitment file is the root of the transcript chain; its sha256 is the
`prev_hash` the first contribution references.

**Independent-recompute check (any participant):** clone at the published rev, run §3's
compile, confirm the printed fingerprint equals the published one. A mismatch = do not
contribute; the coordinator published a different circuit.

---

## 5. Step 2 — sequential ≥1-honest contributions  **[PENDING: needs the MPC driver + Gate 1/2]**

### 5.1 Phase 1 (universal powers-of-tau)

```
InitPhase1(power)  →  p1_0.srs        (coordinator; published)
  contributor A:  read p1_0 → Contribute() → p1_1.srs  + attestation_A
  contributor B:  read p1_1 → Contribute() → p1_2.srs  + attestation_B
  contributor C:  read p1_2 → Contribute() → p1_3.srs  + attestation_C
```

Each contributor, on their own box, in isolation:

```bash
# [PENDING driver] e.g. ./ceremony phase1 contribute --in p1_{n}.srs --out p1_{n+1}.srs
#   - reads the previous SRS (mpcsetup.Phase1.ReadFrom)
#   - draws private entropy (OS CSPRNG + optional dice/hardware; see 5.4)
#   - calls (*Phase1).Contribute()
#   - writes p1_{n+1}.srs (Phase1.WriteTo) and prints the contribution HASH ((*Phase1).hash())
```

**Per-step public attestation** (published immediately, before the next contributor starts):
`{ participant_id, prev_srs_sha256, new_srs_sha256, contribution_hash, timestamp, signature }`.
The signature is over the tuple; the `prev_srs_sha256` chains it to the previous step. A
contributor who never reveals their entropy and destroys it (§8) is the honest link.

### 5.2 Phase 2 (circuit-specific)

Bind the final Phase-1 SRS to the compiled circuit, then repeat the sequential contribution
pattern with `InitPhase2`/`(*Phase2).Contribute()`:

```
InitPhase2(r1cs, p1_final)  →  p2_0.srs, evals   (coordinator; evals published read-only)
  A: read p2_0 → Contribute() → p2_1  + attest
  B: read p2_1 → Contribute() → p2_2  + attest
  C: read p2_2 → Contribute() → p2_3  + attest
```

`evals` (`Phase2Evaluations`) is deterministic from `(r1cs, p1_final)` and carries no secret;
publish it so verifiers can run `ExtractKeys`.

### 5.3 Extract the keys (coordinator, on hbox under `swarm-build`)

```bash
# [PENDING driver] ExtractKeys(p1_final, p2_final, evals, nbConstraints) → (pk, vk)
#   Peak memory ~15–25 GB est. at d=8 (FRI-CUTOVER-PLAN.md:291); the exact figure is the
#   go/no-go measurement at that plan's gate G1 (FRI-CUTOVER-PLAN.md:179-182). If it exceeds
#   the swarm-build cgroup, STOP — do not run bare (that OOM'd + power-cycled the box).
```

The extracted `vk` replaces `fixtures/settlement_groth16.vk`; the `pk` is the ceremony proving
key (large; cached outside git per `groth16_cache.go` layout — but this is the *real* pk, not
a dev cache entry).

### 5.4 Entropy discipline (per contributor)

- Draw from the OS CSPRNG; optionally XOR in an independent physical source (dice, hardware
  RNG). Never a fixed seed, never a reused seed.
- Do the contribution on a box you control, ideally air-gapped for the contribution moment.
- Proceed to §8 (destroy) immediately after your one contribution.

### 5.5 The final beacon  **[PENDING: needs an audited beacon step]**

A public random beacon (e.g. a future Bitcoin block hash, or drand round) folded in as the
**last** contribution removes the "all contributors colluded" residual and makes the ceremony
publicly unbiasable. **Note (verify-the-limit):** the pinned `gnark v0.11.0` `mpcsetup`
package predates the reworked beacon API; before a *real* ceremony, confirm the pinned rev's
`mpcsetup` has no known soundness gap (audit the `phase1.go`/`phase2.go`/`setup.go` in the
module cache) or bump gnark and re-pin. This is a real gate, not a formality — do not run a
production ceremony on an un-audited setup implementation.

---

## 6. Step 3 — the pin cutover: kill the tautology, re-key the anchor  **[PENDING: needs the ceremony output]**

Do this from a **CLEAN tree** so the `VK-REGEN-LOG` row reads `source dirty = no`
(`REPRODUCIBLE-BUILD-AND-FREEZE.md:242,245`).

### 6.1 Kill the recursion self-recompute tautology (the hex-KAT pin)

Today `lookup_recursive_vk(hash)` returns `Some(())` iff `hash == &compute_recursive_vk_hash()`
(`circuit-prove/src/recursive_witness_bundle.rs:180-186`) — the "registry" recomputes the value
it checks against from the same inputs (`compute_recursive_vk_hash` at `:135`, derived from
`RECURSION_P3_REV` at `:111` + the verifier fingerprint). Nothing is pinned to an
externally-frozen ceremony output (`REPRODUCIBLE-BUILD-AND-FREEZE.md:94-106`).

Cutover:

1. Freeze the ceremony's recursion-VK hash as a **hex-KAT constant**, e.g.
   `const RECURSIVE_VK_KAT: [u8; 32] = <ceremony output>;`
2. Change `lookup_recursive_vk` to compare against that frozen constant instead of
   `compute_recursive_vk_hash()`:
   ```rust
   pub fn lookup_recursive_vk(hash: &[u8; 32]) -> Option<()> {
       if hash == &RECURSIVE_VK_KAT { Some(()) } else { None }
   }
   ```
   Keep `compute_recursive_vk_hash()` as a *derivation/self-check* used at pin-derivation
   time, not on the accept path — so a producer that recomputes a *different* hash is now
   **rejected** (the tautology's whole failure mode).
3. **Reconcile `RECURSION_P3_REV`** (`recursive_witness_bundle.rs:111`, `c14b5fc0…`) with the
   real dep rev (`Cargo.toml:236`, `0a4a554`) in the *same* edit — they are decoupled today
   (`REPRODUCIBLE-BUILD-AND-FREEZE.md:99-101`).

### 6.2 Re-key the apex VK anchor pair (one commit)

Per `FRI-CUTOVER-PLAN.md:229-236`:

```bash
# derive the new fingerprint from the ceremony VK object:
cargo test -p circuit-prove derive_deployed_apex_vk_identity_and_check_fixture -- --nocapture
```

Then, in ONE commit, update all four to the new fingerprint:

- `DREGG_APEX_RECURSION_VK` (`circuit-prove/src/apex_shrink_gnark_export.rs:216-217`)
- `DreggApexRecursionVk` (`chain/gnark/settlement_circuit.go:122`)
- `chain/gnark/fixtures/apex_vk_identity.json`
- regenerate `DreggGroth16Verifier25.sol` / `…Upgradeable.sol` / `codegen/out/…vk.sol` and
  `fixtures/settlement_groth16.vk` (via the `DREGG_SNARK=1` export path, now consuming the
  ceremony `vk` not a fresh `groth16.Setup`).

Also re-pin the on-chain `vk_hash` (`DEPLOY-SOLANA-COSMOS-TESTNET.md:177-184`) from
`keccak256("dregg-settlement-vk-dev-setup")` to `keccak256(<ceremony VK bytes>)` at
`InitSettlement`/`instantiate`.

**Negative check (both directions fail-closed):** `check_apex_vk_identity_pin`
(`apex_shrink_gnark_export.rs:224`) / `loadApexVkIdentity` (Go) must now **REJECT the old
artifact**, and `lookup_recursive_vk` must **reject a recomputed-but-different hash** — that
rejection is the proof the tautology is gone (`REPRODUCIBLE-BUILD-AND-FREEZE.md:246-247`;
`FRI-CUTOVER-PLAN.md:234-236,262-264`).

---

## 7. Step 4 — the PUBLIC transcript verifier (anyone can run)  **[PENDING: needs the driver + published transcripts]**

The ceremony is trustless only if a third party can confirm the final key derives from the
full contribution chain (`REPRODUCIBLE-BUILD-AND-FREEZE.md:286-289`). Publish a
`verify-ceremony` procedure that takes ONLY public artifacts — the commitment (§4), every
`p1_*`/`p2_*` SRS, every attestation, and `evals` — and checks:

1. **Circuit binding:** recompile the circuit at the published rev; its
   `groth16CircuitFingerprint` equals the §4 commitment. (The verifier is bound to the *same*
   circuit the VK was made for.)
2. **Phase-1 chain:** `VerifyPhase1(p1_0, p1_1, p1_2, …)` returns nil — each step is a valid
   contribution over its predecessor.
3. **Phase-2 chain:** `VerifyPhase2(p2_0, p2_1, p2_2, …)` returns nil.
4. **Attestation chain:** each attestation's `prev_srs_sha256` matches the prior published SRS,
   each signature verifies, contribution hashes match `(*PhaseN).hash()`.
5. **Key derivation:** `ExtractKeys(p1_final, p2_final, evals, nbConstraints)` reproduces the
   published `fixtures/settlement_groth16.vk` **byte-for-byte**, and its keccak equals the
   pinned on-chain `vk_hash`, and its fingerprint equals the re-keyed `DREGG_APEX_RECURSION_VK`.
6. **Beacon (if used, §5.5):** the final contribution's entropy equals the published beacon
   value.

If any check fails → **the ceremony is re-run** (`REPRODUCIBLE-BUILD-AND-FREEZE.md:288`). A
public verifier who cannot reproduce the VK from the chain must treat the VK as untrusted.

Publish the verifier as a standalone binary + a `README` so it runs from the public artifacts
alone (no dregg source-tree secrets). Distribution: public git remote / `gh release`, per §1.2
— **never** gateway-over-tailnet.

---

## 8. Toxic-waste destruction + no-reuse discipline  **[PENDING: per-contributor, during §5]**

- **Each contributor destroys their entropy immediately after their one `Contribute()`** —
  the private randomness never leaves the contribution box and is wiped (memory zeroed;
  air-gapped box powered off; no seed written to disk). The ≥1-honest guarantee is exactly
  "at least one contributor actually did this."
- **No reuse across ceremonies.** The dev single-party cache (`.groth16-cache/`,
  `groth16_cache.go:27-31`, gitignored) deliberately *reuses* toxic waste for dev speed
  (`:18-24`) — the production ceremony pk/vk **must not** be written into that cache, and a
  second ceremony (e.g. a future circuit change) starts from a **fresh** Phase-1, never
  re-using this ceremony's SRS.
- **The old dev VK is retired, not deleted** (`FRI-CUTOVER-PLAN.md:300-303`): the single-party
  `settlement_groth16.vk` and its Solidity verifier stay in tree at their old revision so the
  old fixtures still pass their old tests — but no production consumer points at them after
  §6/§9. Keep the `d=4`/dev cache entry until the new VK has soaked on devnet
  (`FRI-CUTOVER-PLAN.md:312-313`).

---

## 9. Step 5 — apex re-verify, VK-REGEN-LOG row, and the flip  **[PENDING: needs Gate 2 (ember go)]**

### 9.1 Full-chain re-verify at the target config

Per `FRI-CUTOVER-PLAN.md:252-258` (gate G5): leaf prove → rotated aggregation → apex fold →
apex shrink → gnark wrap → Groth16 verify → Solidity verify, on **real** artifacts at
`d=8, WRAP_LOG_CEIL=15`, including the depth-invariance test at the new ceiling
(`circuit-prove/tests/accumulator.rs` `wrapped_running_vk_is_constant_across_depth`,
`FRI-CUTOVER-PLAN.md:139-141`).

### 9.2 Append the VK-REGEN-LOG row (Control 3)

Inherit the existing regen discipline (`docs/VK-REGEN-CONTROLS.md`). The ceremony re-key goes
through `scripts/emit_descriptors.py` so it **appends** the row (`FRI-CUTOVER-PLAN.md:237-245`).
Ack-gate it: `DREGG_VK_REGEN_ACK="$(git rev-parse HEAD:metatheory/Dregg2)"`
(`VK-REGEN-CONTROLS.md:70-79,117`). Row format (append-only; git history is the tamper-evidence
— never edit prior rows, `docs/VK-REGEN-LOG.md:1-5`):

```
| <when UTC> | <operator>@<host> | emit\|stamp-existing | <HEAD:metatheory/Dregg2> | <repo HEAD> | no | <changed files> |
```

`source dirty` **must** read `no` — do the flip from a clean tree (`FRI-CUTOVER-PLAN.md:245`;
`REPRODUCIBLE-BUILD-AND-FREEZE.md:242`). Then verify the stamp:
`python3 scripts/emit_descriptors.py --verify-provenance --strict` (`VK-REGEN-CONTROLS.md:49-52`).

### 9.3 Control-4 differential (if descriptor shapes moved)

Leaf AIR descriptor **shapes do not change with the FRI degree** (`FRI-CUTOVER-PLAN.md:237-238,
4.3`), so this re-key is `stamp-existing` unless a diff proves otherwise. If a descriptor did
move, run the Control-4 differential (`VK-REGEN-CONTROLS.md:92-112`) — member-for-member,
name-stable, no-narrowing — and a dropped-member canary must red it.

### 9.4 The flip (ONE commit, ember-gated)

Re-point deployed consumers — node config VK hash, contract address/upgrade, light-client pins
(`FRI-CUTOVER-PLAN.md:259-261`) — in one commit. **Gate G5:** an end-to-end turn on the devnet
path settles under the new VK, and the **old-VK proof is rejected** by the new verifier and
vice versa (`FRI-CUTOVER-PLAN.md:262-264`). The devnet path needs a persistent node
(`REPRODUCIBLE-BUILD-AND-FREEZE.md:262-263`; the hbox devnet ledger was lost once to a hard
kill — `deploy/games/RUNBOOK-FUNNEL.md:11-25`, so the replacement node must be a systemd user
unit with a persistent `--data-dir`, not hand-run). **ember-gated.**

---

## 10. Rollback  **[EXECUTABLE anytime a flip has landed]**

Follows `FRI-CUTOVER-PLAN.md:296-313`:

1. **A bad contribution (during §5):** the transcript verifier (§7) rejects it → discard from
   that step, the offending contributor re-contributes (or is dropped) and the chain continues
   from the last good SRS. Nothing public is trusted until §7 passes end-to-end, so a bad
   contribution never reaches a consumer.
2. **A bad flip (after §9.4):** every step is a normal commit on `main` and every artifact is
   regenerable, so rollback is `git revert` of the flip commit (`FRI-CUTOVER-PLAN.md:297-301`).
   The **old VK is never deleted** (§8) — reverting the one flip commit re-points consumers at
   the still-in-tree old VK, which still passes its old tests at that revision.
3. **VK-REGEN-LOG is append-only:** a rollback **appends** a new row (the reverting regen); it
   never edits or removes the ceremony's row (`FRI-CUTOVER-PLAN.md:304-306`). The log records
   the round-trip.
4. **Ceremony re-run:** if §7 fails on the *final* artifacts, the entire ceremony re-runs from
   a fresh Phase-1 (§5) — you cannot patch a broken contribution chain, and you never reuse the
   SRS of a failed ceremony (§8).

---

## 11. Executable-today vs pending — the honest ledger

| step | status | blocking gate |
|---|---|---|
| §2 baseline reads (apex fingerprint, tautology, log tail) | **EXECUTABLE TODAY** | — |
| §3 rehearsal — compile + circuit fingerprint | **EXECUTABLE TODAY** (heavy; hbox + `swarm-build` + `DREGG_SNARK=1`) | — |
| §3 rehearsal — Init/Contribute/Verify/Extract primitives | **PENDING** | the MPC driver (no `cmd/`, no `mpcsetup` import exists in `chain/gnark`) |
| §4 circuit commitment publication | **PENDING** | Gate 1 (`d=8` circuit, FRI G3) + Gate 2 (ember go) |
| §5 sequential contributions + attestations | **PENDING** | MPC driver + Gate 1 + Gate 2 |
| §5.5 final beacon | **PENDING** | audit/upgrade of pinned `gnark v0.11.0` `mpcsetup` |
| §6 hex-KAT pin + apex re-key | **PENDING** | ceremony output (needs §5 done) |
| §7 public transcript verifier | **PENDING** | driver + published transcripts |
| §8 toxic-waste destruction | **PENDING** | runs *inside* §5 |
| §9 apex re-verify + log row + flip | **PENDING** | Gate 2 (ember go) + persistent devnet node |
| §10 rollback | **EXECUTABLE** once a flip exists | — |

**The one thing to internalize:** the ceremony **cannot** be executed today, and not only for
the governance gate — the MPC driver code (§3/§5/§7: coordinator + participant + transcript-
verifier, wiring gnark's `mpcsetup` → `settlement_groth16.vk` → `ExportSolidity`) **does not
exist yet**; `chain/gnark` today has only the single-party `groth16LoadOrSetup`. Writing that
driver + audited beacon is the engineering prerequisite that sits *between* Track B's `d=8`
cutover and this ceremony. Do not narrate §4–§9 as runnable until that driver lands AND both
gates open.

## Provenance

| claim | source (file:line @ HEAD) |
|---|---|
| ceremony = Rung D4 = FRI Phases 4–5, pins `d=8` not `d=4` | `REPRODUCIBLE-BUILD-AND-FREEZE.md:19-22,130-138,223-248`; `FRI-CUTOVER-PLAN.md:225-264` |
| Gate 1 = FRI G3 (real `d=8` proof verifies in gnark) | `FRI-CUTOVER-PLAN.md:220-223` |
| current setup single-party, toxic waste known + cached | `chain/gnark/groth16_cache.go:18-25,83-98` |
| on-chain dev vk_hash = keccak("dregg-settlement-vk-dev-setup") | `docs/ops/DEPLOY-SOLANA-COSMOS-TESTNET.md:12-14,177-184,434-437` |
| recursion VK self-recompute tautology | `circuit-prove/src/recursive_witness_bundle.rs:111,135,180-186` |
| apex VK pin pair (`3ad1c9c6…5503`) + fail-closed teeth | `apex_shrink_gnark_export.rs:216-224`; `chain/gnark/settlement_circuit.go:122` |
| circuit fingerprint = sha256(ccs.WriteTo) 128-bit | `chain/gnark/groth16_cache.go:50-58` |
| gnark MPC API present (v0.11.0 `mpcsetup`) | `chain/gnark/go.mod:13`; `…/gnark@v0.11.0/backend/groth16/bn254/mpcsetup/{phase1,phase2,setup}.go` |
| NO MPC driver in tree (only single-party path) | `grep -rn mpcsetup chain/gnark` → none; `groth16_cache.go`, `settlement_snark_test.go` only |
| VK export + Solidity paths | `settlement_snark_test.go:39,41,113-123,174` |
| regen discipline: ack-gate, provenance, append-only log, Control-4 | `docs/VK-REGEN-CONTROLS.md:40-112,117`; `docs/VK-REGEN-LOG.md:1-5` |
| two-tailnet split — edge ⟂ hbox; funnel is the only public path | `deploy/README.md:17-37`; `deploy/games/RUNBOOK-FUNNEL.md:20-25` |
| setup peak ~15–25 GB est., G1 measures it; `swarm-build` | `FRI-CUTOVER-PLAN.md:179-182,291`; `deploy/README.md:14` |
| rollback: old VK retired-not-deleted, log append-only | `FRI-CUTOVER-PLAN.md:296-313` |
