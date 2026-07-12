# TEE attestation — the PRODUCER + the verify-rail JOIN — status (honest)

Makes an **enclave-attested session a light-client-checkable fact**: the produce side
(`dregg-tee-produce`, NEW) gets a vendor-signed quote out of an enclave with the
session commitment bound into it, and the rail join
(`AgentPlatform::verify_landed_tee_attested`) proves the LANDED attestation slot with
real vendor crypto instead of a byte-compare. The verify side
(`tee-verify/` + `cell/src/tee_attest.rs`) already existed; this wave gave it a
producer, a home for its host-side install (`deos-hermes/src/tee_fact.rs`), and the
join onto the landed-turn rail. Every leg below is stated with its honest status.

## The honest rung name

**Single-hardware-root execution-integrity.** Accepting a TEE fact proves: *the
binary measured as M ran inside a genuine enclave (signed to the CPU/cloud vendor's
attestation root) and bound exactly this finalized session commitment.* It is NOT
trustless (you trust the vendor root — AWS's Nitro root G1 here — plus side-channel
and TCB-recovery caveats), and it says NOTHING about the LLM output's *correctness*
(that remains R3's whole-history STARK leg). It is the one guarantee the
determinism-bound consensus quorum structurally cannot give a non-deterministic
agent loop, which is why it rides its own rail.

## The binding convention (fixed, in writing)

- **`report_data` = the exact 32-byte turn/session commitment** witnessed at
  `grain_turn::ATTESTATION_SLOT` (slot 8, compile-time-pinned in
  `agent-platform/src/node.rs`). The host computes the commitment it is about to
  bind (`drive_serving_attested`), sends it to the enclave as
  `QuoteRequest::report_data`, and the enclave binds EXACTLY those bytes (Nitro:
  the attestation document's `user_data`, required to be exactly 32 bytes by
  `tee-verify`). The verify rail refuses any quote whose `report_data` differs
  from the landed slot value — a quote proves ONE session, not "an enclave exists."
- **The measurement is pinned OUT OF BAND.** The verifier extracts
  `measurement = SHA-256(PCR0‖PCR1‖PCR2)` (Nitro) / the folded SNP launch
  measurement, and the predicate compares it against the caller-pinned expected
  binary. Distribution of the pinned measurement (enclave image reproducible
  build → PCRs) is the renter's out-of-band step, same as pinning a notary key.
- **Freshness rides IN `report_data`, not beside it.** A captured doc verifies
  crypto-forever by design (`NitroVerifier::without_freshness`); a live deployment
  gets freshness by making the bound commitment commit to a fresh nonce/session id,
  plus the optional wall-clock window (`NitroVerifier::new()`, default 1h).

## What EXISTS (all real, all green)

### 1. The verify side (pre-existing, now workspace-homed)

`tee-verify/` — `NitroVerifier` (CBOR/COSE_Sign1 parse, X.509 chain to the PINNED
embedded AWS Nitro root G1, ES384 COSE signature, PCR fold, `user_data` extraction)
and `SnpVerifier` (1184-byte SNP report parse, VCEK ← ASK ← pinned-ARK chain,
P-384 body signature, TCB floor; fail-closed with no pinned AMD roots). Verified
against the REAL captured document `tee-verify/tests/data/nitro_att.bin` — a live
us-east-1 c5.xlarge debug-enclave capture whose app bound `user_data = [0xAB; 32]`.
This crate WAS a detached zero-dependent workspace; it is now a root-workspace
member with three dependents (below), resolving under the one root lock.

### 2. The producer scaffold — `tee-produce/` (NEW crate, `dregg-tee-produce`)

- **Protocol:** `QuoteRequest { report_data: [u8; 32] }` /
  `QuoteResponse { document: Vec<u8> }` as one newline-delimited JSON frame per
  message (binary as hex), generic over `Read + Write` — vsock, TCP, or a pipe —
  mirroring grain-jail's `LineChannel` philosophy including the 1 MiB per-frame
  flood cap. Enclave side: `serve_quotes(reader, writer, &backend)` (per-request
  failures become `error` frames; the loop survives). Host side:
  `request_quote(&mut stream, report_data) -> Result<Vec<u8>, QuoteError>`.
- **`NitroNsmBackend`** (`nitro` feature): the REAL NSM `GetAttestationDoc` via the
  `/dev/nsm` ioctl driver (`aws-nitro-enclaves-nsm-api` 0.4, target-gated to unix),
  `user_data = report_data`. Anywhere but inside a running Nitro Enclave the device
  is absent and it returns `Err`. Compiles on this laptop (`--features nitro`);
  meaningful only in-enclave.
- **`FixtureBackend`** (`fixture-backend` feature): **NOT an attestation producer**
  — a transport/wiring test aid that replays the ONE real captured document, and
  REFUSES any request whose `report_data` is not the `[0xAB; 32]` that live
  enclave actually bound. It cannot attest anything; it can only replay the one
  session that really happened.
- **Honesty contract:** no code path fabricates a document. Every non-hardware
  path is either the labeled captured fixture or a fail-closed `Err`. There is no
  mock/self-signed backend on purpose.

### 3. The host-side install — `deos-hermes/src/tee_fact.rs` (NEW)

The TEE twin of `oracle_fact.rs`: `TeeFactVerifier` dispatches a quote's kind byte
to the real vendor path (`AwsNitro` → `NitroVerifier`; `SevSnp` → `SnpVerifier`,
fail-closed until AMD roots are pinned via `with_snp`; TDX/SGX → refused), and
`install_tee_fact_verifier(&mut registry, verifier)` wraps it in dregg-cell's
fail-closed `TeeWitnessedPredicateVerifier` and `register_custom`s it under
`tee_predicate_vk()`. Default build (unlike the `zk-live`-gated oracle seam) — the
deps are light (X.509/P-384/CBOR, no MPC-TLS).

### 4. The rail JOIN — `AgentPlatform::verify_landed_tee_attested` (NEW)

Rail A (`verify_landed_attested`, UNCHANGED) is a plain byte-compare of the landed
slot. The join runs `verify_landed` (light-client chain verify + manifest
membership), reads the commitment witnessed at `ATTESTATION_SLOT` off the
finalized ledger, then runs
`tee_attestation_predicate(pinned_measurement, ATTESTATION_SLOT)` through the
caller-supplied `WitnessedPredicateRegistry` against the kind-prefixed quote blob
(`encode_tee_proof`). So Rail B's crypto (genuine vendor signature + pinned
measurement + `report_data == landed slot`) now proves the landed binding; an
empty registry, a forged/tampered quote, a wrong binary, or an unbound
`report_data` are each `Err`.

### 5. Tests (all green, non-vacuous, fixture-driven)

- `tee-produce` unit (4): refusal-not-fabrication, malformed-frame answering,
  flood cut-off, client protocol teeth.
- `tee-produce/tests/fixture_loop.rs` (2, `--features fixture-backend`): the
  produce→transport→verify loop over a REAL TCP stream — the transported document
  passes the real COSE/chain verify AND the dregg predicate rail; a
  wrong-commitment request is refused server-side; a tampered transported byte is
  refused by the verifier.
- `deos-hermes` `tee_fact` (3): the installed registry accepts the real Nitro fact
  and refuses wrong-measurement / unbound-slot / tampered-byte; an uninstalled
  registry is `KindNotRegistered`; the SNP arm fails closed without pinned roots.
- `agent-platform`
  `landed_tee_attested_joins_the_real_nitro_quote_to_the_landed_slot`: bind
  `[0xAB; 32]` as the drive's attestation commitment (the SAME bytes the capture
  enclave bound), `drive_serving_attested` lands turns, then the join ACCEPTS with
  the fixture doc + true measurement, and REFUSES each of: wrong measurement,
  tampered document byte, a grain landed under a different commitment, and an
  empty (fail-closed) registry. Full `agent-platform` suite: 25/25.

## What is DEFERRED to hardware (NAMED, not faked)

- **The live NSM call**: running `serve_quotes(NitroNsmBackend)` INSIDE a real
  Nitro Enclave on an EC2 instance (vsock listener in the enclave image, host
  connects with `request_quote`). The code path exists behind `nitro`; only the
  hardware run is deferred.
- **The enclave image build/launch harness**: reproducible `nitro-cli
  build-enclave` (→ the pinned PCR measurement) + `run-enclave` + the vsock
  plumbing as a deploy script. This is what turns "measurement pinned out of band"
  from prose into an operator step.
- **The SNP whole-CVM path**: a live SEV-SNP guest's `/dev/sev-guest` report
  producer (the `tee-produce` protocol is vendor-agnostic; only a backend is
  missing) + pinning the real AMD ARK/ASK per product line in the installer.
- **Freshness in production**: binding a renter-chosen nonce into the committed
  session id so `report_data` freshness is end-to-end (the convention is fixed
  above; the wiring is a caller concern).

## Trust base

The AWS Nitro attestation root G1 (pinned, embedded, fingerprint-checked) and
ES384/X.509 (Nitro leg); the AMD ARK/ASK/VCEK chain + P-384 (SNP leg, when pinned);
BLAKE3/`register_custom` predicate routing on the dregg side; and the R2 landed-turn
rail underneath (the join adds to it, it does not replace it).

## Crates touched

- `tee-produce/` (NEW): protocol + backends + the fixture loop tests.
- `tee-verify/Cargo.toml`: dropped the detached `[workspace]` opt-out — now a
  root-workspace member (its deps were already in the root lock; the stale local
  `Cargo.lock` is ignored). Rationale: three members now depend on it, so it must
  resolve under the root `[patch]`/lock world, exactly the reason `oracle_fact`
  is homed in deos-hermes.
- Root `Cargo.toml`: `members += ["tee-verify", "tee-produce"]` (NOT
  default-members — the default dev loop is unchanged).
- `deos-hermes/`: `src/tee_fact.rs` (NEW) + the `pub mod tee_fact;` registration +
  `dregg-tee-verify` path dep (default build, light).
- `agent-platform/`: `verify_landed_tee_attested` + the end-to-end test in
  `src/lib.rs`; dev-dep `dregg-tee-verify` (the production method takes only
  dregg-cell's registry seam — vendor crypto is injected, never linked into the
  platform's own dep tree).

`cell/src/tee_attest.rs`, the slot rail (`grain-turn`, `node.rs`), and the
byte-compare `verify_landed_attested` are UNCHANGED. No Lean sources touched.
