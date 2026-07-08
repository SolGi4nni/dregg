# FROST MIGRATION — quorum certificates from BLS threshold to threshold Schnorr

The federation's quorum certificate moves from the weighted-threshold BLS aggregate
(`hints`: BLS12-381 pairing + KZG trusted setup + SNARK) to FROST (RFC 9591 threshold
Schnorr): a t-of-n certificate that IS one ordinary ed25519-shaped Schnorr signature,
verified by the single-signer verifier under the federation's GROUP public key. The Lean
spec is already proven: `metatheory/Dregg2/Crypto/Frost.lean`
(`frost_cert_verifies_under_group_key` — the Lagrange-combined partial responses form
exactly the group-key Schnorr response, so `z·g = R + e·pk` holds; `#assert_axioms`-clean),
with `ShamirPrivacy.lean` (sub-threshold subsets learn nothing), `ThresholdReduction.lean`
(threshold-EUF-CMA reduces to single-signer EUF-CMA), and `ThresholdForking.lean` (a forged
cert yields the group discrete log). What FROST buys: the QC rests on the DISCRETE-LOG
carrier the vote signatures already use (ed25519 — no new hardness assumption), sheds the
pairing AND the KZG trusted setup (the `hints` committee setup embeds toxic-waste risk and a
63-member ceiling), and the certificate becomes a plain 64-byte ed25519 signature any
verifier — including the wasm/verifier-PD/pg targets that today refuse BLS — checks with
the `ed25519-dalek` it already links.

This is the LIVE federation's consensus crypto: the sequence is STAGED-ADDITIVE-THEN-CUTOVER.
No stage removes or weakens the BLS path until the removal stage's gate is met.

## The BLS QC surface as found (census, 2026-07-07)

**Produce/verify core**
- `federation/src/threshold.rs` — `FederationCommittee` (hints `GlobalData` + `UniverseSetup`
  + threshold), `MemberSecret`, `ThresholdQC` (BLS aggregate + SNARK proof, arkworks-serialized).
  Sign: `sign_share` (:264) → `aggregate` (:272, `hints::sign_aggregate`). Verify:
  `FederationCommittee::verify` (:286) and `ThresholdQC::verify_with` (:341), both ending in
  `hints::verify_aggregate` (`hints/src/lib.rs`, the pairing + SNARK check).
- `hints/` (`dregg-hints`) — the vendored weighted-threshold BLS library: `ark-bls12-381`,
  `ark-poly-commit` KZG, the SNARK; trusted setup via random RNG or the Ethereum KZG ceremony
  (`new_with_eth_setup`, 63-member max).

**Embedding**
- `federation/src/types.rs:181` — `QuorumCertificate { aggregate_qc: Option<threshold::ThresholdQC>,
  votes: Vec<(usize, Signature)>, threshold }`: the consensus QC carries BOTH the Ed25519 vote
  set (`is_valid_with_keys` :202 / `verify_with_keys` :279, dedup-hardened) and the optional
  constant-size BLS aggregate (`verify_with_committee` :240). The BLS QC is an ACCELERATOR
  alongside an always-present Ed25519 quorum — this is what makes the migration tractable.
- `types/src/lib.rs:189` — opaque `ThresholdQC(pub Vec<u8>)`; carried in
  `AttestedRoot.threshold_qc: Option<ThresholdQC>` (:306) next to `quorum_signatures`.
- `wire/src/message.rs:208,237` — `AttestedRoot` / `AttestedRootPush` carry the opaque QC.
- `persist/src/federation.rs:46` — `StoredAttestedRoot.threshold_qc` (restart re-verification
  is over the Ed25519 quorum; :83 only notes presence).

**Sign path (consensus)**
- `federation/src/node.rs:691-705` — after vote collection reaches quorum, voters' BLS shares
  are aggregated and attached as `qc.aggregate_qc`; `update_attested_root` (:847) copies it
  into `AttestedRoot.threshold_qc` as opaque bytes.
- `federation/src/federation.rs:98` — `Federation.bls_committee: Option<Arc<FederationCommittee>>`;
  `sdk/src/hints_onboarding.rs` — the BLS onboarding/admission ceremony (`AdmissionQC.qc`).

**Verify path (consumers)**
- `federation/src/checkpoint.rs:144` `Checkpoint::verify_with_committee` (preferred BLS path).
- `federation/src/types.rs:333` `verify_attested_root_with_committee`.
- `dfa-federation/src/lib.rs:80` — route-table swap gated on a postcard-encoded `ThresholdQC`.
- `verifier/src/cross_fed.rs:460` — the cross-fed verifier REFUSES a threshold_qc-only root
  without Ed25519 quorum signatures (it has no BLS committee) — evidence the Ed25519 quorum is
  the load-bearing floor everywhere BLS can't reach.
- `starbridge-apps/governed-namespace`, `turn/src/executor/membership_verifier.rs:1182` (uses
  `hints` directly, not via federation), `federation/src/receipt.rs` (`ReceiptQc::Threshold`).

**Model/differential**
- `federation/src/bls_quorum_diff.rs` ⟺ `metatheory/Dregg2/Distributed/BlsQuorumCert.lean`
  (quorum-overlap combinatorics ABOVE the signature scheme — these theorems are
  scheme-agnostic and survive the migration verbatim; only the "accepting cert" carrier
  changes from `BlsThreshold` to `Frost`).

**Dependency footprint (what removal frees)**
- `federation/Cargo.toml:18` `hints`; `:31-34` `ark-serialize/ark-ff/ark-ec/ark-std`
  (ark-* in federation exist FOR the hints/BLS types and the G1-based `dkg.rs`).
- `hints/Cargo.toml` — the whole `ark-*` constellation incl. `ark-bls12-381`,
  `ark-poly-commit`, `ark-crypto-primitives`.
- Downstream `hints` edges: `turn`, `sdk`, `starbridge-apps/governed-namespace`,
  `starbridge-v2`, `dregg-tui`, `wasm`, `discord-bot`, `dregg-doc`, `sel4/dregg-firmament`
  (grep `hints` in Cargo.tomls). FROST verify needs only `ed25519-dalek` + `curve25519-dalek`
  + `sha2` — all already in the tree.

## Staged plan

### Stage 1 — ADDITIVE: FROST QC type + verify behind a selector  ✅ implemented
`federation/src/frost.rs` (this commit's working tree):
- `FrostQC` — one 64-byte `(R ‖ z)` signature; serde + `to_bytes`/`from_bytes`.
- `verify_frost_quorum(group_key: &PublicKey, message, qc)` — RFC 8032 `verify_strict`
  under the group key; this IS the Lean `SchnorrVerifies` relation (`z·B = R + e·A`,
  `e = SHA-512(R‖A‖M) mod ℓ`) and is byte-compatible with what a vetted
  `frost-ed25519` signing stack produces, so the verify side never changes again.
- `QuorumScheme::{Bls(&FederationCommittee), Frost{group_key}}` — the selector, dispatching
  over the EXISTING opaque `dregg_types::ThresholdQC(Vec<u8>)` bytes (`verify_opaque_qc`).
  Both schemes verify side by side; zero changes to `threshold.rs`, `QuorumCertificate`,
  the wire, or persist.
- `FrostTestDealer` + `frost_sign` — trusted-dealer Shamir + the Lean theorem's exact
  Lagrange algebra, for tests/fixtures/differentials (explicitly NOT the production signer:
  no RFC 9591 binding factors, dealer knows the secret — both documented at the seam).
- Tests: t-subset verifies (any subset), sub-threshold forgery fails, cross-scheme bytes
  rejected in both selector arms, FROST cert verifies as a PLAIN ed25519 signature via
  `dregg_types::PublicKey::verify`.

### Stage 2 — production signing + carriage
1. **Signing stack: adopt `frost-ed25519` (Zcash Foundation)** for nonce
   commitments/binding factors/partial-sig aggregation (see recommendation below).
   Mirror check: `~/crates.io/full` index has `frost-core` and `frost-ed25519` both at
   2.2.0 stable (3.0.0-rc.0 is the latest pre-release) — pin `frost-ed25519 = "2.2"`.
   (Mirror lags; re-check crates.io at pin time.)
2. `QuorumCertificate` gains `#[serde(default)] frost_qc: Option<frost::FrostQC>` alongside
   `aggregate_qc` (postcard/serde back-compatible for readers of old bytes; old readers of
   NEW bytes = the epoch gate below). `node.rs:691` attaches both while transitioning.
3. `AttestedRoot.threshold_qc` opaque bytes get a scheme tag (length already disambiguates —
   64 bytes = FROST — but tag explicitly at the `update_attested_root` seam).
4. Verifier call sites (`checkpoint.rs:144`, `types.rs:333`, `dfa-federation`,
   `hints_onboarding` admission) take `QuorumScheme` instead of `&FederationCommittee`.
   `verifier/src/cross_fed.rs` gains the Frost arm — a 32-byte group key is cheap to carry
   where a BLS committee context never could be, closing its "no BLS committee" refusal.

### Stage 3 — DKG for the group key
`federation/src/dkg.rs` is ALREADY a JF-DKG (Feldman commitments, complaints, QUAL) — but over
BLS12-381 G1 for the beacon committee. FROST needs the same protocol over edwards25519:
- Generalize `dkg.rs`'s Feldman round over the ed25519 group (commitments `C_ik = a_ik·B` as
  `EdwardsPoint`), or run `frost-core`'s built-in DKG (`frost_core::keys::dkg`, same
  Pedersen/Feldman shape) — recommendation: frost-core's DKG, so share format and key
  packages match the signing stack with no translation layer.
- `dkg_ceremony.rs` (signed round messages, sealed shares, common-view roots) is
  group-agnostic transport and carries the FROST ceremony UNCHANGED.
- Output: group `PublicKey` (32 bytes) pinned in `Federation` next to (eventually instead of)
  `bls_committee`; per-member share publics for partial-signature audit/slashing.
- Resharing (`ReshareDealing`) ports the same way — FROST supports proactive resharing of the
  same group key, so committee rotation does NOT rotate the group key unless desired.

### Stage 4 — cutover gate, flip, removal
1. **Both-schemes-valid soak**: nodes attach BOTH QCs (stage 2.2); every verifier accepts
   either; a differential test asserts FROST-verifies ⇔ BLS-verifies over live-shaped
   fixtures (TWO-GATES-PROVABLY-AGREE), plus the `bls_quorum_diff.rs` sibling
   `frost_quorum_diff.rs` re-grounding the Lean quorum-overlap model on the FROST carrier.
2. **Flip the default**: producers attach FROST-only; verifiers still accept both (one
   epoch's grace for in-flight roots and persisted `StoredAttestedRoot`s).
3. **Remove BLS**: delete `threshold.rs`'s hints wiring, `hints_onboarding`, the `hints` dep
   from `federation` + downstream Cargo.tomls (census list above), drop `ark-*` from
   federation (NOTE: `dkg.rs`/`beacon.rs` keep ark-bls12-381 only if the beacon stays BLS —
   the beacon is a SEPARATE lane; scope removal to the QC path first). `hints/` itself stays
   only while `turn/membership_verifier.rs:1182` and governed-namespace use it directly —
   those get their own FROST ports before the crate leaves the workspace.
4. Gate to pass before each step: full-workspace build + the federation/checkpoint/epoch/
   dfa-federation/cross-fed test suites + a live-mesh soak on the test federation
   (portal.dregg.studio five-validator + ember n=4) — the Empirical-Validation bar.

### Stage 5 — epoch/VK implications
- **The deployed circuit VK is NOT touched.** The recursive VK hash pins circuit descriptors
  (`docs/VK-REGEN-CONTROLS.md` §1); the QC is verified NATIVELY (Ed25519/BLS), never inside
  the deployed AIR — no descriptor regen, no VK epoch flip, no light-client rebuild for the
  proof system.
- What DOES change: the federation-level formats — `QuorumCertificate` (serde-additive, safe),
  `AttestedRoot.threshold_qc` bytes (opaque, scheme-tagged), and the federation identity
  question: `Federation` id derives from (committee, epoch); introducing/rotating the FROST
  group key rides the EXISTING epoch-transition machinery (`epoch.rs`,
  `apply_epoch_transition` mints a fresh id) — the flip is an epoch transition, not a
  genesis re-roll. Coordinate timing with the ember-gated VK-epoch flip only to avoid two
  simultaneous live-mesh changes, not because they share a mechanism.

## Vetted crate vs clean impl — recommendation

**Split the seam: clean impl for VERIFY (done, stage 1); vetted `frost-ed25519` for SIGNING
(stage 2).** Rationale:
- The verifier is where Lean-spec fidelity matters — and it is tiny: `verify_frost_quorum` is
  RFC 8032 `verify_strict` on a dep we already trust for every vote signature. It matches
  `SchnorrVerifies` symbol-for-symbol; there is nothing for a crate to vet that
  `ed25519-dalek` hasn't been vetted for since forever. Zero new deps.
- The signer is where the CRYPTOGRAPHIC danger lives — nonce generation, binding factors
  (Drijvers/ROS concurrent-session attacks), share handling. That is exactly what the Zcash
  Foundation `frost-*` crates (audited, RFC 9591 reference lineage) exist for. A clean-room
  two-round signer would be the classic "unvetted crypto in the TCB" mistake; the Lean spec
  proves the ALGEBRA, not the nonce hygiene.
- The two compose with no seam risk because FROST(Ed25519, SHA-512)'s output IS an ed25519
  signature: crate-signed certs verify under our clean verifier (and vice versa for the
  test dealer). The differential between them is stage 4's gate.

## Status
- Stage 1 implemented additively: `federation/src/frost.rs` (+ `pub mod frost` in `lib.rs`).
  BLS path untouched. Build + tests green via `cargo build/test -p dregg-federation`.
- Stages 2-5: this document is the plan of record; open the stage-2 lane by pinning
  `frost-ed25519` and threading `QuorumScheme` through the four verifier call sites.
