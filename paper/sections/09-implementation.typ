// =============================================================================
// Section 9: Implementation
// =============================================================================

= Implementation

== Crate Architecture

The system is implemented in approximately 157k lines of Rust across 26 workspace crates:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*Crate*], [*Role*], [*Key Dependencies*]),
    [`macaroon`], [HMAC-SHA256 bearer tokens, attenuation], [hmac, sha2],
    [`secrets`], [Key management, X25519, sealing], [x25519-dalek, chacha20poly1305],
    [`token`], [Capability token lifecycle, validation], [macaroon, secrets],
    [`tokenizer`], [Token serialization, BIP39 HD derivation], [token],
    [`hints`], [BLS12-381 threshold signatures], [ark-bls12-381],
    [`morpheus`], [DAG-based BFT consensus (Lewis-Pye/Shapiro)], [hints],
    [`commit`], [Poseidon2 Merkle trees, commitments], [p3-poseidon2],
    [`trace`], [STARK trace generation, AIR evaluation], [commit, p3-fri],
    [`circuit`], [All AIR circuits (fold, derivation, IVC, etc.)], [trace, commit],
    [`federation`], [Consensus orchestration, revocation trees], [morpheus, hints],
    [`audit`], [Security audit trail, policy evaluation], [token],
    [`bridge`], [High-level API bridging proof + token layers], [circuit, token],
    [`wire`], [Network protocol, QUIC transport], [quinn, postcard],
    [`store`], [Persistent state, Merkle stores], [sled],
    [`cell`], [Cell state, c-lists, permission model], [types],
    [`turn`], [Turn execution, journal, atomicity], [cell, circuit],
    [`coord`], [2PC atomic coordination, causal DAG], [turn, federation],
    [`types`], [Shared types (CellId, CapabilityRef, etc.)], [],
    [`sdk`], [Client SDK, wallet, presentation API], [bridge, wire],
    [`wasm`], [WebAssembly bindings for browser extension], [sdk],
    [`node`], [Federation daemon (API + gossip sync)], [wire, federation],
    [`intent`], [Intent engine, matching, gossip], [token, commit],
    [`net`], [QUIC P2P, topic gossip, Plumtree], [quinn],
    [`demo`], [End-to-end demo harness], [all],
    [`demo-agent`], [Agent simulation for demos], [sdk],
    [`tests`], [Integration test suite], [all],
  ),
  caption: [Workspace crate overview. 26 crates organized by responsibility.],
)

== Performance

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, right, left),
    table.header([*Operation*], [*Latency*], [*Notes*]),
    [Macaroon verify (trusted)], [$tilde 8 mu s$], [HMAC-SHA256, constant-time],
    [Datalog evaluation], [$tilde 12 mu s$], [7 rules, 5 facts, bottom-up],
    [STARK proof generation], [$tilde 64 mu s$], [BabyBear4, real Poseidon2 constraints],
    [STARK verification], [$tilde 438 mu s$], [FRI proximity + Merkle check],
    [BLS threshold verify], [$tilde 32 "ms"$], [4-member committee],
    [End-to-end (wire)], [$tilde 560 "ms"$], [3-node TCP, real STARK],
    [Proof size], [24 KiB], [Single fold step],
  ),
  caption: [Measured performance on Apple M-series. Non-optimized implementation.],
)

== Test Coverage

The test suite includes 1,827 test functions covering:

- Unit tests for each crate (token validation, Datalog evaluation, Poseidon2 correctness, BLS aggregation)
- Integration tests spanning the full pipeline (token creation through STARK verification through turn execution)
- Property-based tests via proptest (conservation invariant, attenuation monotonicity, nullifier uniqueness)
- End-to-end demo scenarios (20+) covering delegation, revocation, multi-party turns, intent fulfillment, pipeline execution, cross-federation swaps, and wallet interactions
- Consensus correctness tests (3--7 node federations under simulated network conditions)
- Security regression tests for all audit findings

== Security Audit Findings (Resolved)

Per the security audit (May 2026), all critical findings have been addressed:

+ Turn executor now verifies Ed25519 signatures via `verify_authorization`.
+ Turn executor verifies ZK proofs via the `ProofVerifier` trait.
+ Coordinator verifies vote signatures with `ed25519_dalek::verify_strict`.
+ Wire protocol uses 64-byte signatures (via `pyana-types`).
+ Integer overflow in excess tracking and note conservation replaced with `checked_add`/`checked_sub`.
+ `CreateCell` rejects non-zero balance (prevents value creation).
+ QC forgery bypass (aggregate_qc short-circuit) removed.
+ Body fact membership now proven via Poseidon2 Merkle STARKs (not just asserted).

== Cryptographic Dependencies

- *Hash functions*: BLAKE3 (general purpose), Poseidon2 over BabyBear (STARK-friendly)
- *Signatures*: Ed25519 (node identity), BLS12-381 (threshold QCs)
- *Encryption*: X25519 + ChaCha20-Poly1305 (sealer/unsealer)
- *Proof system*: Plonky3 (STARK prover/verifier, FRI)
- *Key derivation*: BIP39 HD derivation for stable identity
