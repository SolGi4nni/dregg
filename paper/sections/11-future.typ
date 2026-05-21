// =============================================================================
// Section 11: Future Work
// =============================================================================

= Future Work

== Recursive Proof Composition

Recursive verification is implemented for pairs of proofs (verified via Plonky3). The path to a single constant-size proof covering all authorization sub-proofs requires composing heterogeneous AIRs (derivation + fold + membership) in one recursive proof. The `build_recursive_ivc_chain` function chains N fold proofs; extending this to heterogeneous composition is the primary remaining proof-system work.

== Full Privacy Pipeline

The privacy migration (Section 5) proceeds through six phases. The most impactful near-term change---removing `final_root` from public inputs and replacing it with a blinded presentation tag---provides full unlinkability with minimal circuit additions. The unified recursive proof (Phase 4) eliminates structural information leakage from the multi-proof composition.

== Federation Privacy

Encrypted turn ordering (Section 6) requires either threshold decryption ceremonies or full validity proofs for every turn. The recommended intermediate step is validium-style blind ordering: Bloom filter conflict sets for parallelism detection, lightweight STARKs for nonce/fee validity, and threshold decryption after ordering. Full elimination of decryption (Layer 3) requires encoding conservation and authorization verification in the validity AIR.

== Multi-Hop Gossip

Gossip is currently one-hop. Multi-hop Plumtree forwarding is implemented but not yet wired between federation nodes for cross-silo dissemination. The protocol exists; the integration is pending.

== Formal Verification

seL4's claim to fame is formal verification. Pyana's path:
- STARK proof system provides computational soundness (cheating is exponentially unlikely)
- Capability model is formally expressible (Datalog policies are decidable)
- Conservation invariant is checked by the executor
- Open: formal model of the full system (federation + cells + turns + proofs) in a proof assistant
- Possible: extract the executor's critical path into a verified implementation

== Agent Standard Library

Common patterns that could become protocol-level primitives:
- Request/response (turn + EventualRef)
- Publish/subscribe (intent + routing directive)
- Task queue (intent pool + fulfillment)
- Auction (competitive intent fulfillment with bond comparison)
- Escrow (conditional turn with timeout)
- Reputation oracle (receipt chain aggregation service)

== Proof System Performance

Current targets for agent-scale operation:
- Sub-10ms proof generation for simple authority checks (latency-sensitive coordination)
- Sub-1 KiB proofs for bandwidth-constrained gossip (Binius may deliver this)
- True recursive composition for constant-size multi-capability proofs
- Hardware acceleration (GPU/FPGA proving for throughput)

== Post-Quantum Migration

The STARK path is post-quantum today. Classical components have a staged migration: BLS12-381 threshold signatures $arrow.r$ lattice threshold (awaiting standardization), Ed25519 $arrow.r$ ML-DSA, X25519 $arrow.r$ ML-KEM. These migrations are confined within federation trust boundaries and can be executed per-federation without protocol-wide coordination.

== Open Questions

- *Genesis ceremony design*: How is authority bootstrapped without a single root of trust?
- *Shared mutable state*: How do agents share state that multiple parties can read/write?
- *Heterogeneous agents*: Human-in-the-loop, deterministic services, IoT devices, cross-federation agents
- *Federation scaling*: For very large committees (N > 100), committee-sampling approaches
- *Treasury governance*: Voting mechanism for treasury spending (deferred to governance design)
