# Pyana: Technical Design

## 1. What is Pyana

Pyana is a distributed object-capability runtime where isolated objects (cells) communicate via atomic message turns, delegate authority through attenuated capability chains, and prove authorization in zero knowledge. It is not an auth library bolted onto an existing system -- the authorization structure IS the computational structure. Cells hold unforgeable references to each other, messages are atomic state transitions with journal rollback, and the network is a sealed capability marketplace with privacy-preserving discovery.

The system implements E-style distributed object semantics (promise pipelining, three-party introduction, sealer/unsealer), Mina-style execution (cells as zkApp accounts, turns as ZkappCommands, call forests), seL4-style capability derivation (recast as a proof structure for asynchronous distributed systems), and proof-carrying state (receipt chains as the primary state representation, with federation reduced to an ordering service). Agents own their own state, can exit any federation carrying their full history, and verify each other offline using only STARK proofs and attested Merkle roots.

## 2. Core Insight

**Capability attenuation IS incrementally verifiable computation.** Every time a capability is delegated with restrictions (narrowed to fewer services, shorter time windows, reduced budget), that attenuation step is a fold over a committed fact set -- removing facts, never adding them. Each fold produces a strictly smaller successor state. This monotonic narrowing forms a chain of state transitions that IVC was designed to prove. The prover demonstrates "I hold a valid attenuation chain from a federation-registered issuer, ending at a capability set that satisfies your request." The verifier checks a single STARK proof without seeing any intermediate states, delegation chain, or other capabilities. We get zero-knowledge presentation for free from the capability model -- the authorization structure is the computation being proved.

## 3. Architecture

```
+-------------------------------------------------------------------------+
|                    Browser Extension (wallet)                             |
|  Progressive disclosure UX · SLIP-10 key derivation · auto-lock          |
|  Per-method origin permissions · encrypted secrets at rest               |
+-------------------------------------------------------------------------+
|                    WASM Playground (pyana-wasm)                           |
|  28+ runtime functions · full system simulation in browser               |
|  Turns, cells, capabilities, federation, intents, conditional turns      |
+-------------------------------------------------------------------------+
|                    SDK Layer (pyana-sdk)                                  |
|  AgentWallet · AgentRuntime · SiloClient · HD wallet (BIP39)            |
+-------------------------------------------------------------------------+
|                    Intent Engine (pyana-intent)                           |
|  Gossip broadcast · local Datalog matching · commit-reveal · STARK proof |
+-------------------------------------------------------------------------+
|                    Node / Network Layer                                   |
|  pyana-node (federation daemon, HTTP API, MCP server, gossip sync)      |
|  pyana-net (Quinn QUIC, Plumtree gossip, topic-based dissemination)     |
|  wire (TCP postcard framing, STARK verification on receive)             |
+-------------------------------------------------------------------------+
|                    Federation Layer                                       |
|  federation (Ed25519 consensus, state roots in blocks, light client)    |
|  morpheus (adaptive BFT, Lewis-Pye & Shapiro)                           |
|  hints (BLS12-381 threshold sigs, KZG + SNARK aggregate verification)   |
+-------------------------------------------------------------------------+
|                    Coordination Layer (coord)                             |
|  Causal DAG · 2PC atomic · bounded counters (Stingray budget channels)  |
+-------------------------------------------------------------------------+
|                    Execution Layer                                        |
|  cell (isolated objects, c-lists, notes, programs, revocation channels) |
|  turn (TurnExecutor, call forests, journal rollback, two-phase fee)     |
|  Two-phase bridge (lock/receipt/cancel, destination_federation binding)  |
|  Three-party introduction · EventualRef · routing directives            |
+-------------------------------------------------------------------------+
|                    Proof Layer (circuit)                                  |
|  Plonky3 AIR: P3MerklePoseidon2Air (246 cols, 30 rounds inlined)       |
|  Custom AIRs: Poseidon2, Merkle, BlindedMerkle, NonRevocation,         |
|    NoteSpending, Derivation (173 cols, LessThan), Fold, IVC, Recursive  |
|  Presentation: unlinkable multi-show, committed selective disclosure    |
|  Unified action binding: compute_action_binding(action, resource)       |
+-------------------------------------------------------------------------+
|                    Commitment Layer (commit)                              |
|  4-ary Merkle trees (BLAKE3 fast path / Poseidon2 ZK path)             |
|  Fold deltas (monotonic state transitions) · symbol table               |
+-------------------------------------------------------------------------+
|                    Policy Layer                                           |
|  trace (Datalog evaluator + derivation trace, deny overrides allow)     |
|  token (AuthToken: Macaroon HMAC-SHA256 + Biscuit Ed25519+Datalog)      |
|  tokenizer (X25519-ChaCha20Poly1305 seal/unseal)                       |
+-------------------------------------------------------------------------+
|                    Storage Layer                                          |
|  store (redb ACID, note commitment tree, nullifier set)                 |
|  secrets (OS keychain + AES-256-GCM encrypted file store, zeroize)     |
|  audit (usage log, budget enforcement, consistency proofs)              |
+-------------------------------------------------------------------------+
```

## 4. Execution Model

### Cells

A cell is the fundamental unit of isolated state. Each cell holds:

- Content-addressed identity (`CellId`, 256 bits)
- 8 generic field slots in F_p where p = 2^31 - 2^27 + 1 (BabyBear prime)
- A capability list (c-list): the set of capabilities the cell may exercise
- Permission requirements per action type (all effects mapped to permission requirements)
- Balance (computrons), nonce (replay protection)
- Optional programs (predicates, circuits) defining valid state transitions
- Private notes (anonymous cells for shielded value transfer)
- Cell hash covers ALL fields (prevents partial state manipulation)

Cells are confined: a cell can only reference capabilities in its c-list, and capability transfer respects the confinement invariant.

### Turns

A turn is an atomic transaction over one or more cells. It contains:

- A call forest: a tree of actions, executed depth-first
- A fee in computrons covering execution cost
- A nonce (monotonically increasing per cell)
- Authorization: Ed25519 signature, ZK proof, or both
- Signing message covers balance_change + preconditions + call_forest (prevents malleability)

Turn submission is real: the node receives a turn, executes it via TurnExecutor, and produces a TurnReceipt. Gossip validation verifies turns before rebroadcasting.

If any action in the call forest fails, all effects roll back via journal replay. The executor enforces a conservation invariant: sum of balance changes + fee = 0. Value cannot be created or destroyed within a turn.

### Pipelines (EventualRef and Topological Execution)

The executor processes batches of turns with declared dependency edges as a DAG. A `PipelinedSend` targets an `EventualRef` -- a reference to the output of a pending turn, identified by the turn's hash and an output slot index:

```
Target = Concrete(CellId) | Eventual(source_turn: [u8; 32], slot: u32)
```

When a source turn commits, its outputs populate a resolution table and dependent turns rewrite their targets to concrete CellIds. If turn t_i fails and t_j depends on t_i, then t_j receives `DependencyFailed` without executing. This eliminates round-trip latency in distributed object protocols (E-style promise pipelining).

### Call Forests

Actions within a turn form a tree (call forest), executed depth-first. Child actions run within the scope of their parent -- if a child fails, the parent's sub-effects roll back but the parent can catch the failure. Call forests compose: a multi-party turn merges forests from multiple cells into a single atomic execution.

### Three-Party Introduction

Alice, holding capabilities to both Bob and Carol, introduces Bob to Carol by emitting an `Effect::Introduce` during a turn. This produces a `RoutingDirective`:

```
RoutingDirective { sender: CellId, target: CellId, authorizing_turn: [u8; 32], expires: Option<u64> }
```

The node's routing table is populated from these directives. No global directory exists -- all communication paths form through introductions, not discovery.

### Delegation (Snapshot + Refresh)

A child cell receives a point-in-time snapshot of its parent's c-list:

```
DelegatedRef { source, snapshot: [CapabilityRef], epoch, refreshed_at, max_staleness }
```

The child acts offline using the snapshot. The executor enforces staleness: presentations where `now - refreshed_at > max_staleness` are rejected in both delegation paths. Epoch-based revocation: the parent bumps the epoch, invalidating all outstanding snapshots until children refresh.

### Two-Phase Bridge (Cross-Federation Value Transfer)

Notes are transferred between federations via a lock/receipt/cancel protocol:

1. **BridgeLock**: Notes are locked (not burned) with a `destination_federation` binding. The lock is proven in a STARK that commits `destination_federation` as a public input, preventing cross-federation replay.
2. **BridgeReceipt**: Once the destination federation finalizes the credit, it emits a receipt. The receipt is presented to the source federation to complete the bridge (unlock/burn the note).
3. **BridgeCancel**: After a timeout, if no receipt arrives, the lock is cancelled and value is returned to the sender.

## 5. Capability Model

### C-Lists and Confinement

Each cell holds a c-list: the exhaustive set of capabilities it may exercise. `GrantCapability` checks that the granting cell actually holds authority over the source. A cell cannot delegate what it does not have.

### Attenuation (Monotonic Narrowing)

Delegation chains can only restrict, never expand. A root token grants `{all services, infinite TTL, full budget}`. Each attenuation step produces a new token with a strictly smaller capability set. The fold delta captures exactly what was removed: `Delta = { f in F_old | f not in F_new }`. The fold AIR constraint enforces that only removals (never additions) occur.

### Capability Derivation Tree (CDT)

The distributed analog of seL4's kernel-enforced CDT. Each delegation step records:

```
DelegationEdge { parent: CapHash, child: CapHash, attenuation: Delta, epoch: u64 }
```

These edges form a Merkle-committed tree. The key duality: seL4 ENFORCES the tree (kernel walks it synchronously for revocation); Pyana PROVES the tree (delegator proves their capability descends from a valid root, revoker proves non-membership in the current valid set).

### Sealer/Unsealer (Offline Transfer)

X25519-ChaCha20Poly1305 keypairs enable partition-tolerant offline capability transfer. The sender seals a capability under the recipient's public key with a fresh ephemeral keypair (forward secrecy). The sealed box traverses untrusted channels revealing nothing. The recipient unseals with their private key when they come online. A BLAKE3 commitment binds the ciphertext to the capability without revealing it.

### Breadstuff Tokens (Bearer Authorization)

Capabilities are encoded as Datalog fact sets within bearer tokens. Two token backends:

- **Macaroon**: HMAC-SHA256 chain. Each caveat attenuates the fact set. Constant-time verification. Unknown caveats fail-closed.
- **Biscuit**: Ed25519 signature + embedded Datalog policy. Decentralized verification without sharing the root key. Deny overrides allow in Datalog evaluation.

## 6. Proof System

### Production Backend: Plonky3

Plonky3 is the production proof backend. The `P3MerklePoseidon2Air` achieves full algebraic soundness by inlining all 30 Poseidon2 rounds (8 external + 22 internal) across 246 columns (5 control + 240 auxiliary round states + 1 root). This is a real STARK with real constraints -- no vacuous proofs. The Plonky3 feature gate exists for compile-time flexibility but the AIR is the primary production path.

All proofs use BabyBear4 (degree-4 extension field, |F_{p^4}| ~ 2^124, providing 124-bit challenge security). FRI with 80 queries and blowup factor 4 gives 160-bit soundness; the system bottleneck is the ~124-bit challenge security from BabyBear4, comfortably exceeding NIST PQ Level 1. Proofs are ~38 KiB, generated in sub-second time on Apple M-series.

The custom `stark.rs` implementation (FRI from scratch) has been demoted to `circuit/examples/fri_from_scratch.rs` as a pedagogical reference.

### AIR Circuits

1. **P3MerklePoseidon2Air (Plonky3)**: 246 columns. Full Poseidon2 soundness with all 30 rounds inlined algebraically. Production Merkle membership proofs.

2. **BlindedMerklePoseidon2StarkAir**: Ring membership for issuer anonymity. `blinded_leaf = Poseidon2(leaf_hash, fresh_blinding)`. The verifier cannot determine which federation member issued the credential.

3. **Poseidon2 Permutation**: Proves y = Poseidon2(x). Constraint degree 7. Multiple AIR variants (simple permutation, round-by-round Merkle, blinded Merkle).

4. **Merkle Membership**: Proves leaf exists under root in 4-ary tree. Position validity + hash binding per level. Boundary constraints enforced.

5. **Note Spending**: Proves knowledge of spending key, commitment preimage, and Merkle membership. Produces a position-independent nullifier preventing double-spend. Single AIR with 12 columns.

6. **Multi-Step Derivation**: 173 columns. Proves N valid Datalog rule applications produce ALLOW. 19 constraint families. Handles substitution, equal/memberof/GTE/LT checks, accumulated hash chain. LessThan constraint uses bit decomposition (31 bits each for GTE and LT, columns 107-172).

7. **Fold Chain (Attenuation)**: Proves monotonic fact removal from old root to new root. Only removals possible (membership proofs under old root required for each removed fact).

8. **NonRevocation**: Sorted-set non-membership proofs with adjacency verification. Left/right neighbor bounds proven via Merkle membership, ensuring the gap genuinely exists.

9. **IVC Accumulation**: 7-column trace. Proves a sequence of N valid fold steps with root continuity and hash chain binding. Constant-size output regardless of N. Hash-chain fallback always maintained for comparison.

10. **Recursive Verifier**: Encodes STARK verification (Fiat-Shamir replay, FRI folding, constraint evaluation) as an AIR. Plonky3-based recursive verifier works for pairs; arbitrary-N chaining via `build_recursive_ivc_chain` uses sequential composition.

### Unified Action Binding

`compute_action_binding(action, resource)` produces a single commitment used consistently by prover, wire protocol, and executor. This ensures the proof, the wire message, and the execution all reference the same action-resource pair.

### Body Fact Membership Composition

The full authorization proof composes:

```
Derivation Proof (N rule steps -> ALLOW)
+ Body Membership Proofs (each body fact in tree under R_0)
+ Fold Chain Proof (R_issuer -> R_0 via attenuation)
+ Issuer Ring Membership (BlindedMerklePoseidon2StarkAir)
```

Binding via shared public inputs: derivation's state root = fold chain's final root; fold chain's initial root = issuer's committed capability root; issuer membership uses blinded leaf for anonymity within federation.

### IVC (State Transition Proofs)

Receipt chains (TurnReceipts with pre/post state hashes) are compressed via IVC into constant-size proofs. A verifier needs only: the IVC proof, current state commitment, and nullifier non-membership proof. The IVC fallback path (self-signed hash chain) has been replaced with an error if no STARK is available.

### Proof Backends

| Backend | Field | Proof Size | PQ? | Status |
|---------|-------|-----------|-----|--------|
| BabyBear STARK + Plonky3 | F_{2^31-2^27+1} + FRI | ~38 KiB | Yes | **Production** |
| BabyBear STARK (custom) | Same | ~24 KiB | Yes | Pedagogical (`examples/fri_from_scratch.rs`) |
| Binius | GF(2) tower + Groestl-256 | ~1-4 KiB | Yes | Research (optional dep) |
| Halo2 | BN254/Pasta + KZG | ~1-5 KiB | No | Designed |
| Nova | Pasta cycle (Pallas/Vesta) | ~10 KiB | No | Designed |

Multi-hash roots (Poseidon2, Groestl256, PoseidonBN254) let each backend reference its native commitment.

## 7. Privacy Model

### Anonymous Credential Properties (Achieved)

Pyana's privacy system now provides properties comparable to Idemix/BBS+ anonymous credential systems:

1. **Issuer anonymity within federation** (Phase 1 DONE): `BlindedMerklePoseidon2StarkAir` proves the issuer is a valid federation member without revealing which one. Ring membership via blinded Merkle leaf.

2. **Unlinkable multi-show** (Phase 2 DONE): `presentation_tag = Poseidon2(final_root, presentation_randomness)`. Fresh per presentation, unlinkable across shows. `initial_root` and `final_root` REMOVED from public inputs -- they are now private witness only.

3. **Committed selective disclosure** (Phase 3 DONE): `revealed_facts_commitment` is a STARK public input. The prover chooses which facts to reveal; the proof cryptographically guarantees binding between revealed facts and the derivation trace.

### Public Inputs (Current State)

A fully private, unlinkable presentation proof exposes only:

```
PresentationPublicInputs {
    federation_root: BabyBear,          // which federation (public, shared)
    request_predicate: BabyBear,        // what is being authorized
    presentation_tag: BabyBear,         // blinded, unlinkable per-show tag
    revealed_facts_commitment: BabyBear, // zero if fully private
    revocation_set_root: BabyBear,      // proves non-revocation
}
```

Removed from public/wire: `initial_root`, `final_root`, `chain_length`. These are private witness.

### Three Verification Modes

| Mode | Verifier Learns | Latency | Proof Size |
|------|----------------|---------|-----------|
| **Trusted** | Full cleartext token + Datalog trace | ~8 us | 0 |
| **Selective Disclosure** | Chosen facts + conclusion | ~200 ms | ~45 KB |
| **Fully Private** | One bit (allow/deny) | ~500 ms | ~80 KB |

All three modes work offline. The same Datalog rules yield the same answer; what changes is how much the verifier learns. Mode selection: hold root key -> Trusted; need partial facts -> Selective; need anonymity -> Private.

### Notes (Anonymous Cells)

A note commits to (owner, value, asset_type, creation_nonce, randomness) via Poseidon2. Spending produces a nullifier = Poseidon2(commitment, spending_key, nonce) that is position-independent -- preventing double-spend without revealing which note was consumed. The note commitment tree is federation-maintained; spending proofs demonstrate knowledge of the spending key + Merkle membership without revealing the note.

### Intent Matching (Private Discovery)

Agents broadcast needs as public intents ("I need capability matching spec S"). Wallets evaluate locally using Datalog: "does any token in my wallet satisfy S?" This evaluation never leaves the wallet. If a match exists, the wallet generates a STARK proof of capability satisfaction without revealing which token, what delegation chain, or what else it holds.

### Privacy Roadmap

See `docs/privacy-architecture.md` for the full 6-phase roadmap covering:
- Phase 4: Predicate proof builder API (range/set proofs without revealing values)
- Phase 5: Federation transaction privacy (shielded turn content)
- Phase 6: Cross-verifier unlinkability guarantees

## 8. Intent Engine

### Architecture

1. **Pool**: Content-addressed intents identified by blinded CommitmentIds. Broadcast via gossip.
2. **Match**: Wallets evaluate intents locally against their c-lists using Datalog. No capability information leaves the wallet.
3. **Commit-Reveal**: Satisfier publishes C = H(intent_id || satisfier_secret) before revealing proof. Prevents frontrunning.
4. **Fulfill**: STARK proof of capability satisfaction. Verifier learns only that someone can satisfy the intent.

### MatchSpec Language

Intents declare the shape of needed capability via MatchSpec predicates: required actions, target resources, constraint atoms. The spec reveals what is NEEDED, never what is HELD.

### Stake Requirement

Intent submission requires a Poseidon2 Merkle proof demonstrating the submitter has a valid note commitment in the note tree (proving economic stake without revealing balance or identity). Epoch-scoped stake nullifiers (K=5 per note per epoch) prevent a single note from proving unlimited identities.

### Privacy Properties

The gossip network sees intents (public needs) but never capabilities (private holdings). The requester learns only that someone can satisfy their need. The satisfier reveals only that they can satisfy it. Limitation: the push model means satisfiers must be online and subscribed to the gossip topic.

## 9. Federation

### Simplified BFT Consensus (Hardened)

Federation consensus uses a simplified BFT protocol with Ed25519 signatures. The implementation is hardened:

- **Vote signatures verified**: Individual Ed25519 vote signatures are checked against registered voter public keys. Legacy mode (empty `config.members`) no longer bypasses verification.
- **Proposals signed**: Each proposal carries the proposer's Ed25519 signature, proving authority.
- **Pacemaker/view-change**: 30-second proposal timeout with signed view-change messages. View advances when n-f view-change votes collected.
- **State roots in blocks**: Every finalized block commits to `pre_state_root`, `post_state_root`, `note_tree_root`, and `nullifier_set_root`. Nodes detect divergence immediately after finalization.

### BLS12-381 Threshold Signatures

A quorum certificate is a single aggregate BLS12-381 threshold signature via real KZG polynomial commitments + SNARK proof for aggregate verification. Verification cost is constant regardless of committee size.

### LightClientProof

External verifiers can validate federation state without running a full node:

```
LightClientProof { block_hash, height, state_root, qc }
```

Produced automatically on each finalization. Enables SPV-style verification of attested roots.

### Epoch Reconfiguration

Federation membership changes occur at epoch boundaries. Each epoch carries a new committee set and updated threshold parameters. DelegatedRefs track the epoch at which they were issued. Quorum of current members must approve reconfiguration.

### Attested Roots

The federation attests to:

```
AttestedRoot { nullifier_root, note_tree_root, height, timestamp, qc }
```

The federation does NOT attest to cell state. Cell state is proved by the cell's own receipt chain. The separation means the federation provides anti-double-spend ordering while agents own their own state.

### RevocationChannel (Implemented)

For applications requiring near-instant revocation: a `RevocationChannel` is a circuit breaker between revoker and subjects (698 LOC in `cell/src/revocation_channel.rs`). Subjects voluntarily subscribe and check channel state (Active/Tripped) before exercising gated capabilities. Trip propagates via federation attestation gossip within one consensus round. Degrades gracefully offline (bounded staleness).

### Federation as Ordering Service

The federation is NOT a state container. It orders nullifiers and attests to note tree roots. Agents carry their own state as proof chains. This enables trivial federation exit: stop submitting nullifiers, take your proof chain, join another ordering service or operate standalone.

### Net/Federation Hookup

Consensus messages flow over the QUIC gossip layer. The `node/src/federation_sync.rs` module initializes a GossipNetwork, joins canonical topics (turns, revocations, intents, roots), and bridges gossip events to local node state. See `docs/federation-architecture.md` for the full design.

## 10. Economic Model

### Fee Distribution

Fees collected from turns are distributed:

- **50% to block proposer** (incentivizes running validators)
- **30% to treasury** (funds public goods, governance-controlled)
- **20% burned** (deflationary pressure)

### Anti-Griefing

- **Conditional deposit**: `deposit = 500 + 10 * blocks_until_deadline`. Prevents conditional turn spam by making long-horizon conditions expensive.
- **Epoch-scoped stake nullifiers**: K=5 per note per epoch. A single note cannot prove unlimited identities across intent pools within one epoch.
- **ProofObligation bonds**: Locked note value slashed on timeout.

### Bounded Counters (Stingray)

Each silo holds a local budget slice: `slice(i) = balance * (f+1) / (2f+1)`. Debits locally without coordination until exhaustion. The executor checks `fee <= remaining` before execution (fail-fast) and debits atomically upon commit. Even f Byzantine silos cannot overspend the agent's true balance. Checked arithmetic throughout -- overflow produces an error, never wraps.

See `docs/economic-model.md` for the full economic design including fee markets, validator selection economics, and sustainability analysis.

## 11. Proof-Carrying State

### Receipt Chains

Every committed turn produces a `TurnReceipt` with pre/post state hashes, effects hash, and computron cost. Receipts chain: `receipt[n].post_state_hash == receipt[n+1].pre_state_hash`. The chain IS the state proof -- anyone can verify from genesis without contacting a federation.

### Executor Signatures

Each receipt carries the executor's Ed25519 signature attesting to valid execution (preconditions checked, programs satisfied, conservation enforced). Signatures use `verify_strict` (no malleability).

### IVC Compression

The IVC layer compresses an arbitrary-length receipt chain into a constant-size proof. A verifier needs: (1) the IvcProof (proves chain validity from genesis), (2) current state commitment, (3) nullifier non-membership proof.

### Federation Exit

An agent leaves by stopping nullifier submission. Their proof chain is portable -- it proves state validity from genesis without referencing federation-specific data. The agent can join another ordering service or operate standalone.

### Dual Merkle (BLAKE3 Fast + Poseidon2 ZK)

The commitment layer maintains parallel Merkle trees: BLAKE3 for fast operational hashing, Poseidon2 for in-circuit ZK verification. These are not yet unified -- currently the BLAKE3 Merkle proofs cannot be directly verified inside a STARK. Unification is a known priority.

## 12. Networking

### Quinn QUIC (pyana-net)

All inter-node communication uses QUIC via Quinn with multiplexed streams and 0-RTT resumption. The pyana-net crate handles peer connection brokering and attested root distribution directly within the node.

### Plumtree Gossip

Topic-based hybrid push dissemination: eager push (degree 3) for spanning-tree delivery, lazy push (IHave notifications) for redundancy, periodic Bloom filter anti-entropy. Four gossip topics: turns, revocations, intents, attested roots.

Gossip validation: incoming turns are verified and executed before rebroadcasting. Revocations are verified (signature + non-membership proof). Attested roots are verified against the QC.

### Wire Protocol (TCP)

Postcard-framed TCP for direct silo-to-silo communication. Messages carry STARK proofs verified on receive. Three variants: Presentation (authorization proof), Revocation (non-membership proof), TurnSubmission.

### Node HTTP/WS API

`pyana-node` exposes a localhost HTTP/WebSocket API for local clients. Features:
- Turn submission (executed via TurnExecutor, produces receipts)
- State query, intent posting, federation status
- CORS middleware, rate limiting, body size limits
- Graceful shutdown (SIGINT)
- Passphrase persisted + node identity loaded from `node.key`

### MCP Server (AI Agent Interface)

`pyana-node mcp` exposes 15 tools over JSON-RPC 2.0 (stdio transport) for AI assistant interaction:

`pyana_get_status`, `pyana_create_agent`, `pyana_authorize`, `pyana_submit_turn`, `pyana_grant_capability`, `pyana_revoke_capability`, `pyana_post_intent`, `pyana_fulfill_intent`, `pyana_delegate`, `pyana_check_capabilities`, `pyana_read_cell`, `pyana_get_receipt_chain`, `pyana_seal_data`, `pyana_unseal_data`, `pyana_bridge_note`.

See `docs/agent-substrate.md` for the full agent-as-first-class-citizen design.

### Browser Extension

Injects `window.pyana` into every page. Security model:
- Progressive disclosure UX (privacy picker popup for mode selection)
- Secrets always encrypted at rest (Web Crypto AES-GCM)
- Deterministic key derivation without WASM (SLIP-10 via HMAC-SHA512)
- `authorize` requires explicit user consent (popup confirmation)
- Per-method, time-limited origin permissions
- Auto-lock timeout (5 minutes)

## 13. Storage

- **redb**: ACID crash-safe persistence for cell state, note commitment trees, and nullifier sets
- **Encrypted keychain**: OS keychain integration (via `keyring` crate) + AES-256-GCM encrypted file store for Ed25519 identity keys and sealed secrets. All secret material uses `zeroize` on drop.
- **Note trees**: 4-ary Poseidon2 Merkle tree of note commitments, maintained by the federation
- **Nullifier sets**: Append-only set with ordered leaves enabling non-membership proofs (adjacency verified for soundness)

## 14. SDK

- **AgentWallet**: Token management, attenuation, presentation (all three modes), proof generation, receipt chain maintenance. Wallet keys zeroized on drop.
- **AgentRuntime**: Turn construction, pipeline submission, effect handling, intent broadcasting
- **HD Wallet (BIP39)**: Hierarchical deterministic key derivation for stable agent identities across restarts
- **Verification API**: `wallet.authorize(&token, &request, mode)` returns mode-appropriate `AuthorizationPresentation`
- **SiloClient**: Federation connection, state sync, nullifier submission

## 15. Security Model

### Trust Boundaries

Everything that crosses a trust boundary is post-quantum secure (STARK proofs, Poseidon2/BLAKE3 Merkle commitments, HMAC chains). Classical cryptography (Ed25519, BLS12-381, X25519) exists only between parties that already trust each other within a federation.

### Security Hardening (Comprehensive)

1. Turn executor verifies Ed25519 signatures via `verify_authorization` with `verify_strict` (no signature malleability)
2. Turn executor verifies ZK proofs via `ProofVerifier` trait
3. Coordinator verifies vote signatures with `ed25519_dalek::verify_strict`
4. Wire protocol uses 64-byte signatures (via pyana-types)
5. Integer overflow in excess tracking replaced with checked arithmetic
6. `CreateCell` rejects non-zero balance (prevents minting from nothing)
7. QC forgery bypass (aggregate_qc short-circuit) removed
8. Body fact membership proven via Poseidon2 Merkle STARKs (not just asserted)
9. Signing message covers balance_change + preconditions + call_forest (prevents malleability/downgrade)
10. Domain separation on all signature contexts (STARK, IVC, wallet)
11. Wallet key zeroization complete (sdk, secrets, tokenizer, node, hints)
12. Unknown caveats fail-closed (token, bridge, trace -- 3 enforcement sites)
13. Deny overrides allow in Datalog policy evaluation
14. Non-membership proofs sound (left/right neighbor adjacency verified)
15. Staleness enforced in executor for both delegation paths
16. All effects mapped to permission requirements

### Post-Quantum Roadmap

- Phase 1 (current): STARK path is PQ today
- Phase 2: BLS12-381 -> lattice threshold signatures (Hermine/Oriole/TalonG, pending NIST 2026/2027)
- Phase 3: Ed25519 -> ML-DSA
- Phase 4: X25519 -> ML-KEM

See `docs/pq-roadmap.md` for timeline and migration strategy.

## 16. Comparison

| Property | Pyana | UCAN | Cap'n Proto | Mina | Midnight | seL4 | Cosmos IBC |
|----------|-------|------|-------------|------|----------|------|------------|
| Primary use | Agent auth + runtime | Decentralized auth | RPC framework | General L1 | Privacy DeFi | Kernel security | Cross-chain msg |
| Proof system | BabyBear STARK (Plonky3) | None | None | Kimchi (Plonk) | Plonk | Formal verification | None |
| Privacy | Unlinkable ZK (Idemix-class) | Transparent chains | None | Succinct (not private) | Shielded txns | N/A | Transparent |
| Capability model | Object-cap + Datalog + CDT | UCAN delegation | E-style + 3-party intro | Account perms | UTXO-based | CDT (kernel) | ICS-20 channels |
| Offline verify | Yes (proof + root) | Yes (no privacy) | No (live vat) | Yes | Partial | N/A | No (relayer) |
| PQ-ready | External: yes | No | No | No | No | N/A | No |
| Consensus | Federated BFT (3-64) | None (P2P) | None | Ouroboros | Ouroboros variant | Single machine | Tendermint |
| State model | Proof-carrying chains | Token chains | Live objects | Global ledger | Global ledger | Kernel memory | Per-chain ledger |
| Promise pipelining | Yes (EventualRef) | No | Yes | No | No | No | No |
| Revocation | CDT + epochs + channels | Token expiry | Vat GC | N/A | N/A | CDT (instant) | N/A |
| Multi-show unlinkable | Yes | No | N/A | No | Yes | N/A | N/A |

## 17. Current Status

### What Works Today

- Real STARK proofs with real Poseidon2 constraints (Plonky3: 246 columns, 30 rounds inlined algebraically). No vacuous proofs.
- Full privacy pipeline: ring membership (BlindedMerklePoseidon2StarkAir), unlinkable multi-show (presentation_tag), committed selective disclosure
- Full token-to-proof-to-turn-execution pipeline with pipeline execution and topological ordering
- Turn submission with real execution (TurnExecutor produces receipts, gossip validates before relay)
- Federation with state roots in blocks, vote signature verification, signed proposals, pacemaker/view-change, LightClientProof
- Federation gossip hookup: consensus messages over QUIC gossip (4 topics: turns, revocations, intents, roots)
- Two-phase bridge: BridgeLock/BridgeReceipt/BridgeCancel with destination_federation STARK binding
- RevocationChannel implemented (698 LOC, opt-in instant revocation)
- Fee distribution (50/30/20), conditional deposit anti-griefing, epoch-scoped stake nullifiers
- Browser extension with progressive disclosure UX, SLIP-10 keys, encrypted secrets, per-method origin permissions, auto-lock
- WASM playground with 28+ runtime functions (full system simulation in browser)
- MCP server with 15 tools for AI agent interaction
- Node hardening: CORS, rate limiting, graceful shutdown, passphrase persistence, node.key identity
- TCP wire protocol with STARK verification on receive
- Sealer/unsealer with X25519-ChaCha20Poly1305 for offline capability transfer
- Promise pipelining with EventualRef resolution and three-party introduction
- Note spending proofs with nullifier-based double-spend prevention
- LessThan constraint in derivation AIR (bit decomposition, columns 107-172)
- Boundary constraints on all production AIRs (NonRevocation, MerklePoseidon2, Plonky3)
- Unified action binding: `compute_action_binding(action, resource)` used by prover/wire/executor
- verify_strict everywhere (7 enforcement sites), domain separation on all signatures
- Wallet key zeroization (10 crates), unknown caveats fail-closed, deny overrides allow
- 35 end-to-end demo scenarios covering delegation, revocation, multi-party turns, intents, pipelines, cross-fed atomic, bridge, privacy
- BLS12-381 threshold signatures via KZG polynomial commitments + SNARK aggregate verification

### In Progress

- Recursive proof composition: Plonky3 recursive verifier works for pairs; arbitrary-N chaining uses sequential composition. Full heterogeneous AIR composition (derivation + fold + membership in one recursive proof) not yet operational.
- Dual Merkle systems (BLAKE3 fast / Poseidon2 ZK) not yet unified end-to-end
- Predicate proof builder API (range/set proofs composable into a single STARK) -- individual LT/GTE constraints land, builder API not yet exposed
- Morpheus (full DAG-based BFT) is proven sound but not wired into production federation path (simplified consensus is the production path)
- Multi-hop Plumtree forwarding: implemented in net, wired for gossip, not yet proven at scale

### Designed but Unimplemented

- Post-quantum migration for classical components (waiting on NIST standardization)
- Full constant-size recursive composition of heterogeneous AIRs in a single proof
- Federation transaction privacy (shielded turn content visible to validators)
- SP1/EVM settlement via the `chain/` workspace (excluded from main build)

## 18. Crate Table

26 workspace members, ~156k LOC Rust, ~1827 tests:

| Crate | LOC | Purpose |
|-------|-----|---------|
| `cell` | 8.5k | Isolated objects with c-lists, notes, programs, nullifier sets, revocation channels, bridge |
| `turn` | 16.3k | TurnExecutor: call forests, journal rollback, two-phase fee, conservation, pipeline execution, conditional turns, staleness |
| `coord` | 4.3k | Multi-silo coordination: causal DAG, 2PC atomic commit, Stingray bounded counters |
| `circuit` | 27.3k | STARK prover/verifier, 10 AIRs, IVC, Plonky3 (246-col, 30 rounds), recursive verification, action binding, presentation |
| `commit` | 3.6k | 4-ary Merkle trees (BLAKE3 + Poseidon2), fold deltas, symbol table |
| `trace` | 3.7k | Datalog evaluator with derivation trace extraction, deny-overrides-allow policy |
| `token` | 5.8k | AuthToken trait: Macaroon (HMAC-SHA256) + Biscuit (Ed25519+Datalog), fail-closed caveats |
| `tokenizer` | 1.3k | X25519-ChaCha20Poly1305 seal/unseal daemon |
| `macaroon` | 1.8k | HMAC-chain bearer tokens with constant-time verification |
| `secrets` | 0.8k | OS keychain + AES-256-GCM encrypted file store, atomic writes, zeroize |
| `types` | 1.3k | Canonical types: CellId, Ed25519 (64-byte sigs, verify_strict), AttestedRoot, causal DAG |
| `federation` | 5.8k | Ed25519 consensus, state roots in blocks, vote verification, epoch reconfig, LightClientProof, revocation trees |
| `morpheus` | 4.0k | Adaptive BFT consensus (Lewis-Pye & Shapiro), view-change, block finalization |
| `hints` | 3.2k | BLS12-381 threshold signatures via KZG polynomial commitments + SNARK |
| `bridge` | 5.7k | Connects token pipeline to circuit: presentation builder, blinded membership, mode dispatch |
| `wire` | 5.3k | TCP wire protocol, postcard framing, federation bridge, action binding |
| `net` | 3.7k | Quinn QUIC transport, Plumtree gossip, topic-based dissemination |
| `node` | 3.6k | Federation daemon: HTTP API, MCP server (15 tools), gossip sync, CORS, rate limiting, node.key |
| `intent` | 4.4k | Distributed intent engine: gossip broadcast, local Datalog matching, commit-reveal, epoch-scoped nullifiers |
| `store` | 3.6k | redb persistence, note commitment tree, nullifier set |
| `audit` | 2.5k | Usage logging, consistency proofs, budget enforcement |
| `sdk` | 3.4k | Agent SDK: wallet (zeroize), runtime, verification modes, HD key derivation |
| `wasm` | 2.8k | Browser WASM bindings (28+ runtime functions, full simulation) |
| `demo` | 2.7k | CLI demos and key generation |
| `demo-agent` | 17.0k | End-to-end scenarios: 35 examples covering full pipeline, cross-fed, bridge, privacy |
| `tests` | 6.2k | Integration tests: adversarial boundaries, Byzantine, soundness, fuzz, budget, commitment |

Plus: `chain/` (standalone workspace for SP1/EVM settlement), `extension/` (browser extension), `site/` (demo pages + playground + discovery.json).

## 19. Design Documents

| Document | Scope |
|----------|-------|
| `docs/privacy-architecture.md` | 6-phase roadmap to anonymous credential parity |
| `docs/federation-architecture.md` | Full federation design, current/missing analysis |
| `docs/economic-model.md` | Fee distribution, anti-griefing, sustainability |
| `docs/agent-substrate.md` | seL4-to-Pyana mapping, agent lifecycle, MCP integration |
| `docs/pq-roadmap.md` | Post-quantum migration timeline |
| `docs/proof-carrying-state.md` | Receipt chains, IVC compression, federation exit |
| `docs/verification-modes.md` | Three-mode verification analysis |
| `docs/synchrony-primitive.md` | RevocationChannel design |
| `docs/svenvs-bridge.md` | Cross-federation bridge protocol |

---

License: AGPL-3.0-or-later
