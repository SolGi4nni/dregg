# Consensus Architecture v2: Blocklace + Proof-Carrying Sovereign Cells

## Vision

Every device is a participant. Phones, laptops, cloud nodes — all produce blocks in a shared blocklace. Federations are fluid (subscribe to ordering nodes as needed). Most operations need no consensus at all.

## Theoretical Foundation

| Paper | Insight | `dregg` Application |
|-------|---------|-------------------|
| Blocklace (2402.08068) | CRDT DAG with equivocation detection | Universal data structure replacing linear peer chains |
| Cordial Miners (2205.09174) | 3-round total ordering from DAG, O(n) good case | Ordering for shared-resource conflicts only |
| PCO (2311.13936) | Single-owner ops need only FIFO broadcast | Validates fast-path (most ops are consensus-free) |
| CryptoConcurrency (2212.04895) | Shared resources ALSO mostly consensus-free (COD) | New optimistic tier for multi-owner non-conflicts |
| Adversary Majority (2411.01689) | STARK proofs = unconditional safety (t^S = 1) | Federation compromise costs liveness not safety |
| Permissionless Consensus (2304.14701) | Must be quasi-permissionless for accountability | Always-on ordering nodes are necessary |
| Dyno (2022/597) | Epoch-based reconfig is fine for governed federations | Keep it simple for membership changes |

## Three-Tier Execution Model

### Tier 1: Sovereign (consensus-free, any participation level)

- Single-owner cell transitions
- Bilateral peer-to-peer (Alice ↔ Bob, both online)
- Capability exercises between known parties
- STARK proofs carry validity; no coordinator needed
- Blocklace virtual chain per agent; CRDT merge on reconnect
- **Latency: 0 RTT (local) to 1 RTT (bilateral)**

### Tier 2: Optimistic Shared (COD, usually consensus-free)

- Multiple parties access shared resource (AMM pool, shared account)
- Closable Overspending Detector tracks credits vs debits
- Concurrent operations proceed WITHOUT consensus as long as sum(debits) ≤ balance
- Only on actual overspending: escalate to Tier 3
- Per-RESOURCE instance (not global) — resource owners choose their own COD participants
- **Latency: ~5 RTT (non-conflicting), escalation on conflict**

### Tier 3: Ordered (Cordial Miners, requires 2n/3 ordering nodes online)

- Actual conflicts on shared resources (overspending detected)
- Multi-party atomics where parties are adversarial
- Global nullifier ordering (double-spend prevention for shared note pools)
- Membership changes (epoch transitions)
- **Latency: 3 rounds (good case), needs always-on ordering nodes**

## Data Structure: Blocklace

Replace independent linear peer chains with a unified DAG:

```rust
struct Block {
    identity: SignedHash,      // signed hash of content (WHO created this)
    content: BlockContent,
}

struct BlockContent {
    payload: Payload,          // turn, attestation, membership vote, etc.
    predecessors: Vec<BlockId>,  // hash pointers to known blocks (WHAT I've seen)
}
```

Properties:
- Per-agent virtual chain (total order on each agent's blocks)
- Cross-agent DAG edges (causal ordering between agents)
- CRDT merge (union of block sets, closure-preserving)
- Equivocation detection (two incomparable blocks from same agent = proof of Byzantine)
- Offline operation (produce blocks locally, merge on reconnect)

## Finality Spectrum

| Threshold | Meaning | Use Case |
|-----------|---------|----------|
| 1 (self) | "I committed this" | Sovereign ops, local state |
| 2 (bilateral) | "We both agree" | Peer exchange, bilateral trades |
| n-f (quorum) | "Federation confirms" | Shared resources, nullifiers |
| All (universal) | "Everyone has seen this" | Root anchoring, checkpoints |

No mode switch. Same data structure, same protocol. Just different acknowledgment thresholds.

## Ordering Node Architecture

"Ordering nodes" are the always-on quasi-permissionless participants (Lewis-Pye requirement):

- Cloud-hosted, professionally operated
- Provide Cordial Miners ordering for Tier 3
- Provide COD quorum for Tier 2
- Provide root anchoring for checkpoints
- Subscribe model: agents choose which ordering nodes to trust for their shared resources

Phones/laptops are NOT ordering nodes. They're sovereign participants that produce blocks in the blocklace and consume ordering when needed.

## Migration from Morpheus

1. **Phase 1 (now):** Solo mode with tentative receipts (being implemented)
2. **Phase 2:** Blocklace data structure as the gossip substrate (replaces linear peer chains)
3. **Phase 3:** Cordial Miners tau function for ordering (replaces Morpheus view/QC mechanism)
4. **Phase 4:** COD layer for optimistic shared-resource access (new tier)
5. **Phase 5:** Constitutional amendment for membership governance (replaces fixed threshold)

## Safety Under Adversary Majority

From the adversary majority paper: STARK proofs give us t^S = 1 (unconditional safety).

If the federation is compromised:
- Safety: PRESERVED (STARK proofs are unforgeable regardless of who the validators are)
- Liveness: LOST (can't get new ordering/finality)
- Detection: AUTOMATIC (blocklace shows equivocation)
- Response: FREEZE (preserve last known-good state, alert users)
- Recovery: Governance reconstitutes federation (out-of-band)

Users' existing proofs, state commitments, and capability chains remain valid forever.

## What `dregg` Adds Over Shapiro

Shapiro's program has ZERO privacy and NO proof-carrying data. `dregg` adds:

1. **ZK proofs on every block** — state transitions are PROVEN correct, not just signed
2. **Privacy** — amounts, identities, predicates all hideable (Pedersen, stealth, garbled)
3. **Capability security** — fine-grained authorization with attenuation and facets
4. **Confidential conservation** — no inflation provable without revealing balances
5. **Effect VM** — prove arbitrary multi-effect turns in one STARK
6. **Cross-proof-system composition** — same program provable via STARK, Plonky3, or Kimchi

## Implementation Priority

1. ✅ Solo mode (tentative receipts, single-node progress)
2. ✅ Effect VM (multi-effect turns in one STARK)
3. ✅ Three production provers (STARK + Plonky3 + Kimchi)
4. 🔲 Blocklace data structure (replace linear PeerStateTransition chains)
5. 🔲 Cordial Miners tau ordering (replace Morpheus)
6. 🔲 COD for optimistic shared resources (new tier 2)
7. 🔲 Constitutional amendment for membership
8. 🔲 Formal "grassroots" property proof
