# Anonymous Cross-Federation Bridging

## Problem

The current bridge reveals source federation identity. `PortableNoteProof.source_root` is checked against `trusted_roots` -- the destination learns exactly which federation produced the note. Combined with low bridge volume, this can deanonymize the sender.

## Approach: Federation-Ring STARK with Pedersen Re-blinding

We combine two existing primitives at a new level:

1. **BlindedMerklePoseidon2StarkAir** (ring membership over issuers) -- extended to ring membership over *federation roots*
2. **Pedersen value commitments** (homomorphic, re-blindable) -- used to break the value link between source and destination

The core idea: the spending proof demonstrates membership in a *set* of federation roots without identifying which one, and the value is transferred as a re-randomized commitment that cannot be correlated with the source lock.

## Data Structures

```rust
/// The anonymous bridge proof. Replaces PortableNoteProof for privacy-preserving bridges.
struct AnonBridgeProof {
    /// Nullifier (proves spend happened somewhere).
    nullifier: [u8; 32],
    /// Destination federation binding (prevents replay -- same as current design).
    destination_federation: [u8; 32],
    /// STARK proof of valid spend against ONE of N federation roots (ring).
    /// Public inputs: [blinded_root, ring_root, destination_federation, nullifier_hash]
    /// Private witness: actual source root, blinding, Merkle path in ring tree.
    ring_spend_proof: Vec<u8>,
    /// The "ring tree root" -- a Poseidon2 Merkle root over ALL trusted federation roots.
    /// Published periodically by each federation (or a shared bulletin board).
    federation_ring_root: [u8; 32],
    /// Pedersen commitment to bridged value: commit(v, r_dest) on asset-specific generator.
    value_commitment: [u8; 32],
    /// Range proof that committed value is in [0, 2^64). Bulletproofs over Ristretto.
    range_proof: Vec<u8>,
    /// New note commitment for the destination (unchanged from current design).
    destination_commitment: [u8; 32],
}
```

```rust
/// The federation ring tree: a Merkle tree whose leaves are the note_tree_roots
/// of all trusted federations. Updated each epoch.
struct FederationRingTree {
    /// Poseidon2 Merkle root over leaves = [fed_1.note_tree_root, ..., fed_N.note_tree_root]
    root: [u8; 32],
    /// Epoch number (ring tree is versioned).
    epoch: u64,
    /// Leaf count (padded to power of 4 for the arity-4 Poseidon2 tree).
    leaf_count: usize,
}
```

## Protocol Flow

### Setup (periodic, per epoch)

Each federation publishes its current `note_tree_root`. A **bulletin board** (can be any federation's chain, a shared L1 anchor, or gossip protocol) collects these and builds the `FederationRingTree`. Every federation that wants to accept anonymous bridges imports this ring root.

Trust assumption: each federation independently verifies the ring tree construction (it only needs the list of roots it trusts and can rebuild locally). No central authority.

### Phase 1: Lock (Source Federation)

1. Sender picks a note to bridge, computes nullifier.
2. Sender creates a Pedersen commitment: `C_source = commit(v, r_source)` where `v` is the note value.
3. Source federation locks the note (same as `initiate_bridge` today) but stores `C_source` instead of cleartext value.
4. The lock is local -- no information leaves the source federation yet.

### Phase 2: Prove (Sender, offline)

The sender constructs `AnonBridgeProof`:

1. **Ring spend proof** (new circuit: `FederationRingSpendAir`):
   - Private witness: source federation's `note_tree_root`, Merkle path in the ring tree, note Merkle path within that federation, spending key, blinding factor.
   - Public inputs: `[blinded_federation_leaf, federation_ring_root, destination_federation, nullifier_commitment]`
   - Constraints: (a) note membership in source federation's tree, (b) source federation root membership in ring tree, (c) blinded_federation_leaf = hash(actual_root, blinding), (d) valid spend (nullifier derived correctly from spending key + note data), (e) destination binding.
   - This is a composition of the existing `NoteSpendingAir` with a `BlindedMerklePoseidon2StarkAir` over the ring tree. The blinding factor makes the federation leaf unlinkable across presentations.

2. **Value re-blinding**: sender picks fresh `r_dest`, constructs `C_dest = commit(v, r_dest)`. The ring spend proof additionally constrains that the committed value matches the note's value (private check inside the STARK: `v` is witness, commitment is derived).

3. **Range proof**: standard Bulletproof over `C_dest` proving `v >= 0`.

### Phase 3: Claim (Destination Federation)

Destination receives `AnonBridgeProof` and verifies:

1. `destination_federation` matches local identity.
2. `federation_ring_root` is a known ring root (from a recent epoch).
3. Ring spend STARK verifies against `[blinded_federation_leaf, federation_ring_root, destination_federation, nullifier_commitment]`.
4. Bulletproof range proof verifies over `value_commitment`.
5. Nullifier not in `BridgedNullifierSet`.

On success: mint a new note with commitment `destination_commitment`, insert nullifier into bridged set, sign a receipt.

### Phase 4: Finalize (Source Federation)

Source receives receipt, finalizes the lock (same as today). The receipt references only the nullifier -- the source federation already knows which bridge this corresponds to.

## What the Destination Sees vs Does Not See

| Information | Visible? | Why |
|---|---|---|
| Source federation identity | NO | Hidden by ring membership (blinded leaf in ring tree) |
| Sender identity within source | NO | Hidden by note spending proof (existing property) |
| Exact value transferred | NO | Hidden by Pedersen commitment + range proof |
| Which note was spent | NO | Nullifier is unlinkable to commitment (existing property) |
| Destination federation | YES | Required for replay prevention |
| That a bridge occurred | YES | The proof type is identifiable |
| Ring tree epoch | YES | Needed for verification (limits timing window) |
| Nullifier (for double-spend prevention) | YES | Required for safety |

## Privacy Analysis

**Anonymity set**: all federations in the ring tree. With 50 trusted federations, the destination cannot narrow below 1-of-50 source federations. With 1000, 1-of-1000.

**Timing attack**: the ring tree epoch constrains the time window. Larger epochs (more root updates batched) = better privacy but staler roots. Recommended: epoch = 1 hour, ring tree includes last 24 hours of roots (each federation contributes ~24 entries).

**Volume correlation**: if only one bridge happens per epoch, the anonymity set is 1 regardless of ring size. Mitigation: federations can inject decoy bridge proofs (dummy nullifiers that are pre-spent locally) to maintain minimum volume. Cost: one STARK proof per decoy.

## Performance

| Operation | Cost |
|---|---|
| Ring spend STARK (depth-8 ring tree + depth-8 note tree) | ~2x current spend proof (two Merkle paths) |
| Bulletproof range proof (64-bit) | ~700 bytes, ~1ms verify |
| Ring tree construction (50 federations, 24 epochs) | 1200-leaf Poseidon2 tree, trivial |
| Total proof size | ~15-20 KB (STARK dominates) |
| Verification | ~5ms (STARK) + ~1ms (Bulletproof) |

## Compatibility

- `FederationRingSpendAir` composes with the existing `BlindedMerklePoseidon2StarkAir` pattern -- same blinding technique, one level higher.
- Pedersen commitments are already implemented in `cell/src/value_commitment.rs` on Ristretto.
- The nullifier derivation is unchanged (federation-independent by design).
- Backward compatible: federations can accept both `PortableNoteProof` (non-anonymous) and `AnonBridgeProof` (anonymous) during migration.
- The bulletin board for ring tree roots can piggyback on existing federation gossip (`wire/src/server.rs` already handles cross-node communication).

## Trust Assumptions

1. **Ring tree integrity**: each federation independently verifies (no trust needed).
2. **Soundness**: STARK + Fiat-Shamir (computational, same as existing proofs).
3. **Hiding**: Pedersen commitment (discrete log on Ristretto), blinding factor (information-theoretic for ring membership).
4. **No collusion requirement**: even if all other federations collude, they cannot determine which one produced a given bridge proof (the blinding is local to the sender).
5. **Bulletin board liveness**: if the ring tree is not updated, bridges stall but no funds are lost (timeout cancel still works).
