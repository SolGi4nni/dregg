# Trustless Intent Solving Protocol

## Overview

A 7-layer protocol for fully decentralized, verifiably fair intent matching. No trusted executor, no commit-reveal half-measures, no hardware trust assumptions.

**Goal**: A system where no party can front-run, no party can censor, the solution is provably valid, and settlement is atomic.

**Implementation**: `intent/src/trustless.rs`

## Protocol Architecture

```
Layer    Name           State Transition           Duration
------   -----------    ----------------------     --------
  1      SUBMIT         -> Collecting              ongoing
  2      BATCH          Collecting -> AwaitingDecrypt   instant (consensus)
  3      DECRYPT        AwaitingDecrypt -> Solving  ~2-5 seconds (ceremony)
  4      SOLVE          Solving -> Challenging      race period
  5      PROVE          (within SOLVE)              ~100ms per ring
  6      SELECT         Challenging                 5 waves (~10-15s)
  7      SETTLE         Challenging -> Settled      instant (atomic)
```

## Detailed Protocol

### Layer 1: SUBMIT (Encrypted Intent Broadcast)

**Flow:**
```
Creator -> Encrypt(intent, federation_threshold_key) -> Gossip(encrypted_intent)
```

The intent creator encrypts their intent to the federation's threshold public key using the infrastructure from `federation/src/threshold_decrypt.rs`. The encrypted blob is broadcast via gossip. A `CommitmentId` is attached for deduplication but reveals nothing about the intent contents.

**What gets broadcast:**
```rust
EncryptedIntent {
    ciphertext: threshold_encrypt(serialize(intent), epoch_key),
    creator_commitment: CommitmentId::random(),
    submitted_at: current_height,
}
```

**Why threshold encryption, not individual validator keys:**
- No single validator can decrypt (no information advantage)
- The decryption ceremony is collective (t-of-n)
- If a validator goes offline, others can still decrypt

### Layer 2: BATCH (Consensus-Determined Boundary)

**Flow:**
```
Blocklace finality at height H -> close_batch(H)
```

Every `batch_interval` waves (default 10), the blocklace's finality mechanism determines a batch boundary. This is NOT arbitrary -- it follows directly from the consensus ordering in `blocklace/src/ordering.rs`. The exact set of intents in this batch is determined by which encrypted intents have achieved finality before height H.

**Determinism guarantee**: Two honest nodes with the same view of the blocklace will compute the same batch boundary and the same set of included intents. This is inherited from Cordial Miners' finality properties.

### Layer 3: DECRYPT (Threshold Ceremony)

**Flow:**
```
For each validator v_i (i in 1..n):
    share_i = produce_decryption_share(batch_ciphertexts, key_share_i)
    broadcast(share_i)

When |collected_shares| >= threshold:
    key = combine_shares(collected_shares, threshold)
    for each encrypted_intent in batch:
        plaintext = decrypt(encrypted_intent, key)
    set_decrypted_intents(plaintexts)
    -> transition to Solving
```

Uses the existing Shamir-over-GF(256) scheme from `federation/src/threshold_decrypt.rs`. The MAC-verified shares prevent malicious validators from corrupting the decryption.

**Simultaneity**: All intents in the batch become readable at the same moment (when the threshold is reached). No validator has a head start on reading them.

### Layer 4: SOLVE (Open Competition)

**Flow:**
```
Anyone (solver S):
    intents = read_decrypted_batch()
    solution = find_rings(intents)  // using Johnson's algorithm from solver.rs
    -> submit_solution(solution, bond)
```

This is a PUBLIC optimization problem. The decrypted intents are visible to all. Anyone can run the ring trade solver. This creates a competitive market for solver quality (like Anoma's solver market, but without the front-running risk because intents were hidden until this moment).

**Incentive**: Solvers compete for a fee share from the settlement. Better solution = higher fee.

### Layer 5: PROVE (STARK Validity Proof)

**Flow:**
```
Solver S:
    proof = prove_stark({
        rings_valid: all quantities match, constraints satisfied,
        score_correct: total_score == sum(ring.score for ring in solution),
        no_double_use: each intent_id appears in at most one ring,
        batch_binding: all intent_ids exist in the decrypted batch,
    })
    submit_solution(solution, proof, bond)
```

The proof does NOT need to show optimality (NP-hard). It proves VALIDITY and correct SCORING. The challenge mechanism (Layer 6) handles optimality incentives.

**Integration with circuit/**: The validity proof uses the same STARK infrastructure from `circuit/src/stark.rs` and `circuit/src/plonky3_prover.rs`. The AIR for ring validity is a composition of:
- Conservation constraints (sum of inputs = sum of outputs per asset)
- Uniqueness constraints (each intent used at most once)
- Score computation (arithmetic constraint on accumulated score)

### Layer 6: SELECT (Challenge Window)

**Flow:**
```
After first valid solution S1:
    -> transition to Challenging
    challenge_start = current_height

During window [challenge_start, challenge_start + challenge_window]:
    Any solver can submit S2 where S2.score > S1.score
    If valid: S2 replaces S1, S1's solver loses bond

After challenge_start + challenge_window:
    Winning solution is final
    -> finalize()
```

**Bond mechanics:**
- Every solver posts `min_solver_bond` with their submission
- If a challenger submits a higher-scoring valid solution, the original solver's bond is slashed (they should have tried harder)
- Unchallenged winners get their bond back + fee
- This creates a strong incentive to submit the best solution you can find

### Layer 7: SETTLE (Atomic Compound Turn)

**Flow:**
```
finalize():
    compound_turn = generate_settlements(winning_solution)
    commit_to_blocklace(compound_turn)
    -> all legs execute or none do
```

The winning solution's ring trades are converted into a `CompoundTurn` -- a set of `SettlementAction`s that form a single atomic operation. This uses the same atomic execution semantics as `turn/src/composer.rs` (the `TurnComposer` pattern) but generated programmatically from the solver output.

**Atomicity**: If any leg of the settlement fails (e.g., a cell has been modified between solve and settle), the entire compound turn is rejected. No partial execution.

## Security Analysis

### Layer-by-Layer Adversary Model

| Layer | Adversary Action | Defense |
|-------|-----------------|---------|
| SUBMIT | Front-run by reading intents early | Threshold encryption -- need t-of-n validators to decrypt |
| SUBMIT | Sybil spam (flood with fake intents) | Stake proof requirement (existing `StakeProof` infrastructure) |
| BATCH | Manipulate which intents enter the batch | Consensus-determined boundary -- would need to control consensus |
| BATCH | Backdate intents (submit after seeing others) | Batch boundary is final -- late arrivals go to next batch |
| DECRYPT | Withhold decryption share (DOS) | Only t-of-n needed; liveness survives n-t failures |
| DECRYPT | Submit bad share (corrupt decryption) | Share MAC verification (existing in threshold_decrypt.rs) |
| SOLVE | Submit invalid solution | STARK proof verification rejects invalid solutions |
| SOLVE | Claim inflated score | Score verified against ring scores in proof |
| SELECT | Intentionally submit suboptimal solution | Challenge window + bond slashing incentivizes best effort |
| SELECT | Front-run challengers | Challenge window is fixed duration, not first-come ordering |
| SETTLE | Double-spend between solve and settle | Atomic execution -- either all legs succeed or none |
| SETTLE | Censor the settlement | Consensus liveness -- same as any other turn |

### Collusion Scenarios

**Scenario**: t validators collude to decrypt early.
- **Impact**: They can front-run by seeing intents before others.
- **Mitigation**: t is typically > n/2, so this requires majority collusion (which would already break consensus). Choose t = ceil(2n/3) + 1 for alignment with BFT threshold.

**Scenario**: Solver colludes with a subset of validators.
- **Impact**: The solver could see some intents early (from validators who share their view).
- **Mitigation**: The solver still can't decrypt without t shares. Individual validators only see ciphertext.

**Scenario**: All solvers coordinate to submit suboptimal solutions.
- **Impact**: Users get worse matches than theoretically possible.
- **Mitigation**: Open competition -- anyone can become a solver. The challenge mechanism means a single honest solver breaks the cartel.

### Comparison to t-of-n Trust Assumption

The threshold encryption means we trust that fewer than t validators collude. This is the SAME trust assumption as the consensus layer itself (Cordial Miners requires 2/3 honest validators). So the solving protocol adds NO ADDITIONAL trust assumptions beyond what the blocklace already requires.

## Performance Analysis

### Latency Breakdown (per batch)

| Phase | Duration | Bottleneck |
|-------|----------|-----------|
| Collect | ~10 waves (~20-30s) | Configurable, trades latency for batch size |
| Decrypt ceremony | ~2-5s | Network round for t share messages |
| Solve | ~100ms-2s | Depends on batch size and ring complexity |
| Prove | ~100-500ms | STARK proving (one proof per solution submission) |
| Challenge window | ~5 waves (~10-15s) | Configurable safety margin |
| Settle | <100ms | Single atomic commit |
| **Total** | **~35-55 seconds** | End-to-end latency per batch |

### Throughput

- Batch size: up to 256 intents (configurable via `MAX_INTENTS_PER_BATCH`)
- Ring solver complexity: O(V + E)(C + 1) for Johnson's algorithm, bounded by `max_ring_size`
- Multiple batches can pipeline (batch N solving while batch N+1 collects)
- STARK proving is parallelizable across rings within a solution

### Proving Cost

For a typical batch of 100 intents with 10-20 discovered rings:
- Ring validity: ~50ms per ring (conservation + uniqueness AIR)
- Total score computation: ~10ms
- Batch binding: ~20ms (Merkle proof against decrypted intent set)
- Estimated total proving time: ~600ms-1.2s

## Comparison to Existing Systems

### vs. Anoma Solver Market

| Aspect | Anoma | `dregg` Trustless |
|--------|-------|----------------|
| Intent visibility | Public to solvers immediately | Encrypted until batch decrypt |
| Front-running | Possible (solver sees before execution) | Impossible (threshold encryption) |
| Solver competition | Open market, reputation-based | Open market + STARK proofs + challenge |
| Settlement | Balanced transactions via validity predicates | Atomic compound turns via TurnComposer |
| Optimality guarantee | None (reputation incentive only) | Challenge window with bond slashing |

### vs. Flashbots SUAVE

| Aspect | SUAVE | `dregg` Trustless |
|--------|-------|----------------|
| Privacy mechanism | SGX enclaves (hardware trust) | Threshold encryption (crypto trust) |
| Ordering fairness | Block builder has ordering power | Consensus-determined batch boundary |
| Trust assumption | Intel SGX not compromised | t-of-n validators honest (same as consensus) |
| MEV protection | Encrypted mempool in TEE | Encrypted intents + batch auction |

### vs. CoW Protocol (Ethereum)

| Aspect | CoW Protocol | `dregg` Trustless |
|--------|-------------|----------------|
| Batch auction | Yes (fixed intervals) | Yes (consensus-determined intervals) |
| Solver trust | Reputation + governance | STARK proofs + economic incentives |
| Settlement | On-chain (gas costs) | Blocklace (no gas, atomic turns) |
| Privacy | Intents visible to solvers | Intents encrypted until batch decrypt |
| Challenge | Off-chain reputation only | On-chain challenge window with bond |

## Integration with Existing Infrastructure

### CapTP Integration

Settlements from the trustless engine generate capability transfers. When a ring trade settles, each participant's cell receives a capability token for the assets they acquired. This flows through the existing bearer capability infrastructure:

```
Ring settlement -> CompoundTurn -> TurnComposer -> Action(deposit) with capability token
```

### Storage Integration

Settled batches are archived in the federation's state. The `settled_batches` map provides an audit trail. Each `CompoundTurn` is committed to the blocklace as a first-class turn.

### Bridge Integration

Cross-federation intents (e.g., swap `dregg`-native asset for a Midnight-bridged asset) compose with the conditional turn mechanism from `turn/src/conditional.rs`:

```
1. Batch includes an intent referencing a bridged asset
2. Solution's settlement generates a ConditionalTurn
3. Condition: proof of bridge attestation from Midnight
4. If bridge proof arrives before timeout -> settlement executes
5. If timeout -> settlement reverts (no asset movement)
```

### Dispute Integration

If a solver's proof is later found to be invalid (e.g., a bug in the mock verifier used during testing), the dispute mechanism from `app-framework/src/dispute.rs` can be used to retroactively slash the solver's bond and potentially revert the settlement.

## Configuration

```rust
TrustlessIntentEngine {
    batch_interval: 10,         // waves between batches
    challenge_window: 5,        // waves for challenges
    min_solver_bond: 1000,      // minimum bond in computrons
    decrypt_threshold: 3,       // t-of-n for threshold decryption
    num_validators: 5,          // n validators in federation
}
```

## Future Work

1. **VDF timestamp proofs**: Add Verifiable Delay Function proofs to encrypted intents to prevent backdating/ordering manipulation within a batch.
2. **Real STARK verifier**: Replace `MockProofVerifier` with a real STARK verification circuit that checks ring validity, score computation, and uniqueness.
3. **Solver fee market**: Implement a proper fee auction where the winning solver's fee is determined by the second-best solution's score (Vickrey-style).
4. **Partial decryption**: Allow intents to specify which fields are encrypted vs. public (e.g., asset type public but amount hidden), enabling pre-filtering before full decryption.
5. **Recursive proof composition**: Use recursive STARKs to compose individual ring proofs into a single batch proof (reducing verification cost for large solutions).
6. **Cross-batch intent carry-over**: Intents not matched in one batch automatically roll into the next (with expiry check).
