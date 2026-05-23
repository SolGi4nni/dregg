# Decentralized Uptime Attestation Protocol

## Architecture: Hybrid VDF + Attestor Swarm

Two layers, each mapped to existing pyana primitives:

**Layer 1 (Liveness):** Worker produces a sequential Poseidon2 hash chain via `prove_ivc_stark`. Each step: `h_n = Poseidon2(h_{n-1} || block_height || worker_nonce)`. Gaps in the chain are provable downtime. No trust assumptions -- missing a link requires finding a Poseidon2 preimage (infeasible).

**Layer 2 (Quality):** Attestor swarm measures latency, throughput, capability. Commit-reveal prevents copying. Threshold consensus + challenge-response resolves disputes.

## Primitive Mapping

| Component | Pyana Primitive |
|-----------|----------------|
| Worker registration | Sovereign cell + `CreateObligation` (worker stake) |
| Attestor registration | Sovereign cell + `CreateObligation` (attestor stake) |
| VDF chain | `prove_ivc_stark` / `StateTransitionAir` -- already sequential Poseidon2 |
| Quality measurements | `TemporalPredicateAir` rolling accumulator (value=latency, window=32 blocks) |
| Slash trigger | `SlashObligation` gated by non-revocation proof of conflict |
| Attestor exclusion | `NonRevocationAir` -- add dishonest attestor to revocation tree |
| Challenge-response | Wire protocol request/response with blake3 domain-separated signatures |

## Protocol Lifecycle

### 1. Registration

Worker deploys a temporal accumulator program via `ProgramRegistry::deploy` with `trace_width: 42` (the GPU SLA accumulator from `design-temporal-accumulation`). Stakes via `CreateObligation { stake: MIN_WORKER_STAKE, conditions: slash_on_fraud }`.

Attestors register similarly: `CreateObligation { stake: MIN_ATTESTOR_STAKE, conditions: slash_on_dishonesty }`. Each attestor's sovereign cell stores their signing key commitment.

### 2. Each Block: Worker Extends VDF

Worker produces one IVC step. The `extend_accumulated_hash_wide` function chains: `new_hash = Poseidon2(old_hash || new_root || step_count)`. This feeds `prove_ivc_stark` which compresses N steps into one STARK proof. A missing step is detectable by anyone verifying the chain via `verify_ivc_stark`.

### 3. Each Block: Attestor Swarm Probes

**Commit phase:** Each attestor in the active set (selected by `hash(block_height || attestor_id) mod N < K`) probes the worker over the wire protocol. They commit `blake3("pyana-wire attestation-commit-v1" || measurement || attestor_secret)` on-chain.

**Reveal phase (next block):** Attestors reveal their measurement. The temporal accumulator ingests external measurements: the `value` column receives attested latency, not self-reported.

K-of-N attestors probe per block (K=3, N=total attestors for this worker). Selection is deterministic from block hash -- attestors cannot choose when they probe.

### 4. Dispute Detection

Two conflict types:

**Type A -- VDF gap:** Worker's IVC chain skips step S. Anyone calls `verify_ivc_stark` and sees `step_count` jumps. Automated: no dispute needed. Worker's temporal accumulator records a zero (downtime) for the missing window.

**Type B -- Attestor disagreement:** Attestor A says "down at block B" but attestors B,C say "up at block B" AND the worker's VDF chain includes block B's step. Resolution algorithm:

1. Worker produces signed challenge-response: wire protocol response with timestamp in the disputed window (domain key `"pyana-wire challenge-response-v1"`).
2. If worker produces valid response AND VDF chain is unbroken: attestor A is lying.
3. If worker cannot produce response AND VDF chain is broken: worker was down, honest attestors (B,C) who said "up" are lying.
4. If VDF chain is intact but no challenge-response exists: ambiguous (network partition). No slash; record as "contested" in the accumulator.

### 5. Slash Execution

On fraud proof: `SlashObligation { obligation_id: liar.obligation }`. Stake transfers to the harmed party (worker if attestor lied about downtime; attestor pool if worker colluded). The liar's attestor ID is added to the `NonRevocationAir` revocation tree -- they can no longer pass the non-revocation check required to submit attestations.

### 6. Rewards

Honest attestors earn fees from worker subscription payments (via `FulfillObligation` on the attestation service obligation). Fee per block = `worker_subscription / (blocks_per_epoch * K)`.

## Data Availability Sampling Analysis

With K=3 attestors per block from a pool of N=20:

- Probability a single corrupt attestor is selected for a given block: `3/20 = 0.15`
- For a corrupt majority in one block (2-of-3 corrupt), need 2+ from a corrupt set of size C: `P = C(C,2)*C(N-C,1) / C(N,3) + C(C,3)/C(N,3)`
- With C=3 corrupt out of N=20: P(2+ corrupt selected) = `(3*17 + 1) / 1140 = 0.046`
- Over 100 blocks, probability of never getting caught fabricating: `0.046^100 ~ 10^{-134}`

Even a single block with an honest majority catches fraud. The commit-reveal prevents the corrupt minority from adapting their reports to match the majority after seeing results.

## Key Property

The VDF layer makes liveness self-proving and unforgeable (computational security reducible to Poseidon2). The attestor layer only needs to prove SERVICE QUALITY -- a strictly easier problem because disagreements can be resolved by challenge-response. Slashing only applies to quality attestation fraud, where evidence is unambiguous.
