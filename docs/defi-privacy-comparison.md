# Pyana vs Zcash/Namada: DeFi and Privacy Capability Comparison

## Note Model Comparison

| Feature | Zcash Orchard | Namada MASP | Pyana |
|---------|--------------|-------------|-------|
| Commitment | hash(value, rcm, pk_d, rho) | Zcash-derived, multi-asset | H(owner, fields[8], randomness, creation_nonce) |
| Nullifier derivation | PRF(nsk, rho) | Same as Zcash | H(commitment, spending_key, creation_nonce) |
| Value commitments (Pedersen) | Yes (homomorphic) | Yes | **NO** |
| Binding signature | Yes | Yes | **NO** |
| Multi-asset | No (one pool per asset) | Yes (shared pool) | Yes (fields[0] = asset_type, fields[1] = amount) |
| Merkle membership | Incremental tree | Incremental tree | Poseidon2 4-ary tree, STARK proof |
| Spending proof | Groth16/Halo2 | Groth16 | FRI-based STARK (BabyBear field, 248-bit key) |
| Conservation enforcement | In-circuit via value commitments | Same | **Executor-side sum check** (cleartext in witness) |

## What Pyana HAS

**Private transfers (partial):** Notes hide sender, receiver, and amount from observers. The STARK proof proves spending authority + Merkle membership without revealing note contents. Nullifiers are federation-independent (same note = same nullifier regardless of tree position).

**Multi-asset notes:** `fields[0]` = asset_type, `fields[1]` = amount. Conservation checked per asset_type across all NoteSpend/NoteCreate effects in a turn.

**Cross-federation bridging:** Two-phase conditional lock protocol with Ed25519 receipts. Destination binding prevents cross-federation replay. Portable proofs carry their own verification.

**Intent-centric exchange:** The intent/fulfillment system supports multi-party composition. Actions use `CommitmentMode::Partial` so each party signs their fragment independently. A coordinator assembles fragments into an atomic turn. Fulfillment supports Private/Selective/Trusted verification modes.

**Cell programs as validity predicates:** `CellProgram::Predicate` with `SumEquals`, `FieldGte`, `FieldLte`, `Immutable` constraints. `CellProgram::Circuit` requires ZK proof for state transitions. Analogous to Namada's validity predicates.

**Atomic multi-party turns:** 2PC coordination (coord/atomic) for all-or-nothing commitment of shared call forests. Mina-style excess tracking ensures conservation across balance changes.

## What is MISSING

### For Full Zcash Parity

1. **No Pedersen/homomorphic value commitments.** Conservation is checked by the executor summing cleartext values from NoteSpend/NoteCreate effects. The prover reveals asset_type and value to the executor. This is a major privacy gap: the executor (block producer) sees amounts.

2. **No binding signatures.** Zcash uses binding sigs to prove the prover chose value commitments that actually sum to zero. Without this, pyana relies on the executor to enforce conservation rather than proving it in-circuit.

3. **No encrypted memos / in-band secret distribution.** When Alice sends Bob a note, Bob needs to learn the note's opening (randomness, creation_nonce) to later spend it. Zcash uses encrypted memo fields derivable from Bob's viewing key. Pyana has no protocol for this -- out-of-band delivery is assumed.

4. **No viewing keys.** No mechanism for selective disclosure to auditors without revealing spending authority.

### For Anoma/Namada Parity

5. **No shared anonymity set (MASP-style).** Privacy is per-federation note tree. Each federation has its own tree, so the anonymity set = notes in that federation. Cross-federation bridging reveals asset_type and value in the PortableNoteProof.

6. **No solver infrastructure.** The intent system has matching and fulfillment but no solver marketplace, no solver incentive mechanism, and no protocol for solvers to compete on fill quality.

7. **No partial fills.** The current intent fulfillment is all-or-nothing. An intent for "sell 100 ETH" cannot be filled in parts by multiple counterparties.

### For AMM/DEX

8. **No pool abstraction.** An AMM pool would need to be modeled as a cell with: `fields[0..1]` = reserve_A, `fields[2..3]` = reserve_B, `fields[4]` = LP supply, `fields[5]` = fee_bps, etc. The 8-slot x u64 state is tight but sufficient for constant-product. However, there is no built-in swap invariant -- you would need a `CellProgram::Circuit` proving `new_x * new_y >= old_x * old_y`.

9. **No private swaps against a pool.** Because conservation is checked in cleartext by the executor, a swap would reveal both input and output amounts. Private AMM requires proving the swap satisfies the invariant inside a ZK circuit without revealing reserve state to observers.

10. **No fee accrual mechanism.** LP token minting/burning and fee distribution would need to be built entirely from raw cell programs and note effects.

## Gap Severity for Target Use Cases

| Use Case | Severity | Blocking Issue |
|----------|----------|----------------|
| Private P2P transfer (fixed counterparty) | Medium | Missing memo field (#3) -- workaround via side channel |
| Private multi-asset transfer | High | Executor sees amounts (#1); no shared anonymity set (#5) |
| Intent-mediated exchange (Anoma-style) | Medium | No partial fills (#7), no solver market (#6) |
| AMM / DEX pool | High | No private swaps (#9), tight state slots (#8) |
| Fully private DeFi | Critical | Value commitments (#1) + binding sigs (#2) needed first |

## Recommended Priority

1. **Value commitments + in-circuit conservation** -- prerequisite for everything else. Move conservation proving into the NoteSpendingAir so the executor never sees amounts.
2. **Encrypted memos** -- needed for any self-service transfer flow.
3. **Pool cell program template** -- constant-product circuit proving swap validity.
4. **Partial fill support in intent matching** -- enable solver competition.
5. **MASP-style shared tree** -- merge all asset types into one anonymity pool.
