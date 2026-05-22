# Pyana Protocol Sketch

## 1. State Model

**Global state** is a tuple `(L, N, T, R)` where:

- `L: CellId -> Cell` -- the ledger (map of all cells)
- `N: NullifierSet` -- append-only sorted set of revealed nullifiers (Merkle tree)
- `T: NoteTree` -- append-only commitment tree for private notes
- `R: AttestedRoot[]` -- finalized federation roots (height, merkle_root, quorum_sigs)

**Cell** = `(id, public_key, state, permissions, verification_key?, capabilities, program, token_id, delegation?)`

**CellState** = `(fields[8]: [u8;32], nonce: u64, balance: u64, proved_state: bool, field_visibility[8], commitments[8]?)`

Cell identity is content-addressed: `id = BLAKE3(public_key || token_id)`.

## 2. Actors

- **Agent**: owns a cell, submits turns (signed action forests). Pays fees in computrons.
- **Federation node**: participates in Morpheus consensus. Proposes/votes/finalizes blocks of state transitions. Maintains local ledger replica.
- **Verifier**: checks attested roots, non-membership proofs, and ZK proofs without full state.
- **Coordinator**: orchestrates multi-party atomic turns (2PC). Assembles partial forests, collects votes, issues commit/abort.

## 3. Authorization Rules

Each cell defines `permissions: Action -> AuthRequired` where `AuthRequired in {None, Signature, Proof, Either, Impossible}`.

```
authorized(action, cell) :=
  let req = cell.permissions.for_action(action.effect_type) in
  match req:
    None       -> true
    Impossible -> false
    Signature  -> verify_ed25519(cell.public_key, action.signing_message, action.sig)
    Proof      -> verify_zk(cell.verification_key, action.proof, action.bound_inputs)
    Either     -> Signature OR Proof
```

**Capability access**: To target a cell other than yourself, the actor must hold a non-expired, non-Impossible capability in their c-list referencing that cell.

**Attenuation-only delegation**: `grant(cap) valid iff granted.permissions.is_narrower_or_equal(held.permissions)`. No amplification.

**Breadstuff tokens**: Alternative auth path -- actor presents a capability token hash matching a capability in their c-list that is scoped to the target cell.

## 4. State Transition Rules

A **Turn** is the atomic unit: `(agent, nonce, fee, call_forest, valid_until?, previous_receipt_hash?)`.

### Preconditions (must hold before execution)

```
valid_turn(turn, L) :=
  turn.call_forest non-empty
  AND L[turn.agent] exists
  AND L[turn.agent].state.nonce == turn.nonce
  AND L[turn.agent].state.balance >= turn.fee
  AND (turn.valid_until is None OR now <= turn.valid_until)
```

Per-action preconditions (checked against target cell):
- `nonce == expected` (optional)
- `balance >= min_balance` (optional)
- `fields[i] == expected_value` (optional, per-slot)
- `block_height in [min_height, max_height]` (optional)
- `timestamp in [start, end]` (optional)

### Effects (what changes)

The call forest is walked depth-first. For each action node:

1. Check capability access (actor -> target)
2. Evaluate preconditions against target cell
3. Verify authorization (sig/proof/breadstuff)
4. Apply effects: `Transfer | SetField | CreateCell | GrantCapability | RevokeCapability | IncrementNonce | SetPermissions | SetVerificationKey | NoteSpend | NoteCreate | BridgeMint | BridgeLock | BridgeFinalize | BridgeCancel`
5. Apply balance_change (Mina-style excess tracking)
6. Enforce cell program (predicate constraints or circuit proof)
7. Recurse into children (delegation mode gates cross-cell targeting)

Phase separation: fee + nonce commit is NEVER rolled back (prevents DoS). Forest effects roll back atomically on any failure.

### Conservation Invariants

```
EXCESS: sum of all balance_changes across a turn == 0
NOTE_CONSERVATION: for each asset_type, sum(spent_note_values) == sum(created_note_values)
TRANSFER_CONSERVATION: Transfer(from, to, amount) debits from and credits to by exactly amount
FEE_DISTRIBUTION: fee -> 50% proposer + 30% treasury + 20% burned
```

### Cell Program Enforcement

- `CellProgram::None` -- any authorized change valid
- `CellProgram::Predicate(constraints)` -- post-state must satisfy all constraints (FieldEquals, FieldGte, FieldLte, SumEquals, Immutable)
- `CellProgram::Circuit{hash}` -- action must carry a valid ZK proof; proof verification IS the transition validity check

## 5. Coordination Protocol

**Layer 1 -- Causal Chaining** (cheap, async): Each turn carries hash-pointers to causally-prior turns, forming a DAG. Provides happened-before without global ordering.

**Layer 2 -- Atomic Multi-Party** (2PC):

```
Coordinator -> all Participants: Propose(AtomicForest)
  AtomicForest = (participants[], combined_forest, per_participant_preconditions[], initiator, fee)
  
Each Participant:
  validate forest structure
  check local preconditions against own ledger view
  if OK: sign(forest_hash || VOTE_YES) -> Coordinator
  else:  sign(forest_hash || VOTE_NO, reason) -> Coordinator

Coordinator:
  if all votes = Yes: Commit(receipt) -> all Participants
  if any vote = No:   Abort(reason) -> all Participants
```

All-or-nothing: the combined forest executes atomically or not at all. Partial signatures (CommitmentMode::Partial) allow parties to sign their fragment without seeing the full forest.

## 6. Federation Protocol

Morpheus-shaped BFT consensus with `n` nodes, tolerating `f = floor((n-1)/3)` faults. Threshold = `n - f`.

```
1. PROPOSE: rotating leader proposes a block (set of turns/revocations)
2. VOTE: each node validates the block, casts signed vote
3. FINALIZE: once threshold votes collected, form QuorumCertificate
4. STATE UPDATE: all nodes apply finalized block to local state
5. ATTESTED ROOT: (merkle_root, height, timestamp, quorum_sigs) published
```

**View changes**: if leader is faulty/offline, nodes advance the view (new leader = view mod n).

**Reconfiguration**: epoch transitions with explicit member set changes. New epoch inherits state but resets the leader schedule.

**Cross-federation bridging** (two-phase):
- BridgeLock: lock note on source federation (pending, not permanently spent)
- BridgeMint: mint on destination (requires STARK proof + trusted source root + destination binding)
- BridgeFinalize: source confirms destination receipt, permanently burns the note
- BridgeCancel: after timeout, source unlocks the note (no receipt received)

## 7. Privacy Protocol

| Data | Visibility |
|------|-----------|
| Cell id, public_key, nonce, balance | Public on-chain |
| Cell fields | Per-field: Public, Committed (hash only), or SelectivelyDisclosable |
| Note content (owner, fields, randomness) | Private -- only owner knows |
| Note commitment | Public (in note tree) |
| Nullifier | Public only when spent |
| ZK proof | Public (reveals nothing beyond statement validity) |
| Turn structure (who acted on which cell) | Public |
| Cross-cell capability graph | Public (c-list membership) |

**Progressive disclosure**: committed fields can be revealed selectively via ZK proofs without exposing the value. `proved_state` flag tracks whether all 8 fields were last set by a verified proof.

## 8. Liveness and Safety Properties

**Safety**:
- No double-spend: nullifier set is append-only; insertion of existing nullifier is rejected
- No value creation: excess must be zero; note conservation per asset type
- No privilege escalation: capabilities attenuate-only; permissions checked per-effect
- No cross-federation replay: signatures bind to federation_id; bridge proofs bind to destination
- Atomic rollback: any failure in the call forest reverts all effects (journal replay)
- Fee is always paid: nonce+fee commit before forest execution (DoS resistance)

**Liveness**:
- Requires `n - f` honest federation nodes for block finalization
- A turn can get stuck if: (a) preconditions never become satisfiable, (b) budget gate exhausted for the silo, (c) conditional turn times out
- Atomic multi-party turns abort if any single participant votes No (no partial commits)
- Bridge operations can time out: BridgeCancel reclaims locked value after timeout_height

**Fail-closed defaults**: no proof verifier configured -> all proof-auth actions rejected. No trusted roots -> all bridge mints rejected. Empty federation roots -> no cross-federation trust.
