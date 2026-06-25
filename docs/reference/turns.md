# Turns & the executor

The `dregg-turn` crate is the call-forest transaction model: the atomic unit of
agent execution, the effects it produces, and the executor that walks it,
authorizes it, applies it, and emits a chained receipt.

> Caveat (stated by the crate itself): `turn/src/lib.rs:3-27` declares this the
> **legacy dregg1 Rust executor** — hand-written, UNVERIFIED, and NOT the source
> of truth for dregg's semantics. The verified semantics live in Lean under
> `metatheory/Dregg2/`. This Rust executor remains load-bearing because the
> running node executes on it, "until the swap" to the verified Lean executor.
> The Lean executor runs as a *shadow* over this path (below).

## The unit: Turn → CallForest → CallTree → Action → Effect

A **`Turn`** is "the atomic unit of agent execution" (`turn/src/turn.rs:258-260`).
It carries an `agent: CellId`, a `nonce: u64`, a `call_forest: CallForest`, a
`fee: u64`, optional `memo`/`valid_until`, a `previous_receipt_hash`, a
`depends_on` list, and a set of proof/witness bundles (`conservation_proof`,
`sovereign_witnesses`, `execution_proof*`, `custom_program_proofs`,
`effect_binding_proofs`, `cross_effect_dependencies`, `effect_witness_index_map`)
(`turn/src/turn.rs:259-356`).

A **`CallForest`** is `roots: Vec<CallTree>` plus a lazily-computed
`forest_hash` (`turn/src/forest.rs:30-37`). Each **`CallTree`** is `{ action,
children: Vec<CallTree>, hash }` — a Merkle node whose hash commits to the action
and all descendants (`turn/src/forest.rs:15-24`, `forest.rs:74-90`). "The call
forest IS the transaction" (`turn/src/lib.rs:71-73`): authorization flows
parent→child via capability delegation, and the whole tree commits or rolls back
together.

An **`Action`** targets a cell, names a `method: Symbol` (a BLAKE3 hash of the
method name, `turn/src/action.rs:46-52`), carries `args`, an `Authorization`, a
`Preconditions` clause, a `Vec<Effect>`, a `DelegationMode`, a
`CommitmentMode`, an optional signed `balance_change: Option<i64>`, and
`witness_blobs` (`turn/src/action.rs:73-123`).

`Action::hash` (domain tag `dregg-action-v2:`) folds target, method, args, and
the authorization discriminant + data (`turn/src/action.rs:1442-1457`).
`Turn::hash` (domain tag `dregg-turn-v3:`) folds agent, nonce, the forest hash,
fee, memo, valid_until, depends_on, previous_receipt_hash, and the v3
execution-proof/witness bundle — every load-bearing field, so an in-flight
proof-swap is caught (`turn/src/turn.rs:375-454`, comment at `359-374`).

### Authorization

`Authorization` (`turn/src/action.rs:215-232`) is one of:
`Signature([u8;32],[u8;32])` (Ed25519 over the action hash), `Proof { proof_bytes,
bound_action, bound_resource }` (a ZK proof bound to an (action, resource) pair),
`Breadstuff([u8;32])` (a capability-token hash matched against the actor's c-list),
or `Bearer` (proof-carrying authorization that exercises a capability WITHOUT it
being in the actor's c-list).

`DelegationMode` (`turn/src/action.rs:830-845`): `None` (children cannot reach
other cells with the parent's caps); `ParentsOwn` and `Inherit` are TYPED but NOT
implemented — a cross-cell child under either is rejected fail-closed with
`DelegationModeUnimplemented` (`action.rs:833-840`); `SnapshotRefresh` (child
inherits a point-in-time snapshot of the parent's c-list, revocation eventual,
bounded by `max_staleness`).

## Effects: the 32 ledger mutations

`Effect` (`turn/src/action.rs:948-1403`) is the enum of "what changes in the
ledger." There are 32 variants. The real list:

- **State / book-keeping:** `SetField`, `IncrementNonce`, `EmitEvent`
  (logged in the receipt, no state change, `action.rs:969-970`).
- **Value:** `Transfer { from, to, amount }`, `Burn { target, slot, amount }`
  (provable supply reduction; sets the receipt's `was_burn` flag,
  `action.rs:1264-1279`), `Mint { target, slot, amount }` (cap-gated supply
  entry; debits the issuer well and credits the holder, conserving per-asset;
  placed LAST in the enum so the postcard discriminant of existing variants does
  not shift, `action.rs:1373-1402`).
- **Capability / authority:** `GrantCapability`, `RevokeCapability`,
  `AttenuateCapability` (monotone narrowing only — widening returns `None` and is
  rejected, `action.rs:1280-1296`), `ExerciseViaCapability` (the categorical
  eval map: c-list-slot lookup + inner effects in one step, `action.rs:1119-1130`).
- **Cell mutation / lifecycle:** `SetPermissions`, `SetVerificationKey`,
  `SetProgram` — the first two (and `SetProgram`) are applied LAST within an
  action, after all other effects, using permissions snapshotted before the
  action ran, to block weaken-then-exploit (`action.rs:980-1020`). Plus
  `CreateCell`, `CreateCellFromFactory`, `CellSeal`, `CellUnseal`,
  `CellDestroy` (binds a `DeathCertificate`, terminal), `MakeSovereign`,
  `ReceiptArchive`.
- **Delegation:** `SpawnWithDelegation`, `RefreshDelegation` (executor DERIVES
  the genuine snapshot and refuses a mismatching declaration, `action.rs:1077-1087`),
  `RevokeDelegation`.
- **Notes / cross-federation (privacy):** `NoteSpend` (reveals a nullifier +
  carries a STARK spending proof and optional Pedersen value commitment,
  `action.rs:1021-1044`), `NoteCreate`, `BridgeMint` (portable cross-federation
  note proof, `action.rs:1094-1104`).
- **Pipelining / introduction:** `Introduce` (three-party), `PipelinedSend`
  (dispatch to the result of a pending turn via an `EventualRef`, `action.rs:1113-1118`).
- **Refusal:** `Refusal` — the categorical dual: proof of *non-action* (evidence
  of absence) against an `offered_action_commitment`, verified via the
  `WitnessedPredicateRegistry`; bumps the target cell's nonce and records the
  refusal commitment + reason (`action.rs:1156-1226`).
- **Reactive (Track 2):** `Promise`, `Notify`, `React`. The soundness gift
  (`action.rs:1312-1372`): a promise-hole IS a nullifier; `React` SPENDS
  `pending_id` into the very same production `note_nullifiers` set `NoteSpend`
  uses, so a second react (or a replayed hole) is rejected by the identical
  double-spend gate.

### Linearity discipline

Every effect declares a `LinearityClass` via the exhaustive `Effect::linearity`
match — no `_ =>` arm, so a new variant cannot leave its conservation status
implicit (`turn/src/action.rs:855-862`, `1645-...`). Classes
(`action.rs:885-914`): `Conservative` (paired delta, sum zero — Transfer, the
NoteSpend/NoteCreate pair), `Monotonic` (counters up — IncrementNonce, Refusal),
`Terminal` (one-way — RevokeCapability, RevokeDelegation, CellDestroy,
MakeSovereign, ReceiptArchive, AttenuateCapability), `Generative` (ex nihilo —
Mint, CreateCell), `Annihilative` (Burn; receipt `was_burn` disclosure bound),
`Neutral` (no resource delta). `is_disclosed_non_conservation()` (Generative |
Annihilative) is the predicate the adversarial path uses to require a
`was_burn`/`was_mint` receipt disclosure (`action.rs:935-940`).

## The executor

`TurnExecutor` (`turn/src/executor/mod.rs:487`) holds the cost config, the
program registry, the chain clock (`current_timestamp`, `block_height`),
rate-limit counters, an optional proof verifier and budget gate, the trusted
federation roots / local federation id, the `bridged_nullifiers` and production
`note_nullifiers` sets (the permanent double-spend gates, `mod.rs:524-537`), the
`reactive_registry` (promise-hole store, `mod.rs:538-548`), fee routing cells
(`proposer_cell`/`treasury_cell`/`fee_well_cell`), the per-asset `issuer_wells`,
the factory registry, the per-agent `last_receipt_hash` and per-cell
`per_cell_receipt_head` chains, an optional executor signing key, and the
witnessed-predicate registry (`registry_with_real_verifiers` by default, since
`dregg-turn` links `dregg-circuit` and owns the real STARK verifiers,
`mod.rs:668-686`).

### `execute` — the sole entry point

`TurnExecutor::execute(&self, turn, &mut ledger) -> TurnResult`
(`turn/src/executor/execute.rs:152`) is "the sole entry point for all ledger
state mutations" (`execute.rs:145-148`). It wraps `execute_without_shadow` with
the Lean shadow (below), then returns one of `TurnResult::{Committed, Rejected,
Expired, Pending}` (`turn/src/turn.rs:599-615`).

`execute_without_shadow` (`execute.rs:285`) is the real pipeline:

1. **Admission / validation** (`execute.rs:303-411`): non-empty forest;
   not expired (`current_timestamp <= valid_until`); agent cell exists;
   `agent.state.nonce() == turn.nonce` or `NonceReplay`; balance covers the fee
   (signed balances — any negative reading refuses, `execute.rs:346-357`);
   agent not frozen for migration, and (only if any cell is frozen) no write-set
   cell frozen; **receipt-chain self-binding** — the agent's claimed
   `previous_receipt_hash` must equal the executor's stored head for that agent,
   else `ReceiptChainMismatch`; genesis turns use `None` (`execute.rs:394-411`).
2. **Budget gate** (Stingray): pre-flight `try_debit(fee)`; on later failure the
   debit is refunded via `fast_unlock` (`execute.rs:420-...`).
3. **Pre-state hash** = `ledger.root()` (or the deferred sentinel under symbolic
   witness mode, `execute.rs:451-460`).
4. **Phase 1 — fee + nonce, NEVER rolled back** (`execute.rs:465-491`): debit the
   fee and `increment_nonce()`. This is what stops DoS via
   expensive-but-failing turns: even a turn that fails its forest still pays and
   advances its nonce.
5. **Proof-carrying sovereign fast path** (`execute.rs:493-...`): if
   `turn.execution_proof.is_some()`, the executor does ZERO state interpretation
   — it verifies the STARK (`verify_and_commit_proof`) and updates one 32-byte
   sovereign commitment, then builds a self-contained receipt. This is the
   trust boundary (`lib.rs:44-47`): proof present ⇒ trustless; absent ⇒
   executor-trusted classical walk.
6. **Classical forest walk:** depth-first over the call trees; per action check
   preconditions, verify authorization, apply effects (`execute.rs:138-143`).

### Apply + journal (atomicity)

`apply_effect` (`turn/src/executor/apply.rs:27`) is the per-effect dispatch — a
`match` from each `Effect` variant to its `apply_*` handler. Mutations are
journaled into a `LedgerJournal`, an undo log: "On success, the journal is
dropped (zero cost); on failure, the journal is replayed in reverse to undo ALL
effects" (`turn/src/journal.rs:1-5`). `LedgerJournal::rollback` walks entries
`.rev()` and restores each (and crucially REMOVES any inserted nullifiers from
`note_nullifiers`/`bridged_nullifiers` so a rolled-back spend is re-spendable,
`journal.rs:293-...`, `mod.rs:530-536`). This gives all-or-nothing atomicity
without cloning the ledger.

### Receipt

On commit the executor builds a `TurnReceipt` (`turn/src/turn.rs:844-916`):
`turn_hash`, `forest_hash`, `pre_state_hash`, `post_state_hash`, `timestamp`,
`effects_hash`, `computrons_used`, `action_count`, `previous_receipt_hash`,
`agent`, `federation_id`, and the emitted records (`routing_directives`,
`introduction_exports`, `derivation_records` — capabilities the turn CREATES,
`turn.rs:872-875`; `emitted_events`), plus disclosure bits `was_encrypted`,
`was_burn`, the `consumed_capabilities` witnesses (the capabilities the turn
CONSUMED to authorize, with sorted-Merkle membership against the holder's
pre-state `capability_root`, `turn.rs:906-915`), an optional `executor_signature`,
and a `Finality`.

`effects_hash` = BLAKE3 fold over per-effect `Effect::hash` values, returning
`[0;32]` for an empty list (`turn/src/executor/finalize.rs:484-493`).
`receipt_hash` (domain tag `dregg-receipt-v3`, `turn.rs:921-1001`) binds every
field including the `was_encrypted`/`was_burn`/`consumed_capabilities`
disclosures, so a malicious executor cannot strip or forge them. The executor's
narrower signed message binds the full receipt hash (`turn.rs:921`, v3 note at
`1034-...`).

### Receipt chain = persistence

"The `WitnessedReceipt` chain rooted at each turn IS dregg's persistence layer"
(`turn/src/turn.rs:6-32`): state is recoverable by replaying receipts; the
on-disk snapshot is a cache over this canonical stream; the database is the
cache, the receipt chain is the truth. Each receipt's `previous_receipt_hash`
chain-links it to the prior receipt; the executor enforces this AT WRITE TIME via
`last_receipt_hash` (`mod.rs:602-615`), and `verify::verify_receipt_chain`
checks it offline: genesis has no previous, then for each link agent
consistency, `curr.previous_receipt_hash == prev.receipt_hash()`, and
`curr.pre_state_hash == prev.post_state_hash` (`turn/src/verify.rs:117-177`).

## The verified-Lean shadow

`execute` is the seam where the verified Lean executor observes this Rust path.
`dregg-turn` is FFI-free and reaches the Lean side only through the
`ShadowObserver` trait (`turn/src/shadow.rs:111-141`), into which a native node
injects `dregg_exec_lean::LeanShadowObserver` (`lib.rs:18-24`). The Lean side is
the oracle; this Rust side is the subject under test (`lib.rs:24`).

Under **strict veto mode** (`shadow.rs:124`), `execute` snapshots the full
pre-state ledger before the Rust commit; if the verified Lean executor REJECTED a
turn the Rust executor COMMITTED, the Lean verdict VETOES it — the ledger is
restored to the pre-state (a verified rejection = no state edit) and the result
becomes `Rejected` with the Lean admission reason when one is present
(`execute.rs:168-211`). The verified kernel can only TIGHTEN the decision; it
never launders a Rust rejection into a commit (`execute.rs:181-185`).

The Lean twin of this forest executor is `execFullForestG`
(`metatheory/Dregg2/Exec/FullForestAuth.lean:530`), with theorems for
per-asset conservation (`FullForestAuth.execFullForestG_conserves_per_asset`),
exact conservation (`FullForestAuth.execFullForestG_conserves_exact`),
non-amplification (`FullForestAuth.execFullForestG_no_amplify`),
unauthorized-fails (`FullForestAuth.execFullForestG_unauthorized_fails`), and
per-edge / root attestation (`FullForestAuth.execFullForestG_each_attests`,
`...execFullForestG_root_attests`).
