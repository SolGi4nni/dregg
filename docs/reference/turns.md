# Turns & the executor

The `dregg-turn` crate is the call-forest transaction model: the atomic unit of
agent execution, the effects it produces, and the executor that walks it,
authorizes it, applies it, and emits a chained receipt.

> Caveat (stated by the crate itself): `turn/src/lib.rs:3-27` declares this the
> **legacy dregg1 Rust executor** — hand-written, UNVERIFIED, and NOT the source
> of truth for dregg's semantics. The verified semantics live in Lean under
> `metatheory/Dregg2/`. The verified Lean executor (`execFullForestG` via
> `dregg-lean-ffi`) is the **authoritative** state producer the node runs by
> default on native builds (opt out with `DREGG_LEAN_PRODUCER=0`); this Rust
> executor now runs as a differential cross-check, and as the producer on targets
> where Lean cannot link (wasm32/zkvm).

## The unit: Turn → CallForest → CallTree → Action → Effect

A **`Turn`** is "the atomic unit of agent execution" (`turn/src/turn.rs:260`).
It carries an `agent: CellId`, a `nonce: u64`, a `call_forest: CallForest`, a
`fee: u64`, optional `memo`/`valid_until`, a `previous_receipt_hash`, a
`depends_on` list, and a set of proof/witness bundles (`conservation_proof`,
`sovereign_witnesses`, `execution_proof*`, `custom_program_proofs`,
`effect_binding_proofs`, `cross_effect_dependencies`, `effect_witness_index_map`)
(`turn/src/turn.rs:260-373`).

A **`CallForest`** is `roots: Vec<CallTree>` plus a lazily-computed
`forest_hash` (`turn/src/forest.rs:31-36`). Each **`CallTree`** is `{ action,
children: Vec<CallTree>, hash }` — a Merkle node whose hash commits to the action
and all descendants (`turn/src/forest.rs:16`, `forest.rs:162-175`). "The call
forest IS the transaction" (`turn/src/lib.rs:71-73`): authorization flows
parent→child via capability delegation, and the whole tree commits or rolls back
together.

An **`Action`** targets a cell, names a `method: Symbol` (a BLAKE3 hash of the
method name, `turn/src/action.rs:46-50`), carries `args`, an `Authorization`, a
`Preconditions` clause, a `Vec<Effect>`, a `DelegationMode`, a
`CommitmentMode`, an optional signed `balance_change: Option<i64>`, and
`witness_blobs` (`turn/src/action.rs:73`).

`Action::hash` (domain tag `dregg-action-v2:`) folds target, method, args, and
the authorization discriminant + data (`turn/src/action.rs:1634-1637`).
`Turn::hash` (domain tag `dregg-turn-v3:`) folds agent, nonce, the forest hash,
fee, memo, valid_until, depends_on, previous_receipt_hash, and the v3
execution-proof/witness bundle — every load-bearing field, so an in-flight
proof-swap is caught (`turn/src/turn.rs:375-389`).

### Authorization

`Authorization` (`turn/src/action.rs:215-471`) has eleven variants:

- **`Signature([u8;32],[u8;32])`** — Ed25519 over the canonical signing message
  (stored as two 32-byte halves).
- **`Proof { proof_bytes, bound_action, bound_resource }`** — a ZK proof bound
  to an (action, resource) pair.
- **`Breadstuff([u8;32])`** — a capability-token hash matched against the
  actor's c-list.
- **`Bearer(BearerCapProof)`** — proof-carrying authorization that exercises a
  capability WITHOUT it being in the actor's c-list (delegated authority through
  a delegation chain; a cap can be exercised in the same turn it is delegated).
- **`Unchecked`** — no authorization (only valid if the cell's permissions allow
  it; named `Unchecked` rather than `None` so its usage is grep-able).
- **`CapTpDelivered { handoff_cert, introducer_pk, sender_pk, sender_signature }`**
  — authorization derived from a verified CapTP delivery: the introducer-signed
  handoff certificate plus a sender signature over the canonical CapTP-delivery
  message, binding this specific turn to the certificate's nonce.
- **`Custom { predicate }`** — app-defined authorization: a `WitnessedPredicate`
  (resolved through the executor's `WitnessedPredicateRegistry`, proof bytes in
  `witness_blobs`) proves the condition over the canonical signing message.
- **`OneOf { candidates, proof_index }`** — disjunctive 1-of-N alternation; the
  executor verifies exactly the indexed candidate (an `Unchecked` or nested
  `OneOf` candidate is rejected).
- **`Stealth { one_time_pubkey, ephemeral_pubkey, blinding_scalar, signature }`**
  — one-time-key invocation: the executor verifies `P == c·G + S` and the
  signature under `P`; the persistent spend key never appears in the turn, so
  two invocations are unlinkable.
- **`Token { encoded, key_ref, discharges }`** — first-class biscuit (`eb2_`) /
  macaroon (`em2_`) credential: caveats/Datalog verified deterministically
  against this call's `(action, resource, effects, nonce, federation,
  block_height)`.
- **`HybridSignature { ed25519, ml_dsa, ml_dsa_pk }`** (`action.rs:457`) — the
  quantum-safe turn perimeter: ed25519 + ML-DSA-65 halves over the SAME signing
  message, verifying only when `classical ∧ pq`. Staged, fail-closed: a
  present-but-invalid PQ half rejects regardless of the executor's `require_pq`
  flag (default off during rollout).

`DelegationMode` (`turn/src/action.rs:884`): `None` (children cannot reach
other cells with the parent's caps); `ParentsOwn` and `Inherit` are TYPED but NOT
implemented — a cross-cell child under either is rejected fail-closed with
`DelegationModeUnimplemented` (`action.rs:887-894`); `SnapshotRefresh` (child
inherits a point-in-time snapshot of the parent's c-list, revocation eventual,
bounded by `max_staleness`).

## Effects: the 34 ledger mutations

`Effect` (`turn/src/action.rs:1061-1595`) is the enum of "what changes in the
ledger." There are 34 variants. The real list:

- **State / book-keeping:** `SetField`, `IncrementNonce`, `EmitEvent`
  (logged in the receipt, no state change).
- **Value:** `Transfer { from, to, amount }`, `Burn { target, slot, amount }`
  (provable supply reduction; sets the receipt's `was_burn` flag),
  `Mint { target, slot, amount }` (cap-gated supply entry; debits the issuer
  well and credits the holder, conserving per-asset; appended to the enum so the
  postcard discriminant of existing variants does not shift, `action.rs:1495-1516`).
- **Capability / authority:** `GrantCapability`, `RevokeCapability`,
  `AttenuateCapability` (monotone narrowing only — widening returns `None` and is
  rejected), `ExerciseViaCapability` (the categorical eval map: c-list-slot
  lookup + inner effects in one step).
- **Cell mutation / lifecycle:** `SetPermissions`, `SetVerificationKey`,
  `SetProgram` — all three are applied LAST within an action, after all other
  effects, using permissions snapshotted before the action ran, to block
  weaken-then-exploit. Plus `CreateCell`, `CreateCellFromFactory`, `CellSeal`,
  `CellUnseal`, `CellDestroy` (binds a `DeathCertificate`, terminal),
  `MakeSovereign`, `ReceiptArchive`.
- **Delegation:** `SpawnWithDelegation`, `RefreshDelegation` (executor DERIVES
  the genuine snapshot and refuses a mismatching declaration),
  `RevokeDelegation`.
- **Notes / cross-federation (privacy):** `NoteSpend` (reveals a nullifier +
  carries a STARK spending proof and optional Pedersen value commitment),
  `NoteCreate`, `BridgeMint` (portable cross-federation note proof), and
  `ShieldedTransfer { payload }` (`action.rs:1542`) — the opt-in privacy upgrade
  of the cleartext note path: spend hidden input notes and mint hidden output
  notes with value and owner blind. Admitted on a hidden STARK side (membership
  + nullifier derivation through `HidingFriPcs`), a hidden Pedersen side
  (homomorphic value conservation + per-output range proofs), and the same
  production `note_nullifiers` double-spend gate; the two halves are
  Fiat-Shamir-bound to one transcript. Self-authorizing: the ZK proof of note
  ownership IS the authority. Named residual: the executor verifies the shielded
  proof live, but binding that verification into the `effect_vm` descriptor (so
  a pure light client witnesses it) is a VK-affecting follow-up
  (`action.rs:1517-1546`).
- **Pipelining / introduction:** `Introduce` (three-party), `PipelinedSend`
  (dispatch to the result of a pending turn via an `EventualRef`).
- **Refusal:** `Refusal` — the categorical dual: proof of *non-action* (evidence
  of absence) against an `offered_action_commitment`, verified via the
  `WitnessedPredicateRegistry`; bumps the target cell's nonce and records the
  refusal commitment + reason.
- **Reactive (Track 2):** `Promise`, `Notify`, `React`. The soundness gift:
  a promise-hole IS a nullifier; `React` SPENDS `pending_id` into the very same
  production `note_nullifiers` set `NoteSpend` uses, so a second react (or a
  replayed hole) is rejected by the identical double-spend gate.
- **Custom-VK:** `Custom { cell, program_vk_hash, proof_commitment }`
  (`action.rs:1590`) — a custom-program transition on a sovereign cell,
  adjudicated by an external STARK sub-proof (the paired `CustomProgramProof` /
  `customVmDescriptor2R24` leg). Authority lives ONLY in the sub-proof on the
  proof-carrying sovereign path (registered verifier, `custom_state_binding`
  weld of the sub-proof's `[old_commit8, new_commit8]` to the cell's committed
  roots); the classical apply path refuses it fail-closed
  (`CustomEffectRequiresProofCarryingTurn`).

### Linearity discipline

⚠ **REWRITTEN 2026-07-28. The Rust `LinearityClass` / `Effect::linearity` described here was
DELETED, and two of the claims in the old text were false.**

The old text said the classes were declared in `turn/src/action.rs` and that
`is_disclosed_non_conservation()` "is the predicate the adversarial path uses to require a
`was_burn`/`was_mint` receipt disclosure". Neither held: the predicate had **zero non-test
callers**, and there is **no `was_mint` field on `TurnReceipt` at all**. `was_burn` is set by a
hand-written `matches!(Effect::Burn)` forest walk
(`turn/src/executor/mod.rs::effect_is_burn`/`tree_has_burn_effect`), which never consulted it.

The six-color classification is **authored and proved in Lean** —
`metatheory/Dregg2/Spec/Conservation.lean` (`Conservative`, `Monotonic`, `Terminal`,
`Generative`, `Annihilative`, `Neutral`), with `requires_paired_sibling_iff`,
`is_disclosed_non_conservation_iff` and `paired_and_disclosed_exclusive` axiom-pinned in
`Claims.lean` — and it is **SPEC-ONLY**: no `@[export]`, so nothing in the executor consults it.

What the executor actually enforces is described under [The executor](#the-executor) and keys on
`Action::balance_change`, never on an effect's color: a per-cell non-negativity floor, a scalar
`excess == 0`, and a per-asset `Σδ == 0` gate routed through the verified Lean conservation oracle
(fail-closed on a native release build with no oracle installed). Note value, shielded value and the
`was_burn` disclosure are three further, separate mechanisms. ⚑ Those six invariants are each local
and there is **no proof that they compose into global conservation** — see `HORIZONLOG.md` B2.

## The executor

`TurnExecutor` (`turn/src/executor/mod.rs:738`) holds the cost config, the
program registry, the chain clock (`current_timestamp`, `block_height`),
rate-limit counters, an optional proof verifier and budget gate, the trusted
federation roots / local federation id, the `bridged_nullifiers` and production
`note_nullifiers` sets (the permanent double-spend gates, `mod.rs:777`, `:788`),
the `reactive_registry` (promise-hole store, `mod.rs:831`), fee routing cells
(`proposer_cell`/`treasury_cell`/`fee_well_cell`), the per-asset `issuer_wells`
(`mod.rs:855`), the factory registry, the per-agent `last_receipt_hash` and
per-cell `per_cell_receipt_head` chains (`mod.rs:898`, `:905`), an optional
executor signing key, and the witnessed-predicate registry
(`registry_with_real_verifiers` by default, since `dregg-turn` links
`dregg-circuit` and owns the real STARK verifiers, `mod.rs:977`).

### `execute` — the sole entry point

`TurnExecutor::execute(&self, turn, &mut ledger) -> TurnResult`
(`turn/src/executor/execute.rs:210`) is "the sole entry point for all ledger
state mutations" (`execute.rs:203`). It wraps `execute_without_shadow` with
the Lean shadow (below), then returns one of `TurnResult::{Committed, Rejected,
Expired, Pending}` (`turn/src/turn.rs:605`).

`execute_without_shadow` (`execute.rs:352`) is the real pipeline:

1. **Admission / validation** (`execute.rs:352-501`): non-empty forest;
   not expired (`current_timestamp <= valid_until`, `execute.rs:378`); agent
   cell exists; `agent.state.nonce() == turn.nonce` or `NonceReplay`
   (`execute.rs:424`); balance covers the fee (signed balances — any negative
   reading refuses, `execute.rs:434-441`); agent not frozen for migration, and
   (only if any cell is frozen) no write-set cell frozen (`execute.rs:448-476`);
   **receipt-chain self-binding** — the agent's claimed `previous_receipt_hash`
   must equal the executor's stored head for that agent, else
   `ReceiptChainMismatch`; genesis turns use `None` (`execute.rs:484-495`).
2. **Budget gate** (Stingray): pre-flight `try_debit(fee)`; on later failure the
   debit is refunded via `fast_unlock` (`execute.rs:504-513`).
3. **Pre-state hash** = `ledger.root()` (or the deferred sentinel under symbolic
   witness mode, `execute.rs:536-540`).
4. **Phase 1 — fee + nonce, NEVER rolled back** (`execute.rs:560-580`): debit the
   fee and `increment_nonce()`. This is what stops DoS via
   expensive-but-failing turns: even a turn that fails its forest still pays and
   advances its nonce.
5. **Proof-carrying sovereign fast path** (`execute.rs:584-658`): if
   `turn.execution_proof.is_some()`, the executor does ZERO state interpretation
   — it verifies the STARK (`verify_and_commit_proof`, `execute.rs:621`) and
   updates one 32-byte sovereign commitment, then builds a self-contained
   receipt. This is the trust boundary (`lib.rs:44-47`): proof present ⇒
   trustless; absent ⇒ executor-trusted classical walk.
6. **Classical forest walk:** depth-first over the call trees; per action check
   preconditions, verify authorization, apply effects (`execute.rs:197`).

### Apply + journal (atomicity)

`apply_effect` (`turn/src/executor/apply.rs:124`) is the per-effect dispatch — a
`match` from each `Effect` variant to its `apply_*` handler. Mutations are
journaled into a `LedgerJournal`, an undo log: "On success, the journal is
dropped (zero cost); on failure, the journal is replayed in reverse to undo ALL
effects" (`turn/src/journal.rs:1-6`). `LedgerJournal::rollback` walks entries
`.rev()` and restores each (and crucially REMOVES any inserted nullifiers from
`note_nullifiers`/`bridged_nullifiers` so a rolled-back spend is re-spendable,
`journal.rs:416`). This gives all-or-nothing atomicity without cloning the
ledger.

### Receipt

On commit the executor builds a `TurnReceipt` (`turn/src/turn.rs:856`):
`turn_hash`, `forest_hash`, `pre_state_hash`, `post_state_hash`, `timestamp`,
`effects_hash`, `computrons_used`, `action_count`, `previous_receipt_hash`,
`agent`, `federation_id`, and the emitted records (`routing_directives`,
`introduction_exports`, `derivation_records` — capabilities the turn CREATES;
`emitted_events`), plus disclosure bits `was_encrypted`, `was_burn`, the
`consumed_capabilities` witnesses (the capabilities the turn CONSUMED to
authorize, with sorted-Merkle membership against the holder's pre-state
`capability_root`), an optional `executor_signature`, and a `Finality`.

`effects_hash` = BLAKE3 fold over per-effect `Effect::hash` values, returning
`[0;32]` for an empty list (`turn/src/executor/finalize.rs:488`).
`receipt_hash` (domain tag `dregg-receipt-v5`, `turn.rs:964,993`) binds every
field including the `was_encrypted`/`was_burn`/`consumed_capabilities`
disclosures, so a malicious executor cannot strip or forge them. The executor's
narrower signed message binds the full receipt hash.

### Receipt chain = persistence

"The `WitnessedReceipt` chain rooted at each turn IS dregg's persistence layer"
(`turn/src/turn.rs:6-32`): state is recoverable by replaying receipts; the
on-disk snapshot is a cache over this canonical stream; the database is the
cache, the receipt chain is the truth. Each receipt's `previous_receipt_hash`
chain-links it to the prior receipt; the executor enforces this AT WRITE TIME via
`last_receipt_hash` (`mod.rs:898`), and `verify::verify_receipt_chain`
checks it offline: genesis has no previous, then for each link agent
consistency, `curr.previous_receipt_hash == prev.receipt_hash()`, and
`curr.pre_state_hash == prev.post_state_hash` (`turn/src/verify.rs:140`).

## The verified-Lean shadow

`execute` is the seam where the verified Lean executor observes this Rust path.
`dregg-turn` is FFI-free and reaches the Lean side only through the
`ShadowObserver` trait (`turn/src/shadow.rs:136`), into which a native node
injects `dregg_exec_lean::LeanShadowObserver` (`lib.rs:18-24`). The Lean side is
the oracle; this Rust side is the subject under test (`lib.rs:23`).

Under **strict veto mode** (`shadow.rs:148`), `execute` snapshots the full
pre-state ledger before the Rust commit; if the verified Lean executor REJECTED a
turn the Rust executor COMMITTED, the Lean verdict VETOES it — the ledger is
restored to the pre-state (a verified rejection = no state edit) and the result
becomes `Rejected` with the Lean admission reason when one is present
(`execute.rs:226-260`). The verified kernel can only TIGHTEN the decision; it
never launders a Rust rejection into a commit (`execute.rs:244-260`).

The Lean twin of this forest executor is `execFullForestG`
(`metatheory/Dregg2/Exec/FullForestAuth.lean:530`), with theorems for
per-asset conservation (`FullForestAuth.execFullForestG_conserves_per_asset`),
exact conservation (`FullForestAuth.execFullForestG_conserves_exact`),
non-amplification (`FullForestAuth.execFullForestG_no_amplify`),
unauthorized-fails (`FullForestAuth.execFullForestG_unauthorized_fails`), and
per-edge / root attestation (`FullForestAuth.execFullForestG_each_attests`,
`...execFullForestG_root_attests`).
