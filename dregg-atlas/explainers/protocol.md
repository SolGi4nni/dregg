## thesis

> *A turn is the exercise of an attenuable, proof-carrying token over owned state, leaving a verifiable receipt.* — `docs/DREGG3.md:19-21`

Each clause is concrete code, not slogan:

- **"a turn"** — a `Turn` (`turn/src/turn.rs:241`) is `auth ∘ body ∘ receipt`: a forest of `Action`s, each targeting one cell with a `method`, `args`, an `Authorization`, `Preconditions`, and a list of `Effect`s (`turn/src/action.rs:73-122`). The turn is the unit the executor admits or rejects atomically.
- **"the exercise of … a token"** — the actor does not *describe* what it wants; it *presents* authority. `Authorization` (`turn/src/action.rs:215-443`) is that presentation: an Ed25519 `Signature`, a `Proof`, a `Bearer` capability proof, a `Token` (biscuit/macaroon), a `Custom` witnessed predicate. Exercising a held capability is `Effect::ExerciseViaCapability` (`turn/src/action.rs:1117`).
- **"attenuable"** — every token narrows monotonically and never widens. The gate is `is_attenuation(held, granted) := granted.is_narrower_or_equal(held)` (`cell/src/capability.rs:603-605`). A delegated capability can only restrict the holder's authority.
- **"proof-carrying"** — where authority is not a bare signature, the actor carries a proof the executor *checks deterministically*: STARK delegation proofs, witnessed predicates resolved via a `WitnessedPredicateRegistry`, token caveats verified against this call's `(action, resource, effects, nonce, federation, block_height)` (`turn/src/action.rs:412-442`).
- **"over owned state"** — state is never ownerless. A cell gathers the four substances + program + operator (`docs/DREGG3.md:128-132`); "Nothing is ownerless. Every object IS a cell or lives in one." Mutation is guarded by the cell's own permissions.
- **"leaving a verifiable receipt"** — every committed turn emits a `TurnReceipt` (`turn/src/turn.rs:768`) binding pre/post state, effects, cost, and the prior receipt into a hash chain. A light client verifies only the receipt chain, never re-executes.

The lineage: macaroon → biscuit → capability is the deepest stratum — biscuit's Datalog *became* the derivation circuit, so "the token became the proof system" (`docs/DREGG3.md:23-25`).

## verbs

DREGG3 collapses the historical 52-variant `Effect` enum to **eight kernel verbs** (`docs/DREGG3.md:151-157`): `create · write · move · grant · revoke · shield/unshield · lifecycle`. These are the *structural rules* of the four-substance logic: `move` is exchange for the linear substance (Value); `grant` is authorized production for Authority; `shield`/nullifiers are Evidence-monotonicity; `write` is heap-update under the frame. Everything else among the 52 is a **cell-program pattern** — queues, inboxes, escrows, auctions, namespaces, bridges are factory + `Pred` + these verbs.

The live Rust `Effect` enum (`turn/src/action.rs:950-1365`) maps onto these eight:

- **create** — `CreateCell`, `CreateCellFromFactory`, `NoteCreate`, `SpawnWithDelegation`, `Promise`/`Notify` (create a hole)
- **write** — `SetField`, `SetPermissions`, `SetVerificationKey`, `SetProgram`, `EmitEvent`
- **move** — `Transfer`, the signed `Action::balance_change` delta, `BridgeMint`, `Burn` (asymmetric move to the well)
- **grant** — `GrantCapability`, `Introduce`, `ExerciseViaCapability`, `AttenuateCapability`, `RefreshDelegation`
- **revoke** — `RevokeCapability`, `RevokeDelegation`, `React` (terminal spend of a hole)
- **shield/unshield** — `NoteSpend`, `NoteCreate` (reveal a nullifier / add a commitment)
- **lifecycle** — `CellSeal`, `CellUnseal`, `CellDestroy`, `MakeSovereign`, `ReceiptArchive`

`IncrementNonce` is the prologue, not a verb; `Refusal` is an outcome made first-class. Every variant must declare its conservation discipline through the exhaustive `Effect::linearity` match (`turn/src/action.rs:1607`) — no `_ =>` arm, so `rustc` forces every new effect to answer the conservation question.

## substances

The kernel governs **four substances**, each with its own discipline (`docs/DREGG3.md:56-62`):

- **Value** (balance) — linear; moves, never copies or vanishes. Law: `Σδ = 0`, exact.
- **Authority** (capabilities) — non-forgeable *production*; grows only by authorized construction, narrows freely. Only connectivity begets connectivity.
- **Evidence** (nullifiers/commitments/nonce) — monotone; once known, never unknown. Grow-only.
- **State** (fields/slots) — guarded-mutable; changes only under `Pred`, by its owner. The frame.

**Conservation, `BALANCE_SUM = 0`.** Value is strictly linear. A signed `balance_change` (`turn/src/action.rs:93-102`) withdraws or deposits; at turn end the executor demands the running `excess == 0` and rolls the whole turn back otherwise — `TurnError::ExcessNotZero` (`turn/src/executor/execute.rs:998-1013`).

**Issuer wells with negative balance.** The "no creation from nothing" law is made literal: `AssetId := CellId of the issuer; the issuer carries −supply, so ∀a. Σ_c bal(c,a) = 0 ALWAYS` (`docs/DREGG3.md:133-138`). Mint and burn are not non-conserving verbs — they are the issuer *moving from/to its own well under its own program*. `Burn` is the one disclosed exception — its receipt's `was_burn` flag is bound into `receipt_hash` so an executor cannot strip the disclosure.

## auth-lattice

A cell's `Permissions` (`cell/src/permissions.rs:84-102`) maps each operation to an `AuthRequired` (`cell/src/permissions.rs:4-22`): `None` (always allowed), `Signature`, `Proof`, `Either` (sig or proof), `Impossible` (permanently locked), `Custom { vk_hash }` (app-defined witnessed predicate).

**The partial order** is `is_narrower_or_equal` (`cell/src/permissions.rs:52-71`):

- `Impossible` is the **bottom** (most restrictive): `(Impossible, _) => true`.
- **`None` is the TOP — the widest, least restrictive**: `(_, None) => true`, `(None, _) => false`. This is the subtlety that catches readers: `None` does not mean "no authority"; it means "authority that satisfies *every* requirement." A holder of `None` rights clears every gate.
- `Proof` and `Signature` are each narrower than `Either`; they are incomparable with each other.
- two distinct `Custom`s are **incomparable**.

**Attenuation** is this order read for delegation: `is_attenuation(held, granted) := granted.is_narrower_or_equal(held)` (`cell/src/capability.rs:603-605`). You may grant only what is as restrictive as, or more restrictive than, what you hold — never amplification. The adversarial tests pin the no-widening property exactly (`cell/src/capability.rs:640-651`).

## refusal

A turn can be refused at two structurally distinct sites. The cockpit's `SendResult::Refused { reason, by_executor }` (`starbridge-v2/src/inspect_act.rs:111-117`) makes the distinction first-class:

**`by_executor = false` — the object-capability gate, BEFORE any turn (the anti-ghost tooth).** The affordance surface runs the *real* `is_attenuation` (`required ⊆ held`) and refuses an unauthorized send in-band, before the executor ever runs (`inspect_act.rs:227-247`). A viewer who lacks the rights cannot even form the turn; there is no phantom path where an unauthorized action "almost" runs.

**`by_executor = true` — a kernel guarantee fired INSIDE the executor.** The cap-gate admitted the send, but the verified executor rejected the turn because a substance law fired. The actual sites:
- **Authorization / permission gate** — `verify_authorization` → `TurnError::PermissionDenied` / `InvalidAuthorization` (`turn/src/executor/authorize.rs:241-298`).
- **Non-amplification** — `GrantCapability` runs `is_attenuation` and refuses widening with `TurnError::DelegationDenied` (`turn/src/executor/apply.rs:479-488`); bearer caps reject `BearerCapAmplification`.
- **Conservation** — `ExcessNotZero` at turn end, `NoteConservationViolation`, `CommittedConservationFailed`, `PerAssetConservationViolation`.
- **Freshness / replay** — `NonceReplay`, `CapabilityRevoked`/`Stale`, `ReceiptChainMismatch`, `Expired`.

The first site refuses *the formation of authority*; the second refuses *a turn that violates what the substances are*. Both are surfaced, never swallowed.

## receipts

A committed turn produces a `TurnReceipt` (`turn/src/turn.rs:768-840`) — the cryptographic evidence the light client trusts in lieu of re-execution. Its hash-bound core (`receipt_hash`, domain-separated `"dregg-receipt-v3"`):

- **`turn_hash`** — the hash of the `Turn` that produced this receipt; plus `forest_hash` binding the call-forest shape.
- **`pre_state_hash` / `post_state_hash`** — the agent's committed state before and after. This pair IS the transition.
- **`effects_hash`** — the committed digest of the effects applied.
- **`computrons_used`** — the metered cost (the gas analogue); `action_count` records the forest size.
- **the chain — `previous_receipt_hash`** — links this receipt to the agent's prior one. The whole protocol is "one growing proof object"; causal ordering is non-malleable. A light client verifies only these Q-chains.

Bound into the same hash so a malicious executor cannot strip them: `federation_id`, `was_burn` (the disclosed non-conservation), `consumed_capabilities` (cap-witnesses with sorted-Merkle membership paths), and `derivation_records` (capabilities the turn creates). The optional `executor_signature` attests every bound field to a known executor.

*Two honest edges the atlas flags:* `SetProgram` (`action.rs:1019`) has an executor path but no circuit descriptor rung yet (a documented VK-affecting follow-up), and DelegationMode `ParentsOwn`/`Inherit` are typed-but-unimplemented, rejected fail-closed with `DelegationModeUnimplemented` (`action.rs:831-847`).
