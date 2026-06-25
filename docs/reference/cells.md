# Cells & the substances

The cell is dregg's unit of sovereign, capability-secure state — "the agent-model
analog of a Mina zkApp account" (`cell/src/lib.rs:19`). The `dregg-cell` crate holds
the cell types (identity, mutable state, permissions, c-list, lifecycle); the
`dregg-cell-crypto` crate holds the signing/sealing/encrypting/proving machinery that
operates over those types (`cell-crypto/src/lib.rs:3`).

> Provenance: `dregg-cell` is described in-crate as the **legacy dregg1 Rust cell-state
> model**, NOT the source of truth — the verified semantics live in Lean under
> `metatheory/Dregg2/` (`cell/src/lib.rs:4-15`). The Rust types persist because the
> running executor (`dregg-turn`) depends on them until "THE SWAP."

## The four substances

A cell bundles distinct disciplines that the kernel verbs are the structural rules of.
The canonical roster lives in Lean (`Dregg2.Substrate.VerbRegistry.Substance`,
`metatheory/Dregg2/Substrate/VerbRegistry.lean:72`):

- **`value`** — linear value: moves, never copies or vanishes (`Σδ = 0`, exact).
- **`authority`** — non-forgeable authority: authorized production, free attenuation,
  epoch revocation.
- **`evidence`** — monotone evidence: once known, never unknown (the nullifier /
  commitment ledgers).
- **`state`** — guarded-mutable state: changes only under a `Pred`, only by its owner.

plus two bundle-lifecycle facets, **`birth`** (minting the four-substance cell) and
**`retirement`** (the seal/destroy/sovereign custody automaton). In the Rust cell these
substances are carried, respectively, by `CellState::balance` (value),
`CapabilitySet` + `Permissions` (authority), the nullifier/commitment side-tables and
`Note` (evidence), the `fields`/`fields_map`/`heap` registers (state), and
`CellLifecycle` (retirement).

## `Cell` — the bundle

`Cell` (`cell/src/cell.rs:249`) is "an isolated agent execution context." Its fields:

- `id: CellId` — content-addressed identity, `pub(crate)`-sealed (audit P0-1) so it can
  only be read via `Cell::id()` and only mutated through the ledger (`cell/src/cell.rs:254`).
- `public_key: [u8;32]` — Ed25519 public key, sealed (`cell/src/cell.rs:256`).
- `token_id: [u8;32]` — which token domain the cell belongs to, sealed (`cell/src/cell.rs:271`).
- `state: CellState` — the mutable state (`cell/src/cell.rs:258`).
- `permissions: Permissions` — per-action authorization requirements (`cell/src/cell.rs:260`).
- `verification_key: Option<VerificationKey>` — for ZK-proof validation (`cell/src/cell.rs:262`).
- `delegate: Option<CellId>` + `delegation: Option<DelegatedRef>` — parent pointer and a
  snapshot-and-refresh delegation snapshot (`cell/src/cell.rs:265-269`).
- `capabilities: CapabilitySet` — the c-list (`cell/src/cell.rs:273`).
- `program: CellProgram` — defines valid state transitions; `None` means any authorized
  change is valid (`cell/src/cell.rs:276`).
- `mode: CellMode` — `Hosted` or `Sovereign` (`cell/src/cell.rs:281`).
- `lifecycle: CellLifecycle` — structural state (`cell/src/cell.rs:291`).
- `leaf_cache: LeafDigestCache` — a `#[serde(skip)]` cache of the Merkle-leaf digest,
  read only by `Ledger::hash_cell`, excluded from `PartialEq`/`Eq` (`cell/src/cell.rs:299`).

### Identity is content-addressed

`id == derive_raw(public_key, token_id)` — a domain-separated BLAKE3 of `public_key ‖
token_id` under the key `"dregg-cell-id-v1"` (`types/src/lib.rs:701`, re-exported as
`CellId` via `cell/src/id.rs:5`). The constructors (`Cell::new`, `new_hosted`,
`with_balance`, `from_config`, `spawn_child`) all derive `id` this way
(`cell/src/cell.rs:380`). `verify_id_integrity()` re-checks the invariant
(`cell/src/cell.rs:620`) — authoritative ingest paths call it because nothing in the type
system maintains the equality after construction (`remote_stub_with_id` deliberately
breaks it for peers whose pre-image is unknown — `cell/src/cell.rs:457`).

### Hosted vs Sovereign

`CellMode` (`cell/src/cell.rs:13`): `Hosted` = the federation stores full cell state;
`Sovereign` = the federation stores only a 32-byte state commitment and the agent
provides full state in each turn (`cell/src/cell.rs:16`). `Default` is `Sovereign`
(`cell/src/cell.rs:23`); the ledger holds `SovereignRegistration`s carrying the current
commitment for sovereign cells (`cell/src/ledger.rs:234`).

## `CellState` — the mutable substance store

`CellState` (`cell/src/state.rs:101`) is the value + state + evidence-root registers.
Several scalars are `pub(crate)`-sealed (audit P0-1) and mutate only through verbs:

- `fields: [FieldElement; 16]` — the 16 fixed user slots (`STATE_SLOTS = 16`,
  `cell/src/state.rs:18`), like Mina's `app_state`; `FieldElement = [u8;32]`
  (`cell/src/state.rs:12`).
- `field_visibility` + `commitments` — per-slot progressive disclosure: `Public`,
  `Committed` (only a `BLAKE3(value ‖ nonce)` hash is public), or
  `SelectivelyDisclosable` (`cell/src/state.rs:74`, `cell/src/state.rs:699`). A stale
  commitment after `set_field` returns the all-zero sentinel rather than leaking the
  plaintext (audit P1-2, `cell/src/state.rs:717`).
- `nonce: u64` — monotone action counter; `increment_nonce` refuses on overflow (audit
  P2-2 replaced `wrapping_add`, `cell/src/state.rs:875`).
- `balance: i64` — **signed** value (THE EPOCH, `docs/EPOCH-DESIGN.md` §5): issuer wells
  carry `−supply` so the reachable total is zero (`cell/src/state.rs:127`). Sign
  discipline is **by verb**: ordinary moves use `debit_balance` / `apply_balance_change`
  (refuse below zero, `cell/src/state.rs:570`, `cell/src/state.rs:889`); issuer-well moves
  use `well_debit_balance` / `apply_balance_change_well` (may go negative,
  `cell/src/state.rs:589`, `cell/src/state.rs:905`). The executor gates who may invoke the
  well verbs.
- `proved_state: bool` — true only when all 16 fields were set by a single
  proof-authorized action (`cell/src/state.rs:129`).
- `delegation_epoch`, `committed_height`, `swiss_table_root`, `refcount_table_root`.

### Overflow maps: fields_root, system_roots, heap

The 16-slot array is "unsqueezed" into committed maps (record-layer upgrade):

- **`fields_map` / `fields_root`** — an unbounded `key → FieldElement` map over keys
  `>= 16`; keys `0..15` stay in `fields[]`, keys `>= 16` live in the map
  (`cell/src/state.rs:773` `get_field_ext`, `cell/src/state.rs:786` `set_field_ext`).
  `fields_root` is the OPENABLE sorted-Poseidon2 Merkle root over the map
  (`compute_fields_root`, `cell/src/state.rs:380`) — the same `dregg_circuit::heap_root`
  scheme the circuit uses, so a light client can OPEN it (not an opaque sponge). It
  reserves a position-stable zero leaf for the refusal-audit slot
  (`REFUSAL_AUDIT_EXT_KEY = 2^32`, `cell/src/state.rs:28`, `cell/src/state.rs:334`).
- **`system_roots: [FieldElement; 8]`** — the kernel-owned side-table roots, each at its
  own fixed index `system_root::{ESCROW, QUEUE, REFCOUNT, STURDYREF, DELEG, NULLIFIER,
  COMMIT, SEALED_BOXES}` (`cell/src/state.rs:46`). A `set_field*` can NEVER reach these;
  only the kernel's escrow/queue/nullifier/... transitions touch them, via
  `set_system_root` (`cell/src/state.rs:644`) — a disjoint namespace with a disjoint
  mutator. Digested by `compute_system_roots_digest` (`cell/src/state.rs:261`).
- **`heap_map` / `heap_root`** — a `(collection_id, key) → FieldElement` map; sorted-
  Poseidon2 root via `compute_heap_root` (`cell/src/state.rs:409`), the Rust shadow of
  Lean `Substrate.Heap.root`.

All three roots are **order-canonical, injective, anti-vacuous**: distinct maps cannot
share a root, a tampered value flips the root, and a legacy (no-activity) cell carries a
fixed cell-independent empty constant (`empty_fields_root`, `empty_heap_root`,
`empty_system_roots_digest`) so absorbing it into the commitment is a uniform no-op
(`cell/src/state.rs:1139` anti-vacuity test, `cell/src/state.rs:361`).

### Signed-balance boundary encoding

A signed balance crosses any commitment/wire boundary as an order-preserving biased
`u64`: `biased = bits(balance) ⊕ 2^63`, so `a < b ⇔ biased(a) < biased(b)` unsigned
(`balance_biased`, `cell/src/state.rs:954`). It decomposes into two 32-bit range-table
limbs (`balance_limbs`, `cell/src/state.rs:967`) and serializes as `encode_balance_le`
(`cell/src/state.rs:976`). Pins: `biased(0) = 2^63`, `biased(i64::MIN) = 0`,
`biased(i64::MAX) = u64::MAX` (`cell/src/state.rs:1012`).

## `Permissions` — per-action authority

`Permissions` (`cell/src/permissions.rs`) carries eight `AuthRequired` fields in a fixed
canonical order: `send`, `receive`, `set_state`, `set_permissions`,
`set_verification_key`, `increment_nonce`, `delegate`, `access`. `AuthRequired`
(`cell/src/permissions.rs:5`) is a six-variant lattice: `None`, `Signature`, `Proof`,
`Either`, `Impossible`, `Custom { vk_hash }`. `is_satisfied_by` checks a provided
`AuthKind` against the requirement (`Custom` requires a matching witnessed predicate, not
a bare signature/proof — `cell/src/permissions.rs:33`); `is_narrower_or_equal` defines the
attenuation order (`Impossible` most restrictive, `None` least; distinct `Custom`s
incomparable — `cell/src/permissions.rs:51`).

## `CapabilitySet` — the c-list (authority substance)

`CapabilitySet` (`cell/src/capability.rs:202`) is "the c-list: what other cells this cell
can reference" (`cell/src/cell.rs:272`). Each entry is a `CapabilityRef`
(`cell/src/capability.rs:44`): a `target: CellId`, a local `slot`, `permissions:
AuthRequired`, optional `breadstuff` token hash, optional `expires_at`, optional
`allowed_effects: Option<EffectMask>` facet (None = unrestricted), and an optional
`stored_epoch` for revocation freshness (`cell/src/capability.rs:101`).

Authority moves only down the attenuation lattice: `is_attenuation(held, granted) =
granted.is_narrower_or_equal(held)` (`cell/src/capability.rs:741`). `attenuate` /
`attenuate_faceted` / `attenuate_in_place` produce narrowed caps and refuse to widen
(`cell/src/capability.rs:512`, `cell/src/capability.rs:603`).

`revoke(slot)` is a **tombstone** deletion: it drops the cap from the logical c-list AND
records the slot in `tombstones` (`cell/src/capability.rs:458`), so the openable root
folds a ZERO/padding ghost leaf at the revoked slot's sorted position rather than
compacting (re-indexing) the tree — every other cap's membership witness stays valid, and
the root matches the in-circuit revoke gate byte-for-byte (`cell/src/capability.rs:215`,
`cell/src/state.rs` cap-root context note). `tombstoned_slots()` exposes the set
(`cell/src/capability.rs:701`).

`CapabilityCaveat` (`cell/src/capability.rs:31`) is the additive surface for
witness-attached predicates and typed `FacetConstraint`s on a cap's exercise.

## `CellLifecycle` — retirement

`CellLifecycle` (`cell/src/lifecycle.rs:37`) is the structural state: `Live` (disc 0),
`Sealed` (1), `Migrated` (2), `Destroyed` (3), `Archived` (4) (`cell/src/lifecycle.rs:97`).
Predicates: `accepts_effects()` is true for `Live` and `Archived` only
(`cell/src/lifecycle.rs:109`); `is_live()` is `Live`-ONLY, matching the verified-kernel
`cellLive` predicate (`cell/src/lifecycle.rs:141`); `is_terminal()` is `Destroyed` or
`Migrated` (`cell/src/lifecycle.rs:116`).

Transitions on `Cell`:

- `seal` / `unseal` — *reversible* quiescence; the cell rejects new effects but state and
  history are preserved; a second seal errors `AlreadySealed`, preserving the original
  reason (`cell/src/cell.rs:640`, `cell/src/cell.rs:671`).
- `destroy(&DeathCertificate)` — *permanent*; the certificate must bind to this cell or it
  errors `CertificateMismatch`; once `Destroyed` no transition is allowed
  (`cell/src/cell.rs:695`).
- `archive(&ArchivalAttestation)` — marks the receipt-chain prefix archived; the cell
  STILL accepts effects; must be monotone in `archived_through` (`ArchiveNotMonotone`
  otherwise) and a sealed cell cannot be archived (`cell/src/cell.rs:731`).

Lifecycle is authority-bearing — it is folded into the state commitment, so an executor
cannot omit a destruction and present the cell as still-Live
(`cell/src/commitment.rs:287` `hash_lifecycle_into`; `cell/src/cell.rs:1101` confirms a
seal changes the commitment and an unseal restores it).

## `compute_canonical_state_commitment` — what bytes commit to a cell

`cell/src/commitment.rs:204` is "the **single** source of truth for what bytes commit to
this cell." Both `Cell::state_commitment()` (sovereign-witness path, always fresh,
`cell/src/cell.rs:577`) and `Ledger::hash_cell` (the federation Merkle leaf, via the
`leaf_cache`) route through it, so they are byte-identical. It is a length-seeded BLAKE3
sponge keyed by `CANONICAL_COMMITMENT_CONTEXT = "dregg-cell:canonical-state-commitment
v9"` (`cell/src/commitment.rs:110`) absorbing, in order: identity (`id`/`public_key`/
`token_id`), `mode`, the full `CellState` (nonce, signed balance, 16 fields, visibility,
commitments, proved_state, delegation_epoch, committed_height, swiss/refcount roots,
`fields_root`, `system_roots_digest`, `heap_root`), the eight `Permissions`, the VK hash,
the capability root, delegate, delegation snapshot, program, and lifecycle. Omitting any
authority-bearing field would let two distinct authorities share a commitment
(`cell/src/commitment.rs:179`). The context history (`v4→...→v9`) records each shape
change; the cap root has its own context `"dregg-cell:canonical-capability-root v3"`
(`cell/src/commitment.rs:133`).

The capability root absorbed here is the OPENABLE sorted-Poseidon2 Merkle root computed by
`compute_canonical_capability_root_felt` (`cell/src/commitment.rs:554`) — the SAME
`dregg_circuit::cap_root` implementation the EffectVM circuit's `cap_root` column carries
(per-cap leaf via `cap_ref_to_leaf`, `cell/src/commitment.rs:508`), so the cell-side and
circuit-side roots agree byte-identically. Revoked slots fold ZERO tombstone leaves
(`cell/src/commitment.rs:579`).

### The rotated v9 commitment (cell ≡ circuit)

`compute_canonical_state_commitment_v9_felt` (`cell/src/commitment.rs:1044`) is the
cell-side reconstruction of the EffectVM rotated trace's row-0 `STATE_COMMIT` carrier — a
Poseidon2 `wireCommitR` over 37 pre-iroot limbs (`V9_NUM_PRE_LIMBS`,
`cell/src/commitment.rs:670`) built by `compute_rotated_pre_limbs`
(`cell/src/commitment.rs:900`). Because the rotated limbs carry only a subset of authority
state, register **r23** holds `compute_authority_digest_felt` (`cell/src/commitment.rs:770`),
which folds ALL authority residue not on a named limb (permissions, VK, delegate,
delegation, program, mode, token_id, visibility/commitments/proved/side-table roots,
`fields[8..16]`) — closing the authority-drop hole. A faithful 8-felt (~124-bit) twin
`compute_canonical_state_commitment_v9_felt8` is staged but not yet the live default
(`cell/src/commitment.rs:1076`).

## `Note` — the evidence substance

A `Note` (`cell/src/note.rs:44`) is a "consume-once cell with private state": a committed
tuple `(owner, fields[8], randomness, creation_nonce)`. Spending = revealing its
`Nullifier`; creating = adding a `NoteCommitment` to the note tree
(`cell/src/note.rs:1`). Both are Poseidon2 digests over BabyBear (the same audited
`dregg_circuit::poseidon2` sponge the circuit verifies), encoded via `felt_to_bytes32`,
so cell-side note identity matches the circuit's field-domain commitment
(`cell/src/note.rs:14`). Nullifiers are derived from note-intrinsic data only (no tree
position), making them globally unique and federation-independent so double-spend
protection works across federation boundaries (`cell/src/note.rs:10`). The `NullifierSet`
(`cell/src/nullifier_set.rs`) is an append-only `BTreeSet<Nullifier>` with Merkle
membership and adjacent-neighbor non-membership proofs (`cell/src/nullifier_set.rs:1`).

## `dregg-cell-crypto` — the crypto layer

`dregg-cell-crypto` keeps `dregg-cell` a pure types crate (no `getrandom`,
`ed25519-dalek`, bulletproofs, etc. in the core) and provides the operations over cell
types (`cell-crypto/src/lib.rs:3`):

- `note::new_note` — the OS-randomness note constructor moved off the type
  (`cell-crypto/src/lib.rs:36`).
- `delegation::verify_parent_signature` — Ed25519 verification of a `DelegatedRef`
  (`cell-crypto/src/lib.rs:62`).
- `value_commitment` — Pedersen value commitments + bulletproof range/conservation/asset-
  equality proofs (`cell-crypto/src/value_commitment.rs`).
- `seal` (seal/unseal boxes), `note_encryption` (DH-KDF note encryption), `stealth`
  (stealth addresses), `oblivious_transfer`, `read_cap` (encrypted-slot read caps),
  `capability_proof`, `note_bridge`, `value_link_zk`, `peer_exchange`
  (`cell-crypto/src/lib.rs:14-23`).

## Map: which file holds what

| Concern | File |
| --- | --- |
| `Cell` bundle, identity, lifecycle transitions, leaf cache | `cell/src/cell.rs` |
| `CellState`, fields/maps/heap/system-roots, signed balance | `cell/src/state.rs` |
| Canonical + rotated state commitment, cap root | `cell/src/commitment.rs` |
| `Permissions`, `AuthRequired` lattice | `cell/src/permissions.rs` |
| `CapabilitySet` c-list, attenuation, revoke tombstones | `cell/src/capability.rs` |
| `CellLifecycle`, death certificates, archival | `cell/src/lifecycle.rs` |
| `Note`, `Nullifier`, `NoteCommitment` | `cell/src/note.rs` |
| `NullifierSet` membership / non-membership | `cell/src/nullifier_set.rs` |
| `CellId` derivation | `types/src/lib.rs` (re-exported `cell/src/id.rs`) |
| Crypto operations over cells | `cell-crypto/src/` |
| Verified spec (source of truth) | `metatheory/Dregg2/` |
