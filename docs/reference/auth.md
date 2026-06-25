# Macaroons, biscuits & capabilities

The authorization layer has two distinct mechanisms that converge on one idea — *a key may only narrow*:

1. **Macaroons** (`macaroon/`): HMAC-SHA256 bearer tokens whose caveats can only be appended (attenuation), with optional third-party delegation. The off-chain auth-token layer.
2. **Capabilities** (`cell/src/capability.rs` + `cell/src/permissions.rs`): the in-kernel c-list — typed `CapabilityRef`s in a per-cell capability set, attenuated by an order-theoretic `AuthRequired` lattice and effect-mask facets, committed into an openable sorted-Poseidon2 Merkle root shared byte-identically with the circuit.

A Lean convergence arrow (`Dregg2.Authority.CaveatCapBridge`) proves these two narrowings are renderings of one fact.

---

## Macaroons (`macaroon/`)

### The HMAC caveat chain

A `Macaroon` is `{ nonce: Nonce, location: String, caveats: CaveatSet, tail: [u8; 32] }` (`macaroon/src/macaroon.rs:92`). The tail is an HMAC-SHA256 chain:

```text
T₀ = HMAC(root_key, nonce_bytes)
Tᵢ = HMAC(Tᵢ₋₁, encode(Cᵢ))
```

- `Macaroon::new` seeds `T₀ = hmac_sha256(root_key, nonce.encode())` (`macaroon/src/macaroon.rs:118`).
- `add_first_party` is the one attenuation op: `self.tail = hmac_sha256(&self.tail, &wire.encode())`, then pushes the caveat (`macaroon/src/macaroon.rs:151`). It can only push onto `caveats`, never remove or reorder.
- `verify(root_key, discharges)` replays the chain from the root key, advancing `current_tail` over every caveat's `encode()`, then compares `current_tail` to the stored `tail` with `crypto::constant_time_eq` (`macaroon/src/macaroon.rs:204`, compare at `:257`). It returns the collected first-party caveats (the caller "clears" them against an actual request); it does **not** itself evaluate them against an access.

The chain primitive is `crypto::hmac_sha256` (`HMAC<Sha256>`, `macaroon/src/crypto.rs:24`). The final compare is constant-time via `subtle::ConstantTimeEq` (`macaroon/src/crypto.rs:33`).

**Security property.** Removing, reordering, or tampering a caveat changes the replayed tail, so `verify` rejects (tests `test_removed_caveat_fails` `:499`, `test_tampered_caveat_fails` `:472`, `test_wrong_key_fails` `:459`). Forging a valid tail for tampered caveats requires the secret root key. Note the integrity is purely cryptographic: `Macaroon`'s fields are all `pub` and `Serialize + Deserialize`, so a caller who deserializes one directly can mutate `caveats`/`tail` freely — they just cannot produce a valid `tail` without the root key (the `AUDIT[P2]` note at `macaroon/src/macaroon.rs:76`).

### Caveats

`Caveat` is a trait: `caveat_type() -> CaveatType (u16)`, `name()`, `prohibits(&dyn Access) -> Result<(), CaveatError>`, `encode_body() -> Vec<u8>` (`macaroon/src/caveat.rs:50`). Implementations must be deterministic and side-effect-free. The wire form is `WireCaveat { caveat_type: u16, body: Vec<u8> }`, encoded for HMAC as `[type_id LE u16][body]` (`macaroon/src/caveat.rs:95`).

`CaveatSet` is an ordered `Vec<WireCaveat>` (`macaroon/src/caveat.rs:107`) — order is significant for chain replay; all caveats hold with AND semantics.

Type-ID ranges (`macaroon/src/caveat.rs:24-45`): `0..=31` Dregg platform, `32..=47` user-registerable, `48..=253` user-defined, `254` third-party (`CAV_THIRD_PARTY`), `255` bind-to-parent (`CAV_BIND_TO_PARENT`).

`Access` is the request being authorized against (`macaroon/src/access.rs:16`): `as_any()` for downcasting + `now() -> i64`. The macaroon crate is generic over it — consumers implement it for their domain.

### Action bitmask & resource sets

`Action(u8)` is a 5-bit permission mask: `READ=1<<0, WRITE=1<<1, CREATE=1<<2, DELETE=1<<3, CONTROL=1<<4, ALL=0x1f` (`macaroon/src/action.rs:18-38`). It composes by `intersect` (AND) across stacking caveats — each caveat can only narrow (`macaroon/src/action.rs:61`). `parse("r"|"rw"|"*")` reads single-char flags; `parse("read")` parses `r,e,a,d` not the word "read" (`macaroon/src/action.rs:78`). `Action` implements the `BitMask` trait (`macaroon/src/action.rs:147`).

`ResourceSet<I, M: BitMask>` maps resource IDs to action masks (`macaroon/src/resource.rs:27`). `resolve(id)` checks the exact-match entry and the wildcard entry (the type's `Default` ID), intersecting both when present (`macaroon/src/resource.rs:79`); `prohibits` denies on missing entry or insufficient mask (`macaroon/src/resource.rs:98`).

### Third-party caveats & discharge

A `ThirdPartyCaveat` is `{ location, verifier_key, ticket }` (`macaroon/src/caveat_3p.rs:35`). Adding one (`Macaroon::add_third_party`, `macaroon/src/macaroon.rs:175`):

1. Generate ephemeral discharge key `r`.
2. **Ticket (CID)** = `seal(shared_key_KA, {r, caveats_for_3p})` — decryptable only by the third party (`macaroon/src/caveat_3p.rs:89`).
3. **VerifierKey (VID)** = `seal(current_tail, r)` — decryptable only by the verifier, who can replay the chain to that tail (`macaroon/src/caveat_3p.rs:92`).

Sealing is XChaCha20-Poly1305 (`crypto::seal`/`unseal`, `macaroon/src/crypto.rs:59`/`:75`; 24-byte nonce + AEAD).

The third party decrypts the ticket (`decrypt_ticket`, `:117`), recovers `r`, and mints a discharge with `create_discharge(ticket, r, location, additional_caveats)` (`macaroon/src/macaroon.rs:383`) — a macaroon whose root key is `r` and whose nonce KID is the ticket.

**Binding & verification.** The verifier calls `bind_discharge` (`macaroon/src/macaroon.rs:341`), which appends a `CAV_BIND_TO_PARENT` caveat carrying the full 32-byte `binding_hash = SHA256(root_tail)` (`macaroon/src/crypto.rs:95`) to the discharge. During `verify`, each 3P caveat is matched to a discharge by `(ticket == discharge.nonce.kid) && (location)` (`macaroon/src/macaroon.rs:225`), the VID is decrypted with the chain's tail-at-that-position to recover `r`, and the discharge is checked by the private `verify_discharge` (`:267`):

- **Freshness:** discharge `nonce.created_at` must be within `MAX_DISCHARGE_AGE = 300` seconds; `created_at == 0` is rejected (fail-closed upgrade gate) (`macaroon/src/macaroon.rs:35`, `:275`).
- **Binding required:** a discharge with no matching `CAV_BIND_TO_PARENT` is rejected unconditionally — even an empty one — because an unbound discharge could be replayed against a less-attenuated root (`macaroon/src/macaroon.rs:324`; tests `test_unbound_discharge_rejected_even_when_empty` `:614`, `test_bound_empty_discharge_succeeds` `:651`).
- Nested 3P caveats inside a discharge are not supported (`macaroon/src/macaroon.rs:308`).

### Discharge gateway

`discharge_gateway` turns the 3P flow into a usable service without federation/ZK (`macaroon/src/discharge_gateway.rs:1`). A `DischargeGateway` evaluates a `ConditionEvaluator` against a `DischargeRequest { ticket, client_id, proof, payment, metadata }` and issues a `DischargeResponse` on success. Built-in evaluators: `AlwaysAllow`, `TimeWindowEvaluator`, `AllowlistEvaluator`, `RateLimitEvaluator`, `PaymentEvaluator`, `ProofRequiredEvaluator`, `VerifyingProofEvaluator`, and the combinators `AllOfEvaluator`/`AnyOfEvaluator` (`macaroon/src/lib.rs:67`).

### Wire format

Tokens are MsgPack (`rmp_serde`) → base64url (URL-safe, no pad) → `em2_` prefix (`macaroon/src/format.rs:15`, `encode_token`/`decode_token` `:21`/`:31`). Authorization header scheme `DreggV1`: `DreggV1 em2_<permission>,em2_<discharge>,...` (`macaroon/src/format.rs:18`, `format_auth_header`/`parse_auth_header` `:43`/`:57`).

Defense-in-depth zeroization: `Nonce.rnd`, `Macaroon.tail`, and `WireTicket` are zeroized on drop (`macaroon/src/macaroon.rs:54`/`:107`, `macaroon/src/caveat_3p.rs:49`).

---

## Kernel capabilities (`cell/src/`)

### The c-list

A `CapabilityRef` is an entry in a cell's capability list (`cell/src/capability.rs:43`):
`{ target: CellId, slot: u32, permissions: AuthRequired, breadstuff: Option<[u8;32]>, expires_at: Option<u64>, allowed_effects: Option<EffectMask>, stored_epoch: Option<u64> }`.

- `allowed_effects` implements **E-language facets**: `Some(mask)` exposes only a subset of the target's interface; `None` is unrestricted (`cell/src/capability.rs:57`).
- `stored_epoch` (R7) snapshots the grantor's `delegation_epoch` at store time; the executor re-checks `stored_epoch >= grantor.delegation_epoch()` at exercise so a stored cap dies with its grantor's revocation (`cell/src/capability.rs:82`).

`CapabilitySet` holds `refs: Vec<CapabilityRef>`, a `next_slot` counter, a `tombstones: Vec<u32>` set, and a private `cap_root_cache` (`cell/src/capability.rs:201`). Grant variants assign the next slot: `grant`, `grant_with_breadstuff`, `grant_with_expiry`, `grant_full`, `grant_ref` (preserves every field), `grant_snapshot` (R7 epoch), `grant_faceted` (effect mask) (`cell/src/capability.rs:284`–`:445`). `lookup`, `has_access`, `has_access_at` (the latter rejects `Impossible` perms and expired caps) (`:473`–`:495`).

### Attenuation — narrowing only

`AttenuatedCap` is a slot-free attenuated cap (`cell/src/capability.rs:113`); `insert_attenuated` assigns the *child's* own slot so it never inherits the parent's slot numbering (`:646`). Narrowing operations:

- `attenuate(slot, narrower)`: returns `None` unless `narrower.is_narrower_or_equal(existing.permissions)` (`cell/src/capability.rs:512`).
- `attenuate_faceted`: additionally requires `is_facet_attenuation(parent_mask, effect_mask)` — the new mask must be a bitwise subset (`cell/src/capability.rs:539`).
- `attenuate_in_place(slot, narrower, narrower_effects, narrower_expiry)`: narrows **without changing slot identity** (preserves slot + breadstuff), enforcing strict subset on permissions, effect mask, and expiry (an expiry can only shrink; `None` means leave as-is). Returns the 32-byte leaf commitment of the narrowed cap (`cell/src/capability.rs:594`). Adversarial tests at `:746` prove widening, expiry-extension, and mask-widening are all rejected.

The free function `is_attenuation(held, granted) = granted.is_narrower_or_equal(held)` states the rule: you may only grant rights as restrictive or more restrictive than you hold, never amplify (`cell/src/capability.rs:741`).

### The authority lattice

`AuthRequired` is the order on which narrowing is defined (`cell/src/permissions.rs:5`): `None` (least restrictive), `Signature`, `Proof`, `Either` (signature OR proof), `Impossible` (most restrictive), `Custom { vk_hash: [u8;32] }` (app-defined, satisfied only by a matching `Authorization::Custom`). `is_narrower_or_equal` (`:52`): `Impossible` ≤ everything; everything ≤ `None`; `Proof`/`Signature` ≤ `Either`; a `Custom` is comparable only to an identical `Custom` (vk_hash equality) or `Impossible`/`None`, otherwise incomparable.

`Permissions` carries one `AuthRequired` per action (`send`, `receive`, `set_state`, `set_permissions`, `set_verification_key`, `increment_nonce`, `delegate`, `access`) (`cell/src/permissions.rs:84`). Presets: `default_user` (signature for all but receive), `sovereign_default` (`set_verification_key: Proof`, self-upgrading), `zkapp` (proof for all), `frozen` (`Impossible` for all) (`:106`–`:163`).

### Revocation = tombstones, and the openable cap-root

Revoke does **not** compact the c-list. `revoke(slot)` drops the cap from `refs` (so `lookup`/`has_access` stop seeing it) **and** records the slot in `tombstones` (`cell/src/capability.rs:458`). The capability commitment is an openable sorted-Poseidon2 Merkle tree shared byte-identically with the EffectVM circuit's `cap_root`; compaction would shift every key that sorts after the revoked one and invalidate every other membership witness. The tombstone keeps the revoked slot's position occupied by a `BabyBear::ZERO` padding leaf, reproducing the in-circuit sel-24 revoke gate's zero-fold deletion (`cell/src/capability.rs:215`–`:241`). `restore` (journal rollback) clears the tombstone so the root returns exactly to its pre-revoke value (`:669`). The `cap_root_cache` is an `AtomicU64` packing the cached root felt; every `&mut` path invalidates it (including `iter_mut`, conservatively), so a stale cache can never produce a wrong commitment (`cell/src/capability.rs:135`–`:198`, `:262`).

`CapabilityCaveat` (`cell/src/capability.rs:31`) is an *additive* surface for witness-attached predicates on cap exercise — `FacetConstraint` or `Witnessed(WitnessedPredicate)`. Per its own doc, v1 ships the type + serde round-trip; production wiring onto every `CapabilityRef` is the named Phase-6 payoff, not yet on every cap.

---

## The Lean account & the convergence

The macaroon crate is mirrored by verified Lean models, connected by test-only differentials:

- `Dregg2.Authority.CaveatChain` models the real HMAC chain: `seedTag`/`foldTag`/`replayTag`, `Chain.append` (= `add_first_party`), `Chain.verify` (replay-and-compare). `verify_iff_wellTagged` proves `verify ↔ stored tail = replayed tail`; `honest_chain_verifies` (positive) and `append_narrows`/`append_subset` (attenuation only restricts). Chain integrity is stated **relative to a named portal** `MacKernel.unforgeable` (HMAC EUF-CMA) — Lean does *not* prove HMAC secure; `chain_unforgeable` consumes the carrier via `verifyTag_sound` to conclude the stored tail is a genuine MAC, and a collapsing toy kernel refutes the carrier (`collapse_not_unforgeable`), proving the assumption load-bearing (`CaveatChain.lean`). The Rust side `macaroon/src/caveat_chain_diff.rs` (test-only) re-runs `replayTag` against the real `crypto::hmac_sha256` chain and asserts byte-identity + the rejection teeth.
- `Dregg2.Authority.Discharge` proves discharge monotonicity: discharges only accumulate (`Discharges.le` reflexive/transitive), and `caveat_ok_mono` — a satisfied caveat stays satisfied as gateways settle. The third-party binding flow is mirrored by `MacaroonDischarge` (bound-verifies / unbound-rejected / no-cross-root-replay), with the Rust differential `macaroon/src/discharge_diff.rs`.
- `Dregg2.Authority.CaveatCapBridge` makes the macaroon↔kernel-cap convergence an explicit arrow. The shared narrowing `caveatChainAuthority held keeps = keeps.foldl (· ⊓ ·) held` is `≤ held` (`caveatChainAuthority_le_held`) and narrows under append (`caveatChainAuthority_append_le`); on the delegation verb a single `keep ≤ held` step gives **exact equality** with the kernel `confRights` (`delegationVerb_authority_eq`). The keystone `chainGateG_implies_capAuthorityG` proves that on a coherent node (whose cap-authority `granted` *is* the macaroon chain's narrowing), the macaroon chain gate passing forces the kernel cap gate to pass — turning the `&&` of the two gate legs into a proven implication on the overlap. Non-vacuity is witnessed both polarities (`deleg_nonAmp_*` pass, `deleg_amp_*` reject). `#assert_axioms` pins the keystones clean.
