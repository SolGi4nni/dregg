# Cipherclerk design audit

A design audit of dregg's wallet-grade credential clerk, the `AgentCipherclerk`
(`sdk/src/cipherclerk.rs`, ~8.4k lines), its narrow app handle
(`app-framework/src/cipherclerk.rs`), and the service surface
(`node/src/api.rs` `/cipherclerk/*`). Present tense, file:line'd. This document
assesses what is well-designed, where the surface is awkward, what is missing
against the bar of "a first-class wallet-grade clerk for a verified ocap OS,"
and which gaps are cheap wins versus design milestones.

The clerk is named after Greg Egan's *Polis* (the cipherclerk that holds a
citizen's keys). It is the credential holder every agent carries: identity,
tokens, signing, ZK presentation, receipt-chain state, and HD derivation.

---

## 1. Strengths — what is well-designed

### HD key derivation (BIP39 + BLAKE3)
`from_mnemonic` / `from_seed` / `from_key_bytes` / `derive_sub_agent`
(`cipherclerk.rs:1096–1152`) form a clean ladder. The seed and mnemonic are
retained for sub-agent derivation and backup, zeroized on drop
(`Drop for AgentCipherclerk`), and the export accessors require `&mut self`
plus `#[must_use]` to fence master-secret leakage (`export_mnemonic` 1171,
`export_seed` 1191). `from_key_bytes` takes `Zeroizing<[u8;32]>` and zeroizes
the derived secret explicitly (1059–1084). Stealth keys are derived
deterministically from the signing key so a restored clerk recovers its private
note-receiving identity (1064). This is genuine wallet-grade hygiene, not a
placeholder.

### Macaroon attenuation and the monotone narrowing law
`mint_token` (1271) → `attenuate` (1306) → `delegate` (1354) is a faithful
macaroon chain. Attenuation only narrows: `MacaroonToken::attenuate` appends
caveats to an HMAC chain that the verifier re-walks. The key security
invariant — **attenuated tokens never carry the root forging key** — is
enforced structurally: `HeldToken::new_attenuated` zeroes `root_key` (506) and
carries only the one-way `issuer_key = blake3::derive_key("dregg-proof-key-v1",
root_key)` (469–473). `can_mint()` (575) and `can_prove()` (587) read directly
off whether the root key / proof key is present, so the type cannot lie about
its own authority.

### The caveat-chain binding (anti-tamper for delegated tokens)
The hardest correctness problem — a delegatee who holds only the `proof_key`
mutating caveats and proving over fabricated facts — is closed two ways:
- `caveat_chain_hash` is computed by the delegator from the HMAC-verified token
  (`delegate` 1390–1393) and re-checked by the delegatee before any ZK proof.
- The **whole delegation envelope is signed** (`compute_delegation_signing_message_v2`,
  `delegate` 1398–1411): `token_bytes`, `delegatee`, `service`, `id`,
  `restrictions`, `proof_key`, `caveat_chain_hash`, `membership_leaf`,
  `parent_delegation_hash`, and the delegator pubkey. The binding is captured in
  `HeldToken::delegation_binding` and **re-verified on every authorization use**
  via `reverify_delegation_binding` (620–683), which recomputes the signing
  message from *current* field values — no in-process mutation can bypass it.
- `verified: bool` (404) tracks HMAC-chain verification status; delegated tokens
  are `false` (structural validation only) until presented to a root-key holder.

### Authority-policy explicitness on receive
`DelegationAuthority` (820) makes the trust decision a first-class, non-defaultable
choice: `TrustedKey` / `TrustedKeys` / `ChainsFromParent`, with the footgun
`Open { warn }` gated behind `cfg(test)` / `unsafe-test-utils` (849) so it cannot
land in a production codepath. The wire envelope's `delegator_public_key` is
documented as *asserted, not verified* (789) and the receive path must check it
against policy.

### Anti-blind-signing (faithful explanation)
`ExplainedSignedAction` / `ExplainedSignedTurn` (907, 922) carry a total,
injective-on-semantics rendering of exactly the action/turn being signed
(`explain_action` 2681, `explain_turn` 2687). A citizen UI can show *what* is
being authorized before the signature exists. This is the "third reading of the
term" and is the right shape for a clerk that must never sign blind.

### Sealed-value construction for `HeldToken`
Authority-affecting fields are private; external callers get read-only
accessors (516–598). Direct field mutation is a compile error, enforced by
`compile_fail` doctests (`doctest_compile_fail` mod, end of file). Drop zeroizes
`root_key` and `issuer_key` (445–450).

### The narrow app waist
`AppCipherclerk` (`app-framework/src/cipherclerk.rs:67`) is a deliberate ~6-method
waist over the 100+-method SDK surface: `cell_id`, `public_key`, `make_action`,
`make_turn`, `sign_action`, `sign_turn`, `create_from_factory`. Apps cannot
extract the key or reach the wallet. The `EmbeddedExecutor` (318) closes the
"action authored and dropped on the floor" gap by letting handlers submit and
observe a real `TurnReceipt`. This is a well-drawn userspace/SDK boundary.

---

## 2. Awkward / inconsistent design — where the model leaks

### Three overlapping surfaces, no shared trait
`AgentCipherclerk` (SDK, 107 methods), `AppCipherclerk` (framework, narrow),
and the node `/cipherclerk/*` HTTP routes are three hand-maintained projections
of the same identity. There is no shared trait capturing "the clerk can sign an
action / mint / attenuate," so each surface re-derives the subset it exposes and
they drift independently (e.g. the node routes expose `mint`/`attenuate` but not
`delegate`; the app handle exposes neither). A `Clerk` trait (sign/mint/attenuate/
authorize) implemented by all three would make the projection mechanical.

### `AgentCipherclerk` is doing far too many jobs
The struct (940) mixes: ed25519 identity, HD seed/mnemonic, the token wallet,
the receipt chain + IVC, stealth keys, **sovereign cell state**
(`sovereign_cells`, `sovereign_witness_sequences`), and an optional CapTP client.
Sovereign-cell witnessing (`make_sovereign` 4568, `execute_sovereign_turn` 4621,
`emit_witnessed_receipt` 4840, `convert_effects_to_vm` 5127 — a ~450-line method)
is a *protocol-engine* concern that has migrated into the credential holder. This
is where the model most visibly leaks: the clerk is simultaneously a wallet and a
sovereign-cell execution runtime. These want to be separate types sharing the
signing key.

### Error handling collapses structure at the boundaries
`SdkError` (sdk/src/error.rs) is reasonably structured, but the framework
deliberately flattens it to a `String` in `ExecutorSubmitError`
(`app-framework/src/cipherclerk.rs:511`) — apps lose the ability to branch on
nonce/auth/fee failures. The node routes flatten further to HTTP strings. A
wallet UI cannot distinguish "expired token" from "wrong federation" from
"insufficient fee" without parsing prose.

### Naming friction
- `delegate` / `delegate_with_parent` / `delegate_with_tree` /
  `delegate_with_tree_and_parent` (1354–1525) is a 4-way combinatorial fan-out of
  two orthogonal options (parent-anchored?, pre-generated membership proof?). A
  single `delegate(token, to, restrictions, DelegateOpts { parent, tree })` would
  collapse it.
- `share_capability` / `accept_capability` / `delegate_offline` (CapTP, 6252–6308)
  and `delegate` / `receive_signed_delegation` (macaroon, 1354 / 1583) are **two
  different delegation systems** with similar names on the same type. A reader
  cannot tell from the name which authority model (sturdyref vs macaroon chain)
  they are in. See §3 "one model or two."
- `shared_cclerk` is a `#[doc(hidden)]` legacy alias for `shared_cipherclerk`
  (app-framework 269) — leftover rename debt.

### `make_turn` nonce defaulting
`AppCipherclerk::make_turn` (177) defaults `nonce = 0` and relies on the
submission path to overwrite it; `EmbeddedExecutor::submit_turn` does
(`runtime/...:471`) and also silently rewrites `fee` from 0 to 10_000. A
caller who submits a `make_turn` result through a path that does *not* fix the
nonce gets a replay-able / rejected turn. The nonce should come from the chain
head at build time, not be a defaulted hole.

---

## 3. Missing features (against "first-class wallet-grade clerk for a verified ocap OS")

Each ranked **cheap-win** (implementable now) or **design-milestone** (needs real
design; do not stub).

### Implemented now (this audit's changes)

1. **Wallet hygiene: `forget_token(id)`** — *cheap win, DONE.* There was no way
   to drop a token from the wallet; `tokens` only grew. Added at
   `cipherclerk.rs` (after `find_token_by_id`). Test:
   `forget_token_removes_only_the_matching_id`.

2. **Local revocation: `revoke_token` / `is_locally_revoked` /
   `locally_revoked_count`** — *cheap win, DONE.* The clerk did **not** touch
   `dregg_token::RevocationRegistry` at all (confirmed: no `Revocation` symbol in
   the file before this change). The provider-side registry exists and is
   complete (`token/src/revocation.rs:546`, with `revoke`, `is_revoked`,
   `prove_non_revocation`, `publish_root`, `token_id_to_leaf`). Added a
   wallet-side advisory revocation set whose keying *agrees* with the registry
   leaf (`token_id_to_leaf`), so a local revocation lifts to a published,
   third-party-verifiable one without re-deriving identifiers. Tests:
   `revoke_token_records_and_forgets`,
   `local_revocation_keying_agrees_with_registry_leaf`. (Full registry
   integration — the clerk holding/publishing a `RevocationRegistry` and emitting
   non-revocation proofs — remains a milestone, item 9 below.)

3. **Namespaced HD sub-agents: `derive_sub_agent_at_path(path)`** —
   *cheap win, DONE.* `derive_sub_agent(i)` was hardwired to `dregg/{i}`; the
   underlying `from_seed_at_path` was private. Exposed arbitrary-path derivation
   so a clerk can carve per-device (`dregg/device/laptop`), per-app
   (`dregg/app/orderbook`), or per-purpose (`dregg/signing/cold`) sub-identities,
   all recoverable from one seed — the first building block of multi-device sync.
   Tests: `derive_sub_agent_at_path_namespaces_independent_keys`,
   `derive_sub_agent_at_path_requires_seed`.

### Design milestones (documented, not stubbed)

4. **Key rotation (re-keying a live identity).** *Milestone.* HD derivation gives
   *new* sub-identities cheaply, but there is no "rotate the agent's primary
   signing key while preserving cell ownership and the receipt chain." A real
   rotation needs a kernel-side rebinding (the cell's owner pubkey changes via an
   authenticated effect) plus a receipt-chain hinge linking old→new. This is a
   protocol feature, not a clerk one-liner; stubbing a `rotate_key()` that only
   swaps the in-memory key would be a toy that silently orphans the cell.

5. **Social / threshold recovery.** *Milestone.* No m-of-n guardian recovery, no
   Shamir/threshold split of the seed. Wallet-grade clerks for real users need
   this. Requires a threshold-signature or secret-sharing scheme and a recovery
   ceremony — real crypto design, explicitly out of scope to stub.

6. **Multi-device / sub-agent sync.** *Partial — milestone for the sync half.*
   `derive_sub_agent_at_path` (item 3) gives the *derivation* namespace. The
   missing half is **state sync**: receipt chains, held tokens, and sovereign
   cell state do not replicate across a citizen's devices. Needs a sync protocol
   (CRDT-merge of receipt chains / token sets) — milestone.

7. **Hardware key / WebAuthn / external signer.** *Milestone.* The signing key is
   an in-memory `ed25519_dalek::SigningKey` (942) with no abstraction over the
   signer. There is no `Signer` trait the clerk is generic over, so a YubiKey /
   WebAuthn / HSM / remote-signer cannot back the identity. The right design is a
   `trait ActionSigner { fn sign(&self, msg) -> Signature; fn public_key() }` that
   `AgentCipherclerk` holds instead of a concrete key — a structural refactor
   touching every `self.signing_key.sign(...)` site. Milestone, not a stub.

8. **Watch-only / view keys.** *Milestone, but a building block already exists.*
   There is no watch-only clerk (identity + receipt-chain observation without a
   signing key) — the struct holds `signing_key` unconditionally, so making it
   `Option` is invasive and touches every signing path. Notably, a **view key
   already exists at the stealth layer**: `stealth_meta_address()` (4530) exposes
   a view pubkey for scanning that does not reveal the signing key, and
   `scan_notes` (4552) uses the view key. Promoting that into a first-class
   watch-only `AgentCipherclerk` constructor is the milestone.

9. **Full revocation-registry integration.** *Milestone (item 2 is the cheap
   half).* The clerk should be able to hold/publish a `RevocationRegistry`,
   produce non-revocation proofs for tokens it presents
   (`prove_non_revocation`, `token/src/revocation.rs:644`), and verify a
   counterparty's. The cheap wallet-side set (item 2) keys-compatibly with the
   registry; wiring the proof flow through the clerk is the remaining design work.

10. **Caveat-vocabulary completeness.** *Mostly present; one real gap.* The
    `Attenuation` vocabulary (`token/src/traits.rs:98`) covers app/service action
    masks, feature globs, **validity windows** (`not_before`/`not_after`, time),
    confine-user, OAuth provider/scope, and **budget/rate** (`BudgetSpec`,
    rate-via-window). What is **expressible**: time, scope, rate/budget, resource
    globs. What is **not expressible**: *third-party caveats / discharge
    macaroons*. `MacaroonToken` carries `discharges` (`macaroon_backend.rs:97`
    `add_discharge`, 116 `discharges()`), but the `Attenuation` builder has **no
    way to add a third-party caveat**, and the clerk has no discharge-acquisition
    flow. This is the classic macaroon power feature (caveat "must present a proof
    of X from service Y") and is the one genuinely missing vocabulary item. Adding
    it touches the `token` crate's caveat encoding (a new `CAV_THIRD_PARTY` type,
    the retired slots 6/7 are available) plus a clerk-side discharge flow — too
    large for a one-liner, so it is a milestone, not a cheap win.

11. **Seal-to-recipient / encrypt-to-cap.** *Present for value transfer; gap for
    general capabilities.* There **is** a real encrypt-to-recipient path for
    *notes*: stealth addresses (`generate_stealth_address_for` 4539,
    `private_transfer` 4521) and `make_encrypted_turn` (2578,
    encrypt-to-executor-X25519). What is **missing** is "seal *this capability*
    (macaroon token / sturdyref) to recipient pubkey R so only R can open it" —
    delegation today transmits the `DelegatedToken` in the clear (it is
    signature-bound but not encrypted to the delegatee). A `seal_token_to(token,
    recipient_pk)` returning an X25519-sealed envelope is a plausible future cheap
    win, but it needs a decrypt counterpart and a wire format decision, so it is
    scoped as a small milestone rather than landed here.

12. **Audit log of mints / attenuations.** *Milestone.* The clerk records held
    tokens but keeps no append-only log of *operations* (who minted/attenuated/
    delegated what, when). For a wallet-grade clerk an operations journal (mirror
    of the receipt chain, but for credential ops) is expected. Milestone.

---

## 4. The key design question for the project lead

**Are the agent-side macaroon-token layer and the kernel-side capability crown
ONE model or TWO — and should they converge?**

Today they are **two distinct models that do not meet:**

- **Agent / macaroon layer** (`cipherclerk.rs`): HMAC-chained macaroons,
  attenuation = append-caveat, delegation = signed envelope, presentation = ZK
  membership proof against a *federation Merkle tree* of issuer proof-keys
  (`prove_authorization` 3209, `membership_proof`). Authority = "you hold a token
  whose issuer is in the federation tree and whose caveats permit the request."

- **Kernel capability crown** (`circuit/` + `cell/`): the in-circuit cap-root is
  an *openable sorted-Poseidon2 Merkle* over the cell's c-list, and the cell-side
  `compute_canonical_capability_root_felt` is proven byte-identical to the
  circuit's `cap_root` (`circuit/tests/cap_root_cell_circuit_differential.rs:1` —
  the "A2 differential," the keystone of cap Phase A). Authority =
  "`granted ⊆ held` is enforced in-circuit; `recKDelegateAtten` attenuates a cap
  with a proven `granted ≤ held` gate." This is the model the turn proof actually
  enforces.

These are **different Merkle trees, different leaves, different verifiers.** A
macaroon caveat is *not* a kernel cap; an in-circuit `granted ⊆ held` check is
*not* a macaroon HMAC walk. The clerk's `prove_authorization` proves membership
in the *federation* tree (issuer is enrolled), which is a weaker statement than
the kernel's `granted ⊆ held` over the *c-list* tree. A token can authorize a
request at the macaroon layer while the kernel's cap-root knows nothing about it.

**The convergence question:** should an attenuated macaroon token *be* a kernel
capability leaf — i.e. should `attenuate` produce a c-list entry whose
`granted ⊆ held` the turn proof checks, so the agent-side narrowing and the
in-circuit non-amplification are **the same arrow**? The memory note on the
cap-reshape plan (cell & circuit cap-roots were disjoint, unified in Phase A)
suggests the project already pulled cell↔circuit into one model. The open
question is whether the **macaroon/clerk layer** should be the *third* thing
pulled into that same root, or whether it stays a deliberately-separate
"federation-membership credential" layer that sits *above* the kernel cap crown.
This is the single most consequential design decision for the clerk and wants a
lead-level call.

My read: they **should converge**, with the macaroon layer becoming the
*ergonomic authoring surface* whose `attenuate`/`delegate` emit kernel cap-leaves
(`recKDelegateAtten`-shaped), so there is exactly one non-amplification law
proven once in-circuit rather than two narrowing stories (HMAC-chain monotonicity
and `granted ⊆ held`) that are only informally believed to agree.

---

## 5. Verdict — is the cipherclerk a first-class wallet-grade clerk?

**YELLOW.**

GREEN aspects: HD derivation, macaroon attenuation, the caveat-chain binding,
the signed-envelope delegation with per-use re-verification, the anti-blind-sign
explanation, sealed-value `HeldToken`, and the narrow app waist are all
genuinely wallet-grade and well-engineered — no stubs, no vacuous guarantees.

What holds it back from GREEN:
- **Two unconverged authority models** (§4) — the clerk's macaroon authority and
  the kernel cap crown are not the same arrow; non-amplification is proven in the
  kernel but only *believed* to track the macaroon chain.
- **No external-signer abstraction** (§3.7) — an in-memory ed25519 key is not
  wallet-grade for high-value identities; no hardware/WebAuthn path.
- **No recovery story** (§3.5) — no social/threshold recovery; losing the seed is
  terminal.
- **Third-party-caveat / discharge vocabulary missing** (§3.10) — the one real
  macaroon power feature absent.
- **The clerk is overloaded** (§2) — sovereign-cell execution has migrated into
  the credential holder; these want to be separate types.

None of these are RED (broken/vacuous); they are real, scoped, design-milestone
gaps. With external-signer abstraction, a recovery scheme, and a decision on
macaroon↔cap convergence, this is a GREEN wallet-grade clerk.

---

## Changes landed by this audit (`sdk/src/cipherclerk.rs`)

- `local_revocations: HashSet<String>` field on `AgentCipherclerk` (advisory
  wallet-side revocation set, registry-leaf-compatible).
- `forget_token(id) -> bool` — wallet hygiene.
- `revoke_token(id) -> bool`, `is_locally_revoked(id) -> bool`,
  `locally_revoked_count() -> usize` — local revocation that keys compatibly with
  `dregg_token::RevocationRegistry::token_id_to_leaf`.
- `derive_sub_agent_at_path(path) -> Result<Self, SdkError>` — namespaced HD
  sub-identities.

Tests (all green; `cargo test -p dregg-sdk cipherclerk` → 59 passed, 0 failed):
`forget_token_removes_only_the_matching_id`,
`revoke_token_records_and_forgets`,
`local_revocation_keying_agrees_with_registry_leaf`,
`derive_sub_agent_at_path_namespaces_independent_keys`,
`derive_sub_agent_at_path_requires_seed`.
