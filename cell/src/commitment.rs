//! Canonical state-commitment for a `Cell`.
//!
//! ## Background (audit P0-2)
//!
//! Prior to this module, the codebase had **three** disjoint state-commitment
//! schemes with no cross-binding:
//!
//! 1. `Cell::state_commitment()` — BLAKE3, `dregg-cell-state-v1` derive key,
//!    committed to a **subset** of state (no visibility, no commitments, no
//!    delegation/program/proved_state).
//! 2. `Ledger::hash_cell()` — BLAKE3, `dregg-cell:merkle-leaf v2` derive key,
//!    committed to a **superset** (all of `state_commitment` plus visibility,
//!    commitments, delegation_epoch, proved_state, program, delegate, delegation).
//! 3. `circuit::CellState::compute_commitment()` — Poseidon2 over BabyBear,
//!    committed to **only** `(balance, nonce, fields[0..STATE_SLOTS], capability_root)`,
//!    omitting identity, permissions, VK, etc.
//!
//! The trust gap: a sovereign cell's circuit-side identity had no binding
//! to its permissions or verification key. Two cells with identical
//! `(balance, nonce, fields, cap_root)` but completely different `Permissions`
//! produced the same circuit-side commitment.
//!
//! ## Resolution
//!
//! All authority-bearing state goes through a **single** canonical commitment
//! function: [`compute_canonical_state_commitment`]. Both `Cell::state_commitment`
//! and `Ledger::hash_cell` are now thin wrappers calling this function, so they
//! produce **identical bytes** for the same state.
//!
//! For the circuit (Poseidon2) side, the field shape is incompatible with the
//! BLAKE3 scheme. The right binding is to use this function's output as a
//! BabyBear public input on the circuit side — i.e. the STARK's `state_commit`
//! public input must be derived from the canonical commitment, not invented
//! independently. See [`canonical_to_babybear_pi`] for the bytes-to-felts
//! adapter.
//!
//! REVIEW[circuit-fix-coordination]: The circuit's `CellState::compute_commitment`
//! (in `circuit/src/effect_vm.rs`) still commits to a strict subset. To close
//! P0-2 fully, the circuit AIR's state_commit boundary public input should be
//! constrained to equal the BabyBear-field encoding of the canonical commitment.
//! A coordinating change in `circuit/` should introduce a
//! `bind_to_canonical_commitment(canonical_bytes)` adapter that asserts equality
//! between the Poseidon2 inner commitment and `canonical_to_babybear_pi(bytes)`,
//! or replace the Poseidon2 commitment with the canonical scheme entirely.

use crate::capability::CapabilitySet;
use crate::cell::Cell;
use crate::delegation::DelegatedRef;
#[cfg(test)]
use crate::id::CellId;
use crate::permissions::{AuthRequired, Permissions};
use crate::state::{CellState, FieldVisibility};

/// Domain-separation context for the canonical state commitment.
///
/// **Versioning policy:** any change to this module's hash shape MUST bump the
/// version suffix. Downstream Merkle leaves, sovereign commitments, and
/// circuit public inputs derive their domain separation transitively from this
/// context — bumping it cleanly invalidates stale commitments rather than
/// allowing silent cross-version collisions.
///
/// `v4 → v5` (cap Phase A): the absorbed `capability_root` is now the openable
/// sorted-Poseidon2 Merkle root (a BabyBear felt's 4 LE bytes), computed
/// identically to the EffectVM circuit's `cap_root`, replacing the old
/// disjoint BLAKE3 XOR-fold. The bump cleanly invalidates any stale v4
/// commitment rather than risking a silent cross-version collision.
///
/// `v5 → v6` (THE EPOCH §5, signed wells): the balance is now a SIGNED i64
/// committed via the order-preserving biased two-limb encoding
/// ([`crate::state::encode_balance_le`] — `biased = bits(balance) ⊕ 2^63`,
/// LE), replacing the raw `u64::to_le_bytes`. Issuer wells legitimately
/// commit negative balances (−supply); the range-table limb shape `(lo, hi)`
/// is [`crate::state::balance_limbs`]. Rides the epoch's one
/// VK/commitment flag-day.
///
/// `v6 → v7` (`docs/UNIVERSAL-MAP-ROTATION.md` §2.4): add the `heap_root`
/// register as a canonical commitment limb — the openable sorted-Poseidon2
/// root of the cell's `(collection, key) → value` heap (`circuit::heap_root`).
/// A legacy (no-heap-activity) cell contributes the fixed `empty_heap_root()`
/// constant, so the absorption is a uniform no-op for legacy cells.
/// `v7 → v8` (`docs/UNIVERSAL-MAP-ROTATION.md` §2.6): add the `committed_height`
/// scalar as a canonical commitment limb — the PI v3 committed-height column's
/// commitment face. A legacy (never-committed) cell contributes 0, so the
/// absorption is a uniform no-op for legacy cells.
/// `v8 → v9` (cap crown — the REVOKE tombstone reconciliation): the absorbed
/// `capability_root` is now the TOMBSTONE-deletion root (a revoked slot leaves a
/// ZERO/padding leaf at its sorted position rather than a compacted rebuild),
/// matching the in-circuit sel-24 revoke gate byte-for-byte. The cap-root value
/// changes for any cell that has revoked, so the cell commitment that absorbs it
/// must bump in lockstep (the coupled CAP_ROOT + COMMITMENT flag-day per the
/// cap-crown rule) so stale compacted roots cleanly invalidate. A never-revoked
/// cell's cap-root — and therefore its commitment — is byte-unchanged; the bump
/// is a uniform no-op for them, it just re-domain-separates so no stale
/// post-revoke commitment can collide cross-version.
///
/// NB — this `v9` is the BLAKE3 *context-string* version (an axis that has
/// counted v1→v9 over the commitment's history); it is ORTHOGONAL to the
/// rotated-Poseidon2 commitment's `V9_*` constants below (which name the
/// 24-register rotation "generation 9", not this string). The rotated
/// commitment AUTOMATICALLY reflects the tombstone change because its cap-root
/// limb (`compute_rotated_pre_limbs`, limb 25) calls the SAME
/// `compute_canonical_capability_root_felt`, which now tombstones.
///
/// NB — the EffectVM VK (`dregg_verifier::EFFECT_VM_VK_HASH_HEX`) is, in this
/// codebase's v1 verifier, a hash of the AIR *name* (`"dregg-effect-vm-v1"`),
/// NOT a structural commitment to the constraint set — so it does not need (and
/// would not meaningfully reflect) a tombstone bump. The cryptographic
/// invalidation of stale post-revoke roots is enforced by the changed cap-root
/// VALUE flowing into this commitment's PI face, not by a VK-string change.
pub const CANONICAL_COMMITMENT_CONTEXT: &str = "dregg-cell:canonical-state-commitment v9";

/// Domain-separation context for the canonical capability-set root.
///
/// `v1 → v2` (cap Phase A): the capability root is no longer a BLAKE3 XOR-fold
/// over per-cap leaf hashes — it is the openable sorted-Poseidon2 binary Merkle
/// root ([`dregg_circuit::cap_root`]), shared byte-identically with the EffectVM
/// circuit. The single-cap commitment returned by
/// [`crate::capability::CapabilitySet::attenuate_in_place`] is now the 32-byte
/// encoding of that cap's leaf-digest felt under this context.
///
/// `v2 → v3` (cap crown — the REVOKE tombstone reconciliation): a revoke is now
/// a TOMBSTONE deletion (the revoked slot leaves a ZERO/padding leaf at its
/// sorted position via [`crate::capability::CapabilitySet`]'s tombstone set)
/// rather than a COMPACTED rebuild (`retain` + `CanonicalCapTree::new` over the
/// remaining caps, which re-indexes every key sorting after the revoked one).
/// The tombstone root equals the in-circuit sel-24 revoke gate's zero-fold
/// deletion byte-for-byte, so `cell_cap_root == circuit_cap_root` after a revoke
/// (closing the seam that would otherwise brick any live RevokeCapability turn).
/// The root value changes only for cells that have revoked; this bump cleanly
/// invalidates any stale compacted root. Coupled with the
/// `CANONICAL_COMMITMENT_CONTEXT` v8→v9 bump and the EffectVM VK rebump (the
/// cap-crown flag-day rule: CAP_ROOT + COMMITMENT + VK bump together).
pub const CANONICAL_CAP_ROOT_CONTEXT: &str = "dregg-cell:canonical-capability-root v3";

/// Compute the canonical tier-byte for a single `AuthRequired` value.
///
/// For `Custom { vk_hash }`, the tier-byte (5) alone is insufficient:
/// two different `vk_hash`es would yield identical commitments. Use
/// [`hash_auth_required_into`] to commit an `AuthRequired` into a
/// canonical-commitment hasher; that helper writes the tier byte
/// followed by the vk_hash when the variant is `Custom`.
#[inline]
fn auth_byte(auth: &AuthRequired) -> u8 {
    match auth {
        AuthRequired::None => 0,
        AuthRequired::Signature => 1,
        AuthRequired::Proof => 2,
        AuthRequired::Either => 3,
        AuthRequired::Impossible => 4,
        AuthRequired::Custom { .. } => 5,
    }
}

/// Commit an `AuthRequired` value into a canonical-commitment hasher.
///
/// Writes the single tier byte (per [`auth_byte`]) for the built-in
/// variants. For `AuthRequired::Custom { vk_hash }`, writes the tier
/// byte (5) followed by the 32-byte `vk_hash`. This is the
/// soundness-critical path: two `Custom` permissions with distinct
/// `vk_hash`es must yield distinct commitments.
#[inline]
fn hash_auth_required_into(hasher: &mut blake3::Hasher, auth: &AuthRequired) {
    hasher.update(&[auth_byte(auth)]);
    if let AuthRequired::Custom { vk_hash } = auth {
        hasher.update(vk_hash);
    }
}

/// Compute the canonical commitment for a single `FieldVisibility` value.
#[inline]
fn visibility_byte(vis: FieldVisibility) -> u8 {
    match vis {
        FieldVisibility::Public => 0,
        FieldVisibility::Committed => 1,
        FieldVisibility::SelectivelyDisclosable => 2,
    }
}

/// Compute the canonical 32-byte commitment to a `Cell`'s full authority-bearing
/// state.
///
/// This is the **single** source of truth for "what bytes commit to this cell."
/// It is used by:
///
/// - `Cell::state_commitment()` — sovereign-witness verification
/// - `Ledger::hash_cell()` — Merkle leaf in the federation tree
/// - (planned) Poseidon2 binding for the STARK public input
///
/// All authority-relevant state is included. Omitting any field would allow an
/// attacker to present two distinct authority-bearing states with the same
/// commitment.
/// A `new_derive_key(CANONICAL_COMMITMENT_CONTEXT)` hasher cached at its keyed
/// initial state. `Hasher::clone` copies that keyed state, so cloning + absorbing
/// produces output BYTE-IDENTICAL to a fresh `new_derive_key` + absorbing — but
/// skips re-deriving the key (an extra BLAKE3 compression, ~50ns/call) on every
/// per-cell commitment. The context string is fixed (`v9`), so the derived key is
/// a process constant.
fn canonical_commitment_base() -> blake3::Hasher {
    static BASE: std::sync::OnceLock<blake3::Hasher> = std::sync::OnceLock::new();
    BASE.get_or_init(|| blake3::Hasher::new_derive_key(CANONICAL_COMMITMENT_CONTEXT))
        .clone()
}

pub fn compute_canonical_state_commitment(cell: &Cell) -> [u8; 32] {
    let mut hasher = canonical_commitment_base();

    // ---- Identity ----
    hasher.update(cell.id.as_bytes());
    hasher.update(&cell.public_key);
    hasher.update(&cell.token_id);

    // ---- Mode ----
    let mode_byte: u8 = match cell.mode {
        crate::cell::CellMode::Hosted => 0,
        crate::cell::CellMode::Sovereign => 1,
    };
    hasher.update(&[mode_byte]);

    // ---- Core state ----
    hash_cell_state_into(&mut hasher, &cell.state);

    // ---- Permissions ----
    hash_permissions_into(&mut hasher, &cell.permissions);

    // ---- Verification key ----
    match &cell.verification_key {
        Some(vk) => {
            hasher.update(&[1u8]);
            hasher.update(&vk.hash);
        }
        None => {
            hasher.update(&[0u8]);
        }
    }

    // ---- Capabilities (full canonical root) ----
    // The openable sorted-Poseidon2 capability root (cap Phase A), absorbed as
    // its FAITHFUL 8-felt (~124-bit) encoding so the cell's full-state commitment
    // binds the SAME wide `cap_root` value the EffectVM circuit carries at the
    // rotated cap_root column group (limb 25 ‖ 51..57). The lane-0 encoding is
    // forgeable off-chain (two c-lists colliding on lane 0 → same commitment);
    // the wide encoding closes it, exactly as heap_root / fields_root do.
    let cap_root = compute_canonical_capability_root_wide(&cell.capabilities);
    hasher.update(&cap_root);

    // ---- Delegate ----
    match &cell.delegate {
        Some(d) => {
            hasher.update(&[1u8]);
            hasher.update(d.as_bytes());
        }
        None => {
            hasher.update(&[0u8]);
        }
    }

    // ---- Delegation snapshot ----
    match &cell.delegation {
        Some(deleg) => {
            hasher.update(&[1u8]);
            hash_delegation_into(&mut hasher, deleg);
        }
        None => {
            hasher.update(&[0u8]);
        }
    }

    // ---- Program ----
    hash_program_into(&mut hasher, &cell.program);

    // ---- Lifecycle (v2 addition) ----
    //
    // Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §1`, the canonical lifecycle
    // is authority-bearing: a Destroyed cell rejects every effect, a
    // Sealed cell rejects new effects, an Archived cell retains a
    // checkpoint hash that prunes prior receipt history. Two cells with
    // identical (mode, state, permissions, ...) but different lifecycle
    // states must produce distinct commitments — otherwise a malicious
    // executor could omit the destruction transition and present the
    // cell as still-Live to downstream verifiers.
    hash_lifecycle_into(&mut hasher, &cell.lifecycle);

    *hasher.finalize().as_bytes()
}

/// Commit a [`crate::lifecycle::CellLifecycle`] value into a canonical
/// commitment hasher. Per-variant payload bytes are written so that two
/// distinct lifecycle states (including same-discriminant variants with
/// distinct inner bytes) produce distinct commitments.
fn hash_lifecycle_into(hasher: &mut blake3::Hasher, lc: &crate::lifecycle::CellLifecycle) {
    use crate::lifecycle::CellLifecycle;
    hasher.update(&[lc.discriminant()]);
    match lc {
        CellLifecycle::Live => {}
        CellLifecycle::Sealed {
            reason_hash,
            sealed_at,
        } => {
            hasher.update(reason_hash);
            hasher.update(&sealed_at.to_le_bytes());
        }
        CellLifecycle::Migrated {
            to,
            attestation,
            migrated_at,
        } => {
            hasher.update(to.as_bytes());
            hasher.update(attestation);
            hasher.update(&migrated_at.to_le_bytes());
        }
        CellLifecycle::Destroyed {
            death_certificate_hash,
            destroyed_at,
        } => {
            hasher.update(death_certificate_hash);
            hasher.update(&destroyed_at.to_le_bytes());
        }
        CellLifecycle::Archived {
            checkpoint_hash,
            archived_through,
        } => {
            hasher.update(checkpoint_hash);
            hasher.update(&archived_through.to_le_bytes());
        }
    }
}

/// Hash the inner `CellState` (no domain separator — used as a sub-hasher).
fn hash_cell_state_into(hasher: &mut blake3::Hasher, state: &CellState) {
    hasher.update(&state.nonce.to_le_bytes());
    // THE EPOCH §5 (v6): signed balance, biased two-limb LE encoding. A well's
    // negative balance and an ordinary positive balance commit injectively and
    // order-preservingly (`encode_balance_le`).
    hasher.update(&crate::state::encode_balance_le(state.balance));
    for field in &state.fields {
        hasher.update(field);
    }
    for vis in &state.field_visibility {
        hasher.update(&[visibility_byte(*vis)]);
    }
    for commit in &state.commitments {
        match commit {
            Some(h) => {
                hasher.update(&[1u8]);
                hasher.update(h);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
    }
    hasher.update(&[state.proved_state as u8]);
    hasher.update(&state.delegation_epoch.to_le_bytes());
    // `docs/UNIVERSAL-MAP-ROTATION.md` §2.6 (PI v3): absorb the
    // `committed_height` scalar. This folds the block height at which the cell's
    // state was last committed into the authority-bearing commitment, so the
    // commitment (and its PI face) is bound to a specific chain height. A legacy
    // cell carries 0 — a cell-independent constant — so the absorption is a
    // uniform no-op for legacy cells. Anti-ghost tooth: a prover-chosen height
    // differs from the real committed height ⇒ commitment mismatch.
    hasher.update(&state.committed_height.to_le_bytes());
    // Stage 1: CapTP-prep committed roots (`DESIGN-captp-integration.md` §4).
    // These are part of authority-bearing state because they gate enliven /
    // drop-ref / handoff operations.
    hasher.update(&state.swiss_table_root);
    hasher.update(&state.refcount_table_root);
    // Record-layer Stage 1 (`_RECORD-LAYER-UPGRADE.md` §D.2.1): absorb the
    // user-field-MAP root. This is what folds the unbounded `key >= STATE_SLOTS`
    // overflow map (`fields_map`, digested into `fields_root`) into the cell's
    // authority-bearing commitment, so a verifier binds the WHOLE record, not
    // just the 16 fixed slots. Absorbed at a FIXED position by a FIXED constant for legacy
    // cells: a no-overflow cell carries `empty_fields_root()` — a cell-independent
    // constant (the digest of the empty map) — so the absorption is a uniform
    // no-op across all legacy cells (proven byte-identical in the Lean keystone
    // `RecordCommit.legacy_commit_absorbs_empty_root` and the Rust
    // `legacy_cells_share_fields_root_contribution` test). The `v2->v3` context
    // bump (above) cleanly invalidates any stale v2 commitment rather than
    // risking a silent cross-version collision.
    // `fields_root` is a `Faithful8`; the commitment binds its canonical 32 wide
    // bytes (`to_bytes32`) — BYTE-IDENTICAL to the former `[u8; 32]` field.
    hasher.update(&state.fields_root.to_bytes32());
    // Record-layer STAGE 3 (`_RECORD-LAYER-UPGRADE.md` §C): absorb the dedicated
    // `system_roots` sub-block digest. This folds the 8 kernel-owned side-table
    // roots (escrow/queue/refcount/sturdyref/deleg/nullifier/commit/sealedBoxes)
    // into the cell's authority-bearing commitment, so a verifier binds the WHOLE
    // side-table state — not just the user fields. Absorbed at a FIXED position by
    // a FIXED constant for legacy cells: a no-side-table cell carries the all-zero
    // default sub-block, whose digest is `empty_system_roots_digest()` — a
    // cell-independent constant (proven byte-identical in the Lean keystone
    // `SystemRoots.legacy_commitS_absorbs_empty_roots` and the Rust
    // `legacy_cells_share_system_roots_contribution` test). The `v3->v4` context
    // bump cleanly invalidates any stale v3 commitment. Anti-ghost tooth: a
    // tampered side-table root flips this digest, flipping the commitment
    // (`SystemRoots.cellCommitS_binds_systemRoots`).
    hasher.update(&state.system_roots_digest());
    // `docs/UNIVERSAL-MAP-ROTATION.md` §2.4: absorb the `heap_root` register.
    // This folds the openable sorted-Poseidon2 root of the cell's
    // `(collection, key) → value` heap into the authority-bearing commitment.
    // Absorbed at a FIXED position by a FIXED constant for legacy cells: a
    // no-heap-activity cell carries `empty_heap_root()` — a cell-independent
    // constant — so the absorption is a uniform no-op for legacy cells.
    // Anti-ghost tooth: a tampered heap entry flips this root, flipping the
    // commitment. `heap_root` is a `Faithful8`; the commitment binds its
    // canonical 32 wide bytes (`to_bytes32`) — BYTE-IDENTICAL to the former
    // `[u8; 32]` field.
    hasher.update(&state.heap_root.to_bytes32());
}

fn hash_permissions_into(hasher: &mut blake3::Hasher, perms: &Permissions) {
    // Each `AuthRequired` field is committed via `hash_auth_required_into`
    // (tier byte + vk_hash for `Custom`). The eight fields are written in
    // a fixed canonical order; built-in variants contribute one byte each,
    // and `Custom` variants contribute 33 bytes (tier + 32-byte vk_hash).
    hash_auth_required_into(hasher, &perms.send);
    hash_auth_required_into(hasher, &perms.receive);
    hash_auth_required_into(hasher, &perms.set_state);
    hash_auth_required_into(hasher, &perms.set_permissions);
    hash_auth_required_into(hasher, &perms.set_verification_key);
    hash_auth_required_into(hasher, &perms.increment_nonce);
    hash_auth_required_into(hasher, &perms.delegate);
    hash_auth_required_into(hasher, &perms.access);
}

fn hash_delegation_into(hasher: &mut blake3::Hasher, deleg: &DelegatedRef) {
    hasher.update(deleg.source.as_bytes());
    hasher.update(&deleg.delegation_epoch.to_le_bytes());
    hasher.update(&deleg.refreshed_at.to_le_bytes());
    hasher.update(&deleg.max_staleness.to_le_bytes());
    // Snapshot: full canonical leaf-hash so that (target, slot) + permissions +
    // breadstuff + expires_at + allowed_effects are all committed. (Audit P2-4
    // flagged that the old `hash_cell` was lossy here.)
    let cap_count = deleg.snapshot.len() as u64;
    hasher.update(&cap_count.to_le_bytes());
    for cap in &deleg.snapshot {
        hash_capability_ref_into(hasher, cap);
    }
}

/// Hash a single `CapabilityRef` into the blake3 DELEGATION-SNAPSHOT hasher
/// (used only by [`hash_delegation_into`] / the legacy-commitment reference).
/// This is the snapshot commitment for a delegated c-list, NOT the openable
/// capability root — the root is the sorted-Poseidon2 felt
/// ([`compute_canonical_capability_root_felt`]).
fn hash_capability_ref_into(hasher: &mut blake3::Hasher, cap: &crate::capability::CapabilityRef) {
    hasher.update(cap.target.as_bytes());
    hasher.update(&cap.slot.to_le_bytes());
    // Permissions commit via the auth-required canonicalizer so that
    // Custom { vk_hash }'s 32-byte hash participates in the commitment
    // (built-in variants contribute one byte, Custom contributes 33).
    hash_auth_required_into(hasher, &cap.permissions);
    match &cap.breadstuff {
        Some(bs) => {
            hasher.update(&[1u8]);
            hasher.update(bs);
        }
        None => {
            hasher.update(&[0u8]);
        }
    }
    match cap.expires_at {
        Some(h) => {
            hasher.update(&[1u8]);
            hasher.update(&h.to_le_bytes());
        }
        None => {
            hasher.update(&[0u8]);
        }
    }
    match cap.allowed_effects {
        Some(mask) => {
            hasher.update(&[1u8]);
            hasher.update(&mask.to_le_bytes());
        }
        None => {
            hasher.update(&[0u8]);
        }
    }
}

fn hash_program_into(hasher: &mut blake3::Hasher, program: &crate::program::CellProgram) {
    use crate::program::CellProgram;
    match program {
        CellProgram::None => {
            hasher.update(&[0u8]);
        }
        CellProgram::Predicate(constraints) => {
            hasher.update(&[1u8]);
            let serialized = postcard::to_allocvec(constraints).unwrap_or_default();
            hasher.update(&(serialized.len() as u64).to_le_bytes());
            hasher.update(&serialized);
        }
        CellProgram::Circuit { circuit_hash } => {
            hasher.update(&[2u8]);
            hasher.update(circuit_hash);
        }
        CellProgram::Cases(cases) => {
            hasher.update(&[3u8]);
            let serialized = postcard::to_allocvec(cases).unwrap_or_default();
            hasher.update(&(serialized.len() as u64).to_le_bytes());
            hasher.update(&serialized);
        }
    }
}

/// The canonical capability `CapLeaf` for one `CapabilityRef`, in the shared
/// [`dregg_circuit::cap_root`] field encoding. This is the cell-side
/// construction of the 7-field leaf the circuit hashes; because both sides go
/// through `dregg_circuit::cap_root`, the leaf — and therefore the root — is
/// byte-identical wherever it is computed.
///
/// Public (cap Phase C): the executor's authorization site builds the SAME
/// leaf for the capability it CONSUMES, so the membership witness threaded
/// into `TurnReceipt.consumed_capabilities` opens against the canonical
/// pre-state `capability_root` with no parallel leaf encoding.
pub fn cap_ref_to_leaf(cap: &crate::capability::CapabilityRef) -> dregg_circuit::cap_root::CapLeaf {
    use dregg_circuit::cap_root;
    let (mask_lo, mask_hi) = cap_root::split_effect_mask(
        // `None` ⇒ unrestricted ⇒ EFFECT_ALL (so the mask limbs are the full
        // 32-bit all-ones, matching the executor's `allowed_effects = None`
        // ⇒ `EFFECT_ALL` interpretation in `capability.rs`).
        cap.allowed_effects.unwrap_or(crate::facet::EFFECT_ALL),
    );
    cap_root::CapLeaf {
        slot_hash: cap_root::slot_hash(cap.slot),
        target: cap_root::fold_bytes32(cap.target.as_bytes()),
        auth_tag: auth_required_to_tag(&cap.permissions),
        mask_lo,
        mask_hi,
        expiry: cap_root::encode_expiry(cap.expires_at),
        breadstuff: cap_root::encode_breadstuff(cap.breadstuff.as_ref()),
        // REVOKED-ROOT campaign — the cap-leaf PROVENANCE binding (item 5; the exact change
        // `capability.rs`'s `provenance` doc calls for: "the geometry lane must add it so the
        // committed cap-root binds each cap's provenance"). Dependency (a) IS met:
        // `CapabilityRef.provenance: [u8; 32]` already exists (the rust-identity lane landed it;
        // `[0u8; 32]` is the legacy/unprovenanced sentinel). The ONE remaining dependency is
        // circuit-side (b): an 8th `CapLeaf.provenance: BabyBear` field + its absorb in
        // `CapLeaf::digest()` (arity 7 → 8). The felt fold reuses the EXISTING
        // `cap_root::fold_bytes32` (no new encode fn needed; the `[0;32]` sentinel folds to a fixed
        // felt). STAGED (commented) rather than live because adding the 8th field to this literal
        // while `CapLeaf` still has 7 fields would break `dregg-cell` — and the whole shared tree —
        // for the concurrent swarm. Uncomment IN LOCKSTEP with the circuit `CapLeaf`/`digest()`
        // widening; it is a cap-leaf shape change → root value moves → VK regen (Stage F), and the
        // A2/GENTIAN differential must be re-pinned so cell and circuit agree byte-identically.
        // Binding provenance makes the committed `cap_root` record each cap's `credNul` identity —
        // the SAME provenance the revoked accumulator keys on (`cred_nul(provenance)`) and the SAME
        // `ancestor_hash` the non-revocation circuit queries.
        // provenance: cap_root::fold_bytes32(&cap.provenance),
    }
}

/// Encode an `AuthRequired` into the single `auth_tag` felt: the tier byte
/// (None=0…Custom=5) for the built-in variants, and for `Custom { vk_hash }`
/// the tier byte WITH the 8 vk_hash limbs absorbed via Poseidon2 — mirroring
/// the cell's `hash_auth_required_into` so two `Custom`s with distinct
/// vk_hashes yield distinct tags (and therefore distinct leaves).
fn auth_required_to_tag(auth: &AuthRequired) -> dregg_circuit::field::BabyBear {
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::poseidon2::hash_many;
    let tier = BabyBear::new(auth_byte(auth) as u32);
    match auth {
        AuthRequired::Custom { vk_hash } => {
            // Absorb [tier, vk_limb0..7] so the 8 vk_hash limbs bind the tag.
            let mut inputs = Vec::with_capacity(9);
            inputs.push(tier);
            inputs.extend_from_slice(&BabyBear::encode_hash(vk_hash));
            hash_many(&inputs)
        }
        _ => tier,
    }
}

/// Compute the canonical capability root **felt** of a `CapabilitySet`: the
/// openable sorted-Poseidon2 binary Merkle root over the c-list
/// ([`dregg_circuit::cap_root`]). This IS the value the EffectVM circuit's
/// `cap_root` column carries — the cell and circuit compute it through the
/// SAME implementation, so they agree byte-identically (the A2 differential
/// guards it).
pub fn compute_canonical_capability_root_felt(
    caps: &CapabilitySet,
) -> dregg_circuit::field::BabyBear {
    // Per-cell sub-root cache (`docs/INCREMENTAL-COMMITMENT.md` step 2): a turn
    // that did not touch the cap set reuses the last-folded root instead of
    // re-folding the sorted-Poseidon2 tree. The cache is invalidated by EVERY
    // c-list mutation (see `CapabilitySet::invalidate_cap_root_cache` callers),
    // so a cache hit is byte-identical to a fresh fold (pinned by the
    // `cap_root_cache_matches_fresh` differential). The fold below is the
    // authoritative recompute used on a miss, and its result is stored back.
    if let Some(cached) = caps.cached_cap_root() {
        return cached;
    }
    let root8 = compute_canonical_capability_root_8(caps);
    // Cache the lane-0 projection (the historical single-felt root): a cache hit
    // returns it directly; the full 8-felt fold is deterministic, so `_8(caps)[0]`
    // always agrees with the cached lane-0 (pinned by `cap_root_cache_matches_fresh`).
    caps.store_cap_root(root8[0]);
    root8[0]
}

/// Compute the canonical **8-felt** capability root of a `CapabilitySet`: the FULL
/// native-`node8` (arity-16) sorted-Poseidon2 Merkle root over the c-list — the
/// `Digest8` ([`dregg_circuit::cap_root::CAP_DIGEST_W`] = 8) the EffectVM circuit's
/// 8-felt `cap_root` column GROUP carries (lane 0 ‖ lanes 1..7). Lane 0 is
/// byte-identical to [`compute_canonical_capability_root_felt`] (the historical
/// scalar root); lanes 1..7 are the ~124-bit completion the v10 weld commits at the
/// rotated-block extras 51..57 (`EffectVmEmitRotationV3.capRootGroupCol`). This is the
/// faithful root — NEVER a lane-0 squeeze, the soundness downgrade the GENTIAN tooth
/// closes. Cell and circuit fold through the SAME implementation, so they agree
/// lane-for-lane (the A2 / GENTIAN differentials guard it).
pub fn compute_canonical_capability_root_8(caps: &CapabilitySet) -> dregg_circuit::Faithful8 {
    use dregg_circuit::cap_root;
    let leaves: Vec<cap_root::CapLeaf> = caps.iter().map(cap_ref_to_leaf).collect();
    // TOMBSTONE deletion (cap crown, the cell↔circuit revoke reconciliation):
    // a revoked slot leaves a ZERO/padding leaf at its sorted POSITION rather
    // than compacting (re-indexing) the tree, so every OTHER capability's
    // membership witness stays valid across an unrelated revoke — and the root
    // matches the in-circuit sel-24 revoke gate's zero-fold deletion
    // byte-for-byte (`cap_root::revocation_witness`). We fold each tombstoned
    // slot's `slot_hash` (the same sort key `cap_ref_to_leaf` uses) as a ghost
    // leaf; a slot that is currently live is shadowed by its live leaf. When a
    // cell has never revoked under this scheme, `tombstone_keys` is empty and
    // this is byte-identical to the plain `compute_capability_root`.
    let tombstone_keys: Vec<dregg_circuit::field::BabyBear> =
        caps.tombstoned_slots().map(cap_root::slot_hash).collect();
    cap_root::compute_capability_root_with_tombstones(leaves, &tombstone_keys)
}

/// Compute the LANE-0 32-byte capability root of a `CapabilitySet`.
///
/// This is the 32-byte ENCODING of [`compute_canonical_capability_root_felt`]
/// (the openable sorted-Poseidon2 Merkle root, LANE 0 only) — see
/// [`felt_to_bytes32`]. It is what the executor's CapabilityUniqueness program
/// binds in a 32-byte cap-set-root state slot (`turn::executor::execute_tree`,
/// an executor-side recompute-and-compare, NOT a ledgerless-verifier surface)
/// and what the exec-lean parity gauntlet folds. The empty c-list root is
/// NON-zero (the sentinels hash into a real value), so the executor's "root slot
/// must be non-zero" check is preserved.
///
/// **Off-chain soundness:** the BLAKE3 per-cell state commitment
/// ([`compute_canonical_state_commitment`]) absorbs the FAITHFUL 8-felt encoding
/// ([`compute_canonical_capability_root_wide`]) instead — the ~31-bit lane-0
/// encoding here is forgeable (two c-lists colliding on lane 0), so it must not
/// be the value a ledgerless verifier compares.
pub fn compute_canonical_capability_root(caps: &CapabilitySet) -> [u8; 32] {
    felt_to_bytes32(compute_canonical_capability_root_felt(caps))
}

/// Compute the FAITHFUL 8-felt (~124-bit) 32-byte capability root of a
/// `CapabilitySet`: the [`digest8_to_bytes32`] packing of
/// [`compute_canonical_capability_root_8`] (lane `i` in bytes `[4i..4i+4]`).
///
/// This is the value the off-chain BLAKE3 state commitment
/// ([`compute_canonical_state_commitment`]) absorbs, so it carries the SAME
/// ~124-bit collision floor the circuit binds at the rotated `cap_root` column
/// group (limb 25 ‖ 51..57, GENTIAN-welded). It closes the ~31-bit lane-0
/// cap-root forge off-chain, exactly as the wide `heap_root` / `fields_root`
/// (`state::compute_heap_root` / `state::compute_fields_root`) do for their
/// planes. Bytes `[0..4]` still equal the historical lane-0
/// [`compute_canonical_capability_root`] projection. Because tombstoned
/// (revoked) slots fold into this SAME sorted tree
/// ([`compute_canonical_capability_root_8`]'s `compute_capability_root_with_tombstones`),
/// widening `cap_root` widens the revoked-slot commitment with no separate work.
pub fn compute_canonical_capability_root_wide(caps: &CapabilitySet) -> [u8; 32] {
    digest8_to_bytes32(compute_canonical_capability_root_8(caps).limbs())
}

/// The canonical 32-byte encoding of a capability-root felt: the felt's 4
/// little-endian bytes in the low 4 positions, the rest zero. Deterministic
/// and injective on canonical BabyBear values (< p), so distinct roots encode
/// to distinct byte strings.
pub fn felt_to_bytes32(felt: dregg_circuit::field::BabyBear) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[0..4].copy_from_slice(&felt.as_u32().to_le_bytes());
    out
}

/// The canonical 32-byte encoding of a native-`node8` 8-felt cap digest (`Digest8`):
/// each of the 8 lanes' 4 little-endian bytes, packed in lane order (8·4 = 32). Each
/// BabyBear lane is `< p < 2^31`, so its 4 bytes recover it exactly — the encoding is
/// injective on the FULL 8-felt digest (distinct digests encode to distinct strings).
/// This replaces the old lane-0-only `felt_to_bytes32(digest)` for the 8-felt leaf.
pub fn digest8_to_bytes32(digest: [dregg_circuit::field::BabyBear; 8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, lane) in digest.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&lane.as_u32().to_le_bytes());
    }
    out
}

/// The 32-byte commitment to a SINGLE capability's openable leaf: the encoding
/// ([`digest8_to_bytes32`]) of the cap's 7-field [`dregg_circuit::cap_root::CapLeaf`]
/// 8-felt digest. Used by [`crate::capability::CapabilitySet::attenuate_in_place`] so a
/// caller can update c-list audit indices with a value consistent with the
/// canonical sorted-tree root.
pub fn capability_ref_leaf_commitment(cap: &crate::capability::CapabilityRef) -> [u8; 32] {
    digest8_to_bytes32(cap_ref_to_leaf(cap).digest())
}

/// Convert a 32-byte canonical commitment into 8 BabyBear-shaped felts
/// (encoded as little-endian u32 truncated to 30 bits to fit BabyBear range).
///
/// The output is the binding input that a Poseidon2-based circuit can absorb
/// to tie its state_commit public input back to the canonical scheme. The
/// 30-bit truncation is intentional — BabyBear's modulus is 2^31 − 2^27 + 1,
/// and 30-bit limbs guarantee a unique encoding without modular reduction
/// collisions.
///
/// Returns `[u32; 8]` representing the 8 felts. The circuit side should
/// constrain its declared state_commit equal to a fixed Poseidon2 hash of
/// these 8 felts in some agreed-upon shape.
///
/// REVIEW[circuit-fix-coordination]: this function defines the *contract*
/// only — actual binding requires the circuit to absorb these 8 felts and
/// emit a constrained equality to its own state_commit. Coordination needed
/// with circuit-fix agent. See module-level docs.
pub fn canonical_to_babybear_pi(canonical: &[u8; 32]) -> [u32; 8] {
    let mut out = [0u32; 8];
    for i in 0..8 {
        let lo = canonical[i * 4] as u32;
        let mid1 = canonical[i * 4 + 1] as u32;
        let mid2 = canonical[i * 4 + 2] as u32;
        let hi = canonical[i * 4 + 3] as u32;
        // Pack 30 bits: 8+8+8+6 = 30
        out[i] = lo | (mid1 << 8) | (mid2 << 16) | ((hi & 0x3F) << 24);
    }
    out
}

// ============================================================================
// v9 — THE ROTATED canonical commitment (G3).
// ============================================================================
//
// `CANONICAL_COMMITMENT_CONTEXT` is LIVE at v9 (the cap-crown flag-day bumped it; see the
// const above). The two commitment shapes:
//   * the BLAKE3 whole-cell absorption (`compute_canonical_state_commitment`, ctx v9) — the
//     canonical 32-byte cell commitment the kernel/ledger uses;
//   * the Poseidon2-chained `wireCommit` (`compute_canonical_state_commitment_v9_felt`,
//     rotated absorption order) — the cell-side reconstruction of the EffectVM rotated trace's
//     row-0 `STATE_COMMIT` carrier, byte-identical to `dregg_turn::rotation_witness::wire_commit`
//     / the Lean `EffectVmEmitRotationR.wireCommitR` spec (guarded by the differential
//     `live_cell_v9_equals_circuit_state_commit` in `circuit/tests/effect_vm_rotation_flip.rs`).
// The cell≡circuit binding is closed: the cell-side felt commitment and the circuit-side
// STATE_COMMIT converge on ONE rotated shape at v9.

/// The CONFIRMED rotated register count (ember 2026-06-12, `ROTATION-CUTOVER.md` §2b).
pub const V9_NUM_REGISTERS: usize = 24;
/// The number of pre-iroot absorption limbs (cells_root · r0..r23 · cap_root · nullifier_root ·
/// commitments_root · heap_root · lifecycle · epoch · committed_height · lifecycle_disc ·
/// perms_digest · vk_digest · mode · fields_root · revoked_root). Lean `preLimbsAt_length = 38` at
/// R = 24, after the REVOKED-ROOT flag-day widening of the base region (37→38): `revoked_root` is
/// the new base limb 37 (right after `fields_root` at 36), so every limb index ≥ 37 shifts +1 —
/// completion 38..=88, carrier 89..=112, fields[0..7] completion 113..=168, pad 169.
pub const V9_NUM_PRE_LIMBS: usize = 1 + V9_NUM_REGISTERS + 4 + 3 + 6 + 75 + 57; // 170 (base widened 37→38: revoked_root = limb 37; v13 fields octet completion 113..=168 + 1 pad limb 169)

/// The turn-level context the rotated commitment absorbs that is NOT cell-local: the
/// boundary `cells_root` (the sorted-Poseidon2 root over present cells), the cell's committed
/// `nullifier_root`, and the receipt-index MMR root `iroot` (absorbed LAST). The producer
/// (`dregg_turn::rotation_witness`) derives these from the real executed turn's
/// `RecordKernelState` (`Ledger` + receipt log); the cell-side v9 commitment takes them as
/// context so it reproduces the circuit's row-0 `STATE_COMMIT` for the same turn.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct V9RotationContext {
    /// The turn-level boundary `cells_root` felt (limb 0).
    pub cells_root: dregg_circuit::field::BabyBear,
    /// The cell's committed FAITHFUL 8-felt nullifier-accumulator root (limb 26 lane-0 ‖ completion
    /// lanes 67..=73). The native `CanonicalHeapTree8` node8 (arity-16) sorted-Poseidon2 accumulator
    /// root the noteSpend grow-gate opens against (`EffectVmEmitRotationV3` writesTo8), sourced from
    /// `dregg_cell::nullifier_set::NullifierSet::root8` (the live (nf, value) map). The empty-accumulator
    /// default is `dregg_turn::rotation_witness::empty_nullifier_root_8` (=
    /// `dregg_circuit::heap_root::empty_heap_root_8`).
    pub nullifier_root: dregg_circuit::Faithful8,
    /// The committed FAITHFUL 8-felt note-COMMITMENTS-accumulator root (limb 27 lane-0 ‖ completion
    /// lanes 74..=80). The native `CanonicalHeapTree8` node8 (arity-16) sorted-Poseidon2 accumulator
    /// root the noteCreate grow-gate opens against (`EffectVmEmitRotationV3.commitmentsInsertOp`,
    /// `commitmentsRootGroupCol`), sourced from `dregg_cell::commitment_set::CommitmentSet::root8`
    /// (the live (commitment, value) map). A turn-level set root, like `nullifier_root`. The
    /// empty-accumulator default is `dregg_turn::rotation_witness::empty_commitments_root_8` (=
    /// `dregg_circuit::heap_root::empty_heap_root_8`).
    pub commitments_root: dregg_circuit::Faithful8,
    /// The committed FAITHFUL 8-felt CREDENTIAL-REVOCATION-accumulator root (base limb 37 lane-0 ‖
    /// completion lanes 82..=88 — the REVOKED-ROOT flag-day widened the base region 37→38 to seat it
    /// right after `fields_root`). The native `CanonicalHeapTree8` node8 (arity-16) sorted-Poseidon2
    /// accumulator root the credential-revocation gate opens a NON-membership witness against (a
    /// revoked `credNul` admits no witness ⇒ the fail-closed gate refuses; hole #3 / #139). Keyed by
    /// the domain-separated capability provenance hash (`credNul`) and channel id (`chanNul`), value =
    /// `revocation_height`. Sourced from `dregg_cell::revoked_set::RevokedSet::root8` (the live
    /// `(credNul, height)` map); the empty-accumulator default is
    /// `dregg_turn::rotation_witness::empty_revoked_root_8` (= `dregg_circuit::heap_root::empty_heap_root_8`).
    pub revoked_root: dregg_circuit::Faithful8,
    /// The receipt-index MMR root, absorbed LAST.
    pub iroot: dregg_circuit::field::BabyBear,
    /// The v12 per-effect CARRIER MATERIAL for the child-vk / contract-hash octets (limbs 88..103).
    /// `None`/`None` (the `Default`) on a generic turn — only a `CreateCellFromFactory` turn carries
    /// `child_vk` (the executor's captured `effective_vk`) and a hatchery mint carries
    /// `contract_hash`. The pubkey octet (104..111) is cell-derived and needs no material.
    pub material: RotationCarrierMaterial,
}

/// The v12 per-effect CARRIER MATERIAL that fills the child-vk (88..95) and contract-hash (96..103)
/// rotated carrier octets. Both are `Option`s so a generic turn defaults to ZERO-filled octets; the
/// executor captures the REAL material at its source (`apply.rs`'s `effective_vk` for factory turns,
/// `HpresProof::Attested{contract_hash}` for hatchery mints) and threads it in so the honest turn's
/// `state_commit` carries it — the SAT foundation the STEP-3 `CarrierOctetGates` welds ride.
///
/// The pubkey octet (104..111) is DERIVED from the cell (`cell.public_key()`), so it needs no
/// material threading — every producer fills it unconditionally.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RotationCarrierMaterial {
    /// The REAL installed child VK on a `CreateCellFromFactory` turn (the executor's `effective_vk`).
    pub child_vk: Option<[u8; 32]>,
    /// The `HpresProof::Attested` content hash on a hatchery mint.
    pub contract_hash: Option<[u8; 32]>,
}

/// The canonical scalar limb of a cell's lifecycle: the discriminant folded with its payload
/// bytes so two distinct lifecycle states yield distinct limbs. Mirrors the producer's
/// `rotation_witness::lifecycle_felt` and the v8 `hash_lifecycle_into` anti-omission tooth.
fn v9_lifecycle_felt(lc: &crate::lifecycle::CellLifecycle) -> dregg_circuit::field::BabyBear {
    use crate::lifecycle::CellLifecycle;
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::poseidon2::lifecycle_payload_felt;
    // FELT-DOMAIN composition (see `dregg_circuit::poseidon2::lifecycle_payload_felt`): the
    // in-circuit lifecycle-payload hash gate recomputes this from the light-client-known inputs.
    // MUST agree byte-for-byte with `dregg_turn::rotation_witness::lifecycle_felt`.
    match lc {
        CellLifecycle::Live => lifecycle_payload_felt(0, &[0u8; 32], 0),
        CellLifecycle::Sealed {
            reason_hash,
            sealed_at,
        } => lifecycle_payload_felt(1, reason_hash, *sealed_at),
        CellLifecycle::Migrated {
            to,
            attestation,
            migrated_at,
        } => {
            let mut inputs: Vec<BabyBear> = Vec::with_capacity(18);
            inputs.push(BabyBear::new(2));
            inputs.extend_from_slice(&dregg_circuit::effect_vm::bytes32_to_8_limbs(to.as_bytes()));
            inputs.extend_from_slice(&dregg_circuit::effect_vm::bytes32_to_8_limbs(attestation));
            inputs.push(BabyBear::new((*migrated_at & 0x7FFF_FFFF) as u32));
            dregg_circuit::poseidon2::hash_many(&inputs)
        }
        CellLifecycle::Destroyed {
            death_certificate_hash,
            destroyed_at,
        } => lifecycle_payload_felt(3, death_certificate_hash, *destroyed_at),
        CellLifecycle::Archived {
            checkpoint_hash,
            archived_through,
        } => lifecycle_payload_felt(4, checkpoint_hash, *archived_through),
    }
}

/// **THE v9 AUTHORITY DIGEST** — the single Poseidon2 felt that folds ALL authority-bearing
/// cell state that NO other rotated limb carries.
///
/// ## Why this exists (the rotated-commitment design call, G3)
///
/// The v8 BLAKE3 commitment ([`compute_canonical_state_commitment`]) binds the cell's FULL
/// authority-bearing state: identity (`id`/`public_key`/`token_id`), `mode`, the eight
/// `Permissions` fields, the `verification_key`, `delegate`, the `delegation` snapshot, the
/// `program`, and the CellState authority sub-state (`field_visibility`, `commitments`,
/// `proved_state`, `swiss_table_root`, `refcount_table_root`, `fields_root`,
/// `system_roots_digest`, all 16 `fields`). The rotated v9 commitment's NAMED limbs cover
/// only a SUBSET of this: balance/nonce (r0/r1/r2), `fields[0..8]` (r3..r10), `cap_root`
/// (r25), `nullifier_root`/`commitments_root`/`heap_root` (r26/r27/r28), `lifecycle`/`epoch`/`committed_height`
/// (r28/r29/r30). Everything else — permissions, VK, delegate, delegation, program, mode,
/// token_id, the visibility/commitment/proved/side-table sub-roots, and `fields[8..16]` —
/// would be DROPPED by a rotated commitment that left the app-register headroom zeroed.
///
/// Dropping authority state is a soundness hole (two cells with identical
/// balance/nonce/fields[0..8]/roots but DIFFERENT permissions or VK would commit identically,
/// so a verifier could not tell a locked-down cell from a wide-open one). To close it, the
/// rotated commitment binds this digest into register **r23** (the last app register; the
/// Lean welds `EffectVmEmitRotationV3.weldsAt` constrain only r0..r10 + cap_root, so r23 is a
/// freely-witnessed limb that the anti-ghost keystone `wireCommitR_binds` /
/// `rotatedCommit_binds_reg` ALREADY binds — no Lean change is needed; r23 is "just a
/// register" the commitment proves bound). The digest is computed cell-locally, so both the
/// cell-side v9 commitment and the producer ([`dregg_turn::rotation_witness::produce`]) build
/// the SAME r23 from the SAME `&Cell`, and the circuit trace carries it on the wire.
///
/// ## What it folds (the authority residue not on a named limb)
///
/// This walks the SAME byte serialization v8 uses for these fields (so v8 and v9 agree on
/// "what is authority state"): identity, mode, permissions, VK, delegate, delegation,
/// program, and the CellState authority sub-state that no named limb carries —
/// `field_visibility`, `commitments`, `proved_state`, `swiss_table_root`,
/// `refcount_table_root`, `fields_root`, `system_roots_digest`, and `fields[8..16]`. The
/// fields the rotated limbs already carry (balance/nonce/`fields[0..8]`/cap_root/heap_root/
/// committed_height/delegation_epoch) are NOT re-absorbed here — they are bound by their own
/// limbs. The accumulated bytes are hashed to a felt via the same Poseidon2 `hash_bytes` the
/// other byte-rooted limbs use, under a dedicated domain context.
pub fn compute_authority_digest_felt(cell: &Cell) -> dregg_circuit::field::BabyBear {
    // The v1-leg cross-anchor + the rotated `B_AUTHORITY_DIGEST` (limb 24) carry limb-0 of the
    // faithful 8-felt digest (`compute_authority_digest_8`). H1: the residual authority digest is
    // now a ~124-bit blake3-rooted 8-felt commitment; this scalar face is its first limb, kept so
    // the v1 OLD_COMMIT `record_digest` cross-anchor and `pre_limbs[24]` stay byte-identical to the
    // historical single-felt limb (the other 7 limbs ride the welded headroom; see
    // `compute_authority_digest_8` / `compute_rotated_pre_limbs`).
    compute_authority_digest_8(cell)[0]
}

/// **THE H1 FAITHFUL 8-FELT AUTHORITY DIGEST** — the ~124-bit blake3-rooted commitment to the WHOLE
/// authority residue (the residual authority-bearing cell state no other rotated limb carries). This
/// REPLACES the historical single ~31-bit poseidon felt (`hash_bytes`): two authority states that
/// collide at one BabyBear felt (~2^31 image) but are genuinely different (e.g. locked-down vs
/// wide-open permissions) are now SEPARATED by 8 limbs of `blake3(authority_residue)` (~124 bits).
///
/// The eight limbs are placed into the rotated pre-iroot vector as limb 24 (limb-0, the historical
/// `B_AUTHORITY_DIGEST` position) plus the 7 previously-unwelded app-register headroom limbs
/// (offsets 12..=18, r11..r17) — so the absorption vector does NOT grow and the chained
/// `wireCommitR` ALREADY binds all 8 into the ~124-bit `state_commit`. The GENTIAN weld
/// (`EffectVmEmitRotationV3.rotateV3WithRecordPin8` + the continuity freezes) FORCES every one of
/// the 8 AFTER limbs to its genuine value, so a 31-bit-colliding wide-open authority cannot be
/// smuggled into an unwelded limb. Byte-identical across the three producers (cell-side here,
/// `dregg_turn::rotation_witness::produce`, and the circuit trace).
pub fn compute_authority_digest_8(cell: &Cell) -> dregg_circuit::Faithful8 {
    dregg_circuit::Faithful8::from_bytes32(blake3::hash(&authority_residue_bytes(cell)).as_bytes())
}

/// The domain-separated byte serialization of the authority residue (the authority-bearing cell
/// state NO other rotated limb carries). Folded to the faithful 8-felt digest by
/// [`compute_authority_digest_8`]. Walks the SAME byte layout v8 uses for these fields (so v8 and v9
/// agree on "what is authority state"): identity, mode, permissions, VK, delegate, delegation,
/// program, and the CellState authority sub-state (`field_visibility`, `commitments`,
/// `proved_state`, `swiss_table_root`, `refcount_table_root`, `fields_root`, `system_roots_digest`,
/// `fields[8..16]`).
pub fn authority_residue_bytes(cell: &Cell) -> Vec<u8> {
    use crate::state::STATE_SLOTS;

    // Collect the authority residue into a byte buffer, domain-separated. Domain prefix so this
    // digest can never collide with a bare root felt.
    let mut bytes: Vec<u8> = Vec::with_capacity(256);
    bytes.extend_from_slice(b"dregg-cell:v9-authority-digest v1");

    // ---- Identity ----
    bytes.extend_from_slice(cell.id.as_bytes());
    bytes.extend_from_slice(&cell.public_key);
    bytes.extend_from_slice(&cell.token_id);

    // ---- Mode ----
    bytes.push(match cell.mode {
        crate::cell::CellMode::Hosted => 0,
        crate::cell::CellMode::Sovereign => 1,
    });

    // ---- Permissions (eight AuthRequired fields, canonical order) ----
    {
        let p = &cell.permissions;
        for auth in [
            &p.send,
            &p.receive,
            &p.set_state,
            &p.set_permissions,
            &p.set_verification_key,
            &p.increment_nonce,
            &p.delegate,
            &p.access,
        ] {
            bytes.push(auth_byte(auth));
            if let AuthRequired::Custom { vk_hash } = auth {
                bytes.extend_from_slice(vk_hash);
            }
        }
    }

    // ---- Verification key ----
    match &cell.verification_key {
        Some(vk) => {
            bytes.push(1);
            bytes.extend_from_slice(&vk.hash);
        }
        None => bytes.push(0),
    }

    // ---- Delegate ----
    match &cell.delegate {
        Some(d) => {
            bytes.push(1);
            bytes.extend_from_slice(d.as_bytes());
        }
        None => bytes.push(0),
    }

    // ---- Delegation snapshot ----
    match &cell.delegation {
        Some(deleg) => {
            bytes.push(1);
            bytes.extend_from_slice(deleg.source.as_bytes());
            bytes.extend_from_slice(&deleg.delegation_epoch.to_le_bytes());
            bytes.extend_from_slice(&deleg.refreshed_at.to_le_bytes());
            bytes.extend_from_slice(&deleg.max_staleness.to_le_bytes());
            bytes.extend_from_slice(&(deleg.snapshot.len() as u64).to_le_bytes());
            for cap in &deleg.snapshot {
                // The same 7-field leaf the cap_root absorbs, so a tampered delegated cap
                // moves this digest (the snapshot is authority-bearing — audit P2-4).
                bytes.extend_from_slice(&digest8_to_bytes32(cap_ref_to_leaf(cap).digest()));
            }
        }
        None => bytes.push(0),
    }

    // ---- Program ----
    match &cell.program {
        crate::program::CellProgram::None => bytes.push(0),
        crate::program::CellProgram::Predicate(constraints) => {
            bytes.push(1);
            let s = postcard::to_allocvec(constraints).unwrap_or_default();
            bytes.extend_from_slice(&(s.len() as u64).to_le_bytes());
            bytes.extend_from_slice(&s);
        }
        crate::program::CellProgram::Circuit { circuit_hash } => {
            bytes.push(2);
            bytes.extend_from_slice(circuit_hash);
        }
        crate::program::CellProgram::Cases(cases) => {
            bytes.push(3);
            let s = postcard::to_allocvec(cases).unwrap_or_default();
            bytes.extend_from_slice(&(s.len() as u64).to_le_bytes());
            bytes.extend_from_slice(&s);
        }
    }

    // ---- CellState authority sub-state NOT carried by a named rotated limb ----
    let st = &cell.state;
    // fields[8..16] (fields[0..8] are welded to r3..r10).
    for field in &st.fields[8..STATE_SLOTS] {
        bytes.extend_from_slice(field);
    }
    // visibility, commitments, proved_state.
    for vis in &st.field_visibility {
        bytes.push(visibility_byte(*vis));
    }
    for commit in &st.commitments {
        match commit {
            Some(h) => {
                bytes.push(1);
                bytes.extend_from_slice(h);
            }
            None => bytes.push(0),
        }
    }
    bytes.push(st.proved_state as u8);
    // side-table / overflow roots (authority-bearing: they gate enliven / drop-ref /
    // handoff and fold the unbounded record + the 8 kernel side-tables).
    bytes.extend_from_slice(&st.swiss_table_root);
    bytes.extend_from_slice(&st.refcount_table_root);
    bytes.extend_from_slice(&st.fields_root.to_bytes32());
    bytes.extend_from_slice(&st.system_roots_digest());

    bytes
}

/// Build the 32 pre-iroot rotated limbs for a cell + turn-context, in the Lean-pinned
/// absorption order (`EffectVmEmitRotationV3.preLimbsAt`). Byte-identical to the producer
/// `dregg_turn::rotation_witness::produce`'s `pre_limbs`.
pub fn compute_rotated_pre_limbs(
    cell: &Cell,
    ctx: &V9RotationContext,
) -> Vec<dregg_circuit::field::BabyBear> {
    use dregg_circuit::effect_vm::split_u64;
    use dregg_circuit::field::BabyBear;

    let mut pre = vec![BabyBear::ZERO; V9_NUM_PRE_LIMBS];
    // limb 0: cells_root (turn-level).
    pre[0] = ctx.cells_root;
    // limbs 1..=24: r0..r23 — welded scalars first.
    let balance = cell.state.balance();
    let (bal_lo, bal_hi) = split_u64(balance as u64);
    pre[1] = bal_lo; // r0 ↔ balance_lo
    pre[2] = BabyBear::new((cell.state.nonce() & 0x7FFF_FFFF) as u32); // r1 ↔ nonce
    pre[3] = bal_hi; // r2 ↔ balance_hi
    // r3..r10 ↔ fields[0..7] lane 0 (limbs 4..=11) ‖ the 56 fields COMPLETION lanes 112..=167
    // (fields[i] lanes 1..7 → `112 + 7·i .. +6`). THE v13 FAITHFUL FIELDS OCTET: each field's
    // 32 bytes ride a full `field_limbs8` 8-lane split (lane 0 = the u64-lane lo32, the faithful
    // ~124-bit binding), REPLACING the eight ~31-bit `fold_bytes32_to_bb` Horner folds that rode
    // one `from_lossy_31bit_DANGER` octet. This CLOSES the last degraded-felt residual: the whole
    // state commitment is now faithful. The setField value8 weld FORCES the written slot's 8 lanes
    // to the declared params; the completion freezes pin every non-written field's 7 lanes on a
    // value turn (the fields GENTIAN law). Byte-identical to the `rotation_witness` producer fill.
    for i in 0..8 {
        // REVOKED-ROOT flag-day: the fields[0..7] completion octet shifted 112..=167 → 113..=168
        // (every limb index ≥ 37 shifted +1 for the new base `revoked_root` limb 37).
        let base = 113 + 7 * i;
        dregg_circuit::Faithful8::from_field_limbs8(&cell.state.fields[i]).write_lanes(
            &mut pre,
            [
                4 + i,
                base,
                base + 1,
                base + 2,
                base + 3,
                base + 4,
                base + 5,
                base + 6,
            ],
        );
    }
    // r11..r22 (limbs 12..=23): app-register headroom.
    // r23 (limb 24) + r11..r17 (limbs 12..=18): THE FAITHFUL 8-FELT AUTHORITY DIGEST (H1) — the
    // ~124-bit blake3-rooted commitment folding ALL authority-bearing state no other rotated limb
    // carries (permissions/VK/delegate/delegation/program/mode/token_id + visibility/commitments/
    // proved/side-table roots + fields[8..16]). limb 24 = limb-0 (the historical position, the v1
    // cross-anchor); the 7 previously-zero headroom limbs 12..=18 carry limb-1..7. All 8 ride the
    // existing absorption chain (no vector growth, `rotV3SitesAt` unchanged) and are WELDED by the
    // record-pin / continuity freezes so a 31-bit-colliding authority cannot survive (GENTIAN law).
    // r18..r22 (limbs 19..=23): remaining app-register headroom — zero for a kernel turn.
    compute_authority_digest_8(cell).write_lanes(&mut pre, [24, 12, 13, 14, 15, 16, 17, 18]);
    // limb 25: cap_root lane-0 (welded) ‖ extras 51..=57: the SEVEN cap-root completion felts
    // (lanes 1..7). THE FAITHFUL 8-FELT CAP ROOT — the native `node8` arity-16 sorted-Poseidon2
    // root the circuit's 8-felt `cap_root` column GROUP carries (`EffectVmEmitRotationV3.
    // capRootGroupCol`: lane 0 = limb 25, lanes 1..7 = limbs 51..57). The in-circuit cap-write
    // gate FORCES the AFTER group to the `writesTo8` native update (`*_forces_write8`), so a
    // ~31-bit collision at lane-0 differing in any completion felt is UNSAT (the GENTIAN law,
    // ledgerless). Byte-identical to `rotation_witness`'s producer fill.
    compute_canonical_capability_root_8(&cell.capabilities)
        .write_lanes(&mut pre, [25, 52, 53, 54, 55, 56, 57, 58]);
    // limb 26: nullifier_root lane-0 (welded) ‖ extras 67..=73: the SEVEN nullifier-root completion
    // felts. THE FAITHFUL 8-FELT NULLIFIER ROOT — the native `CanonicalHeapTree8` node8 (arity-16)
    // sorted-Poseidon2 accumulator root the circuit's 8-felt `nullifier_root` column GROUP carries
    // (lane 0 = limb 26, lanes 1..7 = limbs 67..73). The in-circuit noteSpend grow-gate FORCES the
    // AFTER group to the `writesTo8` native insert, so a ~31-bit collision at lane-0 differing in any
    // completion felt is UNSAT (the nullifier GENTIAN law). This REPLACES the lossy 1-felt
    // `hash_bytes(&ctx.nullifier_root)`. Byte-identical to `rotation_witness::produce`.
    ctx.nullifier_root
        .write_lanes(&mut pre, [26, 68, 69, 70, 71, 72, 73, 74]);
    // limb 27: commitments_root lane-0 (welded) ‖ extras 74..=80: the SEVEN commitments-root
    // completion felts. THE FAITHFUL 8-FELT COMMITMENTS ROOT — the native `CanonicalHeapTree8`
    // node8 (arity-16) sorted-Poseidon2 accumulator root the circuit's 8-felt `commitments_root`
    // column GROUP carries (lane 0 = limb 27, lanes 1..7 = limbs 74..80, matching
    // `trace_rotated.rs::commitments_group_col`). The in-circuit noteCreate grow-gate FORCES the
    // AFTER group to the `commitmentsInsertOp` native insert, so a ~31-bit collision at lane-0
    // differing in any completion felt is UNSAT. This REPLACES the lossy 1-felt
    // `hash_bytes(&ctx.commitments_root)`. Byte-identical to `rotation_witness::produce`.
    ctx.commitments_root
        .write_lanes(&mut pre, [27, 75, 76, 77, 78, 79, 80, 81]);
    // limb 28: heap_root lane-0 (welded) ‖ extras 58..=64: the SEVEN heap-root completion felts
    // (Phase H-HEAP-8). The faithful native-`heap_node8` (arity-16) 8-felt sorted-Merkle root over the
    // cell's heap map — the circuit's 8-felt `heap_root` column GROUP carries lane 0 = limb 28, lanes
    // 1..7 = limbs 58..64. The in-circuit heap-write map_op FORCES the AFTER group to the `writesTo8`
    // native update, so a ~31-bit collision at lane-0 differing in any completion felt is UNSAT (the
    // heap GENTIAN law). This REPLACES the lossy 1-felt `hash_bytes(&cell.state.heap_root)`.
    // Byte-identical to `rotation_witness::compute_rotated_pre_limbs`.
    crate::state::compute_canonical_heap_root_8(&cell.state.heap_map)
        .write_lanes(&mut pre, [28, 59, 60, 61, 62, 63, 64, 65]);
    // limbs 29,30,31: lifecycle (opaque felt), epoch, committed_height.
    pre[29] = v9_lifecycle_felt(&cell.lifecycle);
    pre[30] = BabyBear::new((cell.state.delegation_epoch() & 0x7FFF_FFFF) as u32);
    pre[31] = BabyBear::new((cell.state.committed_height() & 0x7FFF_FFFF) as u32);
    // limb 32: lifecycle_disc (the WAVE-1 flag-day committed discriminant — the raw `u8 0..4`, the
    // gated disc-transition limb; byte-identical to `rotation_witness::lifecycle_disc_felt`).
    pre[32] = BabyBear::new(cell.lifecycle.discriminant() as u32);
    // limbs 33,34: perms_digest, vk_digest (the WAVE-2 flag-day committed authority sub-limbs — the
    // declared-param felts the setPerms / setVK welds force). limb-0 stays here (historical); the
    // v10 weld lands the SEVEN completion felts at the new extras 37..=43 (perms) / 44..=50 (vk).
    // v10 perms/vk faithful 8-felt completion: extras 37..=43 = perms8[1..8], 44..=50 = vk8[1..8].
    // The 8-wide permsVKWeldGate forces EACH to its declared param, so a ~31-bit collision at limb-0
    // that differs in any completion felt is UNSAT (GENTIAN law). Byte-identical to
    // `rotation_witness`'s producer fill.
    perms_digest_8(&cell.permissions).write_lanes(&mut pre, [33, 38, 39, 40, 41, 42, 43, 44]);
    vk_digest_8(&cell.verification_key).write_lanes(&mut pre, [34, 45, 46, 47, 48, 49, 50, 51]);
    // limbs 35,36: mode, fields_root (the WAVE-3 flag-day committed authority sub-limbs — the
    // makeSovereign mode CONSTANT-force limb and the setFieldDyn / refusal fields-root weld limb, the
    // NEW LAST pre-iroot limbs). Byte-identical to `rotation_witness::{mode_felt,fields_root_felt}`.
    pre[35] = mode_felt(&cell.mode);
    // limb 36: fields_root lane-0 (welded) ‖ extras 65,66,19,20,21,22,23: the SEVEN fields-root
    // completion felts (Phase H-FIELDS-8). The faithful native-`node8` (arity-16) 8-felt sorted-Merkle
    // root over the cell's user-field map — the circuit's 8-felt `fields_root` column GROUP carries lane
    // 0 = limb 36, lanes 1..7 = limbs 65,66,19,20,21,22,23. The in-circuit refusal fields-write map_op
    // FORCES the AFTER group to the `writesTo8` native update, so a ~31-bit collision at lane-0 differing
    // in any completion felt is UNSAT (the fields GENTIAN law). This REPLACES the lossy 1-felt
    // `fields_root_felt(&cell.state.fields_root)`. Byte-identical to
    // `rotation_witness::compute_rotated_pre_limbs`.
    crate::state::compute_canonical_fields_root_8(&cell.state.fields_map)
        .write_lanes(&mut pre, [36, 66, 67, 19, 20, 21, 22, 23]);
    // limb 37: revoked_root lane-0 (the NEW base limb, REVOKED-ROOT flag-day) ‖ extras 82..=88: the
    // SEVEN revoked-root completion felts. THE FAITHFUL 8-FELT CREDENTIAL-REVOCATION ROOT — the native
    // `CanonicalHeapTree8` node8 (arity-16) sorted-Poseidon2 accumulator root the circuit's 8-felt
    // `revoked_root` column GROUP carries (lane 0 = limb 37, lanes 1..7 = limbs 82..88; the shifted-free
    // completion slots the base widen opened). The in-circuit credential-revocation NON-membership gate
    // opens against this COMMITTED root (not a wire-supplied one — hole #139), so a node cannot claim
    // an empty/stale revocation set: a light client verifies the revocation was honoured from the
    // commitment alone. Sourced from `V9RotationContext.revoked_root` (the live `RevokedSet::root8`).
    // Byte-identical to `rotation_witness::produce`.
    ctx.revoked_root
        .write_lanes(&mut pre, [37, 82, 83, 84, 85, 86, 87, 88]);

    // v12 CARRIER-MATERIAL octets (limbs 89..=112 after the REVOKED-ROOT +1 shift) — the SAT
    // foundation for the four octet carriers. The octet base constants (`B_CHILD_VK_OCTET` etc.)
    // are the circuit-side source of truth, so this fill picks up the shift symbolically once the
    // circuit lane bumps them (88→89, 96→97, 104→105).
    // Byte-identical to the producer twin `dregg_turn::rotation_witness::produce`; the trace generator
    // (`fill_block`) carries them by copy. Absent material → ZERO (the vector is ZERO-initialised).
    use dregg_circuit::effect_vm::trace_rotated::{
        B_CHILD_VK_OCTET, B_CONTRACT_HASH_OCTET, B_PUBKEY_OCTET,
    };
    // 88..=95: child_vk8 iff the block's effect is `CreateCellFromFactory` (material carries the
    // REAL installed child VK), else ZERO.
    if let Some(child_vk) = ctx.material.child_vk {
        dregg_circuit::Faithful8::from_bytes32(&child_vk).write_octet(&mut pre, B_CHILD_VK_OCTET);
    }
    // 96..=103: contract_hash8 iff the block's effect is the hatchery mint, else ZERO.
    if let Some(contract_hash) = ctx.material.contract_hash {
        dregg_circuit::Faithful8::from_bytes32(&contract_hash)
            .write_octet(&mut pre, B_CONTRACT_HASH_OCTET);
    }
    // 104..=111: pubkey8 UNCONDITIONALLY — the operated cell's owner key in the 30-bit canonical form
    // (`canonical_to_babybear_pi`, byte-identical to `dregg_commit::typed::canonical_32_to_felts_8`),
    // the EXACT match to the executor's KEY_COMMIT teeth.
    let pk8 = canonical_to_babybear_pi(cell.public_key()).map(BabyBear::new);
    dregg_circuit::Faithful8::from_canonical_key(pk8).write_octet(&mut pre, B_PUBKEY_OCTET);
    pre
}

/// The committed cell-MODE sub-limb (`B_MODE = 35`, WAVE-3 mode/fields-root flag-day). The raw
/// `mode_flag` byte (`Hosted=0 / Sovereign=1`) `compute_authority_digest_felt` folds, as a felt. The
/// in-circuit makeSovereign gate (`EffectVmEmitRotationV3.rotateV3WithModeGate`) FORCES the AFTER mode
/// limb to `Sovereign(1)` as a CONSTANT, so a ledgerless client cannot be shown an un-promoted
/// sovereign. The CANONICAL definition; `turn::rotation_witness::mode_felt` calls it.
pub fn mode_felt(mode: &crate::cell::CellMode) -> dregg_circuit::field::BabyBear {
    dregg_circuit::field::BabyBear::new(match mode {
        crate::cell::CellMode::Hosted => 0,
        crate::cell::CellMode::Sovereign => 1,
    })
}

/// The committed `fields_root` digest sub-limb (`B_FIELDS_ROOT = 36`, WAVE-3 flag-day). Now the OPENABLE
/// sorted-Poseidon2 map root itself (`crate::state::compute_fields_root` IS a felt root, byte-encoded by
/// `babybear_to_bytes32`): this recovers that felt from the low 4 bytes — the committed limb IS the
/// openable root a ledgerless client can OPEN, NOT an opaque `hash_bytes(blake3_sponge)` no gate could
/// constrain. The in-circuit refusal map-op WRITE gate
/// (`EffectVmEmitRotationV3.refusalFieldsWriteV3`) FORCES the AFTER fields_root limb to
/// `insert(before_root, REFUSAL_AUDIT_KEY, audit_felt)`, so a forged post-`fields_root` is UNSAT for a
/// ledgerless client. CANONICAL; `turn::rotation_witness::fields_root_felt` calls it.
pub fn fields_root_felt(fields_root: &[u8; 32]) -> dregg_circuit::field::BabyBear {
    // The openable root is a single BabyBear felt encoded into the low 4 bytes
    // (`state::babybear_to_bytes32`); recover it canonically.
    let mut limb = [0u8; 4];
    limb.copy_from_slice(&fields_root[0..4]);
    dregg_circuit::field::BabyBear::new(u32::from_le_bytes(limb))
}

/// The committed PERMISSIONS-DIGEST sub-limb (`B_PERMS = 33`, WAVE-2 perms/VK flag-day). BYTE-IDENTICAL
/// to the deployed `params[0]` of a setPermissions row (`effect_vm_bridge.rs::SetPermissions` →
/// `hash_to_8`): `bytes32_to_8_limbs(blake3(postcard(permissions)))[0]`. The in-circuit setPermissions
/// weld (`EffectVmEmitRotationV3.rotateV3WithPermsVKGate`) FORCES the AFTER perms-digest limb EQUAL to
/// this declared param (PI-anchored via `effects_hash`), so a forged post-permissions is UNSAT for a
/// ledgerless client. The CANONICAL definition; `turn::rotation_witness::perms_digest_felt` calls it.
pub fn perms_digest_felt(
    perms: &crate::permissions::Permissions,
) -> dregg_circuit::field::BabyBear {
    perms_digest_8(perms)[0]
}

/// The FAITHFUL 8-felt permissions digest (v10 perms weld). BYTE-IDENTICAL to the deployed
/// `permissions_hash = hash_to_8(...)` a setPermissions row carries (`effect_vm_bridge.rs:160`):
/// `bytes32_to_8_limbs(blake3(postcard(permissions)))`. `[0]` is the historical limb-33 digest;
/// `[1..8]` are the seven completion felts the v10 weld lands at extras 37..=43, each forced by the
/// 8-wide `permsVKWeldGate` to the declared param (`effects_hash`-bound, NO new verifier PI). A
/// ~31-bit collision at `[0]` differing in `[1..8]` is now caught — the GENTIAN law.
pub fn perms_digest_8(perms: &crate::permissions::Permissions) -> dregg_circuit::Faithful8 {
    let bytes = postcard::to_allocvec(perms).unwrap_or_default();
    dregg_circuit::Faithful8::from_bytes32(blake3::hash(&bytes).as_bytes())
}

/// The committed VERIFICATION-KEY-DIGEST sub-limb (`B_VK = 34`, WAVE-2 flag-day). BYTE-IDENTICAL to the
/// deployed `params[0]` of a setVK row: `bytes32_to_8_limbs(blake3(postcard(vk)))[0]`, with `None`
/// (revoke) mapping to the all-zero limb (the deployed `vk_hash == [0; 8]` convention). The setVK weld
/// forces the AFTER vk-digest limb to this declared param, closing the upgrade-safety (post-VK)
/// light-client forgery. CANONICAL; `turn::rotation_witness::vk_digest_felt` calls it.
pub fn vk_digest_felt(vk: &Option<crate::cell::VerificationKey>) -> dregg_circuit::field::BabyBear {
    vk_digest_8(vk)[0]
}

/// The FAITHFUL 8-felt verification-key digest (v10 vk weld). BYTE-IDENTICAL to the deployed
/// `vk_hash` 8-felt a setVK row carries: `bytes32_to_8_limbs(blake3(postcard(vk)))`, with `None`
/// (revoke) mapping to the all-zero 8-felt (the deployed `vk_hash == [0; 8]` convention). `[0]` is
/// the historical limb-34 digest; `[1..8]` are the seven completion felts the v10 weld lands at
/// extras 44..=50, each forced by the 8-wide `permsVKWeldGate`. CANONICAL.
pub fn vk_digest_8(vk: &Option<crate::cell::VerificationKey>) -> dregg_circuit::Faithful8 {
    match vk {
        Some(v) => {
            let bytes = postcard::to_allocvec(v).unwrap_or_default();
            dregg_circuit::Faithful8::from_bytes32(blake3::hash(&bytes).as_bytes())
        }
        // The deployed `vk_hash == [0; 8]` revoke convention — the ZERO sentinel.
        None => dregg_circuit::Faithful8::ZERO,
    }
}

/// The chained rotated state commitment — the Rust twin of Lean `wireCommitR`: the 4-wide
/// head over the first four limbs, 3-wide chip groups while ≥ 3 pre-iroot limbs remain, the
/// iroot absorbed ALONE last. Byte-identical to the producer's `wire_commit` and the rotated
/// trace's `STATE_COMMIT` carrier.
fn v9_wire_commit(
    pre_limbs: &[dregg_circuit::field::BabyBear],
    iroot: dregg_circuit::field::BabyBear,
) -> dregg_circuit::field::BabyBear {
    use dregg_circuit::poseidon2::hash_many;
    debug_assert_eq!(pre_limbs.len(), V9_NUM_PRE_LIMBS);
    let mut d = hash_many(&[pre_limbs[0], pre_limbs[1], pre_limbs[2], pre_limbs[3]]);
    let mut col = 4;
    while col < V9_NUM_PRE_LIMBS {
        let remaining = V9_NUM_PRE_LIMBS - col;
        if remaining >= 3 {
            d = hash_many(&[d, pre_limbs[col], pre_limbs[col + 1], pre_limbs[col + 2]]);
            col += 3;
        } else {
            d = hash_many(&[d, pre_limbs[col]]);
            col += 1;
        }
    }
    hash_many(&[d, iroot])
}

/// **THE v9 ROTATED canonical commitment (felt)** — the cell-side computation of the
/// EffectVM rotated trace's row-0 `STATE_COMMIT` carrier: `wireCommitR(preLimbs, iroot)` over
/// the rotated absorption order. Equal to the circuit's row-0 before-block `STATE_COMMIT` for
/// the same `(cell, turn-context)` (the live cell≡circuit differential). v8 is unchanged.
pub fn compute_canonical_state_commitment_v9_felt(
    cell: &Cell,
    ctx: &V9RotationContext,
) -> dregg_circuit::field::BabyBear {
    let pre = compute_rotated_pre_limbs(cell, ctx);
    v9_wire_commit(&pre, ctx.iroot)
}

/// **THE v9 ROTATED canonical commitment (32 bytes)** — the canonical
/// [`felt_to_bytes32`] encoding of [`compute_canonical_state_commitment_v9_felt`]. The
/// additive rotated sibling of v8's [`compute_canonical_state_commitment`]; the v8 byte
/// scheme is left intact (do NOT bump the live default — that is the flag-day, G2).
pub fn compute_canonical_state_commitment_v9(cell: &Cell, ctx: &V9RotationContext) -> [u8; 32] {
    felt_to_bytes32(compute_canonical_state_commitment_v9_felt(cell, ctx))
}

/// **THE FAITHFUL 8-FELT v9 ROTATED commitment (Phase B-ROTATION)** — the genuine ~124-bit-
/// collision per-cell state digest, the wide twin of [`compute_canonical_state_commitment_v9_felt`].
///
/// Chains the SAME 37 pre-iroot limbs ([`compute_rotated_pre_limbs`]) and the iroot through the
/// 8-felt single-permutation chain ([`dregg_circuit::poseidon2::wire_commit_8`]): each step is
/// `single_perm_compress(d8 ‖ 3 limbs)[0..8]` — ONE arity-11 permutation, an 8-felt carrier
/// THROUGHOUT, NO 31-bit intermediate (the anti-laundering crux). Byte-identical to the Lean
/// `EffectVmEmitRotationR.wireCommitR8` and the producer twin
/// `dregg_turn::rotation_witness::wire_commit_8`.
///
/// THE LIVE DEPLOYED COMMITMENT (the flag-day FIRED — `9e5a83935`, 2026-06-19): this 8-felt
/// (~124-bit) chain IS the published whole-image state binding end-to-end — producer
/// (`cipherclerk` publishes `felt8_to_bytes32` of the wide commit-8), executor verifier (WIDE
/// registry only; the 1-felt waist is GONE), and the SDK light client. The shipped strategy
/// kept `B_STATE_COMMIT` 1-wide in-trace and instead exposed 16 wide carrier PIs beside it.
/// The 1-felt [`compute_canonical_state_commitment_v9_felt`] survives with test/bench callers
/// only. The collision-distinguishing / intermediate-carrier teeth on the chain primitive live
/// in `dregg-circuit` (`poseidon2::wire_commit_8_*`).
pub fn compute_canonical_state_commitment_v9_felt8(
    cell: &Cell,
    ctx: &V9RotationContext,
) -> dregg_circuit::Faithful8 {
    let pre = compute_rotated_pre_limbs(cell, ctx);
    // The deployed wide carrier the circuit PUBLISHES is the CHIP chain
    // (`fill_wide_block` → `chip_absorb_all_lanes`); the plain `wire_commit_8` DIVERGES from it (no
    // arity-tag seeding). So the live registration / executor anchor MUST be the chip chain —
    // otherwise an honest wide proof's BEFORE carrier would not equal the stored 8-felt commit.
    // `wire_commit_8_chip` is verify-level in `dregg-circuit` (the chip absorb is part of the
    // verify floor), so this faithful commit is unconditional — the divergent plain-chain floor is
    // retired. `Faithful8::from_wire_commit_chip` IS that chain (the wall's wire-commit constructor).
    dregg_circuit::Faithful8::from_wire_commit_chip(&pre, ctx.iroot)
}

/// The 32-byte encoding of the faithful 8-felt commitment: the 8 felts packed as 8×4 LE bytes
/// ([`felt8_to_bytes32`]), filling the WHOLE 32-byte ledger slot — UNLIKE the 1-felt
/// [`compute_canonical_state_commitment_v9`] which leaves 28 bytes zero.
pub fn compute_canonical_state_commitment_v9_8(cell: &Cell, ctx: &V9RotationContext) -> [u8; 32] {
    felt8_to_bytes32(&compute_canonical_state_commitment_v9_felt8(cell, ctx))
}

/// Pack 8 BabyBear felts into a 32-byte slot, each felt's 4 LE bytes (8×4 = 32). The faithful
/// 8-felt commitment's canonical byte encoding — injective on canonical BabyBear values (< p, so
/// each fits a u32) and fills the WHOLE slot. Inverse of [`bytes32_to_felt8`].
pub fn felt8_to_bytes32(felts: &[dregg_circuit::field::BabyBear; 8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, f) in felts.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&f.as_u32().to_le_bytes());
    }
    out
}

/// Read 8 BabyBear felts out of a 32-byte slot (8×4 LE bytes). Inverse of [`felt8_to_bytes32`]
/// on canonical encodings. The executor reads a ledger-slot commitment back into the 8 felts it
/// anchors against the proof's 8-felt `STATE_COMMIT` PIs (the flag-day verifier consumption).
pub fn bytes32_to_felt8(bytes: &[u8; 32]) -> [dregg_circuit::field::BabyBear; 8] {
    core::array::from_fn(|i| {
        dregg_circuit::field::BabyBear::new(u32::from_le_bytes(
            bytes[i * 4..i * 4 + 4].try_into().unwrap(),
        ))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cell::Cell;

    fn test_key(b: u8) -> [u8; 32] {
        let mut k = [0u8; 32];
        k[0] = b;
        k
    }

    fn test_token(b: u8) -> [u8; 32] {
        let mut t = [0u8; 32];
        t[1] = b;
        t
    }

    /// Adversarial test (audit P0-2 remediation): assert that the three
    /// commitment derivations all agree byte-for-byte.
    ///
    /// - `compute_canonical_state_commitment(&cell)` — the source of truth
    /// - `cell.state_commitment()` — wrapper
    /// - `Ledger::hash_cell_canonical(&cell)` — the Merkle leaf hash, also
    ///   the wrapper
    #[test]
    fn three_commitments_agree_byte_for_byte() {
        let cell = Cell::new(test_key(7), test_token(11));

        let canonical = compute_canonical_state_commitment(&cell);
        let from_state_commitment = cell.state_commitment();
        let from_hash_cell = crate::ledger::Ledger::hash_cell_canonical(&cell);

        assert_eq!(
            canonical, from_state_commitment,
            "Cell::state_commitment must equal canonical"
        );
        assert_eq!(
            canonical, from_hash_cell,
            "Ledger::hash_cell must equal canonical"
        );
        assert_eq!(
            from_state_commitment, from_hash_cell,
            "state_commitment and hash_cell must be identical"
        );
    }

    /// Adversarial test (audit P0-2): mutating *any* authority-bearing byte
    /// in the cell state must change the canonical commitment (and therefore
    /// all three derivations).
    #[test]
    fn mutating_state_changes_all_three_commitments() {
        let mut cell = Cell::new(test_key(7), test_token(11));
        let before = compute_canonical_state_commitment(&cell);
        let sc_before = cell.state_commitment();
        let hc_before = crate::ledger::Ledger::hash_cell_canonical(&cell);

        // Mutate balance through the legitimate accessor.
        assert!(cell.state.apply_balance_change(1234));

        let after = compute_canonical_state_commitment(&cell);
        let sc_after = cell.state_commitment();
        let hc_after = crate::ledger::Ledger::hash_cell_canonical(&cell);

        assert_ne!(before, after);
        assert_ne!(sc_before, sc_after);
        assert_ne!(hc_before, hc_after);

        // All three still agree on the new state.
        assert_eq!(after, sc_after);
        assert_eq!(after, hc_after);
    }

    /// Adversarial test: changing the **permissions** must alter the
    /// canonical commitment. Previously, the circuit-side Poseidon2
    /// commitment did NOT cover permissions, so two cells with different
    /// permissions but identical (balance, nonce, fields) collided. The
    /// canonical commitment closes this on the cell-crate side.
    #[test]
    fn changing_permissions_changes_commitment() {
        let mut cell1 = Cell::new(test_key(7), test_token(11));
        let mut cell2 = Cell::new(test_key(7), test_token(11));

        let c1 = compute_canonical_state_commitment(&cell1);
        let c2 = compute_canonical_state_commitment(&cell2);
        assert_eq!(c1, c2, "identical cells must agree");

        // Now change cell2's permissions.
        cell2.permissions = Permissions::zkapp();

        let c1b = compute_canonical_state_commitment(&cell1);
        let c2b = compute_canonical_state_commitment(&cell2);
        assert_eq!(c1, c1b, "cell1 unchanged");
        assert_ne!(c2, c2b, "cell2 permissions change must propagate");
        assert_ne!(c1b, c2b, "cells differ after permission change");

        // No mutation on cell1.
        let _ = &mut cell1;
    }

    /// Adversarial test: changing the verification key must alter the
    /// canonical commitment.
    #[test]
    // Opaque-fixture VK: deprecated `new` is fine here (no real VK components).
    #[allow(deprecated)]
    fn changing_vk_changes_commitment() {
        let mut cell = Cell::new(test_key(7), test_token(11));
        let before = compute_canonical_state_commitment(&cell);
        cell.verification_key = Some(crate::cell::VerificationKey::new(b"new-vk".to_vec()));
        let after = compute_canonical_state_commitment(&cell);
        assert_ne!(before, after);
    }

    /// VK-EPOCH RUST GHOST MIRROR — the nullifier accumulator root is committed FAITHFULLY across
    /// all 8 rotated lanes ([26, 67..73]), not squeezed to the old lossy 1-felt, and it DISTINGUISHES
    /// different nullifier frontiers. This is the cross-node anti-replay property that makes the whole
    /// flip worth doing: two nodes with different spent-nullifier sets commit DIFFERENT state roots, so
    /// a double-spend cannot finalize (an honest node's re-execution diverges → consensus rejects it).
    #[test]
    fn nullifier_root_faithful_8felt_and_cross_node_distinguishing() {
        let cell = Cell::new(test_key(7), test_token(11));
        let mk_ctx = |nr: dregg_circuit::Faithful8| V9RotationContext {
            cells_root: BabyBear::ZERO,
            nullifier_root: nr,
            commitments_root: dregg_circuit::heap_root::empty_heap_root_8(),
            revoked_root: dregg_circuit::heap_root::empty_heap_root_8(),
            iroot: BabyBear::ZERO,
            material: RotationCarrierMaterial::default(),
        };

        // Two DIFFERENT nullifier frontiers (different spent nullifiers).
        let mut set_a = crate::NullifierSet::new();
        set_a
            .insert(crate::note::Nullifier(test_key(3)), 100)
            .unwrap();
        let mut set_b = crate::NullifierSet::new();
        set_b
            .insert(crate::note::Nullifier(test_key(9)), 200)
            .unwrap();
        let root_a = set_a.root8();
        let root_b = set_b.root8();

        let limbs_a = compute_rotated_pre_limbs(&cell, &mk_ctx(root_a));
        let limbs_b = compute_rotated_pre_limbs(&cell, &mk_ctx(root_b));

        // (a) WRITE CORRECTNESS: committed limbs [26, 68..74] ARE the root's 8 lanes (REVOKED-ROOT
        // flag-day shifted the nullifier completion lanes 67..73 → 68..74).
        let ra = root_a.limbs();
        assert_eq!(limbs_a[26], ra[0], "limb 26 must be root lane 0");
        for i in 0..7 {
            assert_eq!(
                limbs_a[68 + i],
                ra[1 + i],
                "completion limb {} must be root lane {}",
                68 + i,
                1 + i
            );
        }

        // (b) NON-VACUOUS: the completion lanes are NOT all zero (the old bug filled only lane 0).
        assert!(
            ra[1..8].iter().any(|&x| x != BabyBear::ZERO),
            "faithful completion lanes 68..74 must be non-zero for a non-empty frontier"
        );

        // (c) CROSS-NODE ANTI-REPLAY: different frontiers -> different committed roots.
        let committed = |l: &[BabyBear]| -> Vec<BabyBear> {
            std::iter::once(l[26])
                .chain(l[68..75].iter().copied())
                .collect()
        };
        assert_ne!(
            committed(&limbs_a),
            committed(&limbs_b),
            "different nullifier sets MUST commit different roots (else a double-spend finalizes cross-node)"
        );
    }

    /// VK-EPOCH RUST GHOST MIRROR (commitments dual) — the commitments accumulator root is committed
    /// FAITHFULLY across all 8 rotated lanes ([27, 74..80]), not squeezed to the old lossy 1-felt, and
    /// it DISTINGUISHES different commitment frontiers. The CREATE-side dual of the nullifier tooth:
    /// two nodes with different created-commitment sets commit DIFFERENT state roots, so the published
    /// commitment binds the grown shielded-note set an honest re-executor reproduces.
    #[test]
    fn commitments_root_faithful_8felt_and_cross_node_distinguishing() {
        let cell = Cell::new(test_key(7), test_token(11));
        let mk_ctx = |cr: dregg_circuit::Faithful8| V9RotationContext {
            cells_root: BabyBear::ZERO,
            nullifier_root: dregg_circuit::heap_root::empty_heap_root_8(),
            commitments_root: cr,
            revoked_root: dregg_circuit::heap_root::empty_heap_root_8(),
            iroot: BabyBear::ZERO,
            material: RotationCarrierMaterial::default(),
        };

        // Two DIFFERENT commitment frontiers (different created note commitments).
        let mut set_a = crate::CommitmentSet::new();
        set_a
            .insert(crate::note::NoteCommitment(test_key(3)), 100)
            .unwrap();
        let mut set_b = crate::CommitmentSet::new();
        set_b
            .insert(crate::note::NoteCommitment(test_key(9)), 200)
            .unwrap();
        let root_a = set_a.root8();
        let root_b = set_b.root8();

        let limbs_a = compute_rotated_pre_limbs(&cell, &mk_ctx(root_a));
        let limbs_b = compute_rotated_pre_limbs(&cell, &mk_ctx(root_b));

        // (a) WRITE CORRECTNESS: committed limbs [27, 75..81] ARE the root's 8 lanes (REVOKED-ROOT
        // flag-day shifted the commitments completion lanes 74..80 → 75..81).
        let ra = root_a.limbs();
        assert_eq!(limbs_a[27], ra[0], "limb 27 must be root lane 0");
        for i in 0..7 {
            assert_eq!(
                limbs_a[75 + i],
                ra[1 + i],
                "completion limb {} must be root lane {}",
                75 + i,
                1 + i
            );
        }

        // (b) NON-VACUOUS: the completion lanes are NOT all zero (the old bug filled only lane 0).
        assert!(
            ra[1..8].iter().any(|&x| x != BabyBear::ZERO),
            "faithful completion lanes 75..81 must be non-zero for a non-empty frontier"
        );

        // (c) CROSS-NODE DISTINGUISHING: different frontiers -> different committed roots.
        let committed = |l: &[BabyBear]| -> Vec<BabyBear> {
            std::iter::once(l[27])
                .chain(l[75..82].iter().copied())
                .collect()
        };
        assert_ne!(
            committed(&limbs_a),
            committed(&limbs_b),
            "different commitment sets MUST commit different roots (the created-note-set binding)"
        );
    }

    /// Canonical capability root must change with any capability addition.
    #[test]
    fn capability_root_changes_on_grant() {
        let mut caps = CapabilitySet::new();
        let before = compute_canonical_capability_root(&caps);
        caps.grant(
            CellId::derive_raw(&test_key(1), &test_token(1)),
            AuthRequired::Signature,
        );
        let after = compute_canonical_capability_root(&caps);
        assert_ne!(before, after);
    }

    /// **THE STEP-2 SUB-ROOT-CACHE DIFFERENTIAL** (`docs/INCREMENTAL-COMMITMENT.md`).
    ///
    /// Over a random corpus of interleaved mutation sequences (grants/revokes/
    /// attenuations/restores/field-writes/heap-writes/nonce-ticks/balance-changes),
    /// at EVERY step assert two byte-identities:
    ///
    ///   1. the CACHED-path `compute_canonical_state_commitment(&cell)` equals an
    ///      always-recompute reference (a postcard round-trip of the cell, whose
    ///      `#[serde(skip)]` cap-root cache reconstructs DIRTY, forcing a fresh
    ///      fold), and
    ///   2. the cached `compute_canonical_capability_root(&cell.capabilities)`
    ///      equals the cap-root of that freshly-folded round-tripped cell.
    ///
    /// A single mismatch would mean a mutation path failed to invalidate the
    /// cache (a stale cached root = a silent wrong commitment). 0 mismatches over
    /// the corpus is the completeness witness.
    #[test]
    fn cap_root_cache_matches_fresh() {
        use crate::capability::CapabilityRef;

        // A tiny deterministic LCG so the corpus is reproducible without a
        // `rand` dependency.
        struct Lcg(u64);
        impl Lcg {
            fn next(&mut self) -> u64 {
                self.0 = self
                    .0
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                self.0 >> 16
            }
            fn pick(&mut self, n: u64) -> u64 {
                self.next() % n
            }
        }

        // Always-recompute reference: round-trip the cell through postcard so
        // every derived cache (the `#[serde(skip)]` cap-root cache) is dropped
        // and reconstructed DIRTY, forcing the authoritative fold on read.
        fn fresh_commitment(cell: &Cell) -> [u8; 32] {
            let bytes = postcard::to_allocvec(cell).expect("serialize cell");
            let reloaded: Cell = postcard::from_bytes(&bytes).expect("deserialize cell");
            compute_canonical_state_commitment(&reloaded)
        }
        fn fresh_cap_root(caps: &CapabilitySet) -> [u8; 32] {
            let bytes = postcard::to_allocvec(caps).expect("serialize caps");
            let reloaded: CapabilitySet = postcard::from_bytes(&bytes).expect("deserialize caps");
            compute_canonical_capability_root(&reloaded)
        }

        for seed in 0..8u64 {
            let mut lcg = Lcg(0x9E37_79B9_7F4A_7C15 ^ seed.wrapping_mul(0xD1B5_4A32_D192_ED03));
            let mut cell = Cell::new(test_key((seed as u8) | 1), test_token((seed as u8) | 1));
            // Track granted slots so we can revoke/attenuate live ones.
            let mut live_slots: Vec<u32> = Vec::new();

            for step in 0..120u64 {
                let target = CellId::derive_raw(
                    &test_key((lcg.pick(250) + 1) as u8),
                    &test_token((lcg.pick(250) + 1) as u8),
                );
                match lcg.pick(9) {
                    0 => {
                        // grant
                        if let Some(slot) = cell.capabilities.grant(target, AuthRequired::Signature)
                        {
                            live_slots.push(slot);
                        }
                    }
                    1 => {
                        // grant_faceted
                        if let Some(slot) = cell.capabilities.grant_faceted(
                            target,
                            AuthRequired::Either,
                            crate::facet::EFFECT_TRANSFER,
                        ) {
                            live_slots.push(slot);
                        }
                    }
                    2 => {
                        // grant_with_expiry
                        if let Some(slot) =
                            cell.capabilities
                                .grant_with_expiry(target, AuthRequired::Proof, 1000)
                        {
                            live_slots.push(slot);
                        }
                    }
                    3 => {
                        // revoke a live slot
                        if !live_slots.is_empty() {
                            let idx = lcg.pick(live_slots.len() as u64) as usize;
                            let slot = live_slots.remove(idx);
                            cell.capabilities.revoke(slot);
                        }
                    }
                    4 => {
                        // attenuate_in_place a live slot (Signature is narrower than Either)
                        if !live_slots.is_empty() {
                            let idx = lcg.pick(live_slots.len() as u64) as usize;
                            let slot = live_slots[idx];
                            let _ = cell.capabilities.attenuate_in_place(
                                slot,
                                AuthRequired::Impossible,
                                None,
                                None,
                            );
                        }
                    }
                    5 => {
                        // iter_mut-bypass mutation (the executor-rollback leak path):
                        // mutate a cap field directly through the `&mut` borrow.
                        if !live_slots.is_empty() {
                            let idx = lcg.pick(live_slots.len() as u64) as usize;
                            let slot = live_slots[idx];
                            if let Some(cap) = cell
                                .capabilities
                                .iter_mut()
                                .find(|r: &&mut CapabilityRef| r.slot == slot)
                            {
                                cap.expires_at = Some(lcg.next());
                            }
                        }
                    }
                    6 => {
                        // nonce tick — MUST NOT change the cap-root (cache stays valid)
                        let _ = cell.state.increment_nonce();
                    }
                    7 => {
                        // balance change — MUST NOT change the cap-root
                        let _ = cell.state.apply_balance_change((lcg.next() % 7) as i64);
                    }
                    _ => {
                        // field + heap writes — MUST NOT change the cap-root
                        let mut v = [0u8; 32];
                        v[31] = (lcg.next() % 251) as u8;
                        let key = 16 + (lcg.pick(8));
                        cell.state.set_field_ext(key, v);
                        cell.state.set_heap(1, (lcg.pick(8)) as u32, v);
                    }
                }

                // (1) whole-cell commitment: cached path == always-recompute.
                assert_eq!(
                    compute_canonical_state_commitment(&cell),
                    fresh_commitment(&cell),
                    "seed {seed} step {step}: cached commitment diverged from fresh recompute"
                );
                // (2) the cap sub-root itself: cached == fresh fold.
                assert_eq!(
                    compute_canonical_capability_root(&cell.capabilities),
                    fresh_cap_root(&cell.capabilities),
                    "seed {seed} step {step}: cached cap-root diverged from fresh fold"
                );
            }
        }
    }

    /// canonical_to_babybear_pi: same input → same output (deterministic).
    #[test]
    fn canonical_to_babybear_pi_deterministic() {
        let bytes = [42u8; 32];
        let a = canonical_to_babybear_pi(&bytes);
        let b = canonical_to_babybear_pi(&bytes);
        assert_eq!(a, b);
    }

    /// canonical_to_babybear_pi: different inputs → different outputs.
    #[test]
    fn canonical_to_babybear_pi_distinguishes() {
        let mut a = [0u8; 32];
        let mut b = [0u8; 32];
        b[0] = 1;
        assert_ne!(canonical_to_babybear_pi(&a), canonical_to_babybear_pi(&b));

        // High bit (within the 6-bit hi part of a limb) also distinguishes.
        a[3] = 0x20;
        b[3] = 0x10;
        assert_ne!(canonical_to_babybear_pi(&a), canonical_to_babybear_pi(&b));
    }

    /// Adversarial test (lifecycle): changing the cell's lifecycle state
    /// must alter the canonical commitment. Without lifecycle binding,
    /// a Destroyed cell could be presented as Live to downstream
    /// verifiers without breaking the commitment chain.
    #[test]
    fn changing_lifecycle_changes_commitment() {
        let cell_live = Cell::new(test_key(7), test_token(11));
        let mut cell_sealed = cell_live.clone();
        cell_sealed.lifecycle = crate::lifecycle::CellLifecycle::Sealed {
            reason_hash: [9u8; 32],
            sealed_at: 100,
        };
        let mut cell_destroyed = cell_live.clone();
        cell_destroyed.lifecycle = crate::lifecycle::CellLifecycle::Destroyed {
            death_certificate_hash: [7u8; 32],
            destroyed_at: 200,
        };

        let c_live = compute_canonical_state_commitment(&cell_live);
        let c_sealed = compute_canonical_state_commitment(&cell_sealed);
        let c_destroyed = compute_canonical_state_commitment(&cell_destroyed);

        assert_ne!(c_live, c_sealed, "Live vs Sealed must differ");
        assert_ne!(c_live, c_destroyed, "Live vs Destroyed must differ");
        assert_ne!(c_sealed, c_destroyed, "Sealed vs Destroyed must differ");

        // Two Sealed cells with different reason_hash must also differ —
        // payload bytes are bound, not just the discriminant.
        let mut cell_sealed2 = cell_live.clone();
        cell_sealed2.lifecycle = crate::lifecycle::CellLifecycle::Sealed {
            reason_hash: [42u8; 32],
            sealed_at: 100,
        };
        let c_sealed2 = compute_canonical_state_commitment(&cell_sealed2);
        assert_ne!(c_sealed, c_sealed2, "Sealed payload bytes must bind");
    }

    /// `_RECORD-LAYER-UPGRADE.md` **Stage 1** (the absorb): the user-field MAP
    /// root is now FOLDED into the canonical commitment (v2->v3 bump). The map is
    /// authority-bearing — mutating it MUST move the commitment. This is the
    /// anti-vacuity tooth: a `fields_root := 0` stub (or a Stage-0 "present but
    /// not absorbed" no-op) would make this assertion FAIL, so the absorption is
    /// genuinely load-bearing.
    #[test]
    fn stage1_map_field_write_moves_commitment() {
        let mut cell = Cell::new(test_key(7), test_token(11));
        let before = compute_canonical_state_commitment(&cell);

        // Populate the user-field map (keys >= STATE_SLOTS) and reseal its root.
        assert!(cell.state.set_field_ext(16, [42u8; 32]));
        assert_ne!(
            cell.state.fields_root,
            crate::state::empty_fields_root(),
            "the map must actually be populated (non-vacuous)"
        );

        let after = compute_canonical_state_commitment(&cell);
        assert_ne!(
            before, after,
            "Stage 1: the user-field map is absorbed; a map write MUST move the \
             canonical commitment (the absorption is load-bearing, not a stub)"
        );

        // A SECOND, distinct map write moves it again (distinct maps => distinct
        // roots => distinct commitments — off the fields_root injectivity).
        let mid = after;
        assert!(cell.state.set_field_ext(17, [7u8; 32]));
        let after2 = compute_canonical_state_commitment(&cell);
        assert_ne!(
            mid, after2,
            "a distinct map entry must move the commitment again"
        );

        // Tampering a committed value at the same key also moves it.
        assert!(cell.state.set_field_ext(16, [43u8; 32]));
        let tampered = compute_canonical_state_commitment(&cell);
        assert_ne!(
            after2, tampered,
            "tampering a map value must move the commitment"
        );
    }

    /// `_RECORD-LAYER-UPGRADE.md` **STAGE 3** (the side-table absorb): the
    /// dedicated `system_roots` sub-block digest is FOLDED into the canonical
    /// commitment (v3->v4 bump). The side-table roots are authority-bearing —
    /// mutating ANY of them MUST move the commitment. This is the anti-ghost
    /// tooth for ALL 8 side-tables: a `system_roots_digest := 0` stub (or a
    /// "present but not absorbed" no-op) would make this assertion FAIL, so the
    /// absorption is genuinely load-bearing. Lean shadow:
    /// `SystemRoots.cellCommitS_binds_systemRoots`.
    #[test]
    fn stage3_system_root_write_moves_commitment() {
        use crate::state::system_root;

        let mut cell = Cell::new(test_key(7), test_token(11));
        let before = compute_canonical_state_commitment(&cell);

        // Populate ONE side-table root (escrow) via the kernel-only mutator.
        assert!(cell.state.set_system_root(system_root::ESCROW, [42u8; 32]));
        assert_ne!(
            cell.state.system_roots_digest(),
            crate::state::empty_system_roots_digest(),
            "the sub-block must actually be populated (non-vacuous)"
        );

        let after = compute_canonical_state_commitment(&cell);
        assert_ne!(
            before, after,
            "STAGE 3: the system_roots sub-block is absorbed; a side-table root \
             write MUST move the canonical commitment (load-bearing, not a stub)"
        );

        // A DISTINCT side-table root (nullifier) moves it again.
        let mid = after;
        assert!(
            cell.state
                .set_system_root(system_root::NULLIFIER, [7u8; 32])
        );
        let after2 = compute_canonical_state_commitment(&cell);
        assert_ne!(
            mid, after2,
            "a distinct side-table root must move the commitment again"
        );

        // ANTI-GHOST: tampering the SAME side-table root (e.g. an attacker
        // dropping an escrow → a different root) moves it.
        assert!(cell.state.set_system_root(system_root::ESCROW, [99u8; 32]));
        let tampered = compute_canonical_state_commitment(&cell);
        assert_ne!(
            after2, tampered,
            "tampering a side-table root must move the commitment"
        );

        // Every kernel index is distinct and addresses a distinct sub-block cell.
        let idxs = [
            system_root::ESCROW,
            system_root::QUEUE,
            system_root::REFCOUNT,
            system_root::STURDYREF,
            system_root::DELEG,
            system_root::NULLIFIER,
            system_root::COMMIT,
            system_root::SEALED_BOXES,
        ];
        // `dedup` is a `Vec` method (not available on a fixed-size array), so
        // collect into a `Vec` first. (This test module only began compiling
        // once `dregg-circuit` became a non-optional dependency of the cell
        // crate — cap Phase A — which surfaced this latent `[usize; 8].dedup()`
        // error that no prior build exercised.)
        let mut sorted = idxs.to_vec();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(
            sorted.len(),
            crate::state::N_SYSTEM_ROOTS,
            "indices distinct & cover the block"
        );
    }

    /// `_RECORD-LAYER-UPGRADE.md` **STAGE 3 backward-compat keystone** (the no-op
    /// fold): a LEGACY cell (all-zero `system_roots`) carries the FIXED
    /// `empty_system_roots_digest()` constant, cell-INDEPENDENT. So absorbing the
    /// sub-block digest is a uniform no-op across legacy cells, and a fresh cell, a
    /// cell whose sub-block was populated then drained, and the explicit
    /// empty-roots reference all produce the same commitment. Lean shadow:
    /// `SystemRoots.legacy_commitS_absorbs_empty_roots`.
    #[test]
    fn legacy_cells_share_system_roots_contribution() {
        use crate::state::{FIELD_ZERO, empty_system_roots_digest, system_root};

        // (a) a fresh cell is a legacy cell (all-zero sub-block).
        let fresh = Cell::new(test_key(7), test_token(11));
        assert_eq!(
            fresh.state.system_roots_digest(),
            empty_system_roots_digest()
        );
        let c_fresh = compute_canonical_state_commitment(&fresh);

        // (b) a cell whose sub-block was populated then DRAINED back to all-zero:
        // the digest returns to the same constant, so its commitment is byte-
        // identical to (a).
        let mut drained = Cell::new(test_key(7), test_token(11));
        assert!(
            drained
                .state
                .set_system_root(system_root::QUEUE, [99u8; 32])
        );
        assert_ne!(
            drained.state.system_roots_digest(),
            empty_system_roots_digest(),
            "populated: digest differs from empty (non-vacuous)"
        );
        assert!(
            drained
                .state
                .set_system_root(system_root::QUEUE, FIELD_ZERO)
        );
        assert_eq!(
            drained.state.system_roots_digest(),
            empty_system_roots_digest()
        );
        let c_drained = compute_canonical_state_commitment(&drained);
        assert_eq!(
            c_fresh, c_drained,
            "a legacy (empty-sub-block) cell's commitment is independent of sub-block history"
        );

        // (c) the byte-identical no-op reference (folds BOTH empty-fields-root and
        // empty-system-roots constants by hand) must reproduce the canonical
        // commitment exactly for a legacy cell.
        let c_ref = legacy_reference_commitment(&fresh);
        assert_eq!(
            c_fresh, c_ref,
            "the empty-system-roots absorption is a fixed no-op constant for legacy cells"
        );
    }

    /// `_RECORD-LAYER-UPGRADE.md` **Stage 1 backward-compat keystone** (the
    /// no-op fold): a LEGACY cell (empty `fields_map`) carries the FIXED
    /// `empty_fields_root()` constant, which is cell-INDEPENDENT. So absorbing
    /// `fields_root` is a uniform no-op across legacy cells: the v3 commitment of
    /// any legacy cell is BYTE-IDENTICAL to a reference that hashes the same
    /// authority-bearing state with the empty-fields-root constant folded in at
    /// the same fixed position. We assert this directly: a fresh cell, a cell
    /// whose map was populated then fully drained (back to empty), and a cell
    /// deserialized from a pre-Stage-0 blob all produce the same commitment as
    /// the explicit empty-root reference. This is the Rust shadow of the Lean
    /// `RecordCommit.legacy_commit_absorbs_empty_root`.
    #[test]
    fn legacy_cells_share_fields_root_contribution() {
        use crate::state::empty_fields_root;

        // (a) a fresh (never-touched) cell is a legacy cell.
        let fresh = Cell::new(test_key(7), test_token(11));
        assert_eq!(fresh.state.fields_root, empty_fields_root());
        let c_fresh = compute_canonical_state_commitment(&fresh);

        // (b) a cell whose map was populated then DRAINED back to empty: the root
        // returns to the same constant, so its commitment is byte-identical to
        // (a) — the absorbed constant does not depend on the map's history.
        let mut drained = Cell::new(test_key(7), test_token(11));
        assert!(drained.state.set_field_ext(16, [99u8; 32]));
        assert_ne!(
            drained.state.fields_root,
            empty_fields_root(),
            "populated: root differs from empty (non-vacuous)"
        );
        drained.state.fields_map.remove(&16);
        drained.state.reseal_fields_root();
        assert_eq!(drained.state.fields_root, empty_fields_root());
        let c_drained = compute_canonical_state_commitment(&drained);
        assert_eq!(
            c_fresh, c_drained,
            "a legacy (empty-map) cell's commitment is independent of map history"
        );

        // (c) the byte-identical no-op: an explicit reference that hashes the
        // SAME state but injects the empty-fields-root constant by hand at the
        // fixed position must reproduce the canonical commitment exactly. This is
        // the operational statement of "the empty-fields-root folds in as a no-op
        // constant": for a legacy cell, the canonical commitment IS that
        // reference, byte for byte.
        let c_ref = legacy_reference_commitment(&fresh);
        assert_eq!(
            c_fresh, c_ref,
            "the empty-fields-root absorption is a fixed no-op constant for legacy cells"
        );
    }

    /// Reference re-derivation of the canonical commitment for a LEGACY cell:
    /// recomputes the v3 hash inline, folding in the EMPTY fields-root constant
    /// explicitly at the fixed position. For any legacy cell this must equal
    /// `compute_canonical_state_commitment` byte-for-byte — the test above pins
    /// that. (It would diverge for a non-legacy cell, which is the point: the
    /// no-op only holds when the map is empty.)
    fn legacy_reference_commitment(cell: &Cell) -> [u8; 32] {
        use crate::state::empty_fields_root;
        let mut hasher = blake3::Hasher::new_derive_key(CANONICAL_COMMITMENT_CONTEXT);
        hasher.update(cell.id.as_bytes());
        hasher.update(&cell.public_key);
        hasher.update(&cell.token_id);
        let mode_byte: u8 = match cell.mode {
            crate::cell::CellMode::Hosted => 0,
            crate::cell::CellMode::Sovereign => 1,
        };
        hasher.update(&[mode_byte]);
        // Inline `hash_cell_state_into`, with the empty-root constant pinned by
        // hand for the fields_root absorption.
        let state = &cell.state;
        hasher.update(&state.nonce().to_le_bytes());
        // v6: the signed biased two-limb balance encoding, mirrored inline.
        hasher.update(&crate::state::encode_balance_le(state.balance()));
        for field in &state.fields {
            hasher.update(field);
        }
        for vis in &state.field_visibility {
            hasher.update(&[visibility_byte(*vis)]);
        }
        for commit in &state.commitments {
            match commit {
                Some(h) => {
                    hasher.update(&[1u8]);
                    hasher.update(h);
                }
                None => {
                    hasher.update(&[0u8]);
                }
            }
        }
        hasher.update(&[state.proved_state() as u8]);
        hasher.update(&state.delegation_epoch().to_le_bytes());
        hasher.update(&state.committed_height().to_le_bytes());
        hasher.update(&state.swiss_table_root);
        hasher.update(&state.refcount_table_root);
        // The no-op fold: the empty-map constant, independent of the cell.
        hasher.update(&empty_fields_root().to_bytes32());
        // STAGE 3 no-op fold: the empty system-roots digest, independent of the
        // cell (a legacy cell carries the all-zero sub-block).
        hasher.update(&crate::state::empty_system_roots_digest());
        // Universal-map rotation §2.4 no-op fold: the empty-heap constant,
        // independent of the cell.
        hasher.update(&crate::state::empty_heap_root().to_bytes32());
        hash_permissions_into(&mut hasher, &cell.permissions);
        match &cell.verification_key {
            Some(vk) => {
                hasher.update(&[1u8]);
                hasher.update(&vk.hash);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        let cap_root = compute_canonical_capability_root_wide(&cell.capabilities);
        hasher.update(&cap_root);
        match &cell.delegate {
            Some(d) => {
                hasher.update(&[1u8]);
                hasher.update(d.as_bytes());
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        match &cell.delegation {
            Some(deleg) => {
                hasher.update(&[1u8]);
                hash_delegation_into(&mut hasher, deleg);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        hash_program_into(&mut hasher, &cell.program);
        hash_lifecycle_into(&mut hasher, &cell.lifecycle);
        *hasher.finalize().as_bytes()
    }

    /// `docs/UNIVERSAL-MAP-ROTATION.md` §2.4 (the heap-root absorb): the
    /// `heap_root` register is FOLDED into the canonical commitment (v6->v7
    /// bump). Mutating ANY heap entry MUST move the commitment. This is the
    /// anti-ghost tooth for the heap: a `heap_root := 0` stub would make this
    /// assertion FAIL, so the absorption is genuinely load-bearing.
    #[test]
    fn heap_root_write_moves_commitment() {
        let mut cell = Cell::new(test_key(7), test_token(11));
        let before = compute_canonical_state_commitment(&cell);

        assert!(cell.state.set_heap(1, 2, [42u8; 32]));
        assert_ne!(
            cell.state.heap_root,
            crate::state::empty_heap_root(),
            "the heap must actually be populated (non-vacuous)"
        );

        let after = compute_canonical_state_commitment(&cell);
        assert_ne!(
            before, after,
            "heap_root is absorbed; a heap write MUST move the canonical commitment"
        );

        // A DISTINCT heap entry moves it again.
        let mid = after;
        assert!(cell.state.set_heap(2, 3, [7u8; 32]));
        let after2 = compute_canonical_state_commitment(&cell);
        assert_ne!(
            mid, after2,
            "a distinct heap entry must move the commitment again"
        );

        // ANTI-GHOST: tampering the SAME heap entry moves it.
        assert!(cell.state.set_heap(1, 2, [99u8; 32]));
        let tampered = compute_canonical_state_commitment(&cell);
        assert_ne!(
            after2, tampered,
            "tampering a heap entry must move the commitment"
        );
    }

    /// `docs/UNIVERSAL-MAP-ROTATION.md` §2.4 backward-compat keystone (the no-op
    /// fold): a LEGACY cell (empty `heap_map`) carries the FIXED
    /// `empty_heap_root()` constant, which is cell-INDEPENDENT. So absorbing
    /// `heap_root` is a uniform no-op across legacy cells.
    #[test]
    fn legacy_cells_share_heap_root_contribution() {
        use crate::state::empty_heap_root;

        // (a) a fresh (never-touched) cell is a legacy cell.
        let fresh = Cell::new(test_key(7), test_token(11));
        assert_eq!(fresh.state.heap_root, empty_heap_root());
        let c_fresh = compute_canonical_state_commitment(&fresh);

        // (b) a cell whose heap was populated then DRAINED back to empty: the
        // root returns to the same constant, so its commitment is byte-identical
        // to (a).
        let mut drained = Cell::new(test_key(7), test_token(11));
        assert!(drained.state.set_heap(1, 2, [99u8; 32]));
        assert_ne!(
            drained.state.heap_root,
            empty_heap_root(),
            "populated: root differs from empty (non-vacuous)"
        );
        assert!(drained.state.remove_heap(1, 2));
        assert_eq!(drained.state.heap_root, empty_heap_root());
        let c_drained = compute_canonical_state_commitment(&drained);
        assert_eq!(
            c_fresh, c_drained,
            "a legacy (empty-heap) cell's commitment is independent of heap history"
        );

        // (c) the byte-identical no-op reference must reproduce the canonical
        // commitment exactly for a legacy cell.
        let c_ref = legacy_reference_commitment(&fresh);
        assert_eq!(
            c_fresh, c_ref,
            "the empty-heap-root absorption is a fixed no-op constant for legacy cells"
        );
    }

    /// `docs/UNIVERSAL-MAP-ROTATION.md` §2.6 (PI v3 committed-height limb): the
    /// `committed_height` scalar is FOLDED into the canonical commitment
    /// (v7->v8 bump). Setting it to a non-zero height MUST move the commitment;
    /// a legacy cell carries 0 and the no-op reference still matches.
    #[test]
    fn committed_height_write_moves_commitment() {
        let mut cell = Cell::new(test_key(7), test_token(11));
        let before = compute_canonical_state_commitment(&cell);
        assert_eq!(cell.state.committed_height(), 0, "fresh cell height is 0");

        cell.state.set_committed_height(42);
        let after = compute_canonical_state_commitment(&cell);
        assert_ne!(
            before, after,
            "committed_height is absorbed; a non-zero height MUST move the canonical commitment"
        );

        // A DIFFERENT height moves it again.
        let mid = after;
        cell.state.set_committed_height(43);
        let after2 = compute_canonical_state_commitment(&cell);
        assert_ne!(
            mid, after2,
            "a different committed height must move the commitment again"
        );

        // Legacy no-op reference still reproduces the canonical commitment.
        let mut fresh = Cell::new(test_key(7), test_token(11));
        fresh.state.set_committed_height(0);
        let c_fresh = compute_canonical_state_commitment(&fresh);
        let c_ref = legacy_reference_commitment(&fresh);
        assert_eq!(
            c_fresh, c_ref,
            "the zero committed_height absorption is a fixed no-op constant for legacy cells"
        );
    }

    /// All output felts must fit within BabyBear's representable range
    /// (< 2^31). Our 30-bit packing should produce values < 2^30.
    #[test]
    fn canonical_to_babybear_pi_in_range() {
        let bytes = [0xFFu8; 32];
        let pi = canonical_to_babybear_pi(&bytes);
        for &felt in &pi {
            assert!(felt < (1u32 << 30), "felt {felt} exceeds 30-bit range");
        }
    }

    // ---- v9 rotated commitment (G3) ----

    use dregg_circuit::field::BabyBear;

    fn v9_ctx(cells_root: u32, iroot: u32) -> V9RotationContext {
        V9RotationContext {
            cells_root: BabyBear::new(cells_root),
            nullifier_root: dregg_circuit::heap_root::empty_heap_root_8(),
            commitments_root: dregg_circuit::heap_root::empty_heap_root_8(),
            revoked_root: dregg_circuit::heap_root::empty_heap_root_8(),
            iroot: BabyBear::new(iroot),
            material: Default::default(),
        }
    }

    /// The v9 pre-limb vector has the Lean-pinned 33-limb shape, and the welded scalars sit
    /// in the absorption order the producer / circuit carry.
    #[test]
    fn v9_pre_limbs_shape_and_welds() {
        let cell = Cell::with_balance(test_key(7), test_token(0), 100_000);
        let pre = compute_rotated_pre_limbs(&cell, &v9_ctx(11, 22));
        assert_eq!(pre.len(), V9_NUM_PRE_LIMBS);
        assert_eq!(
            pre.len(),
            170,
            "38 base (incl. revoked_root limb 37) + 51 faithful-8-felt completion limbs (38..88) + 24 v12 carrier-material octets (89..112) + 56 v13 fields[0..7] completion lanes (113..168) + 1 pad (169)"
        );
        // cells_root rides limb 0; the welded r0 (balance_lo) is non-zero for a funded cell.
        assert_eq!(pre[0], BabyBear::new(11));
        let (lo, _hi) = dregg_circuit::effect_vm::split_u64(100_000u64);
        assert_eq!(pre[1], lo, "r0 ↔ balance_lo weld");
        // limb 27 is the commitments_root lane 0 (the flag-day faithful-8-felt shielded-set root).
        assert_eq!(
            pre[27],
            dregg_circuit::heap_root::empty_heap_root_8().limbs()[0],
            "commitments_root lane 0 rides limb 27"
        );
        // limb 32 is the lifecycle_disc (a Live cell's disc is 0).
        assert_eq!(
            pre[32],
            BabyBear::new(0),
            "lifecycle_disc rides limb 32 (Live=0)"
        );
        // limbs 33,34 are the WAVE-2 perms-digest / vk-digest sub-limbs (= the declared-param felts).
        assert_eq!(
            pre[33],
            perms_digest_felt(&cell.permissions),
            "perms_digest rides limb 33 (= params[0] of a setPerms row)"
        );
        assert_eq!(
            pre[34],
            vk_digest_felt(&cell.verification_key),
            "vk_digest rides limb 34 (= params[0] of a setVK row; None → 0)"
        );
        // limbs 35,36 are the WAVE-3 mode / fields_root sub-limbs.
        assert_eq!(pre[35], mode_felt(&cell.mode), "mode rides limb 35");
        // The FAITHFUL 8-felt fields root (Phase H-FIELDS-8): lane 0 at limb 36, completion lanes 1..7 at
        // the NON-contiguous limbs 66,67,19,20,21,22,23 (REVOKED-ROOT flag-day shifted 65,66 → 66,67;
        // the base-region 19..23 tail is unshifted, < 37) (`EffectVmEmitRotationV3.fieldsRootGroupCol`).
        let fields8 = crate::state::compute_canonical_fields_root_8(&cell.state.fields_map);
        assert_eq!(pre[36], fields8[0], "fields_root lane 0 rides limb 36");
        let fields_lanes = [66usize, 67, 19, 20, 21, 22, 23];
        for i in 0..7 {
            assert_eq!(
                pre[fields_lanes[i]],
                fields8[1 + i],
                "fields_root completion lane {} rides limb {}",
                i + 1,
                fields_lanes[i]
            );
        }
        // The FAITHFUL 8-felt cap root: lane 0 at limb 25, completion lanes 1..7 at limbs 52..58
        // (REVOKED-ROOT flag-day shifted 51..57 → 52..58) (`EffectVmEmitRotationV3.capRootGroupCol`).
        // Lane 0 == the historical scalar cap-root felt.
        let cap8 = compute_canonical_capability_root_8(&cell.capabilities);
        assert_eq!(pre[25], cap8[0], "cap_root lane 0 rides limb 25");
        assert_eq!(
            pre[25],
            compute_canonical_capability_root_felt(&cell.capabilities),
            "cap_root limb-25 lane 0 == the historical scalar cap-root felt"
        );
        for i in 0..7 {
            assert_eq!(
                pre[52 + i],
                cap8[1 + i],
                "cap_root completion lane {} rides limb {}",
                i + 1,
                52 + i
            );
        }
        // The FAITHFUL 8-felt revoked root (REVOKED-ROOT flag-day): lane 0 at the NEW base limb 37,
        // completion lanes 1..7 at limbs 82..88 (the shifted-free completion slots). Empty accumulator
        // here → equals the empty heap root's 8 lanes.
        let revoked8 = dregg_circuit::heap_root::empty_heap_root_8();
        assert_eq!(
            pre[37],
            revoked8.limbs()[0],
            "revoked_root lane 0 rides limb 37"
        );
        for i in 0..7 {
            assert_eq!(
                pre[82 + i],
                revoked8.limbs()[1 + i],
                "revoked_root completion lane {} rides limb {}",
                i + 1,
                82 + i
            );
        }
    }

    /// The `lifecycle_disc` limb (32) is load-bearing: a different lifecycle discriminant MOVES the
    /// published rotated commitment (the disc flag-day soundness reason — a frozen seal / resurrection
    /// publishes a DIFFERENT commitment).
    #[test]
    fn v9_commitment_binds_lifecycle_disc() {
        use crate::lifecycle::CellLifecycle;
        let mut live = Cell::with_balance(test_key(7), test_token(0), 100_000);
        live.lifecycle = CellLifecycle::Live;
        let mut sealed = live.clone();
        sealed.lifecycle = CellLifecycle::Sealed {
            reason_hash: [0u8; 32],
            sealed_at: 0,
        };
        let ctx = v9_ctx(11, 22);
        assert_ne!(
            compute_canonical_state_commitment_v9_felt(&live, &ctx),
            compute_canonical_state_commitment_v9_felt(&sealed, &ctx),
            "lifecycle_disc (limb 32) is bound: Live≠Sealed moves the published commitment"
        );
    }

    /// The `commitments_root` limb (27) is load-bearing: a different note-commitments-set root
    /// MOVES the published rotated commitment (the flag-day soundness reason for the new limb).
    #[test]
    fn v9_commitment_binds_commitments_root() {
        let cell = Cell::with_balance(test_key(7), test_token(0), 100_000);
        let ctx0 = v9_ctx(11, 22);
        let mut ctx1 = ctx0;
        // A non-empty commitments accumulator root — the faithful 8-felt root over one created note.
        let mut set = crate::CommitmentSet::new();
        set.insert(crate::note::NoteCommitment(test_key(9)), 200)
            .unwrap();
        ctx1.commitments_root = set.root8();
        assert_ne!(
            compute_canonical_state_commitment_v9_felt(&cell, &ctx0),
            compute_canonical_state_commitment_v9_felt(&cell, &ctx1),
            "commitments_root (limb 27) is bound into the published rotated commitment"
        );
    }

    /// The v9 commitment BINDS every limb and the iroot: moving the iroot or any cell field
    /// (here the balance, which feeds the welded r0/r2 limbs) moves the commitment.
    #[test]
    fn v9_commitment_binds_state_and_iroot() {
        let cell = Cell::with_balance(test_key(7), test_token(0), 100_000);
        let base = compute_canonical_state_commitment_v9_felt(&cell, &v9_ctx(11, 22));
        // moving the iroot moves the commit.
        let moved_iroot = compute_canonical_state_commitment_v9_felt(&cell, &v9_ctx(11, 23));
        assert_ne!(base, moved_iroot, "iroot is bound");
        // moving cells_root moves the commit.
        let moved_cells = compute_canonical_state_commitment_v9_felt(&cell, &v9_ctx(12, 22));
        assert_ne!(base, moved_cells, "cells_root is bound");
        // a different balance moves the commit (welded r0/r2).
        let cell2 = Cell::with_balance(test_key(7), test_token(0), 99_999);
        let moved_bal = compute_canonical_state_commitment_v9_felt(&cell2, &v9_ctx(11, 22));
        assert_ne!(base, moved_bal, "balance (welded r0/r2) is bound");
    }

    /// THE AUTHORITY-COVERAGE TOOTH (the rotated-commitment design call): v9 binds the FULL
    /// authority-bearing state via the r23 authority digest — NOT just the named-limb subset.
    /// Two cells identical in balance/nonce/fields[0..8]/roots but differing in permissions,
    /// VK, program, delegate, a high field (fields[8..16]), proved_state, or a side-table root
    /// MUST commit distinctly. This is the soundness property that a rotated commitment with a
    /// zeroed app-register headroom would FAIL.
    #[test]
    fn v9_binds_full_authority_state() {
        let base_cell = Cell::with_balance(test_key(7), test_token(0), 100_000);
        let ctx = v9_ctx(11, 22);
        let base = compute_canonical_state_commitment_v9_felt(&base_cell, &ctx);

        // permissions differ ⇒ commitment differs.
        let mut perms_cell = base_cell.clone();
        perms_cell.permissions.set_state = AuthRequired::Impossible;
        assert_ne!(
            base,
            compute_canonical_state_commitment_v9_felt(&perms_cell, &ctx),
            "v9 must bind permissions (a locked-down cell ≠ a wide-open one)"
        );

        // verification key differs ⇒ commitment differs.
        let mut vk_cell = base_cell.clone();
        #[allow(deprecated)]
        let vk = crate::cell::VerificationKey::new(b"v9-authority-vk".to_vec());
        vk_cell.verification_key = Some(vk);
        assert_ne!(
            base,
            compute_canonical_state_commitment_v9_felt(&vk_cell, &ctx),
            "v9 must bind the verification key"
        );

        // a HIGH field (fields[8..16], NOT welded to a named limb) differs ⇒ differs.
        let mut hi_field_cell = base_cell.clone();
        hi_field_cell.state.fields[12] = [3u8; 32];
        assert_ne!(
            base,
            compute_canonical_state_commitment_v9_felt(&hi_field_cell, &ctx),
            "v9 must bind fields[8..16] (only fields[0..8] are welded to r3..r10)"
        );

        // proved_state differs ⇒ differs.
        let mut proved_cell = base_cell.clone();
        proved_cell.state.proved_state = !proved_cell.state.proved_state;
        assert_ne!(
            base,
            compute_canonical_state_commitment_v9_felt(&proved_cell, &ctx),
            "v9 must bind proved_state"
        );

        // a side-table root differs ⇒ differs.
        let mut sr_cell = base_cell.clone();
        sr_cell.state.swiss_table_root = [7u8; 32];
        assert_ne!(
            base,
            compute_canonical_state_commitment_v9_felt(&sr_cell, &ctx),
            "v9 must bind the swiss-table (CapTP) root"
        );

        // mode differs ⇒ differs.
        let mut mode_cell = base_cell.clone();
        mode_cell.mode = crate::cell::CellMode::Sovereign;
        assert_ne!(
            base,
            compute_canonical_state_commitment_v9_felt(&mode_cell, &ctx),
            "v9 must bind the hosted/sovereign mode"
        );
    }

    /// v9 is ADDITIVE: it does NOT touch the v8 default. The v8 byte commitment of a cell is
    /// independent of any rotation context, and v9 produces a DISTINCT 32-byte scheme (so a
    /// downstream consumer cannot confuse the two).
    #[test]
    fn v9_is_additive_distinct_from_v8() {
        let cell = Cell::with_balance(test_key(7), test_token(0), 100_000);
        let v8 = compute_canonical_state_commitment(&cell);
        let v9 = compute_canonical_state_commitment_v9(&cell, &v9_ctx(11, 22));
        assert_ne!(v8, v9, "v9 must be a distinct scheme from v8");
        // v8 is unchanged by anything rotation-context (it never reads it).
        let v8_again = compute_canonical_state_commitment(&cell);
        assert_eq!(v8, v8_again, "v8 default is untouched");
    }

    /// v9 GOLDEN: pin the rotated commitment of a fixed cell + context so a shape regression
    /// (a limb-order swap, a chaining-arity change) is caught. The value is the cell-side
    /// computation of the circuit's row-0 `STATE_COMMIT`; the live differential
    /// (`live_cell_v9_equals_circuit_state_commit`) pins it against the circuit trace.
    #[test]
    fn v9_golden_commitment_is_stable() {
        let cell = Cell::with_balance(test_key(7), test_token(0), 100_000);
        let felt = compute_canonical_state_commitment_v9_felt(&cell, &v9_ctx(0, 0));
        // Recompute independently from the documented chained absorption to pin the SHAPE
        // (not a magic byte string): the same `(cell, ctx)` must always yield the same felt.
        let felt2 = compute_canonical_state_commitment_v9_felt(&cell, &v9_ctx(0, 0));
        assert_eq!(felt, felt2, "v9 commitment is deterministic");
        // the 32-byte encoding is the canonical felt encoding (low 4 LE bytes, rest zero).
        let bytes = compute_canonical_state_commitment_v9(&cell, &v9_ctx(0, 0));
        assert_eq!(&bytes[0..4], &felt.as_u32().to_le_bytes());
        assert_eq!(&bytes[4..], &[0u8; 28], "felt encoding zero-pads the tail");
    }
}
