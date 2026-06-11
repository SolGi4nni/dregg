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
//!    committed to **only** `(balance, nonce, fields[0..8], capability_root)`,
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
pub const CANONICAL_COMMITMENT_CONTEXT: &str = "dregg-cell:canonical-state-commitment v5";

/// Domain-separation context for the canonical capability-set root.
///
/// `v1 → v2` (cap Phase A): the capability root is no longer a BLAKE3 XOR-fold
/// over per-cap leaf hashes — it is the openable sorted-Poseidon2 binary Merkle
/// root ([`dregg_circuit::cap_root`]), shared byte-identically with the EffectVM
/// circuit. The single-cap commitment returned by
/// [`crate::capability::CapabilitySet::attenuate_in_place`] is now the 32-byte
/// encoding of that cap's leaf-digest felt under this context.
pub const CANONICAL_CAP_ROOT_CONTEXT: &str = "dregg-cell:canonical-capability-root v2";

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
pub fn compute_canonical_state_commitment(cell: &Cell) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(CANONICAL_COMMITMENT_CONTEXT);

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
    // its canonical 32-byte felt encoding so the cell's full-state commitment
    // binds the SAME `cap_root` value the EffectVM circuit carries.
    let cap_root = compute_canonical_capability_root(&cell.capabilities);
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
    hasher.update(&state.balance.to_le_bytes());
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
    // Stage 1: CapTP-prep committed roots (`DESIGN-captp-integration.md` §4).
    // These are part of authority-bearing state because they gate enliven /
    // drop-ref / handoff operations.
    hasher.update(&state.swiss_table_root);
    hasher.update(&state.refcount_table_root);
    // Record-layer Stage 1 (`_RECORD-LAYER-UPGRADE.md` §D.2.1): absorb the
    // user-field-MAP root. This is what folds the unbounded `key >= 8` overflow
    // map (`fields_map`, digested into `fields_root`) into the cell's authority-
    // bearing commitment, so a verifier binds the WHOLE record, not just the 8
    // fixed slots. Absorbed at a FIXED position by a FIXED constant for legacy
    // cells: a no-overflow cell carries `empty_fields_root()` — a cell-independent
    // constant (the digest of the empty map) — so the absorption is a uniform
    // no-op across all legacy cells (proven byte-identical in the Lean keystone
    // `RecordCommit.legacy_commit_absorbs_empty_root` and the Rust
    // `legacy_cells_share_fields_root_contribution` test). The `v2->v3` context
    // bump (above) cleanly invalidates any stale v2 commitment rather than
    // risking a silent cross-version collision.
    hasher.update(&state.fields_root);
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
    let leaves: Vec<dregg_circuit::cap_root::CapLeaf> = caps.iter().map(cap_ref_to_leaf).collect();
    dregg_circuit::cap_root::compute_capability_root(leaves)
}

/// Compute the canonical 32-byte capability root of a `CapabilitySet`.
///
/// This is the 32-byte ENCODING of [`compute_canonical_capability_root_felt`]
/// (the openable sorted-Poseidon2 Merkle root) — see [`felt_to_bytes32`]. It
/// is what `compute_canonical_state_commitment` absorbs and what the executor's
/// CapabilityUniqueness program binds in a 32-byte cap-set-root state slot
/// (`turn::executor::execute_tree`). The empty c-list root is NON-zero (the
/// sentinels hash into a real value), so the executor's "root slot must be
/// non-zero" check is preserved.
pub fn compute_canonical_capability_root(caps: &CapabilitySet) -> [u8; 32] {
    felt_to_bytes32(compute_canonical_capability_root_felt(caps))
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

/// The 32-byte commitment to a SINGLE capability's openable leaf: the encoding
/// ([`felt_to_bytes32`]) of the cap's 7-field [`dregg_circuit::cap_root::CapLeaf`]
/// digest. Used by [`crate::capability::CapabilitySet::attenuate_in_place`] so a
/// caller can update c-list audit indices with a value consistent with the
/// canonical sorted-tree root.
pub fn capability_ref_leaf_commitment(cap: &crate::capability::CapabilityRef) -> [u8; 32] {
    felt_to_bytes32(cap_ref_to_leaf(cap).digest())
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
    fn changing_vk_changes_commitment() {
        let mut cell = Cell::new(test_key(7), test_token(11));
        let before = compute_canonical_state_commitment(&cell);
        cell.verification_key = Some(crate::cell::VerificationKey::new(b"new-vk".to_vec()));
        let after = compute_canonical_state_commitment(&cell);
        assert_ne!(before, after);
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

        // Populate the user-field map (keys >= 8) and reseal its root.
        assert!(cell.state.set_field_ext(8, [42u8; 32]));
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
        assert!(cell.state.set_field_ext(9, [7u8; 32]));
        let after2 = compute_canonical_state_commitment(&cell);
        assert_ne!(
            mid, after2,
            "a distinct map entry must move the commitment again"
        );

        // Tampering a committed value at the same key also moves it.
        assert!(cell.state.set_field_ext(8, [43u8; 32]));
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
        assert!(drained.state.set_field_ext(8, [99u8; 32]));
        assert_ne!(
            drained.state.fields_root,
            empty_fields_root(),
            "populated: root differs from empty (non-vacuous)"
        );
        drained.state.fields_map.remove(&8);
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
        hasher.update(&state.balance().to_le_bytes());
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
        hasher.update(&state.swiss_table_root);
        hasher.update(&state.refcount_table_root);
        // The no-op fold: the empty-map constant, independent of the cell.
        hasher.update(&empty_fields_root());
        // STAGE 3 no-op fold: the empty system-roots digest, independent of the
        // cell (a legacy cell carries the all-zero sub-block).
        hasher.update(&crate::state::empty_system_roots_digest());
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
        let cap_root = compute_canonical_capability_root(&cell.capabilities);
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
}
