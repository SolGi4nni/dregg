//! # Identity builders — the SDK surface for identity cells with KERI-shaped
//! pre-rotation (identity step 2: the identity-council factory + verbs).
//!
//! The cell program lives in [`starbridge_polis::identity`] (the
//! `next_keys_digest` register + the `KeyRotationGate` rotate verb; kernel
//! semantics proven in `metatheory/Dregg2/Apps/PreRotation.lean`); this
//! module builds the turns that drive it, riding the normal
//! [`AgentRuntime::turn()`](crate::AgentRuntime::turn) path.
//!
//! ## The contract, in brief
//!
//! * Every key-state event commits to the digest of the NEXT, unexposed key
//!   set ([`next_keys_digest`]). Rotation must EXHIBIT the preimage (the
//!   [`TurnBuilder::reveal`](crate::turns::TurnBuilder::reveal) verb): a
//!   thief holding every CURRENT signing key still cannot rotate.
//! * A rotation installs the presented commitment, re-commits fresh in the
//!   same turn (the forward chain), and waits out the charter's cooling
//!   window — visible to the council the whole time.
//! * The receipt stream over the two key registers IS the key-event log
//!   (the KERI KEL shape).
//!
//! ## Lifecycle
//!
//! 1. **Plan** — [`create_identity`] → [`GovernanceCellPlan`] (deploy /
//!    create / fund / adopt, the shared polis bootstrap).
//! 2. **Genesis** — [`genesis_effects`]: the first pre-commitment + the
//!    birth key-set commitment + the pinned council commitment, one turn
//!    (UNINIT → ACTIVE; no preimage — nothing was committed yet).
//! 3. **Rotate** — [`AgentRuntime::rotate_identity`] (or [`rotate_effects`]
//!    + `.reveal(..)` by hand): exhibit, install, re-commit, stamp.
//!
//! Key custody note: the NEXT key set's commitment preimage is the rotation
//! credential. Losing it makes the identity unrotatable BY DESIGN
//! (`rotate_compromise_resistant` admits nothing else) — escrow it with the
//! recovery council, not alongside the current keys.

use dregg_cell::CellId;
use dregg_cell::state::FieldElement;
use dregg_turn::Effect;

use crate::error::SdkError;
use crate::polis::{GovernanceCellPlan, PolisError, bootstrap_plan};
use crate::receipt::Receipt;
use crate::runtime::AgentRuntime;

pub use starbridge_polis::STATE_SLOT;
pub use starbridge_polis::identity::{
    COUNCIL_COMMIT_SLOT, CURRENT_KEYS_COMMIT_SLOT, IdentityCharter, IdentityState, IdentityStatus,
    LAST_ROTATED_AT_SLOT, NEXT_KEYS_DIGEST_SLOT, STATE_ACTIVE, STATE_RETIRED, STATE_UNINIT,
    identity_factory_descriptor, inspect_identity, key_set_commitment, next_keys_digest,
};

use dregg_cell::field_from_u64;

fn set(cell: CellId, index: u8, value: FieldElement) -> Effect {
    Effect::SetField {
        cell,
        index: index as usize,
        value,
    }
}

/// Plan a new identity cell of `charter` (devices/recovery council +
/// cooling window). The standard polis bootstrap follows: deploy the
/// descriptor, run `create_effects` / `fund_effects` /
/// `execute_as(.., adopt_effects, ADOPT_TURN_FEE)`, then [`genesis_effects`].
pub fn create_identity(
    charter: &IdentityCharter,
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    operator: CellId,
    funder: CellId,
) -> Result<GovernanceCellPlan, PolisError> {
    Ok(bootstrap_plan(
        identity_factory_descriptor(charter)?,
        owner_pubkey,
        token_id,
        operator,
        funder,
        0,
    ))
}

/// Build the genesis turn (KERI `icp`): install the birth key-set
/// commitment, the FIRST next-keys pre-commitment, the pinned council
/// commitment, and step UNINIT → ACTIVE.
///
/// `birth_keys_commit` = [`key_set_commitment`] of the current (exposed)
/// device keys; `first_next_digest` = [`next_keys_digest`] of the next,
/// UNEXPOSED key set's commitment — generate that set now, commit it here,
/// expose it only at the first rotation.
///
/// **Safety contract**: the program admits genesis without a preimage ONLY
/// while the register is unborn (`old == 0`); an ACTIVE identity always
/// carries nonzero key registers, and the council commitment is pinned for
/// life.
pub fn genesis_effects(
    cell: CellId,
    charter: &IdentityCharter,
    birth_keys_commit: FieldElement,
    first_next_digest: FieldElement,
) -> Vec<Effect> {
    vec![
        set(cell, CURRENT_KEYS_COMMIT_SLOT, birth_keys_commit),
        set(cell, NEXT_KEYS_DIGEST_SLOT, first_next_digest),
        set(
            cell,
            COUNCIL_COMMIT_SLOT,
            charter.council.members_commitment(),
        ),
        set(cell, STATE_SLOT, field_from_u64(STATE_ACTIVE)),
    ]
}

/// Build the rotate turn's effects (KERI `rot`): install
/// `presented_commit` as current, commit `fresh_next_digest` (the next
/// chain link), and stamp `height` (MUST be the execution height — the
/// program pins it).
///
/// The turn must ALSO exhibit `presented_commit` as a `Preimage32` witness
/// ([`TurnBuilder::reveal`](crate::turns::TurnBuilder::reveal)) — without
/// it the executor refuses, regardless of signatures.
/// [`AgentRuntime::rotate_identity`] assembles the whole shape.
pub fn rotate_effects(
    cell: CellId,
    presented_commit: FieldElement,
    fresh_next_digest: FieldElement,
    height: u64,
) -> Vec<Effect> {
    vec![
        set(cell, CURRENT_KEYS_COMMIT_SLOT, presented_commit),
        set(cell, NEXT_KEYS_DIGEST_SLOT, fresh_next_digest),
        set(cell, LAST_ROTATED_AT_SLOT, field_from_u64(height)),
    ]
}

/// Build the retire turn: step ACTIVE → RETIRED (terminal, inert — no
/// further rotation or touch can commit).
pub fn retire_effects(cell: CellId) -> Vec<Effect> {
    vec![set(cell, STATE_SLOT, field_from_u64(STATE_RETIRED))]
}

impl AgentRuntime {
    /// Rotate an identity cell's key set — the `rotate(new_keys,
    /// next_digest)` verb on the identity noun, riding the normal
    /// `.turn()` path.
    ///
    /// `new_keys` is the key set whose commitment was PRE-COMMITTED in the
    /// cell's `next_keys_digest` register (committed before exposure;
    /// exposed here, the preimage EXHIBIT); `fresh_next_digest` is the
    /// commitment to the set after it ([`next_keys_digest`] of an
    /// unexposed [`key_set_commitment`]) — the forward chain's next link.
    ///
    /// The executor admits the turn only if the exhibited commitment is
    /// the committed preimage, the install matches, the fresh digest is
    /// live, and the charter's cooling window has passed — presenting any
    /// other key set is refused even when the turn is signed by all
    /// current keys.
    pub fn rotate_identity(
        &self,
        identity_cell: CellId,
        new_keys: &[[u8; 32]],
        fresh_next_digest: FieldElement,
    ) -> Result<Receipt, SdkError> {
        let presented = key_set_commitment(new_keys);
        let height = self.block_height();
        self.turn()
            .on(identity_cell)
            .method("rotate")
            .effects(rotate_effects(
                identity_cell,
                presented,
                fresh_next_digest,
                height,
            ))
            .reveal(presented)
            .sign()?
            .submit()
    }
}

// =============================================================================
// VRF sortition keys — the vrf-keyed sortition surface
// =============================================================================
//
// Per-agent ECVRF sortition (`dregg_federation::vrf`, RFC 9381
// ECVRF-EDWARDS25519-SHA512-TAI) lets an agent PRIVATELY learn whether the
// beacon selected it for a duty (`sortition_select(beacon, sk, role,
// threshold)`) and reveal a publicly-checkable ticket only if so — the
// targeting-resistant complement to `dregg_federation::beacon::select_jury`,
// which computes a public roster anyone can enumerate (and therefore target)
// the instant the beacon lands.
//
// ## Key class: a CURRENT-key-class member of the identity cell
//
// ECVRF-EDWARDS25519 key generation IS RFC 8032 Ed25519 key generation
// (RFC 9381 §5.5), so a VRF key is managed exactly like a device signing
// key:
//
// * its 32-byte public key is one MEMBER of the key set committed by
//   [`key_set_commitment`] into `CURRENT_KEYS_COMMIT_SLOT`
//   ([`key_set_with_vrf`] builds that set), and
// * the NEXT epoch's VRF public key sits inside the unexposed set whose
//   digest is pre-committed under [`next_keys_digest`] —
//
// so KERI-shaped pre-rotation covers sortition keys with no new verb: a
// rotation (`rotate_identity`) retires the exfiltratable VRF secret along
// with the signing keys, and a thief holding the current VRF secret can
// neither block the rotation nor carry selection power past it. Derive the
// per-epoch seed with [`derive_vrf_seed`] from the SAME unexposed master
// material whose escrow discipline the module docs above prescribe.
//
// A juror-verifier therefore checks two bindings: the cryptographic one
// (`dregg_federation::vrf::verify_sortition`) and the identity one (the
// ticket's `public_key` is a member of the candidate's CURRENT committed
// key set — the `key_set_commitment` opening).

/// blake3 `derive_key` context for per-epoch VRF seeds. Distinct from every
/// other derive-key context in the tree (`dregg-fed-id-v1`,
/// `dregg-beacon-output-v1`, `dregg-beacon-draw-v1`, …).
pub const VRF_SEED_CONTEXT: &str = "dregg-identity-vrf-seed-v1";

/// Derive the VRF seed for one key epoch from the identity's unexposed
/// master seed: `blake3::derive_key(VRF_SEED_CONTEXT, master ‖ epoch_be)`.
///
/// `key_epoch` is the identity cell's rotation generation (0 at genesis,
/// +1 per `rotate_identity`), so each rotation FORWARD-derives a fresh VRF
/// key whose public half was already pre-committed in `next_keys_digest` —
/// compromise of one epoch's VRF secret says nothing about the next
/// (one-wayness of the derive), and the master seed never touches a prover.
pub fn derive_vrf_seed(master_seed: &[u8; 32], key_epoch: u64) -> [u8; 32] {
    let mut input = [0u8; 40];
    input[..32].copy_from_slice(master_seed);
    input[32..].copy_from_slice(&key_epoch.to_be_bytes());
    blake3::derive_key(VRF_SEED_CONTEXT, &input)
}

/// The VRF public key for a seed — byte-identical to the Ed25519 verifying
/// key of the same seed, because ECVRF-EDWARDS25519 keygen IS RFC 8032
/// keygen (RFC 9381 §5.5). This is why the SDK needs no VRF implementation
/// of its own: commitment-side key management rides `ed25519-dalek`, and
/// proving/verifying live in `dregg_federation::vrf` (whose
/// `keygen_agrees_with_ed25519_dalek` test pins this very agreement).
pub fn vrf_public_key(vrf_seed: &[u8; 32]) -> [u8; 32] {
    ed25519_dalek::SigningKey::from_bytes(vrf_seed)
        .verifying_key()
        .to_bytes()
}

/// The key set an identity commits when it carries a sortition key: the
/// device signing keys PLUS the VRF public key, in that order (members are
/// position-committed, so the convention is part of the opening). Feed the
/// result to [`key_set_commitment`] for `CURRENT_KEYS_COMMIT_SLOT` /
/// [`genesis_effects`], or hash its commitment with [`next_keys_digest`]
/// for the pre-commitment — same as any other key set.
pub fn key_set_with_vrf(device_keys: &[[u8; 32]], vrf_public: [u8; 32]) -> Vec<[u8; 32]> {
    let mut keys = Vec::with_capacity(device_keys.len() + 1);
    keys.extend_from_slice(device_keys);
    keys.push(vrf_public);
    keys
}

#[cfg(test)]
mod vrf_surface_tests {
    use super::*;

    #[test]
    fn vrf_seed_derivation_is_deterministic_and_epoch_separated() {
        let master = [7u8; 32];
        assert_eq!(derive_vrf_seed(&master, 3), derive_vrf_seed(&master, 3));
        assert_ne!(derive_vrf_seed(&master, 3), derive_vrf_seed(&master, 4));
        assert_ne!(derive_vrf_seed(&master, 3), derive_vrf_seed(&[8u8; 32], 3));
        // The derived seed is not the master (one-way derive, no echo).
        assert_ne!(derive_vrf_seed(&master, 0), master);
    }

    #[test]
    fn vrf_public_key_is_the_ed25519_verifying_key() {
        let seed = [21u8; 32];
        let expected = ed25519_dalek::SigningKey::from_bytes(&seed)
            .verifying_key()
            .to_bytes();
        assert_eq!(vrf_public_key(&seed), expected);
    }

    #[test]
    fn key_set_with_vrf_changes_the_commitment() {
        let devices = [[1u8; 32], [2u8; 32]];
        let vrf_pk = vrf_public_key(&derive_vrf_seed(&[9u8; 32], 0));
        let with = key_set_commitment(&key_set_with_vrf(&devices, vrf_pk));
        let without = key_set_commitment(&devices);
        assert_ne!(with, without);
        // Position-committed: the same members in the documented order
        // reproduce the commitment.
        let again = key_set_commitment(&key_set_with_vrf(&devices, vrf_pk));
        assert_eq!(with, again);
    }
}
