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
    CURRENT_KEYS_COMMIT_SLOT, COUNCIL_COMMIT_SLOT, IdentityCharter, IdentityState, IdentityStatus,
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
