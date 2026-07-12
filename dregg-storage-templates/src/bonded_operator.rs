//! # `bonded_operator` — bonded-operator registration helper
//!
//! A *bonded operator* is an actor who posts a bond and thereby becomes
//! an accountable operator cell: the bond is the stake a governance
//! process can slash on dispute. This module is a thin, reusable
//! wrapper over the [`relay_operator`](crate::relay_operator) reference
//! template — it does **not** define a new factory, slot layout, or
//! cell program. A bonded operator *is* a relay-operator cell, viewed
//! through the bond/standing lens:
//!
//! - the posted bond lands in
//!   [`BOND_AMOUNT_SLOT`](crate::relay_operator::BOND_AMOUNT_SLOT) and
//!   must be `>=` the floor in
//!   [`BOND_MIN_SLOT`](crate::relay_operator::BOND_MIN_SLOT);
//! - the operator's public-key hash pins identity in
//!   [`OPERATOR_PK_HASH_SLOT`](crate::relay_operator::OPERATOR_PK_HASH_SLOT);
//! - a freshly-opened operator starts in good standing with
//!   [`DISPUTE_COUNT_SLOT`](crate::relay_operator::DISPUTE_COUNT_SLOT)
//!   at zero.
//!
//! Registration (factory install) and slashing/quota semantics live in
//! [`relay_operator`](crate::relay_operator); this module only adds the
//! ergonomic "open a bonded operator" constructor (with the bond-floor
//! and identity-pinning checks a caller wants *before* it mints the
//! cell) plus read helpers over the bond and standing.

use dregg_app_framework::{FactoryDescriptor, FieldElement, StarbridgeAppContext};

use crate::relay_operator::{
    self, BOND_AMOUNT_SLOT, BOND_MIN_SLOT, DISPUTE_COUNT_SLOT, OPERATOR_PK_HASH_SLOT,
    QUOTA_BYTES_PER_EPOCH_SLOT, RELAY_OPERATOR_FACTORY_VK,
};

// =============================================================================
// Re-exports — a bonded operator uses the relay-operator factory/slots.
// =============================================================================

/// The factory a bonded-operator cell is minted under. Aliased from
/// [`relay_operator::RELAY_OPERATOR_FACTORY_VK`] so callers of this
/// module don't have to reach across into the relay lane, and so it is
/// unambiguous that we reuse — not reinvent — the operator factory.
pub const BONDED_OPERATOR_FACTORY_VK: [u8; 32] = RELAY_OPERATOR_FACTORY_VK;

// =============================================================================
// Defaults for the relay-facet slots a bond-focused caller doesn't set.
// =============================================================================

/// Default per-epoch byte quota for a freshly-opened bonded operator.
/// Chosen inside the factory descriptor's `FieldConstraint::Range` for
/// the quota slot (`1_000 ..= 1_000_000_000`).
pub const DEFAULT_QUOTA_BYTES_PER_EPOCH: u64 = 1_000_000;

/// Commitment to an *empty* route table — the `route_table_root` a
/// bonded operator carries before it has registered any routes. The
/// factory requires this slot be non-zero, so a bonded operator that is
/// not yet routing still commits to the empty-table root rather than a
/// zero root.
pub fn empty_route_table_root() -> [u8; 32] {
    *blake3::hash(b"dregg-bonded-operator:empty-route-table").as_bytes()
}

// =============================================================================
// Errors
// =============================================================================

/// Why a bonded-operator registration was rejected before minting.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BondError {
    /// The posted bond is below the required minimum (the floor).
    BondBelowFloor {
        /// The bond the caller tried to post.
        bond: u64,
        /// The floor the operator must clear.
        bond_min: u64,
    },
    /// The operator public-key hash is all-zero, i.e. identity is not
    /// pinned. A bonded operator must commit to a real key.
    UnpinnedOperator,
}

impl core::fmt::Display for BondError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BondError::BondBelowFloor { bond, bond_min } => write!(
                f,
                "posted bond {bond} is below the required minimum {bond_min}"
            ),
            BondError::UnpinnedOperator => {
                write!(f, "operator public-key hash is zero (identity not pinned)")
            }
        }
    }
}

impl std::error::Error for BondError {}

// =============================================================================
// BondedOperator
// =============================================================================

/// A validated bonded-operator cell state, ready to be minted under the
/// relay-operator factory. Thin newtype over the relay-operator
/// [`initial_state`](crate::relay_operator::initial_state) array.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BondedOperator {
    state: [FieldElement; 8],
}

impl BondedOperator {
    /// The genesis cell state, in relay-operator slot order. Feed this
    /// to the factory to mint the operator cell.
    pub fn initial_state(&self) -> [FieldElement; 8] {
        self.state
    }

    /// Borrow the genesis cell state.
    pub fn state(&self) -> &[FieldElement; 8] {
        &self.state
    }

    /// The bond posted into [`BOND_AMOUNT_SLOT`].
    pub fn bond_amount(&self) -> u64 {
        field_to_u64(&self.state[BOND_AMOUNT_SLOT as usize])
    }

    /// The bond floor pinned into [`BOND_MIN_SLOT`].
    pub fn bond_min(&self) -> u64 {
        field_to_u64(&self.state[BOND_MIN_SLOT as usize])
    }

    /// The per-epoch byte quota pinned into [`QUOTA_BYTES_PER_EPOCH_SLOT`].
    pub fn quota_bytes_per_epoch(&self) -> u64 {
        field_to_u64(&self.state[QUOTA_BYTES_PER_EPOCH_SLOT as usize])
    }

    /// The operator public-key hash pinned into [`OPERATOR_PK_HASH_SLOT`].
    pub fn operator_pk_hash(&self) -> [u8; 32] {
        self.state[OPERATOR_PK_HASH_SLOT as usize]
    }

    /// The dispute counter in [`DISPUTE_COUNT_SLOT`]. Zero for a
    /// freshly-opened operator; each resolved dispute advances it by one
    /// (see the `slash` case in [`relay_operator`]).
    pub fn dispute_count(&self) -> u64 {
        field_to_u64(&self.state[DISPUTE_COUNT_SLOT as usize])
    }

    /// `true` while the bond still clears its floor — the invariant a
    /// governance process checks before honoring the operator.
    pub fn bond_meets_floor(&self) -> bool {
        self.bond_amount() >= self.bond_min()
    }

    /// `true` while the operator has no recorded disputes.
    pub fn is_in_good_standing(&self) -> bool {
        self.dispute_count() == 0
    }

    /// Reconstruct a view over an existing on-ledger operator cell
    /// state (e.g. one read back from the ledger) so the read helpers
    /// above can be reused. Performs no validation — a cell already
    /// minted has been validated by the executor.
    pub fn from_state(state: [FieldElement; 8]) -> Self {
        BondedOperator { state }
    }
}

// =============================================================================
// Open / register
// =============================================================================

/// Open a bonded operator with a bond, a floor, and a pinned key,
/// using [`DEFAULT_QUOTA_BYTES_PER_EPOCH`] and the
/// [`empty_route_table_root`] for the relay-facet slots the bond lens
/// does not set.
///
/// Rejects a bond below the floor and an unpinned (zero) operator key.
/// The returned [`BondedOperator`] carries `dispute_count = 0`.
pub fn open_bonded_operator(
    bond_amount: u64,
    bond_min: u64,
    operator_pk_hash: [u8; 32],
) -> Result<BondedOperator, BondError> {
    open_bonded_operator_with(
        bond_amount,
        bond_min,
        operator_pk_hash,
        DEFAULT_QUOTA_BYTES_PER_EPOCH,
        empty_route_table_root(),
    )
}

/// Open a bonded operator with full control over the relay-facet slots
/// (`quota_bytes_per_epoch`, `route_table_root`).
///
/// Enforces the two bonded-operator invariants a caller wants checked
/// before minting: the operator key must be pinned (non-zero) and the
/// posted bond must clear the floor. Everything else — the on-cell
/// enforcement of slashing, quota, and dispatch — is the relay-operator
/// program's job and is unchanged here.
pub fn open_bonded_operator_with(
    bond_amount: u64,
    bond_min: u64,
    operator_pk_hash: [u8; 32],
    quota_bytes_per_epoch: u64,
    route_table_root: [u8; 32],
) -> Result<BondedOperator, BondError> {
    if operator_pk_hash == [0u8; 32] {
        return Err(BondError::UnpinnedOperator);
    }
    if bond_amount < bond_min {
        return Err(BondError::BondBelowFloor {
            bond: bond_amount,
            bond_min,
        });
    }

    let state = relay_operator::initial_state(
        bond_amount,
        bond_min,
        quota_bytes_per_epoch,
        operator_pk_hash,
        route_table_root,
    );

    Ok(BondedOperator { state })
}

/// The [`FactoryDescriptor`] bonded operators are minted under — the
/// relay-operator descriptor, reused verbatim.
pub fn bonded_operator_factory_descriptor() -> FactoryDescriptor {
    relay_operator::relay_operator_factory_descriptor()
}

/// Install the operator factory on a [`StarbridgeAppContext`]. Delegates
/// to [`relay_operator::register`]; a bonded operator does not add a
/// second factory. Returns the factory VK.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    relay_operator::register(ctx)
}

// =============================================================================
// Field decoding — inverse of the crate's `u64_field`.
// =============================================================================

/// Decode the scalar packed by
/// [`crate::u64_field`]: a big-endian `u64` in the trailing 8 bytes of
/// a 32-byte field element.
fn field_to_u64(field: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&field[24..32]);
    u64::from_be_bytes(b)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn test_pk() -> [u8; 32] {
        *blake3::hash(b"operator-key").as_bytes()
    }

    #[test]
    fn bond_below_floor_is_rejected() {
        let err = open_bonded_operator(50, 100, test_pk()).unwrap_err();
        assert_eq!(
            err,
            BondError::BondBelowFloor {
                bond: 50,
                bond_min: 100
            }
        );
    }

    #[test]
    fn bond_exactly_at_floor_is_accepted() {
        // The floor is inclusive: bond == bond_min clears it.
        let op = open_bonded_operator(100, 100, test_pk()).expect("bond at floor registers");
        assert!(op.bond_meets_floor());
        assert_eq!(op.bond_amount(), 100);
        assert_eq!(op.bond_min(), 100);
    }

    #[test]
    fn valid_bond_registers_in_good_standing() {
        let op = open_bonded_operator(500, 100, test_pk()).expect("valid bond registers");
        assert_eq!(op.bond_amount(), 500);
        assert_eq!(op.bond_min(), 100);
        assert!(op.bond_meets_floor());
        assert_eq!(op.dispute_count(), 0);
        assert!(op.is_in_good_standing());
    }

    #[test]
    fn operator_pubkey_is_pinned() {
        let pk = test_pk();
        let op = open_bonded_operator(500, 100, pk).expect("valid bond registers");
        // Read helper agrees with the raw slot.
        assert_eq!(op.operator_pk_hash(), pk);
        assert_eq!(op.state()[OPERATOR_PK_HASH_SLOT as usize], pk);
    }

    #[test]
    fn unpinned_operator_is_rejected() {
        let err = open_bonded_operator(500, 100, [0u8; 32]).unwrap_err();
        assert_eq!(err, BondError::UnpinnedOperator);
    }

    #[test]
    fn bond_lands_in_bond_amount_slot() {
        let op = open_bonded_operator(777, 100, test_pk()).unwrap();
        assert_eq!(
            field_to_u64(&op.state()[BOND_AMOUNT_SLOT as usize]),
            777,
            "posted bond must land in BOND_AMOUNT_SLOT"
        );
    }

    #[test]
    fn defaults_are_within_factory_ranges() {
        // The default quota and empty-route root must satisfy the
        // relay-operator factory's field constraints so a
        // default-opened bonded operator is a *valid* cell.
        let op = open_bonded_operator(500, 100, test_pk()).unwrap();
        assert_eq!(op.quota_bytes_per_epoch(), DEFAULT_QUOTA_BYTES_PER_EPOCH);
        assert!((1_000..=1_000_000_000).contains(&op.quota_bytes_per_epoch()));
        assert_ne!(
            op.state()[6], // ROUTE_TABLE_ROOT_SLOT
            [0u8; 32],
            "route_table_root must be non-zero for the factory"
        );
    }

    #[test]
    fn with_variant_sets_relay_facet_slots() {
        let route = *blake3::hash(b"routes").as_bytes();
        let op = open_bonded_operator_with(500, 100, test_pk(), 4_096, route).unwrap();
        assert_eq!(op.quota_bytes_per_epoch(), 4_096);
        assert_eq!(op.state()[6], route);
    }

    #[test]
    fn from_state_round_trips_the_read_helpers() {
        let op = open_bonded_operator(500, 100, test_pk()).unwrap();
        let view = BondedOperator::from_state(op.initial_state());
        assert_eq!(view.bond_amount(), 500);
        assert_eq!(view.operator_pk_hash(), test_pk());
        assert!(view.is_in_good_standing());
    }

    #[test]
    fn a_disputed_operator_reads_out_of_good_standing() {
        // Simulate a slashed cell: dispute_count advanced to 1.
        let mut state = open_bonded_operator(500, 100, test_pk())
            .unwrap()
            .initial_state();
        state[DISPUTE_COUNT_SLOT as usize] = crate::u64_field(1);
        let view = BondedOperator::from_state(state);
        assert_eq!(view.dispute_count(), 1);
        assert!(!view.is_in_good_standing());
    }

    #[test]
    fn factory_vk_matches_relay_operator() {
        assert_eq!(BONDED_OPERATOR_FACTORY_VK, RELAY_OPERATOR_FACTORY_VK);
        assert_eq!(
            bonded_operator_factory_descriptor().factory_vk,
            RELAY_OPERATOR_FACTORY_VK
        );
    }
}
