//! `FactoryDescriptor`-shaped reference template for directory cells.
//!
//! Per `STORAGE-AS-CELL-PROGRAMS.md`, every storage primitive becomes a
//! factory in `dregg_cell::factory::FactoryDescriptor` shape: the slot
//! layout + state constraints declare the cell-program pattern, and the
//! executor enforces those constraints on every state-modifying turn.
//!
//! The [`DirectoryCell`](crate::directory::DirectoryCell) data structure
//! is the in-memory operational form of a directory; the descriptor
//! returned by [`directory_factory_descriptor`] is the on-ledger
//! contract that says "this cell is a directory" — its slot layout, its
//! lifetime invariants, and the capability grants the factory may
//! issue at creation time.
//!
//! # Slot layout (the `DirectorySlots` constants)
//!
//! | Slot | Meaning |
//! |------|---------|
//! | 0    | Directory schema version (currently `1`, `WriteOnce`)         |
//! | 1    | Total entry count (monotone — never decreases on a healthy directory; expirations are out-of-band) |
//! | 2    | Membership-set Merkle root (admins / readers)                |
//! | 3    | Capacity cap (max entries; `WriteOnce` at creation)          |
//! | 4    | Gossip-topic id (derived `WriteOnce` from the cell id)       |
//! | 5    | Entries Merkle root (commits to the `BTreeMap<Name, Entry>`) |
//! | 6    | Created-at block height (`WriteOnce`)                        |
//! | 7    | Reserved for sub-directory parent ref (used by MetaDirectory)|
//!
//! The eight slots map onto `dregg_cell::STATE_SLOTS`. The `entries`
//! data themselves live off-cell (a Merkle tree); slot 5 commits to
//! that tree's root so the executor can verify swap operations against
//! a Merkle-membership witness.
//!
//! # State constraints
//!
//! The factory bakes in five invariants:
//!
//! * `WriteOnce` on slot 0 (schema version)
//! * `WriteOnce` on slot 3 (capacity)
//! * `WriteOnce` on slot 4 (gossip topic id, derived from cell id)
//! * `WriteOnce` on slot 6 (created-at height)
//! * `Monotonic` on slot 1 (entry count — guards against operator
//!   under-counting attempts; expirations bypass this by going through
//!   a separate `gc` turn that may decrement)
//!
//! Apps can layer further constraints (rate-limit per epoch via
//! `RateLimitBySum`, sender ACLs via `SenderAuthorized + PublicRoot`,
//! etc.) by extending `state_constraints` at descriptor-build time.

use dregg_cell::factory::{ChildVkStrategy, FactoryDescriptor};
use dregg_cell::{CellMode, StateConstraint, field_from_u64};

/// Slot-index constants for the directory cell-program pattern.
///
/// These are referenced both by the [`directory_factory_descriptor`]
/// (to bake `WriteOnce` / `Monotonic` constraints onto the right slot
/// indices) and by callers building turns over a directory cell (to
/// know which slot to `SetField` against).
pub struct DirectorySlots;

impl DirectorySlots {
    /// Schema version (currently 1). `WriteOnce`.
    pub const SCHEMA_VERSION: u8 = 0;
    /// Total entry count. `Monotonic` (only `gc_expired` turns may
    /// decrement, via a separate factory or override).
    pub const ENTRY_COUNT: u8 = 1;
    /// Membership-set Merkle root.
    pub const MEMBERSHIP_ROOT: u8 = 2;
    /// Capacity cap. `WriteOnce` at creation.
    pub const CAPACITY: u8 = 3;
    /// Gossip-topic id. `WriteOnce`; derived deterministically from
    /// the cell id at creation.
    pub const GOSSIP_TOPIC: u8 = 4;
    /// Entries Merkle root.
    pub const ENTRIES_ROOT: u8 = 5;
    /// Created-at block height. `WriteOnce`.
    pub const CREATED_AT: u8 = 6;
    /// Parent meta-directory ref (used when this directory is a child
    /// of a `MetaDirectory`).
    pub const PARENT_REF: u8 = 7;
}

/// Tuning knobs for the directory factory descriptor.
#[derive(Clone, Debug)]
pub struct DirectoryFactoryConfig {
    /// Factory program VK hash (content-identity of the factory).
    pub factory_vk: [u8; 32],
    /// Child cell program VK hash; the program that runs on every
    /// directory cell created by this factory.
    pub child_program_vk: [u8; 32],
    /// Per-epoch creation budget (None = unbounded).
    pub creation_budget: Option<u64>,
    /// Whether created cells are hosted (federation-evaluated) or
    /// sovereign (agent-witnessed).
    pub default_mode: CellMode,
}

impl DirectoryFactoryConfig {
    /// Build a default config from the factory VK alone, using the
    /// factory's VK as the child program VK (mints-itself pattern).
    pub fn from_factory_vk(factory_vk: [u8; 32]) -> Self {
        Self {
            factory_vk,
            child_program_vk: factory_vk,
            creation_budget: None,
            default_mode: CellMode::Hosted,
        }
    }
}

/// The reference `FactoryDescriptor` for the directory cell-program
/// pattern.
///
/// This is the on-ledger contract that the
/// [`DirectoryCell`](crate::directory::DirectoryCell) data structure
/// operationally embodies. The returned descriptor:
///
/// * declares the slot layout via its baked-in `state_constraints`,
/// * holds the canonical lifetime invariants
///   (`WriteOnce` on capacity / topic / created-at, `Monotonic` on
///   entry count),
/// * lists no `field_constraints` (initial slot values are determined
///   by the registering app at creation time; the lifetime checks
///   handle the rest), and
/// * grants no capability templates (sub-directory grants are emitted
///   by separate factory descriptors registered alongside).
///
/// Apps that want richer enforcement (e.g. rate-limit per epoch,
/// sender-set ACLs) extend `state_constraints` on the returned value
/// before calling [`FactoryDescriptor::hash`].
pub fn directory_factory_descriptor(cfg: DirectoryFactoryConfig) -> FactoryDescriptor {
    let state_constraints = vec![
        StateConstraint::WriteOnce {
            index: DirectorySlots::SCHEMA_VERSION,
        },
        StateConstraint::WriteOnce {
            index: DirectorySlots::CAPACITY,
        },
        StateConstraint::WriteOnce {
            index: DirectorySlots::GOSSIP_TOPIC,
        },
        StateConstraint::WriteOnce {
            index: DirectorySlots::CREATED_AT,
        },
        StateConstraint::Monotonic {
            index: DirectorySlots::ENTRY_COUNT,
        },
        // The schema-version slot is also pinned to the value `1`.
        StateConstraint::FieldEquals {
            index: DirectorySlots::SCHEMA_VERSION,
            value: field_from_u64(1),
        },
    ];

    FactoryDescriptor {
        factory_vk: cfg.factory_vk,
        child_program_vk: Some(cfg.child_program_vk),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(cfg.child_program_vk))),
        allowed_cap_templates: Vec::new(),
        field_constraints: Vec::new(),
        state_constraints,
        default_mode: cfg.default_mode,
        creation_budget: cfg.creation_budget,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn descriptor_bakes_writeonce_and_monotonic_constraints() {
        let cfg = DirectoryFactoryConfig::from_factory_vk([0xAB; 32]);
        let desc = directory_factory_descriptor(cfg);

        // Five WriteOnce/Monotonic + the FieldEquals pin = six total.
        assert_eq!(desc.state_constraints.len(), 6);

        let mut write_once_slots: Vec<u8> = desc
            .state_constraints
            .iter()
            .filter_map(|c| match c {
                StateConstraint::WriteOnce { index } => Some(*index),
                _ => None,
            })
            .collect();
        write_once_slots.sort();
        assert_eq!(
            write_once_slots,
            vec![
                DirectorySlots::SCHEMA_VERSION,
                DirectorySlots::CAPACITY,
                DirectorySlots::GOSSIP_TOPIC,
                DirectorySlots::CREATED_AT,
            ]
        );

        // Monotonic on entry count.
        assert!(desc.state_constraints.iter().any(|c| matches!(
            c,
            StateConstraint::Monotonic {
                index
            } if *index == DirectorySlots::ENTRY_COUNT
        )));
    }

    #[test]
    fn descriptor_hash_is_deterministic() {
        let cfg = DirectoryFactoryConfig::from_factory_vk([0xCD; 32]);
        let a = directory_factory_descriptor(cfg.clone()).hash();
        let b = directory_factory_descriptor(cfg).hash();
        assert_eq!(a, b);
    }

    #[test]
    fn descriptor_hash_changes_with_factory_vk() {
        let a =
            directory_factory_descriptor(DirectoryFactoryConfig::from_factory_vk([1u8; 32])).hash();
        let b =
            directory_factory_descriptor(DirectoryFactoryConfig::from_factory_vk([2u8; 32])).hash();
        assert_ne!(a, b);
    }
}
