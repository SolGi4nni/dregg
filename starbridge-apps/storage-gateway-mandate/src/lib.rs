//! # starbridge-storage-gateway-mandate
//!
//! Scaffold for the **Storage Gateway Mandate** starbridge-app, mapping
//! `metatheory/Dregg2/Apps/StorageGatewayMandate*.lean` onto dregg-native
//! primitives.
//!
//! The mandate cell carries:
//! - `object_key`, `last_op` (GET/PUT/LIST encoded as 0/1/2);
//! - `volume_spent` (monotonic Stingray debit tracker);
//! - immutable `commitment_anchor` and `volume_ceiling`.
//!
//! Predicate-layer admission mirrors Lean `sgmAdmitM`: op allowlist, prefix
//! authorization (PUT), clearance (GET), and volume-budget debits.

#![forbid(unsafe_code)]

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, CellProgram,
    ChildVkStrategy, Effect, Event, FactoryDescriptor, FieldConstraint, FieldElement,
    InspectorDescriptor, StarbridgeAppContext, StateConstraint, TransitionCase, TransitionGuard,
    canonical_program_vk, field_from_bytes, field_from_u64, hex_encode_32, symbol,
};

// =============================================================================
// Storage domain (VFS ops)
// =============================================================================

/// Storage gateway operation (Lean `StorageOp`: GET / PUT / LIST).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StorageOp {
    /// Read — requires compartment clearance on `read_compartment`.
    Get,
    /// Write — requires key under mandated prefix.
    Put,
    /// List — op-allowlist + volume debit only.
    List,
}

impl StorageOp {
    /// Encode as an `Int` field value (Lean `StorageOp.toInt`).
    pub const fn to_field_value(self) -> u64 {
        match self {
            Self::Get => 0,
            Self::Put => 1,
            Self::List => 2,
        }
    }

    /// Decode from a field-encoded op (Lean `StorageOp.ofInt`).
    pub fn from_field_value(value: u64) -> Option<Self> {
        match value {
            0 => Some(Self::Get),
            1 => Some(Self::Put),
            2 => Some(Self::List),
            _ => None,
        }
    }

    /// Per-op Stingray volume debit (Lean `opCost`).
    pub const fn demo_cost(self) -> u64 {
        match self {
            Self::Get => 1,
            Self::Put => 5,
            Self::List => 2,
        }
    }
}

/// Default demo prefix (Lean `demoMandate.keyPrefix`).
pub const DEFAULT_KEY_PREFIX: &str = "uploads/";

/// Default Stingray volume ceiling (Lean `demoMandate.volumeBudget.ceiling`).
pub const DEFAULT_VOLUME_CEILING: u64 = 10;

/// Default commitment-anchor bucket tag (Lean `demoMandate.anchor`).
pub const DEFAULT_COMMITMENT_ANCHOR: u64 = 42;

/// Demo read-compartment label (Lean `readCompartment`).
pub const DEFAULT_READ_COMPARTMENT: &str = "storage-read";

// =============================================================================
// Slot layout (mandate cell)
// =============================================================================

/// Slot 0 — `object_key`. Content-addressed key hash for the last op.
pub const OBJECT_KEY_SLOT: u8 = 0;

/// Slot 1 — `last_op`. Encoded [`StorageOp`] (0/1/2).
pub const LAST_OP_SLOT: u8 = 1;

/// Slot 2 — `volume_spent`. Monotonic Stingray debit tracker.
pub const VOLUME_SPENT_SLOT: u8 = 2;

/// Slot 3 — `commitment_anchor`. Immutable bucket/compartment tag.
pub const COMMITMENT_ANCHOR_SLOT: u8 = 3;

/// Slot 4 — `volume_ceiling`. Immutable Stingray slice ceiling.
pub const VOLUME_CEILING_SLOT: u8 = 4;

/// Slot 5 — `key_prefix_hash`. Immutable authorized prefix commitment.
pub const KEY_PREFIX_HASH_SLOT: u8 = 5;

/// Slot 6 — `read_compartment_hash`. Immutable GET clearance label.
pub const READ_COMPARTMENT_SLOT: u8 = 6;

// =============================================================================
// Factory configuration
// =============================================================================

/// The factory VK we publish for the storage-gateway mandate factory.
pub const SGM_FACTORY_VK: [u8; 32] = *b"starbridge-sgm-mandate-factory!!";

/// Default per-epoch creation budget.
pub const DEFAULT_CREATION_BUDGET: u64 = 512;

/// Hash an object key string for slot storage.
pub fn object_key_field(key: &str) -> FieldElement {
    field_from_bytes(key.as_bytes())
}

/// Hash the mandated key prefix.
pub fn key_prefix_field(prefix: &str) -> FieldElement {
    field_from_bytes(prefix.as_bytes())
}

/// Whether `op` is in the allowed set (Lean `opAllowed`).
pub fn op_allowed(op: StorageOp, allowed: &[StorageOp]) -> bool {
    allowed.contains(&op)
}

/// Object key lies under the mandated prefix (Lean `keyUnderPrefix` / `putPrefixOK`).
pub fn key_under_prefix(prefix: &str, key: &str) -> bool {
    key.starts_with(prefix)
}

/// GET requires compartment clearance (Lean `getClearanceOK` scaffold).
pub fn get_clearance_ok(actor_labels: &[FieldElement], read_compartment: FieldElement) -> bool {
    actor_labels.contains(&read_compartment)
}

/// Stingray volume debit admission (Lean `Slice.tryDebit`).
pub fn volume_debit_ok(spent: u64, cost: u64, ceiling: u64) -> bool {
    spent.saturating_add(cost) <= ceiling
}

/// Compute new spent after a successful debit.
pub fn volume_after_debit(spent: u64, cost: u64) -> Option<u64> {
    let new = spent.checked_add(cost)?;
    if new <= ceiling_for_demo() {
        Some(new)
    } else {
        None
    }
}

fn ceiling_for_demo() -> u64 {
    DEFAULT_VOLUME_CEILING
}

/// **`sgm_admit`** — predicate-level one-step admission (Lean `sgmAdmitM`).
pub fn sgm_admit(
    spent: u64,
    ceiling: u64,
    key: &str,
    prefix: &str,
    op: StorageOp,
    allowed: &[StorageOp],
    actor_labels: &[FieldElement],
    read_compartment: FieldElement,
) -> Option<u64> {
    if !op_allowed(op, allowed) {
        return None;
    }
    match op {
        StorageOp::Get => {
            if !get_clearance_ok(actor_labels, read_compartment) {
                return None;
            }
            let cost = op.demo_cost();
            if volume_debit_ok(spent, cost, ceiling) {
                Some(spent + cost)
            } else {
                None
            }
        }
        StorageOp::Put => {
            if !key_under_prefix(prefix, key) {
                return None;
            }
            let cost = op.demo_cost();
            if volume_debit_ok(spent, cost, ceiling) {
                Some(spent + cost)
            } else {
                None
            }
        }
        StorageOp::List => {
            let cost = op.demo_cost();
            if volume_debit_ok(spent, cost, ceiling) {
                Some(spent + cost)
            } else {
                None
            }
        }
    }
}

/// Cell-program skeleton: immutable anchor/ceiling/prefix + monotonic volume + bounded spend.
pub fn sgm_cell_program() -> CellProgram {
    CellProgram::Cases(vec![
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![
                StateConstraint::Immutable {
                    index: COMMITMENT_ANCHOR_SLOT,
                },
                StateConstraint::Immutable {
                    index: VOLUME_CEILING_SLOT,
                },
                StateConstraint::Immutable {
                    index: KEY_PREFIX_HASH_SLOT,
                },
                StateConstraint::Immutable {
                    index: READ_COMPARTMENT_SLOT,
                },
                StateConstraint::FieldLteField {
                    left_index: VOLUME_SPENT_SLOT,
                    right_index: VOLUME_CEILING_SLOT,
                },
            ],
        },
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("storage_op"),
            },
            constraints: vec![
                StateConstraint::Monotonic {
                    index: VOLUME_SPENT_SLOT,
                },
            ],
        },
    ])
}

/// Canonical child program VK.
pub fn sgm_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&sgm_cell_program())
}

/// Build the `FactoryDescriptor` for storage-gateway mandate cells.
pub fn sgm_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: SGM_FACTORY_VK,
        child_program_vk: Some(sgm_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(sgm_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![
            FieldConstraint::NonZero {
                field_index: COMMITMENT_ANCHOR_SLOT as u32,
            },
            FieldConstraint::NonZero {
                field_index: VOLUME_CEILING_SLOT as u32,
            },
        ],
        state_constraints: vec![
            StateConstraint::Immutable {
                index: COMMITMENT_ANCHOR_SLOT,
            },
            StateConstraint::Monotonic {
                index: VOLUME_SPENT_SLOT,
            },
            StateConstraint::FieldLteField {
                left_index: VOLUME_SPENT_SLOT,
                right_index: VOLUME_CEILING_SLOT,
            },
        ],
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![sgm_factory_descriptor()]
}

// =============================================================================
// Turn builders
// =============================================================================

/// Build the on-ledger [`Action`] recording one storage op.
///
/// Effects (Lean `sgmStorageChain`):
/// 1. `SetField(OBJECT_KEY_SLOT, key_hash)`
/// 2. `SetField(LAST_OP_SLOT, op_code)`
/// 3. `SetField(VOLUME_SPENT_SLOT, new_spent)`
/// 4. `EmitEvent("storage-op", [op, key_hash, blob_hash, new_spent])`
pub fn build_storage_op_action(
    cipherclerk: &AppCipherclerk,
    mandate_cell: CellId,
    key: &str,
    op: StorageOp,
    new_volume_spent: u64,
    blob_hash: FieldElement,
) -> Action {
    let key_field = object_key_field(key);
    let op_field = field_from_u64(op.to_field_value());
    let spent_field = field_from_u64(new_volume_spent);

    let effects = vec![
        Effect::SetField {
            cell: mandate_cell,
            index: OBJECT_KEY_SLOT as usize,
            value: key_field,
        },
        Effect::SetField {
            cell: mandate_cell,
            index: LAST_OP_SLOT as usize,
            value: op_field,
        },
        Effect::SetField {
            cell: mandate_cell,
            index: VOLUME_SPENT_SLOT as usize,
            value: spent_field,
        },
        Effect::EmitEvent {
            cell: mandate_cell,
            event: Event::new(
                symbol("storage-op"),
                vec![op_field, key_field, blob_hash, spent_field],
            ),
        },
    ];

    cipherclerk.make_action(mandate_cell, "storage_op", effects)
}

/// Convenience wrappers mirroring GET / PUT / LIST turn-builder names.
pub fn build_storage_get_action(
    cipherclerk: &AppCipherclerk,
    mandate_cell: CellId,
    key: &str,
    new_volume_spent: u64,
) -> Action {
    build_storage_op_action(
        cipherclerk,
        mandate_cell,
        key,
        StorageOp::Get,
        new_volume_spent,
        field_from_u64(0),
    )
}

pub fn build_storage_put_action(
    cipherclerk: &AppCipherclerk,
    mandate_cell: CellId,
    key: &str,
    new_volume_spent: u64,
    blob_hash: FieldElement,
) -> Action {
    build_storage_op_action(
        cipherclerk,
        mandate_cell,
        key,
        StorageOp::Put,
        new_volume_spent,
        blob_hash,
    )
}

pub fn build_storage_list_action(
    cipherclerk: &AppCipherclerk,
    mandate_cell: CellId,
    key_prefix: &str,
    new_volume_spent: u64,
) -> Action {
    build_storage_op_action(
        cipherclerk,
        mandate_cell,
        key_prefix,
        StorageOp::List,
        new_volume_spent,
        field_from_u64(0),
    )
}

/// Build an initialization action pinning anchor, ceiling, prefix, and read compartment.
pub fn build_init_gateway_action(
    cipherclerk: &AppCipherclerk,
    mandate_cell: CellId,
    commitment_anchor: u64,
    volume_ceiling: u64,
    key_prefix: &str,
    read_compartment: &str,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: mandate_cell,
            index: COMMITMENT_ANCHOR_SLOT as usize,
            value: field_from_u64(commitment_anchor),
        },
        Effect::SetField {
            cell: mandate_cell,
            index: VOLUME_CEILING_SLOT as usize,
            value: field_from_u64(volume_ceiling),
        },
        Effect::SetField {
            cell: mandate_cell,
            index: KEY_PREFIX_HASH_SLOT as usize,
            value: key_prefix_field(key_prefix),
        },
        Effect::SetField {
            cell: mandate_cell,
            index: READ_COMPARTMENT_SLOT as usize,
            value: field_from_bytes(read_compartment.as_bytes()),
        },
        Effect::EmitEvent {
            cell: mandate_cell,
            event: Event::new(
                symbol("storage-gateway-initialized"),
                vec![
                    field_from_u64(commitment_anchor),
                    field_from_u64(volume_ceiling),
                    key_prefix_field(key_prefix),
                    field_from_bytes(read_compartment.as_bytes()),
                ],
            ),
        },
    ];

    cipherclerk.make_action(mandate_cell, "init_gateway", effects)
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// Register the storage-gateway-mandate starbridge-app on a shared context.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(sgm_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "sgm-gateway".into(),
        descriptor: serde_json::json!({
            "component": "dregg-sgm-gateway",
            "module": "/starbridge-apps/storage-gateway-mandate/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["object_key", "last_op", "volume_spent", "commitment_anchor"],
            "slot_layout": {
                "object_key": OBJECT_KEY_SLOT,
                "last_op": LAST_OP_SLOT,
                "volume_spent": VOLUME_SPENT_SLOT,
                "commitment_anchor": COMMITMENT_ANCHOR_SLOT,
                "volume_ceiling": VOLUME_CEILING_SLOT,
                "key_prefix_hash": KEY_PREFIX_HASH_SLOT,
                "read_compartment": READ_COMPARTMENT_SLOT,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&sgm_child_program_vk()),
            "storage_ops": ["GET", "PUT", "LIST"],
        }),
    });

    ctx.register_inspector_with("sgm-storage-form", || {
        serde_json::json!({
            "component": "dregg-sgm-storage-form",
            "module": "/starbridge-apps/storage-gateway-mandate/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "builders_module": "/starbridge-apps/storage-gateway-mandate/turn-builders.js",
            "methods": [
                "storage_get",
                "storage_put",
                "storage_list",
                "init_gateway"
            ],
        })
    });

    factory_vk
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, Authorization, EmbeddedExecutor};

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    fn test_cell() -> CellId {
        CellId::from_bytes([9u8; 32])
    }

    const ALLOWED: [StorageOp; 3] = [StorageOp::Put, StorageOp::Get, StorageOp::List];

    #[test]
    fn factory_descriptor_is_stable() {
        let h1 = sgm_factory_descriptor().hash();
        let h2 = sgm_factory_descriptor().hash();
        assert_eq!(h1, h2);
    }

    #[test]
    fn storage_op_round_trip_encoding() {
        assert_eq!(StorageOp::from_field_value(0), Some(StorageOp::Get));
        assert_eq!(StorageOp::from_field_value(1), Some(StorageOp::Put));
        assert_eq!(StorageOp::from_field_value(2), Some(StorageOp::List));
        assert_eq!(StorageOp::Get.to_field_value(), 0);
    }

    #[test]
    fn sgm_admit_matches_lean_demo_guards() {
        let writer = field_from_bytes(b"writer");
        let read_comp = field_from_bytes(DEFAULT_READ_COMPARTMENT.as_bytes());
        let labels = [writer];

        // PUT under prefix succeeds.
        assert_eq!(
            sgm_admit(
                0,
                DEFAULT_VOLUME_CEILING,
                "uploads/doc.txt",
                DEFAULT_KEY_PREFIX,
                StorageOp::Put,
                &ALLOWED,
                &labels,
                read_comp,
            ),
            Some(5)
        );

        // PUT outside prefix rejected.
        assert_eq!(
            sgm_admit(
                0,
                DEFAULT_VOLUME_CEILING,
                "secret/doc.txt",
                DEFAULT_KEY_PREFIX,
                StorageOp::Put,
                &ALLOWED,
                &labels,
                read_comp,
            ),
            None
        );

        // GET without read clearance rejected.
        let guest = field_from_bytes(b"guest");
        assert_eq!(
            sgm_admit(
                0,
                DEFAULT_VOLUME_CEILING,
                "uploads/doc.txt",
                DEFAULT_KEY_PREFIX,
                StorageOp::Get,
                &ALLOWED,
                &[guest],
                read_comp,
            ),
            None
        );

        // Over-debit rejected (three PUTs at cost 5 exhaust ceiling 10).
        assert_eq!(
            sgm_admit(
                10,
                DEFAULT_VOLUME_CEILING,
                "uploads/a.txt",
                DEFAULT_KEY_PREFIX,
                StorageOp::Put,
                &ALLOWED,
                &labels,
                read_comp,
            ),
            None
        );
    }

    #[test]
    fn storage_op_action_writes_slots_and_emits_event() {
        let cipherclerk = test_cipherclerk();
        let blob = field_from_u64(0xdeadbeef);
        let action = build_storage_put_action(&cipherclerk, test_cell(), "uploads/x.txt", 5, blob);
        assert_eq!(action.effects.len(), 4);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, .. } if *index == OBJECT_KEY_SLOT as usize
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, .. } if *index == LAST_OP_SLOT as usize
        ));
        assert!(matches!(
            &action.effects[2],
            Effect::SetField { index, .. } if *index == VOLUME_SPENT_SLOT as usize
        ));
        assert!(matches!(&action.effects[3], Effect::EmitEvent { .. }));
    }

    #[test]
    fn storage_action_carries_real_signature() {
        let cipherclerk = test_cipherclerk();
        let action = build_storage_get_action(&cipherclerk, test_cell(), "uploads/y.txt", 1);
        match action.authorization {
            Authorization::Signature(a, b) => {
                assert!(a != [0u8; 32] || b != [0u8; 32]);
            }
            other => panic!("expected Signature, got {other:?}"),
        }
    }

    #[test]
    fn register_installs_factory_and_inspectors() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, SGM_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(ctx.inspector_registry().get("sgm-gateway").is_some());
        assert!(ctx.inspector_registry().get("sgm-storage-form").is_some());
    }
}