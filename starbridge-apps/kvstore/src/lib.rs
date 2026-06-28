//! # starbridge-kvstore
//!
//! **A verified key-value register store, exposed as a SERVICE CELL.**
//!
//! This is the worked exemplar of CELLS-AS-SERVICE-OBJECTS: a cell that
//! publishes a first-class, typed [`InterfaceDescriptor`] and whose methods are
//! driven through the [`dregg_app_framework::invoke`] front door — the userspace
//! method-dispatch layer that lives *slightly above* the effect-VM and desugars
//! a method call to the ordinary verified effects it names. There is **no
//! `Effect::Invoke`**, no kernel change, no new circuit rung: the kernel and the
//! light client keep seeing only the `SetField` effects they already enforce and
//! witness. The one extra fact — that an invoked method is a member of the cell's
//! interface — is decided by the SAME verified DFA router
//! ([`InterfaceDescriptor::route_method`]) the protocol already uses.
//!
//! ## What the store is
//!
//! A single cell holding a small **register file** with a live header:
//!
//! | slot                  | meaning                          | tooth            |
//! |-----------------------|----------------------------------|------------------|
//! | [`VERSION_SLOT`]      | monotone store version           | `Monotonic`      |
//! | [`COUNT_SLOT`]        | live entry count (occupied regs) | `FieldLte` ≤ cap |
//! | [`LAST_KEY_SLOT`]     | register index last touched      | —                |
//! | [`LAST_VALUE_SLOT`]   | value last written (`0` on clear)| —                |
//! | [`REG_MIN`]`..=`[`REG_MAX`] | key-addressed value registers | —             |
//!
//! The "key" is the register index ([`REG_MIN`]`..=`[`REG_MAX`], so [`CAPACITY`]
//! entries). The header slots make the store **legible**: the entry count, the
//! last key, and the last value are committed state a card binds and a peer reads.
//! It is a genuinely useful primitive — a verified, rollback-proof config/KV store
//! whose every mutation is a receipted turn a light client can replay.
//!
//! ## The published interface (three typed methods)
//!
//! | method   | semantics                | auth        | args            | desugars to |
//! |----------|--------------------------|-------------|-----------------|-------------|
//! | `put`    | [`Semantics::Replayable`]| `Signature` | `(reg, value)`  | bump version + `SetField(reg, value)` |
//! | `delete` | [`Semantics::Replayable`]| `Signature` | `(reg)`         | bump version + `SetField(reg, 0)`     |
//! | `get`    | [`Semantics::Serviced`]  | `None`      | `(reg)`         | — (the named OFE seam: a pure read, no turn) |
//!
//! `put`/`delete` are **replayable**: they desugar (via `invoke()`) to a verified
//! turn whose post-state the executor checks against the store's [`CellProgram`].
//! `get` is **serviced**: its answer rides the OFE cross-cell-read
//! (`crossCellRead_refines_observedField`), not a replay — so `invoke()` refuses
//! to desugar it, naming the seam honestly rather than faking a write.
//!
//! ## The verified guarantee (the program bites)
//!
//! The store's [`CellProgram`] scopes [`StateConstraint::Monotonic`] on
//! [`VERSION_SLOT`] to the `put`/`delete` method cases. The version therefore
//! never rolls back: a replayed or reordered mutation that would lower the store
//! version is an EXECUTOR REFUSAL on the verified commit path — not a userspace
//! check. The `put` case additionally carries the **capacity tooth**
//! ([`StateConstraint::FieldLte`] bounding [`COUNT_SLOT`] by [`CAPACITY`]) so the
//! committed entry count can never overflow the register file. The cap-gate
//! (`Signature` on the mutators) is enforced twice over: at
//! the `invoke()` front door (an unauthorized caller is refused before any turn
//! is built) and again by the executor (the desugared turn carries a real
//! signature the kernel verifies).
//!
//! ## How an app uses it
//!
//! 1. Install [`store_program`] on the store cell (the methods it dispatches).
//! 2. Register [`interface_descriptor`] in a [`InterfaceRegistry`] so the
//!    Service Explorer (and any peer) resolves the cell's typed interface.
//! 3. Build invocations with [`KvStore::put`] / [`KvStore::delete`] (which call
//!    `invoke_with_descriptor` under the hood) and submit the returned [`Turn`]
//!    through an executor ([`dregg_app_framework::EmbeddedExecutor::submit_turn`]).
//!
//! ## The four modern app-framework axes
//!
//! This crate demonstrates the unified starbridge-app template. The SAME
//! [`store_program`] backs every axis:
//!   - **AX1 — verified core**: [`store_program`] + `Monotonic(VERSION_SLOT)` +
//!     the [`COUNT_SLOT`] capacity tooth (this file) — the invariants the executor
//!     enforces.
//!   - **AX2 — deos surface**: [`deos::kvstore_app`] / [`deos::register_deos`]
//!     (`src/deos.rs`) — the store composed as a `DeosApp`.
//!   - **AX3 — service cell**: [`KvStore`] / `invoke()` (this file) — the typed
//!     [`InterfaceDescriptor`] driven through the front door.
//!   - **AX4 — deos-view card**: [`card::kvstore_card_value`] (`src/card.rs`) — the
//!     UI as a renderer-independent `deos.ui.*` view-tree.

/// AX4 — the deos-view CARD: the app's UI as a renderer-independent `deos.ui.*`
/// view-tree (pure `serde_json`, no `deos-view` dependency).
pub mod card;
/// AX2 — the deos-native surface: the store composed as a [`DeosApp`]
/// ([`deos::kvstore_app`], [`deos::register_deos`], the [`deos::fire_put`] /
/// [`deos::fire_delete`] fires).
pub mod deos;

use dregg_app_framework::{
    AppCipherclerk, Effect, FieldElement, InterfaceRegistry, InvokeAuthority, InvokeRefused,
    field_from_u64, invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::program::{CellProgram, StateConstraint, TransitionCase, TransitionGuard};
use dregg_turn::Turn;
use dregg_types::CellId;

// =============================================================================
// State schema (the register-file slot layout)
// =============================================================================

/// State field slot carrying the **monotone store version** — bumped on every
/// `put`/`delete`. Scoped [`StateConstraint::Monotonic`] in [`store_program`], so
/// the store version can never roll back (a replay/reorder attack is an executor
/// refusal). Slot indices are `0..16` (per `dregg_cell::STATE_SLOTS`).
pub const VERSION_SLOT: usize = 0;

/// State field slot carrying the **live entry count** — the number of occupied
/// value registers. A `put` to a fresh key raises it, a `delete` of a present key
/// lowers it; an overwrite leaves it unchanged. Scoped [`StateConstraint::FieldLte`]
/// ≤ [`CAPACITY`] in [`store_program`] (the capacity tooth: the store can never
/// commit a count claiming more entries than it has registers). Driven by the
/// live-state fire path ([`deos::fire_put`] / [`deos::fire_delete`]).
pub const COUNT_SLOT: usize = 1;

/// State field slot carrying the **register index last touched** by a `put`/
/// `delete` — a header signal a card binds so the surface names the last key.
pub const LAST_KEY_SLOT: usize = 2;

/// State field slot carrying the **value last written** — the value of the last
/// `put` (or `0` after a `delete`). A header signal a card binds.
pub const LAST_VALUE_SLOT: usize = 3;

/// The lowest register index a `put`/`delete`/`get` may address. Registers
/// `REG_MIN..=REG_MAX` are the key-addressed value slots (the header slots
/// `0..REG_MIN` are the store's own, not keys).
pub const REG_MIN: usize = 4;

/// The highest register index a `put`/`delete`/`get` may address. Registers
/// `REG_MIN..=REG_MAX` are the key-addressed value slots.
pub const REG_MAX: usize = 15;

/// The number of key-addressed value registers (`REG_MIN..=REG_MAX`) — the store
/// capacity, the ceiling the [`COUNT_SLOT`] capacity tooth bounds.
pub const CAPACITY: usize = REG_MAX - REG_MIN + 1;

/// The `put` method name (a [`Semantics::Replayable`], `Signature`-gated mutator).
pub const METHOD_PUT: &str = "put";
/// The `get` method name (a [`Semantics::Serviced`] read — the named OFE seam).
pub const METHOD_GET: &str = "get";
/// The `delete` method name (a [`Semantics::Replayable`], `Signature`-gated mutator).
pub const METHOD_DELETE: &str = "delete";

/// Is `reg` a valid, writable register index (`REG_MIN..=REG_MAX`)? A `put`/
/// `delete` against `VERSION_SLOT` or an out-of-range slot is rejected here
/// before any turn is built (the version slot is the program's, not a key).
pub fn is_valid_register(reg: usize) -> bool {
    (REG_MIN..=REG_MAX).contains(&reg)
}

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The store's first-class typed interface** — the three methods it publishes,
/// with their auth and replayable-vs-serviced semantics.
///
/// This is the richer-than-derived descriptor: `derive_replayable` would make
/// every method `Replayable`/`None`, but the store wants `put`/`delete`
/// `Signature`-gated and `get` marked `Serviced`. An app registers THIS in a
/// [`InterfaceRegistry`] so the Service Explorer resolves the real auth + seam
/// shape, not the permissive derived default.
pub fn interface_descriptor() -> InterfaceDescriptor {
    InterfaceDescriptor::new(vec![
        // put(reg, value): a Signature-gated write.
        MethodSig {
            args_schema: ArgsSchema::Fixed(2),
            auth_required: AuthRequired::Signature,
            ..MethodSig::replayable(method_symbol(METHOD_PUT))
        },
        // delete(reg): a Signature-gated clear.
        MethodSig {
            args_schema: ArgsSchema::Fixed(1),
            auth_required: AuthRequired::Signature,
            ..MethodSig::replayable(method_symbol(METHOD_DELETE))
        },
        // get(reg): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(1),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_GET))
        },
    ])
}

/// **The store cell's [`CellProgram`]** — the method-dispatch + the verified
/// invariant.
///
/// A [`CellProgram::Cases`] whose `MethodIs` guards make the derived interface
/// expose `put`/`delete`/`get`, and whose `put`/`delete` cases carry
/// [`StateConstraint::Monotonic`] on [`VERSION_SLOT`] (the rollback-proof
/// invariant). The `put` case additionally carries the **capacity tooth** —
/// [`StateConstraint::FieldLte`] bounding [`COUNT_SLOT`] by [`CAPACITY`] — so the
/// committed entry count can never claim more entries than the store has registers
/// (an executor refusal, not a userspace check). An `Always` catch-all admits the
/// agent's own bookkeeping turns (nonce bumps) so a non-method turn is not
/// default-denied.
pub fn store_program() -> CellProgram {
    let bump_version = StateConstraint::Monotonic {
        index: VERSION_SLOT as u8,
    };
    // The capacity tooth: a committed entry count never exceeds the register
    // capacity. Big-endian field compare (`COUNT <= CAPACITY`).
    let count_within_capacity = StateConstraint::FieldLte {
        index: COUNT_SLOT as u8,
        value: field_from_u64(CAPACITY as u64),
    };
    CellProgram::Cases(vec![
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: method_symbol(METHOD_PUT),
            },
            constraints: vec![bump_version.clone(), count_within_capacity],
        },
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: method_symbol(METHOD_DELETE),
            },
            constraints: vec![bump_version],
        },
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: method_symbol(METHOD_GET),
            },
            constraints: vec![],
        },
        // Catch-all: the agent's own non-method turns (nonce bookkeeping) are not
        // dispatch-bound and must not be default-denied.
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![],
        },
    ])
}

/// Register the store's [`interface_descriptor`] for `store` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults
/// before falling back to derive-from-program. After this, the explorer
/// resolves the store's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, store: CellId) {
    registry.register(store, interface_descriptor());
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed key-value store** — bundles the store cell with its
/// published interface, and builds method invocations through the `invoke()`
/// front door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it
/// through an executor ([`dregg_app_framework::EmbeddedExecutor::submit_turn`],
/// a node `/turns/submit`, …) to actually commit. A refusal at the front door
/// (unknown method, insufficient authority, a serviced seam) is surfaced as an
/// [`InvokeRefused`] before any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct KvStore {
    /// The store cell this handle drives.
    pub cell: CellId,
    /// The store's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl KvStore {
    /// A handle to the store cell `cell`, carrying the store's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        KvStore {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `put(reg, value)`** — write `value` into register `reg` and bump
    /// the store version to `new_version`.
    ///
    /// Routes through the verified DFA, cap-gates on `Signature` (`authority`
    /// must hold it), and desugars to `[SetField(VERSION, new_version),
    /// SetField(reg, value)]` targeting the `put` method symbol. `new_version`
    /// must be `>=` the store's current version or the executor's
    /// [`StateConstraint::Monotonic`] refuses the committed turn.
    pub fn put(
        &self,
        cipherclerk: &AppCipherclerk,
        reg: usize,
        value: FieldElement,
        new_version: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, KvError> {
        if !is_valid_register(reg) {
            return Err(KvError::InvalidRegister(reg));
        }
        let effects = vec![
            Effect::SetField {
                cell: self.cell,
                index: VERSION_SLOT,
                value: field_from_u64(new_version),
            },
            // The header signals: the last key touched + the value written.
            Effect::SetField {
                cell: self.cell,
                index: LAST_KEY_SLOT,
                value: field_from_u64(reg as u64),
            },
            Effect::SetField {
                cell: self.cell,
                index: LAST_VALUE_SLOT,
                value,
            },
            Effect::SetField {
                cell: self.cell,
                index: reg,
                value,
            },
        ];
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            METHOD_PUT,
            vec![field_from_u64(reg as u64), value],
            effects,
            authority,
        )
        .map_err(KvError::Refused)
    }

    /// **Invoke `delete(reg)`** — clear register `reg` (set it to zero) and bump
    /// the store version to `new_version`. Same routing/auth/desugar shape as
    /// [`KvStore::put`], with a zero value.
    pub fn delete(
        &self,
        cipherclerk: &AppCipherclerk,
        reg: usize,
        new_version: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, KvError> {
        if !is_valid_register(reg) {
            return Err(KvError::InvalidRegister(reg));
        }
        let effects = vec![
            Effect::SetField {
                cell: self.cell,
                index: VERSION_SLOT,
                value: field_from_u64(new_version),
            },
            // The header signals: the last key touched + a cleared value.
            Effect::SetField {
                cell: self.cell,
                index: LAST_KEY_SLOT,
                value: field_from_u64(reg as u64),
            },
            Effect::SetField {
                cell: self.cell,
                index: LAST_VALUE_SLOT,
                value: [0u8; 32],
            },
            Effect::SetField {
                cell: self.cell,
                index: reg,
                value: [0u8; 32],
            },
        ];
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            METHOD_DELETE,
            vec![field_from_u64(reg as u64)],
            effects,
            authority,
        )
        .map_err(KvError::Refused)
    }

    /// **Attempt to invoke `get(reg)`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `get` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read, not a replay desugar. This method
    /// exists to make the seam legible (and testable): a serviced read is not a
    /// turn, and `invoke()` will not pretend otherwise.
    pub fn get(&self, cipherclerk: &AppCipherclerk, reg: usize) -> Result<Turn, KvError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            METHOD_GET,
            vec![field_from_u64(reg as u64)],
            vec![],
            InvokeAuthority::None,
        )
        .map_err(KvError::Refused)
    }
}

/// Why a [`KvStore`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KvError {
    /// The register index is not in `REG_MIN..=REG_MAX` (the version slot and
    /// out-of-range slots are not keys).
    InvalidRegister(usize),
    /// The `invoke()` front door refused (unknown method, insufficient
    /// authority, or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for KvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            KvError::InvalidRegister(reg) => write!(
                f,
                "register {reg} is not a valid key (expected {REG_MIN}..={REG_MAX})"
            ),
            KvError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for KvError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interface_publishes_three_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 3);
        assert!(iface.verify_id());

        let put = iface.method(&method_symbol(METHOD_PUT)).unwrap();
        assert_eq!(put.semantics, Semantics::Replayable);
        assert_eq!(put.auth_required, AuthRequired::Signature);

        let get = iface.method(&method_symbol(METHOD_GET)).unwrap();
        assert_eq!(get.semantics, Semantics::Serviced);

        let del = iface.method(&method_symbol(METHOD_DELETE)).unwrap();
        assert_eq!(del.auth_required, AuthRequired::Signature);
    }

    #[test]
    fn program_dispatches_on_the_published_methods() {
        let iface = InterfaceDescriptor::derive_replayable(&store_program());
        // The derived interface (from the program's MethodIs guards) names the
        // same three methods the published descriptor declares.
        for m in [METHOD_PUT, METHOD_GET, METHOD_DELETE] {
            assert!(iface.method(&method_symbol(m)).is_some(), "{m} dispatched");
        }
    }

    #[test]
    fn invalid_register_rejected_before_any_turn() {
        let cclerk = AppCipherclerk::new(dregg_app_framework::AgentCipherclerk::new(), [0x11; 32]);
        let store = KvStore::new(cclerk.cell_id());
        // The version slot is not a key.
        assert!(matches!(
            store.put(
                &cclerk,
                VERSION_SLOT,
                [1u8; 32],
                1,
                InvokeAuthority::Signature
            ),
            Err(KvError::InvalidRegister(VERSION_SLOT))
        ));
        // Out of range.
        assert!(matches!(
            store.put(&cclerk, 99, [1u8; 32], 1, InvokeAuthority::Signature),
            Err(KvError::InvalidRegister(99))
        ));
    }
}
