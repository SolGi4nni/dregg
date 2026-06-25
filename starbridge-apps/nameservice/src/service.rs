//! # nameservice — a SERVICE CELL on the `invoke()` front door.
//!
//! This is the second worked citizen of CELLS-AS-SERVICE-OBJECTS (after the
//! `starbridge-kvstore` exemplar): a name registry that publishes a first-class,
//! typed [`InterfaceDescriptor`] and whose methods are driven through the
//! [`dregg_app_framework::invoke`] front door — the userspace method-dispatch
//! layer that lives *slightly above* the effect-VM and desugars a method call to
//! the ordinary verified effects it names. There is **no `Effect::Invoke`**, no
//! kernel change, no new circuit rung: the kernel and the light client keep
//! seeing only the `SetField` effects they already enforce and witness. The one
//! extra fact — that an invoked method is a member of the cell's interface — is
//! decided by the SAME verified DFA router ([`InterfaceDescriptor::route_method`])
//! the protocol already uses.
//!
//! It re-expresses the nameservice's core — register / release / resolve — on the
//! invoke() front door and the per-cell umem-heap. The crate's
//! [`FactoryDescriptor`](crate::name_factory_descriptor) federation surface (rent,
//! ownership, sturdyrefs, the web-of-cells re-expression) is unchanged and
//! remains the path for per-name sovereign cells; THIS module is the
//! service-object face of the same registry primitive.
//!
//! ## What the registry is
//!
//! A single cell whose state slots ARE its per-cell umem-heap: slot
//! [`VERSION_SLOT`] is a monotone registry version, and slots
//! [`NAME_SLOT_MIN`]`..=`[`NAME_SLOT_MAX`] are the name-addressed mapping
//! registers. A `name` is hashed to its heap address ([`name_slot`]); the value
//! stored there is the [`CellId`] the name points at. The map is therefore
//! inspectable in the Service Explorer exactly as any cell's committed state is —
//! a `name → cell` binding is a committed field a light client can replay.
//!
//! ## The published interface (three typed methods)
//!
//! | method     | semantics                | auth        | args                  | desugars to |
//! |------------|--------------------------|-------------|-----------------------|-------------|
//! | `register` | [`Semantics::Replayable`]| `Signature` | `(name, target_cell)` | bump version + `SetField(name_slot, target)` |
//! | `release`  | [`Semantics::Replayable`]| `Signature` | `(name)`              | bump version + `SetField(name_slot, 0)`      |
//! | `resolve`  | [`Semantics::Serviced`]  | `None`      | `(name)`              | — (the named OFE seam: a pure read, no turn)  |
//!
//! `register`/`release` are **replayable**: they desugar (via `invoke()`) to a
//! verified turn whose post-state the executor checks against the registry's
//! [`CellProgram`]. `resolve` is **serviced**: its answer rides the OFE
//! cross-cell-read (`crossCellRead_refines_observedField`), not a replay — so
//! `invoke()` refuses to desugar it, naming the seam honestly rather than faking
//! a write. The committed `name → cell` field IS the resolved answer.
//!
//! ## The verified guarantee (the program bites)
//!
//! The registry's [`CellProgram`] scopes [`StateConstraint::Monotonic`] on
//! [`VERSION_SLOT`] to the `register`/`release` cases. The version therefore never
//! rolls back: a replayed or reordered mutation that would lower the registry
//! version is an EXECUTOR REFUSAL on the verified commit path — not a userspace
//! check. The cap-gate (`Signature` on the mutators) is enforced twice over: at
//! the `invoke()` front door (an unauthorized caller is refused before any turn is
//! built) and again by the executor (the desugared turn carries a real signature
//! the kernel verifies).
//!
//! ## A note on the heap width
//!
//! The umem-heap here is the cell's 16 state slots, so this exemplar holds a small
//! fixed register file of bindings and [`name_slot`] is a hash into it (distinct
//! names can collide on a 15-slot heap — pick the wider sparse-heap addressing for
//! a production registry). The point proven is the SHAPE: a `name → cell` map that
//! lives on the per-cell heap, mutated through invoke()-desugared verified turns,
//! version-bumped and rollback-proof.

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
// State schema (the name-registry heap layout)
// =============================================================================

/// State field slot carrying the **monotone registry version** — bumped on every
/// `register`/`release`. Scoped [`StateConstraint::Monotonic`] in
/// [`registry_program`], so the registry version can never roll back (a
/// replay/reorder attack is an executor refusal). Slot indices are `0..16` (per
/// `dregg_cell::STATE_SLOTS`).
pub const VERSION_SLOT: usize = 0;

/// The lowest heap slot a `name → cell` binding may occupy.
pub const NAME_SLOT_MIN: usize = 1;

/// The highest heap slot a `name → cell` binding may occupy. Slots
/// `NAME_SLOT_MIN..=NAME_SLOT_MAX` are the name-addressed mapping registers.
pub const NAME_SLOT_MAX: usize = 15;

/// The `register` method name (a [`Semantics::Replayable`], `Signature`-gated
/// mutator that binds `name → target_cell`).
pub const METHOD_REGISTER: &str = "register";
/// The `release` method name (a [`Semantics::Replayable`], `Signature`-gated
/// mutator that clears a `name` binding).
pub const METHOD_RELEASE: &str = "release";
/// The `resolve` method name (a [`Semantics::Serviced`] read — the named OFE
/// seam: look up the [`CellId`] a `name` is bound to).
pub const METHOD_RESOLVE: &str = "resolve";

/// The **heap address** a `name` occupies — a hash of the name into the
/// `NAME_SLOT_MIN..=NAME_SLOT_MAX` register range.
///
/// Deterministic and replay-stable (BLAKE3 of the name, reduced mod the heap
/// width), so `register`, `resolve` and `release` of the same name always touch
/// the same slot. On a 15-slot heap distinct names CAN collide; a production
/// registry widens the heap (sparse umem addressing) — see the module note.
pub fn name_slot(name: &str) -> usize {
    let h = method_symbol(name);
    let n = u64::from_be_bytes(h[0..8].try_into().expect("8-byte prefix"));
    let width = (NAME_SLOT_MAX - NAME_SLOT_MIN + 1) as u64;
    NAME_SLOT_MIN + (n % width) as usize
}

/// The field-element encoding of a `name` — the first argument every method
/// carries (so the route/args schema is stable across register/resolve/release).
pub fn name_felt(name: &str) -> FieldElement {
    method_symbol(name)
}

/// The field-element encoding of a target [`CellId`] — the registry stores the
/// raw cell-id bytes as the binding's value, so [`resolve`](NameService::resolve)
/// reads them back byte-for-byte.
pub fn target_felt(target: CellId) -> FieldElement {
    target.0
}

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The registry's first-class typed interface** — the three methods it
/// publishes, with their auth and replayable-vs-serviced semantics.
///
/// This is the richer-than-derived descriptor: `derive_replayable` would make
/// every method `Replayable`/`None`, but the registry wants `register`/`release`
/// `Signature`-gated and `resolve` marked `Serviced`. An app registers THIS in a
/// [`InterfaceRegistry`] so the Service Explorer resolves the real auth + seam
/// shape, not the permissive derived default.
pub fn interface_descriptor() -> InterfaceDescriptor {
    InterfaceDescriptor::new(vec![
        // register(name, target_cell): a Signature-gated binding write.
        MethodSig {
            args_schema: ArgsSchema::Fixed(2),
            auth_required: AuthRequired::Signature,
            ..MethodSig::replayable(method_symbol(METHOD_REGISTER))
        },
        // release(name): a Signature-gated binding clear.
        MethodSig {
            args_schema: ArgsSchema::Fixed(1),
            auth_required: AuthRequired::Signature,
            ..MethodSig::replayable(method_symbol(METHOD_RELEASE))
        },
        // resolve(name): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(1),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_RESOLVE))
        },
    ])
}

/// **The registry cell's [`CellProgram`]** — the method-dispatch + the verified
/// invariant.
///
/// A [`CellProgram::Cases`] whose `MethodIs` guards make the derived interface
/// expose `register`/`release`/`resolve`, and whose `register`/`release` cases
/// carry [`StateConstraint::Monotonic`] on [`VERSION_SLOT`] (the rollback-proof
/// invariant). An `Always` catch-all admits the agent's own bookkeeping turns
/// (nonce bumps) so a non-method turn is not default-denied.
pub fn registry_program() -> CellProgram {
    let bump_version = vec![StateConstraint::Monotonic {
        index: VERSION_SLOT as u8,
    }];
    CellProgram::Cases(vec![
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: method_symbol(METHOD_REGISTER),
            },
            constraints: bump_version.clone(),
        },
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: method_symbol(METHOD_RELEASE),
            },
            constraints: bump_version,
        },
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: method_symbol(METHOD_RESOLVE),
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

/// Register the registry's [`interface_descriptor`] for `registry` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults
/// before falling back to derive-from-program. After this, the explorer resolves
/// the registry's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed name registry** — bundles the registry cell with its
/// published interface, and builds method invocations through the `invoke()`
/// front door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it
/// through an executor ([`dregg_app_framework::EmbeddedExecutor::submit_turn`], a
/// node `/turns/submit`, …) to actually commit. A refusal at the front door
/// (unknown method, insufficient authority, a serviced seam) is surfaced as an
/// [`InvokeRefused`] before any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct NameService {
    /// The registry cell this handle drives.
    pub cell: CellId,
    /// The registry's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl NameService {
    /// A handle to the registry cell `cell`, carrying the registry's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        NameService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `register(name, target_cell)`** — bind `name` to `target` on the
    /// registry heap and bump the registry version to `new_version`.
    ///
    /// Routes through the verified DFA, cap-gates on `Signature` (`authority` must
    /// hold it), and desugars to `[SetField(VERSION, new_version),
    /// SetField(name_slot(name), target)]` targeting the `register` method symbol.
    /// `new_version` must be `>=` the registry's current version or the executor's
    /// [`StateConstraint::Monotonic`] refuses the committed turn.
    pub fn register(
        &self,
        cipherclerk: &AppCipherclerk,
        name: &str,
        target: CellId,
        new_version: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, NameError> {
        if name.is_empty() {
            return Err(NameError::EmptyName);
        }
        let effects = vec![
            Effect::SetField {
                cell: self.cell,
                index: VERSION_SLOT,
                value: field_from_u64(new_version),
            },
            Effect::SetField {
                cell: self.cell,
                index: name_slot(name),
                value: target_felt(target),
            },
        ];
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            METHOD_REGISTER,
            vec![name_felt(name), target_felt(target)],
            effects,
            authority,
        )
        .map_err(NameError::Refused)
    }

    /// **Invoke `release(name)`** — clear the `name` binding (set its heap slot to
    /// zero) and bump the registry version to `new_version`. Same
    /// routing/auth/desugar shape as [`NameService::register`], with a zero value.
    pub fn release(
        &self,
        cipherclerk: &AppCipherclerk,
        name: &str,
        new_version: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, NameError> {
        if name.is_empty() {
            return Err(NameError::EmptyName);
        }
        let effects = vec![
            Effect::SetField {
                cell: self.cell,
                index: VERSION_SLOT,
                value: field_from_u64(new_version),
            },
            Effect::SetField {
                cell: self.cell,
                index: name_slot(name),
                value: [0u8; 32],
            },
        ];
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            METHOD_RELEASE,
            vec![name_felt(name)],
            effects,
            authority,
        )
        .map_err(NameError::Refused)
    }

    /// **Attempt to invoke `resolve(name)`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `resolve` is a [`Semantics::Serviced`]
    /// read, answered by the OFE cross-cell-read (the committed `name → cell`
    /// field), not a replay desugar. This method exists to make the seam legible
    /// (and testable): a serviced read is not a turn, and `invoke()` will not
    /// pretend otherwise. To actually READ the binding, read the committed state
    /// at [`name_slot`]`(name)`.
    pub fn resolve(&self, cipherclerk: &AppCipherclerk, name: &str) -> Result<Turn, NameError> {
        if name.is_empty() {
            return Err(NameError::EmptyName);
        }
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            METHOD_RESOLVE,
            vec![name_felt(name)],
            vec![],
            InvokeAuthority::None,
        )
        .map_err(NameError::Refused)
    }
}

/// Why a [`NameService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NameError {
    /// The name was empty (a name must address a heap slot).
    EmptyName,
    /// The `invoke()` front door refused (unknown method, insufficient authority,
    /// or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for NameError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NameError::EmptyName => write!(f, "a name must be non-empty"),
            NameError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for NameError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    #[test]
    fn interface_publishes_three_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 3);
        assert!(iface.verify_id());

        let reg = iface.method(&method_symbol(METHOD_REGISTER)).unwrap();
        assert_eq!(reg.semantics, Semantics::Replayable);
        assert_eq!(reg.auth_required, AuthRequired::Signature);

        let resolve = iface.method(&method_symbol(METHOD_RESOLVE)).unwrap();
        assert_eq!(resolve.semantics, Semantics::Serviced);

        let rel = iface.method(&method_symbol(METHOD_RELEASE)).unwrap();
        assert_eq!(rel.auth_required, AuthRequired::Signature);
    }

    #[test]
    fn program_dispatches_on_the_published_methods() {
        let iface = InterfaceDescriptor::derive_replayable(&registry_program());
        for m in [METHOD_REGISTER, METHOD_RELEASE, METHOD_RESOLVE] {
            assert!(iface.method(&method_symbol(m)).is_some(), "{m} dispatched");
        }
    }

    #[test]
    fn name_slot_is_in_range_and_stable() {
        for name in ["alice", "bob", "deos://root", "a-very-long-federation-name"] {
            let s = name_slot(name);
            assert!((NAME_SLOT_MIN..=NAME_SLOT_MAX).contains(&s));
            assert_eq!(s, name_slot(name), "name_slot is deterministic");
            assert_ne!(s, VERSION_SLOT, "a binding never collides with the version");
        }
    }

    #[test]
    fn empty_name_rejected_before_any_turn() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = NameService::new(cclerk.cell_id());
        assert!(matches!(
            svc.register(&cclerk, "", cclerk.cell_id(), 1, InvokeAuthority::Signature),
            Err(NameError::EmptyName)
        ));
    }
}
