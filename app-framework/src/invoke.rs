//! **`invoke()` — cells-as-service-objects method dispatch at the USERSPACE layer.**
//!
//! A cell already does method-dispatch: an [`Action`] carries a `method:
//! Symbol` + `args`, and a [`dregg_cell::CellProgram::Cases`] program scopes a
//! transition to a method via [`dregg_cell::TransitionGuard::MethodIs`]. The
//! [`dregg_cell::InterfaceDescriptor`] gives that interface a first-class,
//! content-addressed TYPE (a set of [`dregg_cell::MethodSig`]s rooted at an
//! `interface_id`).
//!
//! This module is the **`invoke()` front door**, and the load-bearing design
//! decision is twofold:
//!
//! 1. It lives *slightly higher than the effect-VM primitive*, NOT as a kernel
//!    [`Effect`]. There is no `Effect::Invoke`. Method-matching is a USERSPACE
//!    routing concern; the kernel and the circuit keep seeing only the effects
//!    they already know.
//! 2. The interface *instance* is a USERSPACE object — it is NOT a committed
//!    field of the cell. The descriptor is resolved at this layer, either
//!    DERIVED on the fly from the cell's `CellProgram::Cases`
//!    ([`dregg_cell::InterfaceDescriptor::derive_replayable`], which reads only
//!    the program — no committed `interface_id`, no commitment dependency), or
//!    looked up from a userspace [`InterfaceRegistry`] that an app maintains for
//!    richer per-method auth/semantics than the program alone expresses.
//!
//! # What `invoke()` does (and does not)
//!
//! [`invoke`] resolves a method against a cell's interface (derived-from-program
//! or registry-supplied), cap-gates on the method's declared `auth_required`,
//! and then DESUGARS to an ordinary [`Action`] carrying the underlying existing
//! effects the method names — fired through the normal executor path. Concretely:
//!
//! 1. **Resolve the descriptor in userspace.** Either derive it from the cell's
//!    `CellProgram` (the methods the cell ACTUALLY dispatches on, all
//!    `Replayable`) or take an explicit descriptor an app registered. No
//!    commitment, no `Cell::interfaces` field.
//! 2. **Route the method.** The method name is hashed to its `Symbol` and routed
//!    through the descriptor's VERIFIED DFA router
//!    ([`dregg_cell::InterfaceDescriptor::route_method`] — the same
//!    `dregg_dfa::Router::classify` a federation constitution audits, not an
//!    ad-hoc `find`). An unknown method does not route → refused, fail-closed.
//! 3. **Gate on the method's semantics.** A [`dregg_cell::Semantics::Replayable`]
//!    method desugars to its underlying effects (this function's job). A
//!    [`dregg_cell::Semantics::Serviced`] method is a NAMED SEAM — its answer
//!    rides the OFE cross-cell-read (`crossCellRead_refines_observedField`), not
//!    a pure replay; `invoke` refuses to desugar it and points at that seam.
//! 4. **Cap-gate on `auth_required`.** The caller declares the authority it holds
//!    ([`InvokeAuthority`]); it must satisfy the method's
//!    [`dregg_cell::AuthRequired`]. An insufficient holder is refused before any
//!    effect is built.
//! 5. **Desugar to an `Action` + fire.** The underlying existing effects (the
//!    ones the method names — `SetField`, `Transfer`, … — supplied by the caller)
//!    are wrapped in an [`Action`] targeting the method symbol, signed by the
//!    framework cipherclerk, wrapped in a [`Turn`], and submitted through the
//!    normal executor. The receipt is the ordinary turn receipt.
//!
//! The `Effect` enum is UNCHANGED: no new variant, no non-exhaustive match, the
//! desktop link stays clean. `invoke()` is sugar that resolves to effects the
//! kernel already enforces and the circuit already witnesses; the cell-commitment
//! is untouched because the interface lives entirely in userspace.

use std::collections::HashMap;

use dregg_cell::Cell;
use dregg_cell::interface::{InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_turn::Turn;
use dregg_turn::action::{Action, Effect};
use dregg_types::CellId;

use crate::cipherclerk::AppCipherclerk;

/// The authority a caller presents when invoking a method.
///
/// `invoke()` checks this against the method's declared
/// [`dregg_cell::AuthRequired`] BEFORE building any effect — the cap-gate.
/// This is the *userspace declaration* of what the caller can satisfy; the
/// actual cryptographic check (a real signature/proof binding the action hash)
/// is performed downstream by the executor when the desugared turn runs. The
/// gate here is the early, legible refusal: an `auth_required: Signature` method
/// invoked by a caller holding only [`InvokeAuthority::None`] is rejected at the
/// front door rather than producing a turn the executor would later reject.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InvokeAuthority {
    /// The caller holds no special authority (only methods declaring
    /// [`AuthRequired::None`] may be invoked).
    None,
    /// The caller can produce a valid signature from the cell's key.
    Signature,
    /// The caller can produce a valid ZK proof against the cell's key.
    Proof,
    /// The caller holds a custom authority identified by its `vk_hash` (must
    /// match the method's `AuthRequired::Custom { vk_hash }`).
    Custom { vk_hash: [u8; 32] },
}

impl InvokeAuthority {
    /// Does this caller authority satisfy a method's declared `auth_required`?
    ///
    /// Mirrors the executor's auth-tier semantics:
    /// - [`AuthRequired::None`] — satisfied by anything.
    /// - [`AuthRequired::Signature`] — needs [`InvokeAuthority::Signature`].
    /// - [`AuthRequired::Proof`] — needs [`InvokeAuthority::Proof`].
    /// - [`AuthRequired::Either`] — needs `Signature` OR `Proof`.
    /// - [`AuthRequired::Impossible`] — never satisfied (a permanently locked
    ///   method has no invocation).
    /// - [`AuthRequired::Custom { vk_hash }`] — needs a matching
    ///   [`InvokeAuthority::Custom`].
    ///
    /// Public so the symmetric reactive front-door ([`crate::reactor`]) can
    /// cap-gate a reaction on the SAME authority tiers `invoke()` gates a
    /// command on — one authority-satisfaction predicate for both faces.
    pub fn satisfies(self, required: &AuthRequired) -> bool {
        match required {
            AuthRequired::None => true,
            AuthRequired::Signature => self == InvokeAuthority::Signature,
            AuthRequired::Proof => self == InvokeAuthority::Proof,
            AuthRequired::Either => {
                matches!(self, InvokeAuthority::Signature | InvokeAuthority::Proof)
            }
            AuthRequired::Impossible => false,
            AuthRequired::Custom { vk_hash } => {
                matches!(self, InvokeAuthority::Custom { vk_hash: held } if held == *vk_hash)
            }
        }
    }
}

/// **A userspace registry of cell interfaces.**
///
/// The interface descriptor is NOT a committed field of a cell — it lives in
/// userspace. An app that wants richer per-method auth/semantics than
/// [`InterfaceDescriptor::derive_replayable`] gives (which makes every
/// program-dispatched method `Replayable` with `AuthRequired::None`) registers
/// the explicit descriptor here and resolves through it.
///
/// This is the higher-layer home for "what interface does this cell expose":
/// an app populates it (from a captp handshake, a config file, a deploy-time
/// declaration), and [`invoke`] consults it before falling back to
/// derive-from-program.
#[derive(Clone, Debug, Default)]
pub struct InterfaceRegistry {
    by_cell: HashMap<CellId, InterfaceDescriptor>,
}

impl InterfaceRegistry {
    /// A new empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register the interface a cell exposes (overwriting any prior entry).
    pub fn register(&mut self, cell: CellId, descriptor: InterfaceDescriptor) {
        self.by_cell.insert(cell, descriptor);
    }

    /// The registered descriptor for a cell, if any.
    pub fn get(&self, cell: &CellId) -> Option<&InterfaceDescriptor> {
        self.by_cell.get(cell)
    }

    /// Resolve the descriptor for a cell: the explicitly-registered one if
    /// present, else the interface DERIVED from the cell's program
    /// ([`InterfaceDescriptor::derive_replayable`]). This is the canonical
    /// userspace resolution — always succeeds (a cell with no method-dispatch
    /// derives the empty interface).
    pub fn resolve(&self, cell: &Cell) -> InterfaceDescriptor {
        match self.by_cell.get(&cell.id()) {
            Some(d) => d.clone(),
            None => InterfaceDescriptor::derive_replayable(&cell.program),
        }
    }
}

/// Why an [`invoke`] was refused at the userspace front door (before any turn is
/// fired). Each variant is a fail-closed refusal: no effect is built, nothing is
/// submitted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InvokeRefused {
    /// The method name does not route to any declared method of the resolved
    /// interface (via the verified DFA router). Unknown method, fail-closed.
    UnknownMethod {
        /// The method name that did not route.
        method: String,
    },
    /// The method is declared but its authority requirement is not satisfied by
    /// the caller's presented [`InvokeAuthority`].
    Unauthorized {
        /// The method name.
        method: String,
        /// What the method requires.
        required: AuthRequired,
    },
    /// The method is a [`Semantics::Serviced`] method — its answer rides the OFE
    /// cross-cell-read, NOT a pure-replay effect desugar. `invoke()` does not
    /// fire it; the serviced-answer carrier is the named seam (no kernel effect).
    ServicedSeam {
        /// The method name.
        method: String,
    },
}

impl std::fmt::Display for InvokeRefused {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownMethod { method } => {
                write!(
                    f,
                    "method `{method}` is not a declared method of the interface"
                )
            }
            Self::Unauthorized { method, required } => write!(
                f,
                "method `{method}` requires {required:?}; caller authority is insufficient"
            ),
            Self::ServicedSeam { method } => write!(
                f,
                "method `{method}` is a Serviced method; its answer rides the OFE cross-cell-read \
                 (named seam) — no effect desugar"
            ),
        }
    }
}

impl std::error::Error for InvokeRefused {}

/// **Resolve a method invocation into an [`Action`]** against an EXPLICIT
/// descriptor — the pure routing core, with no cipherclerk and no executor.
///
/// The `descriptor` is the userspace interface for `target` (resolved by the
/// caller, e.g. via [`InterfaceRegistry::resolve`]). There is NO commitment
/// check: the interface is a userspace object, not a committed cell field.
///
/// Performs route-method → gate-semantics → cap-gate-auth and returns the
/// desugared, UNSIGNED [`Action`] carrying the underlying `effects` targeting the
/// resolved method symbol, alongside the matched [`MethodSig`].
///
/// Separated from [`invoke`] so the routing/auth logic is testable without a
/// cipherclerk or a running executor, and so a caller that builds its own turn
/// envelope (multi-action atomic groups, remote submission) can reuse it.
pub fn resolve_against(
    target: CellId,
    descriptor: &InterfaceDescriptor,
    method: &str,
    args: Vec<dregg_cell::state::FieldElement>,
    effects: Vec<Effect>,
    authority: InvokeAuthority,
) -> Result<(Action, MethodSig), InvokeRefused> {
    // (2) Route the method through the VERIFIED DFA router (not an ad-hoc find).
    let symbol = method_symbol(method);
    let sig = descriptor
        .route_method(&symbol)
        .ok_or_else(|| InvokeRefused::UnknownMethod {
            method: method.to_string(),
        })?
        .clone();

    // (3) Serviced methods do not desugar to a replay effect — named seam.
    if sig.semantics == Semantics::Serviced {
        return Err(InvokeRefused::ServicedSeam {
            method: method.to_string(),
        });
    }

    // (4) Cap-gate on the method's declared authority.
    if !authority.satisfies(&sig.auth_required) {
        return Err(InvokeRefused::Unauthorized {
            method: method.to_string(),
            required: sig.auth_required.clone(),
        });
    }

    // (5) Desugar to an ordinary Action targeting the method symbol, carrying the
    //     underlying existing effects. No new Effect variant: the kernel/circuit
    //     see only effects they already know. The action is unsigned here; the
    //     cipherclerk path signs it.
    let action = Action {
        target,
        method: symbol,
        args,
        authorization: dregg_turn::action::Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: dregg_turn::action::DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: Vec::new(),
    };

    Ok((action, sig))
}

/// **Resolve a method invocation against the interface DERIVED from the cell's
/// program** — the no-registry path.
///
/// Resolves the cell's interface in userspace via
/// [`InterfaceDescriptor::derive_replayable`] (reads only `cell.program`, no
/// commitment), then routes/gates/desugars via [`resolve_against`]. Every method
/// a derived interface exposes is `Replayable` with `AuthRequired::None`, so for
/// richer auth use an [`InterfaceRegistry`] + [`resolve_against`].
pub fn resolve_invocation(
    cell: &Cell,
    method: &str,
    args: Vec<dregg_cell::state::FieldElement>,
    effects: Vec<Effect>,
    authority: InvokeAuthority,
) -> Result<(Action, MethodSig), InvokeRefused> {
    let descriptor = InterfaceDescriptor::derive_replayable(&cell.program);
    resolve_against(cell.id(), &descriptor, method, args, effects, authority)
}

/// **`invoke(cell, method, args)` — the userspace front door.**
///
/// Resolves `method` against the cell's interface (derived from its program, OR
/// — via [`invoke_with_descriptor`] — an explicit userspace descriptor), routes
/// it through the verified DFA, gates semantics + auth, then SIGNS the desugared
/// [`Action`] with `cipherclerk` and wraps it in a [`Turn`] ready for the normal
/// executor path. The returned turn carries the underlying existing effects — the
/// kernel and circuit see only effects they already know; there is NO
/// `Effect::Invoke`, and no cell-commitment dependency.
///
/// The caller submits the returned [`Turn`] through their executor
/// ([`crate::DreggEngine::execute_turn`], a node `/turns/submit`, …). `invoke`
/// itself does no I/O — it is the build-the-turn half, mirroring
/// [`AppCipherclerk::make_action`] / [`AppCipherclerk::make_turn`].
pub fn invoke(
    cipherclerk: &AppCipherclerk,
    cell: &Cell,
    method: &str,
    args: Vec<dregg_cell::state::FieldElement>,
    effects: Vec<Effect>,
    authority: InvokeAuthority,
) -> Result<Turn, InvokeRefused> {
    let descriptor = InterfaceDescriptor::derive_replayable(&cell.program);
    invoke_with_descriptor(
        cipherclerk,
        cell.id(),
        &descriptor,
        method,
        args,
        effects,
        authority,
    )
}

/// [`invoke`] against an EXPLICIT userspace descriptor (e.g. from an
/// [`InterfaceRegistry`]) rather than the derived-from-program one — for cells
/// whose interface carries richer per-method auth/semantics than the program
/// alone expresses.
#[allow(clippy::too_many_arguments)]
pub fn invoke_with_descriptor(
    cipherclerk: &AppCipherclerk,
    target: CellId,
    descriptor: &InterfaceDescriptor,
    method: &str,
    args: Vec<dregg_cell::state::FieldElement>,
    effects: Vec<Effect>,
    authority: InvokeAuthority,
) -> Result<Turn, InvokeRefused> {
    let (action, _sig) = resolve_against(target, descriptor, method, args, effects, authority)?;
    let signed = cipherclerk.sign_action(action);
    Ok(cipherclerk.make_turn(signed))
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig};
    use dregg_cell::program::{CellProgram, TransitionCase, TransitionGuard};
    use dregg_types::CellId;

    /// A cell whose `Cases` program dispatches on the given methods (so its
    /// derived interface exposes them, all Replayable).
    fn cell_dispatching(method_names: &[&str]) -> Cell {
        let cases = method_names
            .iter()
            .map(|name| TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: method_symbol(name),
                },
                constraints: vec![],
            })
            .collect();
        let mut cell = Cell::with_balance([7u8; 32], [0u8; 32], 0);
        cell.program = CellProgram::Cases(cases);
        cell
    }

    fn an_effect(cell: CellId) -> Effect {
        Effect::SetField {
            cell,
            index: 0,
            value: [1u8; 32],
        }
    }

    #[test]
    fn invoke_of_replayable_method_desugars_to_underlying_effect() {
        // A method the cell's PROGRAM dispatches on resolves (derived interface),
        // to an Action targeting the method symbol carrying the UNDERLYING effect.
        let cell = cell_dispatching(&["send", "dequeue"]);
        let effects = vec![an_effect(cell.id())];

        let (action, sig) = resolve_invocation(
            &cell,
            "send",
            vec![],
            effects.clone(),
            InvokeAuthority::None,
        )
        .expect("a program-dispatched method must resolve from the derived interface");

        // It desugared to the underlying existing effect — no new Effect variant.
        assert_eq!(action.method, method_symbol("send"));
        assert_eq!(action.target, cell.id());
        assert_eq!(action.effects.len(), 1);
        assert!(matches!(action.effects[0], Effect::SetField { .. }));
        assert_eq!(sig.semantics, Semantics::Replayable);
    }

    #[test]
    fn invoke_refuses_unknown_method() {
        let cell = cell_dispatching(&["send"]);
        let refused = resolve_invocation(
            &cell,
            "undeclared",
            vec![],
            vec![an_effect(cell.id())],
            InvokeAuthority::Signature,
        )
        .unwrap_err();
        assert!(matches!(refused, InvokeRefused::UnknownMethod { .. }));
    }

    #[test]
    fn registry_descriptor_carries_auth_and_serviced_semantics() {
        // The derived interface is all-Replayable/None; a userspace registry
        // supplies richer per-method auth + Serviced semantics.
        let cell = cell_dispatching(&["send", "close", "peek"]);
        let desc = InterfaceDescriptor::new(vec![
            MethodSig::replayable(method_symbol("send")),
            MethodSig {
                args_schema: ArgsSchema::Fixed(1),
                auth_required: AuthRequired::Signature,
                ..MethodSig::replayable(method_symbol("close"))
            },
            MethodSig {
                semantics: Semantics::Serviced,
                ..MethodSig::replayable(method_symbol("peek"))
            },
        ]);
        let mut reg = InterfaceRegistry::new();
        reg.register(cell.id(), desc);
        let resolved = reg.resolve(&cell);

        // `close` requires a Signature: a None caller is refused at the front door.
        let refused = resolve_against(
            cell.id(),
            &resolved,
            "close",
            vec![[0u8; 32]],
            vec![an_effect(cell.id())],
            InvokeAuthority::None,
        )
        .unwrap_err();
        assert!(matches!(
            refused,
            InvokeRefused::Unauthorized {
                required: AuthRequired::Signature,
                ..
            }
        ));

        // A Signature caller satisfies it.
        let (action, _) = resolve_against(
            cell.id(),
            &resolved,
            "close",
            vec![[0u8; 32]],
            vec![an_effect(cell.id())],
            InvokeAuthority::Signature,
        )
        .expect("signature caller satisfies the Signature gate");
        assert_eq!(action.method, method_symbol("close"));

        // `peek` is Serviced: it does not desugar to a replay effect (named seam).
        let seam = resolve_against(
            cell.id(),
            &resolved,
            "peek",
            vec![],
            vec![],
            InvokeAuthority::None,
        )
        .unwrap_err();
        assert!(matches!(seam, InvokeRefused::ServicedSeam { .. }));
    }

    #[test]
    fn registry_falls_back_to_derived_when_unregistered() {
        // An unregistered cell resolves to its derived (program) interface.
        let cell = cell_dispatching(&["send"]);
        let reg = InterfaceRegistry::new();
        let resolved = reg.resolve(&cell);
        assert!(resolved.method(&method_symbol("send")).is_some());
        // And `send` (Replayable, None) invokes cleanly.
        let (action, _) = resolve_against(
            cell.id(),
            &resolved,
            "send",
            vec![],
            vec![an_effect(cell.id())],
            InvokeAuthority::None,
        )
        .expect("derived-fallback send resolves");
        assert_eq!(action.method, method_symbol("send"));
    }

    #[test]
    fn authority_satisfies_tiers() {
        assert!(InvokeAuthority::None.satisfies(&AuthRequired::None));
        assert!(!InvokeAuthority::None.satisfies(&AuthRequired::Signature));
        assert!(InvokeAuthority::Signature.satisfies(&AuthRequired::Signature));
        assert!(InvokeAuthority::Signature.satisfies(&AuthRequired::Either));
        assert!(InvokeAuthority::Proof.satisfies(&AuthRequired::Either));
        assert!(!InvokeAuthority::Signature.satisfies(&AuthRequired::Proof));
        // Impossible is never satisfied.
        assert!(!InvokeAuthority::Signature.satisfies(&AuthRequired::Impossible));
        // Custom must match the vk_hash.
        let vk = [9u8; 32];
        assert!(
            InvokeAuthority::Custom { vk_hash: vk }
                .satisfies(&AuthRequired::Custom { vk_hash: vk })
        );
        assert!(
            !InvokeAuthority::Custom { vk_hash: [1u8; 32] }
                .satisfies(&AuthRequired::Custom { vk_hash: vk })
        );
    }
}
