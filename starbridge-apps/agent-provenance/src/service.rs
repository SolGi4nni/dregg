//! # agent-provenance — the LOG as a SERVICE CELL on the `invoke()` front door.
//!
//! The append-only provenance log re-expressed as a CELLS-AS-SERVICE-OBJECTS
//! citizen (after the `bounty-board` / `kvstore` / `nameservice` exemplars). A
//! new `service` module on the existing crate: it publishes a first-class, typed
//! [`InterfaceDescriptor`] and drives the log through the
//! [`dregg_app_framework::invoke`] front door — the userspace method-dispatch
//! layer that sits *slightly above* the effect-VM and desugars a method call to
//! the ordinary verified effects it names. There is **no `Effect::Invoke`**, no
//! kernel change, no new circuit rung: the kernel and the light client keep
//! seeing only the [`SetField`](dregg_app_framework::Effect::SetField) /
//! [`EmitEvent`](dregg_app_framework::Effect::EmitEvent) effects they already
//! enforce and witness. The one extra fact — that an invoked method is a member
//! of the cell's interface — is decided by the SAME verified DFA router
//! ([`InterfaceDescriptor::route_method`]) the protocol already uses.
//!
//! ## Non-degrading: the SAME canonical append turn
//!
//! [`ProvenanceService::append`] builds the IDENTICAL four effects
//! [`build_append_action`](crate::build_append_action) builds — write the new
//! hash-chain link at `entry_slot(i)` (`WriteOnce`), advance `HEAD` to `i + 1`
//! (`Monotonic` forward), point `TIP` at the new digest, and emit
//! `provenance-appended`. So the gating teeth re-enforce on every
//! invoke()-desugared turn exactly as they do on a factory-born log cell's turns:
//!
//! | Slot              | Caveat       | Bites on |
//! |-------------------|--------------|----------|
//! | `ENTRY_BASE + i`  | `WriteOnce`  | `append` (first write from zero), then frozen |
//! | `HEAD_SLOT`       | `Monotonic`  | every append (cursor only grows — no rewind) |
//!
//! ## The published interface (the log as typed methods)
//!
//! | method   | semantics                 | auth        | args            | desugars to |
//! |----------|---------------------------|-------------|-----------------|-------------|
//! | `append` | [`Semantics::Replayable`] | `Signature` | `(digest, claim)` | `SetField(entry, HEAD, TIP)` + `EmitEvent` |
//! | `view`   | [`Semantics::Serviced`]   | `None`      | `()`            | — (the named OFE read seam: no turn) |
//!
//! `append` is **replayable**: it desugars (via `invoke()`) to a verified turn
//! whose post-state the executor re-checks against the log's installed
//! [`provenance_cell_program`](crate::provenance_cell_program). `view` is
//! **serviced**: the log's committed chain IS the answer (it rides the OFE
//! cross-cell-read, not a replay), so `invoke()` refuses to desugar it and names
//! the seam honestly rather than faking a write.
//!
//! ## The verified guarantee (the program bites)
//!
//! The cap-gate (`Signature` on `append`) is enforced twice over: at the
//! `invoke()` front door (an unauthorized caller is refused before any turn is
//! built — anti-ghost) and again by the executor (the desugared turn carries a
//! real signature the kernel verifies). Tamper-evidence is a real executor
//! refusal at the verified commit path: `entry_slot(i)` is `WriteOnce`, so an
//! overwrite is an EXECUTOR REFUSAL, not a userspace check — and a rewound `HEAD`
//! (`Monotonic`) is likewise a real refusal on the invoke()-desugared turn.

use dregg_app_framework::{
    AppCipherclerk, Effect, Event, FieldElement, InterfaceRegistry, InvokeAuthority, InvokeRefused,
    field_from_u64, invoke_with_descriptor, symbol,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_turn::Turn;
use dregg_types::CellId;

use crate::{HEAD_SLOT, TIP_SLOT, entry_slot, link_hash};

// =============================================================================
// Method names
// =============================================================================

/// The `append` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// commit the next hash-chain link (`entry_slot(i)` `WriteOnce`, advance `HEAD`
/// `Monotonic`, point `TIP`, emit `provenance-appended`).
pub const METHOD_APPEND: &str = "append";
/// The `view` method — a [`Semantics::Serviced`] read (the named OFE seam): read
/// the log's committed chain. Never desugared.
pub const METHOD_VIEW: &str = "view";

/// The append method's fixed arity. The published `append` descriptor declares
/// `(i, prev, claim, …)` — the conceptual call shape (the entry index, the link
/// predecessor, the attested claim digest, plus the derived link digest the
/// invocation carries). The desugared invocation's `args` carry `[digest,
/// claim]` (the committed event payload), exactly as
/// [`build_append_action`](crate::build_append_action)'s `provenance-appended`
/// event does; the arity is interface metadata, not a runtime arg-count check.
pub const APPEND_ARITY: u8 = 4;

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The log's first-class typed interface** — the two methods it publishes, with
/// their auth and replayable-vs-serviced semantics.
///
/// This is the richer-than-derived descriptor: `derive_replayable` would make
/// every method `Replayable`/`None`, but the log wants `append`
/// `Signature`-gated and `view` marked `Serviced`. An app registers THIS in an
/// [`InterfaceRegistry`] so the Service Explorer resolves the real auth + seam
/// shape, not the permissive derived default.
pub fn interface_descriptor() -> InterfaceDescriptor {
    InterfaceDescriptor::new(vec![
        // append(i, prev, claim, …): commit the next hash-chain link.
        MethodSig {
            args_schema: ArgsSchema::Fixed(APPEND_ARITY),
            auth_required: AuthRequired::Signature,
            ..MethodSig::replayable(method_symbol(METHOD_APPEND))
        },
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// Register the log's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults
/// before falling back to derive-from-program. After this, the explorer resolves
/// the log's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed provenance log cell** — bundles the log cell with its
/// published interface, and builds method invocations through the `invoke()`
/// front door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it
/// through an executor
/// ([`dregg_app_framework::EmbeddedExecutor::submit_turn`], a node
/// `/turns/submit`, …) to actually commit. A refusal at the front door (unknown
/// method, insufficient authority, a serviced seam) is surfaced as an
/// [`InvokeRefused`] before any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct ProvenanceService {
    /// The log cell this handle drives.
    pub cell: CellId,
    /// The log's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl ProvenanceService {
    /// A handle to the log cell `cell`, carrying the log's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        ProvenanceService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `append(i, prev, claim)`** — commit the i-th hash-chain link:
    /// write `entry_slot(i) = link_hash(prev, claim)` (`WriteOnce`, admitted from
    /// zero on a fresh slot), advance `HEAD → i + 1` (`Monotonic` forward), point
    /// `TIP` at the new digest, and emit `provenance-appended`. Routes through the
    /// verified DFA, cap-gates on `Signature`, and desugars to those same four
    /// effects targeting the `append` method symbol — the IDENTICAL body
    /// [`build_append_action`](crate::build_append_action) builds.
    ///
    /// A competing overwrite of a sealed entry (`WriteOnce`) or a rewound `HEAD`
    /// (`Monotonic`) is an executor refusal on the desugared turn, not a userspace
    /// check.
    pub fn append(
        &self,
        cipherclerk: &AppCipherclerk,
        i: usize,
        prev: &FieldElement,
        claim: &FieldElement,
        authority: InvokeAuthority,
    ) -> Result<Turn, ProvenanceServiceError> {
        let digest = link_hash(prev, claim);
        let effects = vec![
            self.set(entry_slot(i), digest),
            self.set(HEAD_SLOT, field_from_u64((i + 1) as u64)),
            self.set(TIP_SLOT, digest),
            Effect::EmitEvent {
                cell: self.cell,
                event: Event::new(symbol("provenance-appended"), vec![digest, *claim]),
            },
        ];
        self.invoke(
            cipherclerk,
            METHOD_APPEND,
            vec![digest, *claim],
            effects,
            authority,
        )
    }

    /// **Attempt to invoke `view()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `view` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read (the log's committed chain), not a
    /// replay desugar. This method exists to make the seam legible (and testable):
    /// a serviced read is not a turn, and `invoke()` will not pretend otherwise. To
    /// actually READ the log, read the committed digests at the log's entry slots
    /// and re-derive with [`verify_chain`](crate::verify_chain).
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, ProvenanceServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// A `SetField` effect on this log cell.
    fn set(&self, index: usize, value: FieldElement) -> Effect {
        Effect::SetField {
            cell: self.cell,
            index,
            value,
        }
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door
    /// against this log's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, ProvenanceServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(ProvenanceServiceError::Refused)
    }
}

/// Why a [`ProvenanceService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProvenanceServiceError {
    /// The `invoke()` front door refused (unknown method, insufficient authority,
    /// or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for ProvenanceServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProvenanceServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for ProvenanceServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::GENESIS_PREV;
    use dregg_app_framework::AgentCipherclerk;

    #[test]
    fn interface_publishes_two_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 2);
        assert!(iface.verify_id());

        let append = iface.method(&method_symbol(METHOD_APPEND)).unwrap();
        assert_eq!(
            append.semantics,
            Semantics::Replayable,
            "append is replayable"
        );
        assert_eq!(
            append.auth_required,
            AuthRequired::Signature,
            "append is sig-gated"
        );

        let view = iface.method(&method_symbol(METHOD_VIEW)).unwrap();
        assert_eq!(view.semantics, Semantics::Serviced);
        assert_eq!(view.auth_required, AuthRequired::None);
    }

    #[test]
    fn the_interface_names_the_log_vocabulary() {
        let iface = interface_descriptor();
        for m in [METHOD_APPEND, METHOD_VIEW] {
            assert!(iface.method(&method_symbol(m)).is_some(), "{m} published");
        }
        assert!(
            iface.method(&method_symbol("frobnicate")).is_none(),
            "an unknown method is not a member of the interface"
        );
    }

    #[test]
    fn unauthorized_append_refused_at_the_front_door() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = ProvenanceService::new(cclerk.cell_id());
        let claim = crate::claim_digest(b"a claim");
        // `append` needs `Signature`; a `None` holder is refused before any turn.
        assert!(matches!(
            svc.append(&cclerk, 0, &GENESIS_PREV, &claim, InvokeAuthority::None),
            Err(ProvenanceServiceError::Refused(
                InvokeRefused::Unauthorized {
                    required: AuthRequired::Signature,
                    ..
                }
            ))
        ));
    }

    #[test]
    fn view_is_a_serviced_seam_never_desugared() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = ProvenanceService::new(cclerk.cell_id());
        assert!(matches!(
            svc.view(&cclerk),
            Err(ProvenanceServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }
}
