//! # escrow-market — a SERVICE CELL on the `invoke()` front door.
//!
//! The escrowed-delivery marketplace re-expressed as a CELLS-AS-SERVICE-OBJECTS
//! citizen (after the `starbridge-kvstore` and `starbridge-nameservice`
//! exemplars), proving the pattern generalizes to a non-trivial, four-organ app.
//! A new `service` module on the existing crate: it publishes a first-class,
//! typed [`InterfaceDescriptor`] and drives the escrow lifecycle through the
//! [`dregg_app_framework::invoke`] front door — the userspace method-dispatch
//! layer that sits *slightly above* the effect-VM and desugars a method call to
//! the ordinary verified effects it names. There is **no `Effect::Invoke`**, no
//! kernel change, no new circuit rung: the kernel and the light client keep
//! seeing only the [`SetField`](dregg_app_framework::Effect::SetField) effects
//! they already enforce and witness. The one extra fact — that an invoked method
//! is a member of the cell's interface — is decided by the SAME verified DFA
//! router ([`InterfaceDescriptor::route_method`]) the protocol already uses.
//!
//! ## Non-degrading: the SAME canonical four-organ program
//!
//! The service face installs the IDENTICAL canonical [`escrow_cell_program`] the
//! [`FactoryDescriptor`](crate::escrow_factory_descriptor) bakes into every
//! factory-born escrow cell. So the four organ teeth re-enforce on every
//! invoke()-desugared turn exactly as they do on a factory-born cell's turns:
//!
//! | Organ      | Caveat                                            | Bites on |
//! |------------|---------------------------------------------------|----------|
//! | TRUSTLINE  | `FieldLteField { ESCROWED ≤ CEILING }`            | every turn |
//! | MAILBOX    | `WriteOnce(DELIVERY_HASH)`                         | every turn |
//! | FLASHWELL  | `AffineEq { RELEASED + REFUNDED − ESCROWED = 0 }` | `settle` |
//! | LIFECYCLE  | `StrictMonotonic(STATE)`                          | every turn |
//!
//! The `FactoryDescriptor` federation surface, the `DeosApp` composition skin,
//! and the inspector are UNCHANGED — this module is the service-object face of
//! the same escrow primitive.
//!
//! ## The published interface (the lifecycle as typed methods)
//!
//! | method   | semantics                | auth        | args                   | desugars to |
//! |----------|--------------------------|-------------|------------------------|-------------|
//! | `list`   | [`Semantics::Replayable`]| `Signature` | `(seller, ceiling)`    | `SetField(SELLER, CEILING, STATE=LISTED)` |
//! | `fund`   | [`Semantics::Replayable`]| `Signature` | `(buyer, amount)`      | `SetField(BUYER, ESCROWED, STATE=FUNDED)` |
//! | `ship`   | [`Semantics::Replayable`]| `Signature` | `(delivery_hash)`      | `SetField(DELIVERY, STATE=SHIPPED)` |
//! | `settle` | [`Semantics::Replayable`]| `Signature` | `(released, refunded)` | `SetField(RELEASED, REFUNDED, STATE=SETTLED)` |
//! | `view`   | [`Semantics::Serviced`]  | `None`      | `()`                   | — (the named OFE seam: a pure read, no turn) |
//!
//! `list`/`fund`/`ship`/`settle` are **replayable**: they desugar (via
//! `invoke()`) to a verified turn whose post-state the executor checks against
//! the escrow [`CellProgram`]. `view` is **serviced**: the order's committed
//! state IS the answer (it rides the OFE cross-cell-read,
//! `crossCellRead_refines_observedField`, not a replay), so `invoke()` refuses to
//! desugar it and names the seam honestly rather than faking a write.
//!
//! ## The verified guarantee (the program bites)
//!
//! The cap-gate (`Signature` on every mutator) is enforced twice over: at the
//! `invoke()` front door (an unauthorized caller is refused before any turn is
//! built — anti-ghost) and again by the executor (the desugared turn carries a
//! real signature the kernel verifies). The lifecycle is rollback-proof at the
//! verified commit path: `STATE` is `StrictMonotonic`, so a replayed/reordered
//! `settle` (or any non-advancing step) is an EXECUTOR REFUSAL, not a userspace
//! check — and an over-ceiling `fund` (`FieldLteField`) and a value-conjuring
//! `settle` (`AffineEq`) are likewise real refusals on the invoke()-desugared
//! turn.
//!
//! ## A note on the rights ladder
//!
//! The deos composition surface scopes a richer observer ⊂ buyer ⊂ seller
//! attenuation ladder ([`OBSERVER_RIGHTS`](crate::OBSERVER_RIGHTS) …) on the real
//! cap-graph. The service face uses the `invoke()` [`AuthRequired`] *tier*
//! (`Signature`) for every mutator — the legible early cap-gate — and leaves the
//! attenuation-lattice roles to the deos surface, which is untouched.

use dregg_app_framework::{
    AppCipherclerk, Effect, FieldElement, InterfaceRegistry, InvokeAuthority, InvokeRefused,
    invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::program::CellProgram;
use dregg_turn::Turn;
use dregg_types::CellId;

use crate::{BUYER_HASH_SLOT, ESCROWED_SLOT, STATE_SLOT};
use crate::{
    CEILING_SLOT, DELIVERY_HASH_SLOT, REFUNDED_SLOT, RELEASED_SLOT, SELLER_HASH_SLOT, STATE_FUNDED,
    STATE_LISTED, STATE_SETTLED, STATE_SHIPPED, amount_field, escrow_cell_program, party_hash,
    state_field,
};

// =============================================================================
// Method names
// =============================================================================

/// The `list` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// the seller opens a listing (`SELLER`, `CEILING`, `STATE → LISTED`).
pub const METHOD_LIST: &str = "list";
/// The `fund` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// the buyer escrows `amount ≤ CEILING` (`BUYER`, `ESCROWED`, `STATE → FUNDED`).
pub const METHOD_FUND: &str = "fund";
/// The `ship` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// the seller commits the sealed delivery (`DELIVERY`, `STATE → SHIPPED`).
pub const METHOD_SHIP: &str = "ship";
/// The `settle` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// the deal closes conserving the escrow (`RELEASED`, `REFUNDED`, `STATE →
/// SETTLED`).
pub const METHOD_SETTLE: &str = "settle";
/// The `view` method — a [`Semantics::Serviced`] read (the named OFE seam): read
/// the order's committed lifecycle state. Never desugared.
pub const METHOD_VIEW: &str = "view";

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The escrow's first-class typed interface** — the five methods it publishes,
/// with their auth and replayable-vs-serviced semantics.
///
/// This is the richer-than-derived descriptor: `derive_replayable` would make
/// every method `Replayable`/`None`, but the escrow wants its four mutators
/// `Signature`-gated and `view` marked `Serviced`. An app registers THIS in an
/// [`InterfaceRegistry`] so the Service Explorer resolves the real auth + seam
/// shape, not the permissive derived default.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // list(seller, ceiling): open the listing.
        mutator(METHOD_LIST, 2),
        // fund(buyer, amount): the buyer escrows ≤ ceiling.
        mutator(METHOD_FUND, 2),
        // ship(delivery_hash): commit the sealed delivery.
        mutator(METHOD_SHIP, 1),
        // settle(released, refunded): conserve + close.
        mutator(METHOD_SETTLE, 2),
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// **The escrow service cell's [`CellProgram`]** — the IDENTICAL canonical
/// [`escrow_cell_program`] the factory bakes into every escrow cell.
///
/// Reusing the canonical program (rather than a service-specific copy) is the
/// non-degrading choice: the four organ caveats — TRUSTLINE `FieldLteField`,
/// MAILBOX `WriteOnce(DELIVERY)`, FLASHWELL `AffineEq` on `settle`, and LIFECYCLE
/// `StrictMonotonic(STATE)` — re-enforce on every invoke()-desugared turn exactly
/// as on a factory-born cell's turns. Install it on the service cell before
/// driving the methods.
pub fn escrow_service_program() -> CellProgram {
    escrow_cell_program()
}

/// Register the escrow's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults
/// before falling back to derive-from-program. After this, the explorer resolves
/// the escrow's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed escrow cell** — bundles the escrow cell with its
/// published interface, and builds method invocations through the `invoke()`
/// front door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it
/// through an executor ([`dregg_app_framework::EmbeddedExecutor::submit_turn`], a
/// node `/turns/submit`, …) to actually commit. A refusal at the front door
/// (unknown method, insufficient authority, a serviced seam) is surfaced as an
/// [`InvokeRefused`] before any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct EscrowService {
    /// The escrow cell this handle drives.
    pub cell: CellId,
    /// The escrow's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl EscrowService {
    /// A handle to the escrow cell `cell`, carrying the escrow's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        EscrowService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `list(seller, ceiling)`** — open the listing: write `SELLER`,
    /// `CEILING` (the trustline ceiling, `WriteOnce`), advance `STATE → LISTED`.
    /// Routes through the verified DFA, cap-gates on `Signature`, and desugars to
    /// the underlying `SetField`s targeting the `list` method symbol.
    pub fn list(
        &self,
        cipherclerk: &AppCipherclerk,
        seller: &str,
        ceiling: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, EscrowError> {
        if seller.is_empty() {
            return Err(EscrowError::EmptyParty);
        }
        let effects = vec![
            self.set(SELLER_HASH_SLOT, party_hash(seller)),
            self.set(CEILING_SLOT, amount_field(ceiling)),
            self.set(STATE_SLOT, state_field(STATE_LISTED)),
        ];
        self.invoke(
            cipherclerk,
            METHOD_LIST,
            vec![party_hash(seller), amount_field(ceiling)],
            effects,
            authority,
        )
    }

    /// **Invoke `fund(buyer, amount)`** — the buyer escrows `amount` (the TRUSTLINE
    /// draw, `≤ CEILING` or the executor's `FieldLteField` refuses), binds `BUYER`,
    /// advances `STATE → FUNDED`.
    pub fn fund(
        &self,
        cipherclerk: &AppCipherclerk,
        buyer: &str,
        amount: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, EscrowError> {
        if buyer.is_empty() {
            return Err(EscrowError::EmptyParty);
        }
        let effects = vec![
            self.set(BUYER_HASH_SLOT, party_hash(buyer)),
            self.set(ESCROWED_SLOT, amount_field(amount)),
            self.set(STATE_SLOT, state_field(STATE_FUNDED)),
        ];
        self.invoke(
            cipherclerk,
            METHOD_FUND,
            vec![party_hash(buyer), amount_field(amount)],
            effects,
            authority,
        )
    }

    /// **Invoke `ship(delivery_hash)`** — the seller commits the sealed-delivery
    /// digest into `DELIVERY_HASH` (the MAILBOX `WriteOnce` commitment), advances
    /// `STATE → SHIPPED`.
    pub fn ship(
        &self,
        cipherclerk: &AppCipherclerk,
        sealed_delivery: FieldElement,
        authority: InvokeAuthority,
    ) -> Result<Turn, EscrowError> {
        let effects = vec![
            self.set(DELIVERY_HASH_SLOT, sealed_delivery),
            self.set(STATE_SLOT, state_field(STATE_SHIPPED)),
        ];
        self.invoke(
            cipherclerk,
            METHOD_SHIP,
            vec![sealed_delivery],
            effects,
            authority,
        )
    }

    /// **Invoke `settle(released, refunded)`** — close the deal: write `RELEASED`,
    /// `REFUNDED`, advance `STATE → SETTLED`. The FLASHWELL `AffineEq(RELEASED +
    /// REFUNDED == ESCROWED)` (and the universal no-mint `AffineLe`) makes the
    /// split atomic and value-neutral: a split that does not conserve the escrow is
    /// an executor refusal, never committed.
    pub fn settle(
        &self,
        cipherclerk: &AppCipherclerk,
        released: u64,
        refunded: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, EscrowError> {
        let effects = vec![
            self.set(RELEASED_SLOT, amount_field(released)),
            self.set(REFUNDED_SLOT, amount_field(refunded)),
            self.set(STATE_SLOT, state_field(STATE_SETTLED)),
        ];
        self.invoke(
            cipherclerk,
            METHOD_SETTLE,
            vec![amount_field(released), amount_field(refunded)],
            effects,
            authority,
        )
    }

    /// **Attempt to invoke `view()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `view` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read (the order's committed lifecycle state),
    /// not a replay desugar. This method exists to make the seam legible (and
    /// testable): a serviced read is not a turn, and `invoke()` will not pretend
    /// otherwise. To actually READ the order, read the committed state at the
    /// escrow's slots ([`STATE_SLOT`](crate::STATE_SLOT), …).
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, EscrowError> {
        self.invoke(
            cipherclerk,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// A `SetField` effect on this escrow cell.
    fn set(&self, index: usize, value: FieldElement) -> Effect {
        Effect::SetField {
            cell: self.cell,
            index,
            value,
        }
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door
    /// against this escrow's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, EscrowError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(EscrowError::Refused)
    }
}

/// Why an [`EscrowService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EscrowError {
    /// A party identifier (seller/buyer) was empty.
    EmptyParty,
    /// The `invoke()` front door refused (unknown method, insufficient authority,
    /// or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for EscrowError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EscrowError::EmptyParty => write!(f, "a party identifier must be non-empty"),
            EscrowError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for EscrowError {}

/// The big-endian-padded `u64` a value slot encodes — the inverse of
/// [`amount_field`] for reading the escrow's committed amount registers back.
pub fn field_value_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    #[test]
    fn interface_publishes_five_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 5);
        assert!(iface.verify_id());

        for m in [METHOD_LIST, METHOD_FUND, METHOD_SHIP, METHOD_SETTLE] {
            let sig = iface.method(&method_symbol(m)).unwrap();
            assert_eq!(sig.semantics, Semantics::Replayable, "{m} is replayable");
            assert_eq!(
                sig.auth_required,
                AuthRequired::Signature,
                "{m} is sig-gated"
            );
        }
        let view = iface.method(&method_symbol(METHOD_VIEW)).unwrap();
        assert_eq!(view.semantics, Semantics::Serviced);
        assert_eq!(view.auth_required, AuthRequired::None);
    }

    #[test]
    fn the_service_program_is_the_canonical_escrow_program() {
        assert_eq!(escrow_service_program(), escrow_cell_program());
    }

    #[test]
    fn empty_party_rejected_before_any_turn() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = EscrowService::new(cclerk.cell_id());
        assert!(matches!(
            svc.list(&cclerk, "", 1000, InvokeAuthority::Signature),
            Err(EscrowError::EmptyParty)
        ));
        assert!(matches!(
            svc.fund(&cclerk, "", 100, InvokeAuthority::Signature),
            Err(EscrowError::EmptyParty)
        ));
    }

    #[test]
    fn field_value_roundtrips() {
        assert_eq!(field_value_u64(&amount_field(800)), 800);
    }
}
