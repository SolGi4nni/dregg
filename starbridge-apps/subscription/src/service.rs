//! # subscription — the pub/sub queue as a SERVICE CELL on the `invoke()` front door.
//!
//! The third axis (AX3) of a modern starbridge-app: the feed re-expressed as a
//! CELLS-AS-SERVICE-OBJECTS citizen (after the `bounty-board` / `kvstore` /
//! `nameservice` exemplars). A new `service` module on the existing crate: it
//! publishes a first-class, typed [`InterfaceDescriptor`] and drives the queue
//! through the [`dregg_app_framework::invoke`] front door — the userspace
//! method-dispatch layer that sits *slightly above* the effect-VM and desugars a
//! method call to the ordinary verified effects it names. There is **no
//! `Effect::Invoke`**, no kernel change, no new circuit rung: the kernel and the
//! light client keep seeing only the [`SetField`](dregg_app_framework::Effect::SetField)
//! / [`EmitEvent`](dregg_app_framework::Effect::EmitEvent) effects they already
//! enforce and witness. The one extra fact — that an invoked method is a member of
//! the cell's interface — is decided by the SAME verified DFA router
//! ([`InterfaceDescriptor::route_method`]) the protocol already uses.
//!
//! ## Which program backs the runtime faces
//!
//! The service installs/assumes [`crate::feed_invariants_program`] — the FLAT
//! life-of-cell invariants (`WriteOnce` capacity/owner, `FieldLteField(tail <=
//! head)`, `Monotonic` head/tail) — exactly as the deos surface (AX2) does via
//! [`crate::seed_feed`]. This is the SAME shared cell program every *runtime* axis
//! of this crate installs; it is the "same program backs every runtime axis"
//! invariant here. The full operation-scoped [`crate::subscription_program`]
//! `Cases` shape (which adds `SenderAuthorized` membership + the per-op
//! `MonotonicSequence` exact-+1) is the AIR-bound AX1 program, pinned by the child
//! VK in the [`crate::subscription_factory_descriptor`]; the runtime faces stay on
//! the flat invariants so they are end-to-end testable without wrestling
//! `SenderAuthorized` roots, and so a head ROLLBACK (`Monotonic`) and an OVER-DRAW
//! (`FieldLteField`) still bite as real executor refusals on every invoke-desugared
//! turn.
//!
//! ## The published interface (the queue as typed methods)
//!
//! | method            | semantics                | auth        | args                       |
//! |-------------------|--------------------------|-------------|----------------------------|
//! | `publish`         | [`Semantics::Replayable`]| `Signature` | `(head, root, payload)`    |
//! | `consume`         | [`Semantics::Replayable`]| `Signature` | `(tail)`                   |
//! | `grant_publisher` | [`Semantics::Replayable`]| `Signature` | `(root)`                   |
//! | `grant_consumer`  | [`Semantics::Replayable`]| `Signature` | `(root)`                   |
//! | `view`            | [`Semantics::Serviced`]  | `None`      | `()`                       |
//!
//! `publish`/`consume`/`grant_publisher`/`grant_consumer` are **replayable**: they
//! desugar (via `invoke()`) to a verified turn whose post-state the executor checks
//! against the installed [`crate::feed_invariants_program`]. `view` is **serviced**:
//! the feed's committed state IS the answer (it rides the OFE cross-cell-read), so
//! `invoke()` refuses to desugar it and names the seam honestly rather than faking a
//! write.

use dregg_app_framework::{
    AppCipherclerk, CellId, Effect, FieldElement, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, Turn, field_from_u64, invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::program::CellProgram;

use crate::{CONSUMERS_ROOT_SLOT, PUBLISHERS_ROOT_SLOT, consume_effects, publish_effects};

// =============================================================================
// Method names
// =============================================================================

/// The `publish` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// a publisher delivers (advance `SEQ_HEAD`, fold `MESSAGE_ROOT`, write
/// `LATEST_PAYLOAD`).
pub const METHOD_PUBLISH: &str = "publish";
/// The `consume` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// a consumer draws a delivered item forward (advance `SEQ_TAIL` under `tail <=
/// head`).
pub const METHOD_CONSUME: &str = "consume";
/// The `grant_publisher` method — a [`Semantics::Replayable`], `Signature`-gated
/// mutator: the owner admits a publisher (advance `PUBLISHERS_ROOT`).
pub const METHOD_GRANT_PUBLISHER: &str = "grant_publisher";
/// The `grant_consumer` method — a [`Semantics::Replayable`], `Signature`-gated
/// mutator: the owner admits a consumer (advance `CONSUMERS_ROOT`).
pub const METHOD_GRANT_CONSUMER: &str = "grant_consumer";
/// The `view` method — a [`Semantics::Serviced`] read (the named OFE seam): read
/// the feed's committed head-of-queue state. Never desugared.
pub const METHOD_VIEW: &str = "view";

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The subscription feed's first-class typed interface** — the five methods it
/// publishes, with their auth and replayable-vs-serviced semantics.
///
/// This is the richer-than-derived descriptor: `derive_replayable` would make
/// every method `Replayable`/`None`, but the feed wants its four mutators
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
        // publish(head, root, payload): deliver an item.
        mutator(METHOD_PUBLISH, 3),
        // consume(tail): draw a delivered item forward.
        mutator(METHOD_CONSUME, 1),
        // grant_publisher(root): the owner admits a publisher.
        mutator(METHOD_GRANT_PUBLISHER, 1),
        // grant_consumer(root): the owner admits a consumer.
        mutator(METHOD_GRANT_CONSUMER, 1),
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// The cell program the subscription SERVICE face installs/assumes — the FLAT
/// [`crate::feed_invariants_program`], the SAME shared cell program the deos
/// surface (AX2) installs via [`crate::seed_feed`]. See the module docs: the
/// runtime faces stay on the flat invariants; the full operation-scoped
/// [`crate::subscription_program`] `Cases` is the AIR-bound AX1 program pinned by
/// the child VK.
pub fn subscription_service_program() -> CellProgram {
    crate::feed_invariants_program()
}

/// Register the feed's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults
/// before falling back to derive-from-program. After this, the explorer resolves
/// the feed's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed subscription feed cell** — bundles the feed cell with
/// its published interface, and builds method invocations through the `invoke()`
/// front door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it through
/// an executor ([`dregg_app_framework::EmbeddedExecutor::submit_turn`], a node
/// `/turns/submit`, …) to actually commit. A refusal at the front door (unknown
/// method, insufficient authority, a serviced seam) is surfaced as an
/// [`InvokeRefused`] before any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct SubscriptionService {
    /// The feed cell this handle drives.
    pub cell: CellId,
    /// The feed's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl SubscriptionService {
    /// A handle to the feed cell `cell`, carrying the feed's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        SubscriptionService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `publish(head, root, payload)`** — a publisher delivers: advance
    /// `SEQ_HEAD` to `new_head` (`Monotonic`), fold the message into `MESSAGE_ROOT`,
    /// write `LATEST_PAYLOAD`, and emit `subscription-published`. Routes through the
    /// verified DFA, cap-gates on `Signature`, and desugars to
    /// [`crate::publish_effects`].
    pub fn publish(
        &self,
        cipherclerk: &AppCipherclerk,
        new_head: u64,
        new_message_root: FieldElement,
        payload_hash: FieldElement,
        authority: InvokeAuthority,
    ) -> Result<Turn, SubscriptionServiceError> {
        let effects = publish_effects(self.cell, new_head, new_message_root, payload_hash);
        self.invoke(
            cipherclerk,
            METHOD_PUBLISH,
            vec![field_from_u64(new_head), new_message_root, payload_hash],
            effects,
            authority,
        )
    }

    /// **Invoke `consume(tail)`** — a consumer draws a delivered item forward:
    /// advance `SEQ_TAIL` to `new_tail` (under `tail <= head`) and emit
    /// `subscription-consumed`. An over-draw past the head is an executor refusal
    /// (`FieldLteField(tail <= head)`).
    pub fn consume(
        &self,
        cipherclerk: &AppCipherclerk,
        new_tail: u64,
        consumed_payload: FieldElement,
        authority: InvokeAuthority,
    ) -> Result<Turn, SubscriptionServiceError> {
        let effects = consume_effects(self.cell, new_tail, consumed_payload);
        self.invoke(
            cipherclerk,
            METHOD_CONSUME,
            vec![field_from_u64(new_tail)],
            effects,
            authority,
        )
    }

    /// **Invoke `grant_publisher(root)`** — the owner admits a publisher: advance
    /// `PUBLISHERS_ROOT` to `new_root` (a single `SetField`).
    pub fn grant_publisher(
        &self,
        cipherclerk: &AppCipherclerk,
        new_root: FieldElement,
        authority: InvokeAuthority,
    ) -> Result<Turn, SubscriptionServiceError> {
        let effects = vec![self.set(PUBLISHERS_ROOT_SLOT, new_root)];
        self.invoke(
            cipherclerk,
            METHOD_GRANT_PUBLISHER,
            vec![new_root],
            effects,
            authority,
        )
    }

    /// **Invoke `grant_consumer(root)`** — the owner admits a consumer: advance
    /// `CONSUMERS_ROOT` to `new_root` (a single `SetField`). Symmetric to
    /// [`Self::grant_publisher`].
    pub fn grant_consumer(
        &self,
        cipherclerk: &AppCipherclerk,
        new_root: FieldElement,
        authority: InvokeAuthority,
    ) -> Result<Turn, SubscriptionServiceError> {
        let effects = vec![self.set(CONSUMERS_ROOT_SLOT, new_root)];
        self.invoke(
            cipherclerk,
            METHOD_GRANT_CONSUMER,
            vec![new_root],
            effects,
            authority,
        )
    }

    /// **Attempt to invoke `view()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `view` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read (the feed's committed head-of-queue
    /// state), not a replay desugar. This method exists to make the seam legible
    /// (and testable): a serviced read is not a turn, and `invoke()` will not
    /// pretend otherwise. To actually READ the feed, read the committed state at the
    /// feed's slots ([`crate::SEQ_HEAD_SLOT`], …).
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, SubscriptionServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// A `SetField` effect on this feed cell.
    fn set(&self, index: u8, value: FieldElement) -> Effect {
        Effect::SetField {
            cell: self.cell,
            index: index as usize,
            value,
        }
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door against
    /// this feed's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, SubscriptionServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(SubscriptionServiceError::Refused)
    }
}

/// **Build the per-period payment `Turn` for a billing plan, THROUGH the Payable DSI.**
///
/// The billing half of a subscription ([`crate::obligation`]) moves value with the SAME
/// shared [`Payable`](dregg_app_framework::Payable) interface every value-bearing app
/// speaks: the subscriber cell `pay`s the period `price` of the plan `asset` to the
/// provider. The invocation routes through the verified DFA router and desugars to the
/// ONE conserved kernel [`dregg_app_framework::Effect::Transfer`] (per-asset Σδ=0) — no
/// `Effect::Invoke`, no new commitment field.
///
/// The proven [`StandingObligation`](dregg_cell::obligation_standing) core
/// ([`crate::obligation::Subscription::pay`]) enforces the *schedule* (one-shot per
/// period, never early, exact amount, lapse-on-miss); THIS builds the *value move*. Pair
/// them: discharge the obligation period, submit this turn.
pub fn build_period_payment(
    cipherclerk: &AppCipherclerk,
    plan: &crate::obligation::BillingPlan,
    authority: InvokeAuthority,
) -> Result<Turn, SubscriptionServiceError> {
    dregg_app_framework::pay(
        cipherclerk,
        plan.subscriber,
        *plan.asset.as_bytes(),
        plan.price.max(0) as u64,
        plan.provider,
        authority,
    )
    .map_err(SubscriptionServiceError::Refused)
}

/// Why a [`SubscriptionService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SubscriptionServiceError {
    /// The `invoke()` front door refused (unknown method, insufficient authority,
    /// or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for SubscriptionServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SubscriptionServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for SubscriptionServiceError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interface_publishes_five_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 5);
        assert!(iface.verify_id());

        for m in [
            METHOD_PUBLISH,
            METHOD_CONSUME,
            METHOD_GRANT_PUBLISHER,
            METHOD_GRANT_CONSUMER,
        ] {
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
    fn publish_carries_three_args() {
        let iface = interface_descriptor();
        let publish = iface.method(&method_symbol(METHOD_PUBLISH)).unwrap();
        assert_eq!(publish.args_schema, ArgsSchema::Fixed(3));
        let consume = iface.method(&method_symbol(METHOD_CONSUME)).unwrap();
        assert_eq!(consume.args_schema, ArgsSchema::Fixed(1));
    }

    #[test]
    fn build_period_payment_routes_through_the_payable_dsi() {
        use crate::obligation::BillingPlan;
        use dregg_app_framework::{AgentCipherclerk, AppCipherclerk};

        let cipherclerk = AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32]);
        let plan = BillingPlan::new(
            cipherclerk.cell_id(),
            CellId::from_bytes([2; 32]),
            CellId::from_bytes([9; 32]),
            50,
            100,
            1000,
            0,
        );
        // A Signature-bearing caller builds the period payment turn (the conserved
        // Transfer through the Payable interface).
        assert!(
            build_period_payment(&cipherclerk, &plan, InvokeAuthority::Signature).is_ok(),
            "a signature-authorized subscriber pays the period through Payable"
        );
        // No authority → the sig-gated `pay` refuses at the front door (fail-closed).
        assert!(matches!(
            build_period_payment(&cipherclerk, &plan, InvokeAuthority::None),
            Err(SubscriptionServiceError::Refused(_))
        ));
    }
}
