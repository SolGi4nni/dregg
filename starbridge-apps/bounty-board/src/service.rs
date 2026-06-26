//! # bounty-board — the lifecycle as a SERVICE CELL on the `invoke()` front door.
//!
//! The canonical four-state bounty re-expressed as a CELLS-AS-SERVICE-OBJECTS
//! citizen (after the `starbridge-kvstore`, `starbridge-nameservice`, and
//! `starbridge-escrow-market` exemplars). A new `service` module on the existing
//! crate: it publishes a first-class, typed [`InterfaceDescriptor`] and drives
//! the bounty lifecycle through the [`dregg_app_framework::invoke`] front door —
//! the userspace method-dispatch layer that sits *slightly above* the effect-VM
//! and desugars a method call to the ordinary verified effects it names. There is
//! **no `Effect::Invoke`**, no kernel change, no new circuit rung: the kernel and
//! the light client keep seeing only the
//! [`SetField`](dregg_app_framework::Effect::SetField) effects they already
//! enforce and witness. The one extra fact — that an invoked method is a member
//! of the cell's interface — is decided by the SAME verified DFA router
//! ([`InterfaceDescriptor::route_method`]) the protocol already uses.
//!
//! ## Non-degrading: the SAME canonical lifecycle program
//!
//! The service face installs the IDENTICAL canonical
//! [`bounty_cell_program`](crate::bounty_cell_program) the
//! [`FactoryDescriptor`](crate::bounty_factory_descriptor) bakes into every
//! factory-born bounty cell. So the lifecycle teeth re-enforce on every
//! invoke()-desugared turn exactly as they do on a factory-born cell's turns:
//!
//! | Slot              | Caveat            | Bites on |
//! |-------------------|-------------------|----------|
//! | `TITLE_HASH`      | `WriteOnce`       | `post` (admit-from-zero), then frozen |
//! | `REWARD`          | `WriteOnce`       | `post` (admit-from-zero), then frozen |
//! | `STATE`           | `StrictMonotonic` | every turn (OPEN→CLAIMED→SUBMITTED→PAID) |
//! | `CLAIMANT_HASH`   | `WriteOnce`       | `claim` (first-claimer-wins) |
//! | `SUBMISSION_HASH` | `WriteOnce`       | `submit` |
//!
//! The `FactoryDescriptor` federation surface, the
//! [`DeosApp`](dregg_app_framework::DeosApp) composition skin
//! ([`bounty_app`](crate::bounty_app)), and the inspector are UNCHANGED — this
//! module is the service-object FACE of the same bounty primitive.
//!
//! ## The published interface (the lifecycle as typed methods)
//!
//! | method   | semantics                | auth        | args                | desugars to |
//! |----------|--------------------------|-------------|---------------------|-------------|
//! | `post`   | [`Semantics::Replayable`]| `Signature` | `(title, reward)`   | `SetField(TITLE, REWARD, STATE=OPEN)` |
//! | `claim`  | [`Semantics::Replayable`]| `Signature` | `(claimant)`        | `SetField(CLAIMANT, STATE=CLAIMED)` |
//! | `submit` | [`Semantics::Replayable`]| `Signature` | `(artifact)`        | `SetField(SUBMISSION, STATE=SUBMITTED)` |
//! | `payout` | [`Semantics::Replayable`]| `Signature` | `()`                | `SetField(STATE=PAID)` |
//! | `view`   | [`Semantics::Serviced`]  | `None`      | `()`                | — (the named OFE seam: a pure read, no turn) |
//!
//! `post`/`claim`/`submit`/`payout` are **replayable**: they desugar (via
//! `invoke()`) to a verified turn whose post-state the executor checks against
//! the bounty [`CellProgram`](dregg_cell::program::CellProgram). `view` is
//! **serviced**: the bounty's committed lifecycle state IS the answer (it rides
//! the OFE cross-cell-read, `crossCellRead_refines_observedField`, not a replay),
//! so `invoke()` refuses to desugar it and names the seam honestly rather than
//! faking a write.
//!
//! ## The verified guarantee (the program bites)
//!
//! The cap-gate (`Signature` on every mutator) is enforced twice over: at the
//! `invoke()` front door (an unauthorized caller is refused before any turn is
//! built — anti-ghost) and again by the executor (the desugared turn carries a
//! real signature the kernel verifies). The lifecycle is a rollback-proof one-way
//! ratchet at the verified commit path: `STATE` is `StrictMonotonic`, so a
//! replayed/reordered/no-advance step is an EXECUTOR REFUSAL, not a userspace
//! check — and a claimant overwrite (`WriteOnce(CLAIMANT_HASH)`, first-claimer-
//! wins) is likewise a real refusal on the invoke()-desugared turn.

use dregg_app_framework::{
    AppCipherclerk, Effect, FieldElement, InterfaceRegistry, InvokeAuthority, InvokeRefused,
    field_from_bytes, invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_turn::Turn;
use dregg_types::CellId;

use crate::{
    CLAIMANT_HASH_SLOT, REWARD_SLOT, STATE_CLAIMED, STATE_OPEN, STATE_PAID, STATE_SLOT,
    STATE_SUBMITTED, SUBMISSION_HASH_SLOT, TITLE_HASH_SLOT, claimant_hash, reward_field,
    state_field, title_hash,
};

// =============================================================================
// Method names
// =============================================================================

/// The `post` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// open a bounty (`TITLE_HASH`, `REWARD` `WriteOnce`, `STATE → OPEN`).
pub const METHOD_POST: &str = "post";
/// The `claim` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// a worker takes the bounty (`CLAIMANT_HASH` `WriteOnce`, `STATE → CLAIMED`).
pub const METHOD_CLAIM: &str = "claim";
/// The `submit` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// deliver work (`SUBMISSION_HASH` `WriteOnce`, `STATE → SUBMITTED`).
pub const METHOD_SUBMIT: &str = "submit";
/// The `payout` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// settle the bounty (`STATE → PAID`, terminal).
pub const METHOD_PAYOUT: &str = "payout";
/// The `view` method — a [`Semantics::Serviced`] read (the named OFE seam): read
/// the bounty's committed lifecycle state. Never desugared.
pub const METHOD_VIEW: &str = "view";

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The bounty's first-class typed interface** — the five methods it publishes,
/// with their auth and replayable-vs-serviced semantics.
///
/// This is the richer-than-derived descriptor: `derive_replayable` would make
/// every method `Replayable`/`None`, but the bounty wants its four mutators
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
        // post(title, reward): open the bounty.
        mutator(METHOD_POST, 2),
        // claim(claimant): a worker takes it (first-claimer-wins).
        mutator(METHOD_CLAIM, 1),
        // submit(artifact): deliver work.
        mutator(METHOD_SUBMIT, 1),
        // payout(): settle (terminal).
        mutator(METHOD_PAYOUT, 0),
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// Register the bounty's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults
/// before falling back to derive-from-program. After this, the explorer resolves
/// the bounty's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed bounty cell** — bundles the bounty cell with its
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
pub struct BountyService {
    /// The bounty cell this handle drives.
    pub cell: CellId,
    /// The bounty's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl BountyService {
    /// A handle to the bounty cell `cell`, carrying the bounty's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        BountyService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `post(title, reward)`** — open the bounty: write `TITLE_HASH`,
    /// `REWARD` (both `WriteOnce`, admitted from zero on this first turn), advance
    /// `STATE → OPEN`. Routes through the verified DFA, cap-gates on `Signature`,
    /// and desugars to the underlying `SetField`s targeting the `post` method
    /// symbol.
    pub fn post(
        &self,
        cipherclerk: &AppCipherclerk,
        title: &str,
        reward: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, BountyServiceError> {
        if title.is_empty() {
            return Err(BountyServiceError::EmptyField);
        }
        let title_h = title_hash(title);
        let reward_f = reward_field(reward);
        let effects = vec![
            self.set(TITLE_HASH_SLOT, title_h),
            self.set(REWARD_SLOT, reward_f),
            self.set(STATE_SLOT, state_field(STATE_OPEN)),
        ];
        self.invoke(
            cipherclerk,
            METHOD_POST,
            vec![title_h, reward_f],
            effects,
            authority,
        )
    }

    /// **Invoke `claim(claimant)`** — a worker takes the bounty: bind
    /// `CLAIMANT_HASH` (`WriteOnce` → first-claimer-wins), advance `STATE →
    /// CLAIMED`. A competing second claim is an executor refusal
    /// (`WriteOnce(CLAIMANT_HASH)` / `StrictMonotonic(STATE)`).
    pub fn claim(
        &self,
        cipherclerk: &AppCipherclerk,
        claimant: &str,
        authority: InvokeAuthority,
    ) -> Result<Turn, BountyServiceError> {
        if claimant.is_empty() {
            return Err(BountyServiceError::EmptyField);
        }
        let claimant_h = claimant_hash(claimant);
        let effects = vec![
            self.set(CLAIMANT_HASH_SLOT, claimant_h),
            self.set(STATE_SLOT, state_field(STATE_CLAIMED)),
        ];
        self.invoke(
            cipherclerk,
            METHOD_CLAIM,
            vec![claimant_h],
            effects,
            authority,
        )
    }

    /// **Invoke `submit(artifact)`** — the claimant delivers work: bind
    /// `SUBMISSION_HASH` (`WriteOnce`), advance `STATE → SUBMITTED`.
    pub fn submit(
        &self,
        cipherclerk: &AppCipherclerk,
        artifact_uri: &str,
        authority: InvokeAuthority,
    ) -> Result<Turn, BountyServiceError> {
        if artifact_uri.is_empty() {
            return Err(BountyServiceError::EmptyField);
        }
        let artifact_h = field_from_bytes(artifact_uri.as_bytes());
        let effects = vec![
            self.set(SUBMISSION_HASH_SLOT, artifact_h),
            self.set(STATE_SLOT, state_field(STATE_SUBMITTED)),
        ];
        self.invoke(
            cipherclerk,
            METHOD_SUBMIT,
            vec![artifact_h],
            effects,
            authority,
        )
    }

    /// **Invoke `payout()`** — the poster settles a submitted bounty: advance
    /// `STATE → PAID` (terminal). A re-payout is a no-advance `PAID → PAID` the
    /// executor's `StrictMonotonic(STATE)` refuses.
    pub fn payout(
        &self,
        cipherclerk: &AppCipherclerk,
        authority: InvokeAuthority,
    ) -> Result<Turn, BountyServiceError> {
        let effects = vec![self.set(STATE_SLOT, state_field(STATE_PAID))];
        self.invoke(cipherclerk, METHOD_PAYOUT, vec![], effects, authority)
    }

    /// **Attempt to invoke `view()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `view` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read (the bounty's committed lifecycle
    /// state), not a replay desugar. This method exists to make the seam legible
    /// (and testable): a serviced read is not a turn, and `invoke()` will not
    /// pretend otherwise. To actually READ the bounty, read the committed state at
    /// the bounty's slots ([`STATE_SLOT`](crate::STATE_SLOT), …).
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, BountyServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// A `SetField` effect on this bounty cell.
    fn set(&self, index: usize, value: FieldElement) -> Effect {
        Effect::SetField {
            cell: self.cell,
            index,
            value,
        }
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door
    /// against this bounty's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, BountyServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(BountyServiceError::Refused)
    }
}

/// Why a [`BountyService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BountyServiceError {
    /// A required text field (title / claimant / artifact) was empty.
    EmptyField,
    /// The `invoke()` front door refused (unknown method, insufficient authority,
    /// or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for BountyServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BountyServiceError::EmptyField => write!(f, "a required text field must be non-empty"),
            BountyServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for BountyServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    #[test]
    fn interface_publishes_five_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 5);
        assert!(iface.verify_id());

        for m in [METHOD_POST, METHOD_CLAIM, METHOD_SUBMIT, METHOD_PAYOUT] {
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
    fn the_derived_interface_names_the_same_methods() {
        // The published descriptor's methods are exactly the lifecycle vocabulary.
        let iface = interface_descriptor();
        for m in [
            METHOD_POST,
            METHOD_CLAIM,
            METHOD_SUBMIT,
            METHOD_PAYOUT,
            METHOD_VIEW,
        ] {
            assert!(iface.method(&method_symbol(m)).is_some(), "{m} published");
        }
    }

    #[test]
    fn empty_field_rejected_before_any_turn() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = BountyService::new(cclerk.cell_id());
        assert!(matches!(
            svc.post(&cclerk, "", 500, InvokeAuthority::Signature),
            Err(BountyServiceError::EmptyField)
        ));
        assert!(matches!(
            svc.claim(&cclerk, "", InvokeAuthority::Signature),
            Err(BountyServiceError::EmptyField)
        ));
    }

    #[test]
    fn unauthorized_claim_refused_at_the_front_door() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = BountyService::new(cclerk.cell_id());
        // `claim` needs `Signature`; a `None` holder is refused before any turn.
        assert!(matches!(
            svc.claim(&cclerk, "bob", InvokeAuthority::None),
            Err(BountyServiceError::Refused(
                InvokeRefused::Unauthorized { .. }
            ))
        ));
    }

    #[test]
    fn view_is_a_serviced_seam_never_desugared() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = BountyService::new(cclerk.cell_id());
        assert!(matches!(
            svc.view(&cclerk),
            Err(BountyServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }
}
