//! # The discord-bot AS a SERVICE CELL on the `invoke()` front door.
//!
//! This is the bot's modern service-cell face: its command surface published as a
//! first-class, typed, content-addressed [`InterfaceDescriptor`] whose methods are
//! driven through the [`dregg_app_framework::invoke`] front door — the userspace
//! method-dispatch layer that lives *slightly above* the effect-VM and desugars a
//! method call to the ordinary verified effects it names. There is **no
//! `Effect::Invoke`**, no kernel change, no new circuit rung: the kernel and the
//! light client keep seeing only the `SetField`/`EmitEvent` effects they already
//! enforce and witness. The one extra fact — that an invoked method is a member of
//! the bot's interface — is decided by the SAME verified DFA router
//! ([`InterfaceDescriptor::route_method`]) the protocol already uses, exactly as in
//! the `starbridge-kvstore` / `starbridge-nameservice` citizens.
//!
//! ## Why this exists
//!
//! Historically the bot's commands were a bespoke integration: per-command code
//! that hand-built a canonical `Action` (via the starbridge `build_*_action`
//! helpers) and pushed it down a custodial submit path, OR — for the older
//! surfaces — signed a legacy BLAKE3-MAC and POSTed it to a devnet HTTP endpoint.
//! Neither shape made the bot a *typed cap-gated dregg method* a light client or
//! the Service Explorer could enumerate. This module gives the bot the same shape
//! every other citizen has: ONE published [`InterfaceDescriptor`], routed through
//! `invoke()`.
//!
//! The bot's existing `build_*_action` helpers ALREADY target named methods —
//! `cclerk.make_action(cell, "register_name", effects)`,
//! `"issue_credential"`, `"propose_table_update"`, … — so the modernization is not
//! a rewrite of effect construction: it is *routing those same actions through the
//! published, typed, cap-gated interface*. [`BotService::invoke_built_action`] is
//! that bridge — it takes a canonical [`Action`] a `build_*_action` produced and
//! re-expresses its `args`+`effects` through the verified DFA + cap-gate of the
//! published interface, returning the ordinary signed [`Turn`].
//!
//! ## The published interface
//!
//! | method                 | semantics    | auth        | desugars to / status |
//! |------------------------|--------------|-------------|----------------------|
//! | `issue_credential`     | Replayable   | `Signature` | issuer-cell `SetField`+`EmitEvent` (canonical) |
//! | `revoke_credential`    | Replayable   | `Signature` | issuer-cell `SetField`+`EmitEvent` (canonical) |
//! | `register_name`        | Replayable   | `Signature` | registry-cell `SetField`+`EmitEvent` (canonical) |
//! | `set_name_target`      | Replayable   | `Signature` | registry-cell `SetField`+`EmitEvent` (canonical) |
//! | `propose_table_update` | Replayable   | `Signature` | namespace-cell `SetField`+`EmitEvent` (canonical) |
//! | `vote_on_proposal`     | Replayable   | `Signature` | namespace-cell `SetField`+`EmitEvent` (canonical) |
//! | `gallery_bid`          | Replayable   | `Signature` | auction-cell mutation (the BESPOKE REMAINDER — still rides the legacy BLAKE3-MAC HTTP path; typed here so the explorer sees it) |
//! | `resolve_name`         | Serviced     | `None`      | — the OFE read seam (`crossCellRead_refines_observedField`) |
//! | `gallery_view`         | Serviced     | `None`      | — a read of the gallery's committed state |
//! | `attest_presence`      | Serviced     | `None`      | — the bot-signed presence attestation rides OUTSIDE the turn replay (a bot-issued MAC, named honestly as a seam) |
//!
//! The mutators are **replayable**: routed through `invoke()` they desugar to a
//! verified turn whose post-state the executor checks. The reads are **serviced**:
//! their answer rides the OFE cross-cell-read, not a replay — so `invoke()` refuses
//! to desugar them, naming the seam honestly rather than faking a write.
//!
//! ## The cap-gate (enforced twice over)
//!
//! Every mutator declares [`AuthRequired::Signature`]. The gate bites at the
//! `invoke()` front door (a caller presenting only [`InvokeAuthority::None`] is
//! refused before any turn is built) AND again by the executor (the desugared turn
//! carries a real `AppCipherclerk` signature the kernel verifies). The bot's
//! per-user custodial cipherclerk can always produce a `Signature`, so live
//! commands invoke with [`InvokeAuthority::Signature`].

use dregg_app_framework::{
    AppCipherclerk, FieldElement, InterfaceRegistry, InvokeAuthority, InvokeRefused,
    invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::program::{CellProgram, StateConstraint, TransitionCase, TransitionGuard};
use dregg_cell::{Credential, Requirement};
use dregg_turn::Turn;
use dregg_turn::action::Action;
use dregg_types::CellId;

// =============================================================================
// Method names — the bot's command surface, mirroring the method symbols its
// canonical `build_*_action` helpers ALREADY target.
// =============================================================================

/// `issue_credential(...)` — issue a verifiable credential off an issuer cell.
/// Matches `starbridge_identity::build_issue_credential_action`'s method symbol.
pub const METHOD_ISSUE_CREDENTIAL: &str = "issue_credential";
/// `revoke_credential(...)` — record a credential revocation on the issuer cell.
pub const METHOD_REVOKE_CREDENTIAL: &str = "revoke_credential";
/// `register_name(...)` — bind a name in a nameservice registry cell. Matches
/// `starbridge_nameservice::build_register_action`'s method symbol.
pub const METHOD_REGISTER_NAME: &str = "register_name";
/// `set_name_target(...)` — point a registered name at a resolve target.
pub const METHOD_SET_NAME_TARGET: &str = "set_name_target";
/// `propose_table_update(...)` — propose a governed-namespace route-table update.
pub const METHOD_PROPOSE_TABLE_UPDATE: &str = "propose_table_update";
/// `vote_on_proposal(...)` — cast a committee vote on a pending proposal.
pub const METHOD_VOTE_ON_PROPOSAL: &str = "vote_on_proposal";
/// `gallery_bid(...)` — place a bid on a gallery auction. (THE BESPOKE REMAINDER:
/// still served by the legacy BLAKE3-MAC HTTP endpoint; declared here so the
/// Service Explorer enumerates the bot's gallery surface as a typed cap-gated
/// method, ready for the canonical-action cutover.)
pub const METHOD_GALLERY_BID: &str = "gallery_bid";
/// `resolve_name(name)` — read the cell a name is bound to. A [`Semantics::Serviced`]
/// read: the OFE cross-cell-read seam, never a replay desugar.
pub const METHOD_RESOLVE_NAME: &str = "resolve_name";
/// `gallery_view(...)` — read the gallery's committed listing/auction state. A
/// [`Semantics::Serviced`] read.
pub const METHOD_GALLERY_VIEW: &str = "gallery_view";
/// `attest_presence(...)` — the bot's signed presence attestation. A
/// [`Semantics::Serviced`] read: the attestation is a bot-issued MAC that rides
/// OUTSIDE the verified turn replay, so it is named honestly as a seam rather than
/// faked as a state mutation.
pub const METHOD_ATTEST_PRESENCE: &str = "attest_presence";

/// The state slot carrying the bot service cell's **monotone command version** —
/// bumped on every mutating invocation. Scoped [`StateConstraint::Monotonic`] in
/// [`service_program`] so a replayed/reordered mutation that would lower the
/// version is an executor refusal on the verified commit path.
pub const VERSION_SLOT: usize = 0;

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The bot's first-class typed interface** — the command surface it publishes,
/// with each method's auth and replayable-vs-serviced semantics.
///
/// This is the richer-than-derived descriptor: [`InterfaceDescriptor::derive_replayable`]
/// would make every method `Replayable`/`None`, but the bot wants its mutators
/// `Signature`-gated and its reads marked `Serviced`. An app registers THIS in an
/// [`InterfaceRegistry`] (see [`register_interface`]) so the Service Explorer
/// resolves the real auth + seam shape, not the permissive derived default.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let sig_mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: Requirement::AtLeast(Credential::Signature),
        ..MethodSig::replayable(method_symbol(name))
    };
    let serviced_read = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: Requirement::Root,
        semantics: Semantics::Serviced,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // ── canonical Signature-gated mutators (route cleanly through invoke()) ──
        sig_mutator(METHOD_ISSUE_CREDENTIAL, 3),
        sig_mutator(METHOD_REVOKE_CREDENTIAL, 2),
        sig_mutator(METHOD_REGISTER_NAME, 3),
        sig_mutator(METHOD_SET_NAME_TARGET, 2),
        sig_mutator(METHOD_PROPOSE_TABLE_UPDATE, 2),
        sig_mutator(METHOD_VOTE_ON_PROPOSAL, 2),
        // ── the bespoke remainder, typed for the explorer ──
        sig_mutator(METHOD_GALLERY_BID, 2),
        // ── serviced reads / named seams ──
        serviced_read(METHOD_RESOLVE_NAME, 1),
        serviced_read(METHOD_GALLERY_VIEW, 1),
        serviced_read(METHOD_ATTEST_PRESENCE, 1),
    ])
}

/// **The bot service cell's [`CellProgram`]** — the method-dispatch + the verified
/// invariant.
///
/// A [`CellProgram::Cases`] whose `MethodIs` guards make the derived interface
/// expose every published method, and whose mutator cases carry
/// [`StateConstraint::Monotonic`] on [`VERSION_SLOT`] (the rollback-proof command
/// version). An `Always` catch-all admits the bot's own bookkeeping turns (nonce
/// bumps) so a non-method turn is not default-denied.
pub fn service_program() -> CellProgram {
    let bump = || {
        vec![StateConstraint::Monotonic {
            index: VERSION_SLOT as u8,
        }]
    };
    let case = |name: &str, constraints: Vec<StateConstraint>| TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: method_symbol(name),
        },
        constraints,
    };
    CellProgram::Cases(vec![
        case(METHOD_ISSUE_CREDENTIAL, bump()),
        case(METHOD_REVOKE_CREDENTIAL, bump()),
        case(METHOD_REGISTER_NAME, bump()),
        case(METHOD_SET_NAME_TARGET, bump()),
        case(METHOD_PROPOSE_TABLE_UPDATE, bump()),
        case(METHOD_VOTE_ON_PROPOSAL, bump()),
        case(METHOD_GALLERY_BID, bump()),
        case(METHOD_RESOLVE_NAME, vec![]),
        case(METHOD_GALLERY_VIEW, vec![]),
        case(METHOD_ATTEST_PRESENCE, vec![]),
        // Catch-all: the bot's own non-method turns (nonce bookkeeping) must not be
        // default-denied.
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![],
        },
    ])
}

/// Register the bot's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults
/// before falling back to derive-from-program. After this, the explorer resolves
/// the bot's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — driving the bot's commands through invoke()
// =============================================================================

/// **A handle to the bot AS a deployed service cell** — bundles the bot's service
/// cell with its published interface, and routes command invocations through the
/// `invoke()` front door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it
/// through the bot's executor / `/turns/submit` to actually commit. A refusal at
/// the front door (unknown method, insufficient authority, a serviced seam) is
/// surfaced as a [`BotServiceError`] before any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct BotService {
    /// The bot's service cell (the dispatch target the interface is rooted at).
    pub cell: CellId,
    /// The bot's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl BotService {
    /// A handle to the bot service cell `cell`, carrying the bot's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        BotService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **The bridge — route a canonical [`Action`] through the published interface.**
    ///
    /// `action` is the [`Action`] a `build_*_action` helper produced (it already
    /// carries the right `effects` and `args` and targets the right method). This
    /// re-expresses it through the bot's typed cap-gated interface: route `method`
    /// through the verified DFA, cap-gate on the method's declared `auth_required`
    /// against `authority`, then desugar the action's `args`+`effects` into a fresh
    /// signed [`Turn`] (signed by `cipherclerk`). The kernel/circuit see only the
    /// effects they already enforce — no `Effect::Invoke`.
    ///
    /// This is the clean modernization seam: the live command keeps using the
    /// canonical effect-construction it already has, and GAINS the typed,
    /// cap-gated, DFA-routed, explorer-enumerable service-cell face.
    pub fn invoke_built_action(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        action: Action,
        authority: InvokeAuthority,
    ) -> Result<Turn, BotServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            action.args,
            action.effects,
            authority,
        )
        .map_err(BotServiceError::Refused)
    }

    /// **Route raw effects** through the published interface — the no-prebuilt-Action
    /// path for callers that construct effects directly (rather than via a
    /// `build_*_action` helper). Same route → cap-gate → desugar shape as
    /// [`BotService::invoke_built_action`].
    pub fn invoke_effects(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<dregg_app_framework::Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, BotServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(BotServiceError::Refused)
    }

    /// **Attempt to invoke a serviced read** (`resolve_name`, `gallery_view`,
    /// `attest_presence`) — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: a serviced method is answered by the OFE
    /// cross-cell-read / a bot-issued attestation, NOT a replay desugar. This makes
    /// the seam legible (and testable): `invoke()` will not pretend a read is a
    /// turn. To actually READ, read the committed state (or, for presence, ask the
    /// bot for its signed attestation).
    pub fn invoke_serviced(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
    ) -> Result<Turn, BotServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            vec![],
            InvokeAuthority::None,
        )
        .map_err(BotServiceError::Refused)
    }

    /// A route-membership witness that `method` belongs to the bot's COMMITTED
    /// interface — the one fact a light client must witness about an invoke (beyond
    /// the underlying effect's existing rung). Reuses the descriptor's DFA
    /// route-membership AIR; `None` if `method` is not a declared method.
    pub fn route_membership_witness(&self, method: &str) -> Option<(Vec<u8>, [u8; 32])> {
        self.descriptor
            .route_membership_witness(&method_symbol(method))
    }
}

/// Why a [`BotService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BotServiceError {
    /// The `invoke()` front door refused (unknown method, insufficient authority,
    /// or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for BotServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BotServiceError::Refused(r) => write!(f, "bot service invoke refused: {r}"),
        }
    }
}

impl std::error::Error for BotServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, Effect};

    fn an_effect(cell: CellId) -> Effect {
        Effect::SetField {
            cell,
            index: 0,
            value: [1u8; 32],
        }
    }

    #[test]
    fn interface_publishes_the_command_surface() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 10);
        assert!(iface.verify_id(), "the interface_id must self-verify");

        // The canonical mutators are Signature-gated + Replayable.
        for m in [
            METHOD_ISSUE_CREDENTIAL,
            METHOD_REVOKE_CREDENTIAL,
            METHOD_REGISTER_NAME,
            METHOD_SET_NAME_TARGET,
            METHOD_PROPOSE_TABLE_UPDATE,
            METHOD_VOTE_ON_PROPOSAL,
            METHOD_GALLERY_BID,
        ] {
            let sig = iface.method(&method_symbol(m)).expect("declared method");
            assert_eq!(sig.semantics, Semantics::Replayable, "{m} is replayable");
            assert_eq!(sig.auth_required, AuthRequired::Signature, "{m} sig-gated");
        }

        // The reads are Serviced + None.
        for m in [
            METHOD_RESOLVE_NAME,
            METHOD_GALLERY_VIEW,
            METHOD_ATTEST_PRESENCE,
        ] {
            let sig = iface.method(&method_symbol(m)).expect("declared method");
            assert_eq!(sig.semantics, Semantics::Serviced, "{m} is serviced");
            assert_eq!(sig.auth_required, AuthRequired::None, "{m} no auth");
        }
    }

    #[test]
    fn program_dispatches_on_every_published_method() {
        // The derived interface (from the program) names every published method —
        // so the Service Explorer's derive-from-program fallback sees the surface.
        let derived = InterfaceDescriptor::derive_replayable(&service_program());
        for m in [
            METHOD_ISSUE_CREDENTIAL,
            METHOD_REVOKE_CREDENTIAL,
            METHOD_REGISTER_NAME,
            METHOD_SET_NAME_TARGET,
            METHOD_PROPOSE_TABLE_UPDATE,
            METHOD_VOTE_ON_PROPOSAL,
            METHOD_GALLERY_BID,
            METHOD_RESOLVE_NAME,
            METHOD_GALLERY_VIEW,
            METHOD_ATTEST_PRESENCE,
        ] {
            assert!(
                derived.method(&method_symbol(m)).is_some(),
                "{m} must be program-dispatched"
            );
        }
    }

    #[test]
    fn mutator_routes_and_cap_gates() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x22; 32]);
        let svc = BotService::new(cclerk.cell_id());
        let action = cclerk.make_action(svc.cell, METHOD_REGISTER_NAME, vec![an_effect(svc.cell)]);

        // A Signature caller routes cleanly to a desugared, signed Turn.
        let turn = svc
            .invoke_built_action(
                &cclerk,
                METHOD_REGISTER_NAME,
                action.clone(),
                InvokeAuthority::Signature,
            )
            .expect("a signature caller invokes the register_name mutator");
        // The desugared turn is the ordinary signed turn shape (no Effect::Invoke),
        // agent-bound to the invoking cipherclerk's cell.
        assert_eq!(turn.agent, cclerk.cell_id(), "the turn is agent-bound");

        // A None caller is refused at the front door (the cap-gate bites BEFORE any
        // turn is built).
        let refused = svc
            .invoke_built_action(&cclerk, METHOD_REGISTER_NAME, action, InvokeAuthority::None)
            .unwrap_err();
        assert!(matches!(
            refused,
            BotServiceError::Refused(InvokeRefused::Unauthorized {
                required: Requirement::AtLeast(Credential::Signature),
                ..
            })
        ));
    }

    #[test]
    fn serviced_read_is_a_named_seam() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x33; 32]);
        let svc = BotService::new(cclerk.cell_id());
        let seam = svc
            .invoke_serviced(&cclerk, METHOD_RESOLVE_NAME, vec![[0u8; 32]])
            .unwrap_err();
        assert!(matches!(
            seam,
            BotServiceError::Refused(InvokeRefused::ServicedSeam { .. })
        ));
    }

    #[test]
    fn unknown_method_is_refused() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x44; 32]);
        let svc = BotService::new(cclerk.cell_id());
        let action = cclerk.make_action(svc.cell, "not_a_method", vec![an_effect(svc.cell)]);
        let refused = svc
            .invoke_built_action(&cclerk, "not_a_method", action, InvokeAuthority::Signature)
            .unwrap_err();
        assert!(matches!(
            refused,
            BotServiceError::Refused(InvokeRefused::UnknownMethod { .. })
        ));
    }

    #[test]
    fn declared_method_has_a_route_membership_witness() {
        let svc = BotService::new(CellId([7u8; 32]));
        let (proof, root) = svc
            .route_membership_witness(METHOD_ISSUE_CREDENTIAL)
            .expect("a declared method has a membership witness");
        assert_eq!(root, svc.descriptor.to_route_table().commitment);
        assert!(
            svc.descriptor
                .verify_route_membership(&method_symbol(METHOD_ISSUE_CREDENTIAL), &proof)
        );
        // An undeclared method has no membership witness (fail-closed).
        assert!(svc.route_membership_witness("not_a_method").is_none());
    }
}
