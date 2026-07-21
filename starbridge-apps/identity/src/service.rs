//! # identity — the credential lifecycle as a SERVICE CELL on the `invoke()` front door.
//!
//! The per-issuer credential lifecycle re-expressed as a CELLS-AS-SERVICE-OBJECTS
//! citizen (the same template the `starbridge-bounty-board`,
//! `starbridge-kvstore`, and `starbridge-escrow-market` exemplars wear). A new
//! `service` module on the existing crate: it publishes a first-class, typed
//! [`InterfaceDescriptor`] and drives the issuer lifecycle through the
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
//! ## Non-degrading: the SAME canonical issuer program
//!
//! The service face installs the IDENTICAL canonical
//! [`issuer_program`](crate::issuer_program) the
//! [`FactoryDescriptor`](crate::issuer_factory_descriptor) bakes into every
//! factory-born issuer cell (via [`seed_issuer`](crate::seed_issuer)). So the
//! lifecycle teeth re-enforce on every invoke()-desugared turn exactly as they do
//! on a factory-born cell's turns:
//!
//! | Slot               | Caveat                      | Bites on |
//! |--------------------|-----------------------------|----------|
//! | `SCHEMA_COMMITMENT`| `WriteOnce`                 | the setup turn, then frozen |
//! | `ISSUANCE_COUNTER` | `MonotonicSequence` (+1)    | every issuer turn (`issue`, `revoke`) |
//! | `REVOCATION_ROOT`  | `Monotonic` (append-only)   | `revoke` (a rewind is refused) |
//! | `ISSUER_AUTH_ROOT` | `SenderAuthorized(PublicRoot)` | every issuer turn (the authority tooth) |
//!
//! Because `issuer_program` carries `SenderAuthorized(PublicRoot)`, a mutator's
//! desugared turn MUST carry the issuer's Merkle-membership witness
//! ([`issuer_membership_witness`](crate::issuer_membership_witness)) for the
//! executor's real `MerkleMembership` STARK to admit the authorized signer. The
//! signature is computed over `Action::hash`, which covers `witness_blobs`, so the
//! witness must be attached BEFORE signing — which [`invoke_with_descriptor`]
//! (which signs internally) forecloses. The mutator path therefore routes through
//! [`resolve_against`] (the routing → auth → seam core that
//! [`invoke_with_descriptor`] itself wraps), attaches the witness, then signs and
//! wraps the turn. The serviced-read and refusal paths — which never build a turn —
//! go through [`invoke_with_descriptor`] directly.
//!
//! ## The published interface (the lifecycle as typed methods)
//!
//! | method   | semantics                 | auth        | args         | desugars to |
//! |----------|---------------------------|-------------|--------------|-------------|
//! | `issue`  | [`Semantics::Replayable`] | `Signature` | `(counter)`  | `SetField(ISSUANCE_COUNTER)` + `EmitEvent` |
//! | `revoke` | [`Semantics::Replayable`] | `Signature` | `(new_root)` | `SetField(REVOCATION_ROOT, ISSUANCE_COUNTER)` + `EmitEvent` |
//! | `present`| [`Semantics::Serviced`]   | `None`      | `()`         | — (the named seam: a holder-side disclosure read, no turn) |
//! | `verify` | [`Semantics::Serviced`]   | `None`      | `()`         | — (the named seam: a verifier-side re-derive read, no turn) |
//!
//! `issue`/`revoke` are **replayable** issuer-state mutators: they desugar (via
//! the invoke front door) to a verified turn whose post-state the executor checks
//! against the issuer [`CellProgram`](dregg_cell::program::CellProgram). `present`
//! and `verify` are **serviced**: a credential presentation is the holder's own
//! disclosure and a verification is a verifier-side re-derivation — neither mutates
//! the issuer cell, so `invoke()` refuses to desugar them and names the seam
//! honestly rather than faking an issuer turn.
//!
//! ## The verified guarantee (the program bites)
//!
//! The cap-gate (`Signature` on both mutators) is enforced twice over: at the
//! `invoke()` front door (an unauthorized caller is refused before any turn is
//! built — anti-ghost) and again by the executor (the desugared turn carries a
//! real signature the kernel verifies). The issuance sequence is a rollback-proof
//! per-turn ratchet at the verified commit path: `ISSUANCE_COUNTER` is
//! `MonotonicSequence`, so a replayed / non-`+1` issuance is an EXECUTOR REFUSAL,
//! not a userspace check — and a revocation-root rewind (`Monotonic(REVOCATION_ROOT)`)
//! and a non-member signer (`SenderAuthorized`, the real `MerkleMembership` STARK)
//! are likewise real refusals on the invoke()-desugared turn.

use dregg_app_framework::{
    AppCipherclerk, Effect, FieldElement, InterfaceRegistry, InvokeAuthority, InvokeRefused,
    field_from_u64, invoke_with_descriptor, resolve_against,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_turn::Turn;
use dregg_types::CellId;

use crate::{ISSUANCE_COUNTER_SLOT, REVOCATION_ROOT_SLOT, issuer_membership_witness};

// =============================================================================
// Method names
// =============================================================================

/// The `issue` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// the issuer mints a credential (`ISSUANCE_COUNTER` advances by exactly +1 under
/// `MonotonicSequence`; the turn carries the membership witness so the
/// `SenderAuthorized` authority tooth admits the signer).
pub const METHOD_ISSUE: &str = "issue";
/// The `revoke` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// the issuer revokes a credential (`REVOCATION_ROOT` advances strictly under
/// `Monotonic`; the issuer's every-turn `MonotonicSequence` also advances the
/// counter +1).
pub const METHOD_REVOKE: &str = "revoke";
/// The `present` method — a [`Semantics::Serviced`] read (the named seam): a
/// holder produces a credential disclosure. Never desugared to an issuer turn.
pub const METHOD_PRESENT: &str = "present";
/// The `verify` method — a [`Semantics::Serviced`] read (the named seam): a
/// verifier re-derives a presentation. Never desugared to an issuer turn.
pub const METHOD_VERIFY: &str = "verify";

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The issuer's first-class typed interface** — the four lifecycle methods it
/// publishes, with their auth and replayable-vs-serviced semantics.
///
/// This is the richer-than-derived descriptor: `derive_replayable` would make
/// every method `Replayable`/`None`, but the issuer wants its two mutators
/// `Signature`-gated and the `present` / `verify` reads marked `Serviced`. An app
/// registers THIS in an [`InterfaceRegistry`] so the Service Explorer resolves the
/// real auth + seam shape, not the permissive derived default.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    let serviced = |name: &str| MethodSig {
        args_schema: ArgsSchema::Fixed(0),
        auth_required: AuthRequired::None,
        semantics: Semantics::Serviced,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // issue(counter): mint a credential (counter advances +1).
        mutator(METHOD_ISSUE, 1),
        // revoke(new_root): revoke (revocation root advances; counter +1).
        mutator(METHOD_REVOKE, 1),
        // present(): a holder-side disclosure — the named seam, never desugared.
        serviced(METHOD_PRESENT),
        // verify(): a verifier-side re-derivation — the named seam, never desugared.
        serviced(METHOD_VERIFY),
    ])
}

/// Register the issuer's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults
/// before falling back to derive-from-program. After this, the explorer resolves
/// the issuer's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — building invocations through the invoke() front door
// =============================================================================

/// **A handle to a deployed issuer cell** — bundles the issuer cell with its
/// published interface, and builds method invocations through the `invoke()`
/// front door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it
/// through an executor
/// ([`dregg_app_framework::EmbeddedExecutor::submit_turn`], a node
/// `/turns/submit`, …) to actually commit. A refusal at the front door (unknown
/// method, insufficient authority, a serviced seam) is surfaced as an
/// [`InvokeRefused`] before any turn is built — fail-closed.
///
/// The mutators (`issue`, `revoke`) attach the issuer's Merkle-membership witness
/// ([`issuer_membership_witness`](crate::issuer_membership_witness)) so the reused
/// [`issuer_program`](crate::issuer_program)'s `SenderAuthorized(PublicRoot)`
/// authority tooth admits the signer on the green path.
#[derive(Clone, Debug)]
pub struct IdentityService {
    /// The issuer cell this handle drives.
    pub cell: CellId,
    /// The issuer's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl IdentityService {
    /// A handle to the issuer cell `cell`, carrying the issuer's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        IdentityService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `issue(new_counter)`** — the issuer mints a credential: advance
    /// `ISSUANCE_COUNTER` to `new_counter` (the executor's `MonotonicSequence`
    /// requires `new == old + 1`, so a stale / replayed value is refused) and emit
    /// `credential-issued`. Routes through the verified DFA, cap-gates on
    /// `Signature`, attaches the membership witness, and signs.
    pub fn issue(
        &self,
        cipherclerk: &AppCipherclerk,
        new_counter: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, IdentityServiceError> {
        let counter_f = field_from_u64(new_counter);
        let effects = vec![
            self.set(ISSUANCE_COUNTER_SLOT, counter_f),
            Effect::EmitEvent {
                cell: self.cell,
                event: dregg_app_framework::Event::new(
                    dregg_app_framework::symbol("credential-issued"),
                    vec![counter_f],
                ),
            },
        ];
        self.invoke_mutator(
            cipherclerk,
            METHOD_ISSUE,
            vec![counter_f],
            effects,
            authority,
        )
    }

    /// **Invoke `revoke(new_root, new_counter)`** — the issuer revokes: advance
    /// `REVOCATION_ROOT` strictly (the executor's `Monotonic` refuses a rewind) and
    /// — under the issuer's every-turn `MonotonicSequence` — advance
    /// `ISSUANCE_COUNTER` by exactly +1. Emits `credential-revoked`.
    pub fn revoke(
        &self,
        cipherclerk: &AppCipherclerk,
        new_root: u64,
        new_counter: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, IdentityServiceError> {
        let root_f = field_from_u64(new_root);
        let counter_f = field_from_u64(new_counter);
        let effects = vec![
            self.set(REVOCATION_ROOT_SLOT, root_f),
            self.set(ISSUANCE_COUNTER_SLOT, counter_f),
            Effect::EmitEvent {
                cell: self.cell,
                event: dregg_app_framework::Event::new(
                    dregg_app_framework::symbol("credential-revoked"),
                    vec![root_f],
                ),
            },
        ];
        self.invoke_mutator(cipherclerk, METHOD_REVOKE, vec![root_f], effects, authority)
    }

    /// **Attempt to invoke `present()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: a credential presentation is the holder's
    /// own disclosure (produced by [`dregg_credentials::present`](crate::present)),
    /// not an issuer turn. This method makes the seam legible (and testable): a
    /// serviced read is not a turn, and `invoke()` will not pretend otherwise.
    pub fn present(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, IdentityServiceError> {
        self.serviced(cipherclerk, METHOD_PRESENT)
    }

    /// **Attempt to invoke `verify()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: a verification is a verifier-side
    /// re-derivation (via [`dregg_credentials::verify`](crate::verify)), not an
    /// issuer turn. Like [`present`](Self::present), it names the seam honestly.
    pub fn verify(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, IdentityServiceError> {
        self.serviced(cipherclerk, METHOD_VERIFY)
    }

    /// A `SetField` effect on this issuer cell.
    fn set(&self, index: usize, value: FieldElement) -> Effect {
        Effect::SetField {
            cell: self.cell,
            index: index as u64,
            value,
        }
    }

    /// Route → cap-gate → desugar → ATTACH WITNESS → sign → wrap, the mutator path
    /// through the `invoke()` front door against this issuer's published descriptor.
    ///
    /// Uses [`resolve_against`] (the routing/auth/seam core that
    /// [`invoke_with_descriptor`] wraps) so the issuer's membership witness can be
    /// attached BEFORE signing — the signature covers `witness_blobs`, and the
    /// reused [`issuer_program`](crate::issuer_program)'s `SenderAuthorized` tooth
    /// needs the witness for the executor's real `MerkleMembership` STARK to admit
    /// the signer on the green path.
    fn invoke_mutator(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, IdentityServiceError> {
        let (mut action, _sig) = resolve_against(
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(IdentityServiceError::Refused)?;
        action.witness_blobs = vec![issuer_membership_witness(cipherclerk)];
        let signed = cipherclerk.sign_action(action);
        Ok(cipherclerk.make_turn(signed))
    }

    /// The serviced-read path through [`invoke_with_descriptor`] — it routes the
    /// method and, finding it [`Semantics::Serviced`], refuses to desugar (a named
    /// seam) before any turn is built. No witness is needed (no turn is produced).
    fn serviced(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
    ) -> Result<Turn, IdentityServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
        .map_err(IdentityServiceError::Refused)
    }
}

/// Why an [`IdentityService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IdentityServiceError {
    /// The `invoke()` front door refused (unknown method, insufficient authority,
    /// or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for IdentityServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IdentityServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for IdentityServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32])
    }

    #[test]
    fn interface_publishes_four_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 4);
        assert!(iface.verify_id());

        for m in [METHOD_ISSUE, METHOD_REVOKE] {
            let sig = iface.method(&method_symbol(m)).unwrap();
            assert_eq!(sig.semantics, Semantics::Replayable, "{m} is replayable");
            assert_eq!(
                sig.auth_required,
                AuthRequired::Signature,
                "{m} is sig-gated"
            );
        }
        for m in [METHOD_PRESENT, METHOD_VERIFY] {
            let sig = iface.method(&method_symbol(m)).unwrap();
            assert_eq!(sig.semantics, Semantics::Serviced, "{m} is serviced");
            assert_eq!(sig.auth_required, AuthRequired::None);
        }
    }

    #[test]
    fn the_interface_names_the_lifecycle_vocabulary() {
        let iface = interface_descriptor();
        for m in [METHOD_ISSUE, METHOD_PRESENT, METHOD_VERIFY, METHOD_REVOKE] {
            assert!(iface.method(&method_symbol(m)).is_some(), "{m} published");
        }
        // An unknown method is not a member of the interface (fail-closed).
        assert!(iface.method(&method_symbol("frobnicate")).is_none());
    }

    #[test]
    fn unauthorized_issue_refused_at_the_front_door() {
        let cclerk = test_cipherclerk();
        let svc = IdentityService::new(cclerk.cell_id());
        // `issue` needs `Signature`; a `None` holder is refused before any turn.
        assert!(matches!(
            svc.issue(&cclerk, 1, InvokeAuthority::None),
            Err(IdentityServiceError::Refused(
                InvokeRefused::Unauthorized { .. }
            ))
        ));
    }

    #[test]
    fn present_and_verify_are_serviced_seams_never_desugared() {
        let cclerk = test_cipherclerk();
        let svc = IdentityService::new(cclerk.cell_id());
        assert!(matches!(
            svc.present(&cclerk),
            Err(IdentityServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
        assert!(matches!(
            svc.verify(&cclerk),
            Err(IdentityServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }

    #[test]
    fn an_authorized_issue_builds_a_signed_turn_carrying_the_witness() {
        let cclerk = test_cipherclerk();
        let svc = IdentityService::new(cclerk.cell_id());
        let turn = svc
            .issue(&cclerk, 1, InvokeAuthority::Signature)
            .expect("a Signature holder may build an issue invocation");
        // The desugared action carries the membership witness (so the reused
        // issuer_program's SenderAuthorized tooth admits the signer downstream).
        let action = &turn.call_forest.roots[0].action;
        assert_eq!(
            action.witness_blobs.len(),
            1,
            "the membership witness rides"
        );
    }
}
