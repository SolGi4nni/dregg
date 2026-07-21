//! # privacy-voting — the propose/vote/tally lifecycle as a SERVICE CELL on the
//! `invoke()` front door.
//!
//! The third axis (AX3) of a modern starbridge-app: the poll + ballot lifecycle
//! re-expressed as a CELLS-AS-SERVICE-OBJECTS citizen (after the `bounty-board`,
//! `kvstore`, and `escrow-market` exemplars). A `service` module on the existing
//! crate that publishes a first-class, typed [`InterfaceDescriptor`] and drives the
//! lifecycle through the [`dregg_app_framework::invoke`] front door — the userspace
//! method-dispatch layer that sits *slightly above* the effect-VM and desugars a
//! method call to the ordinary verified effects it names. There is **no
//! `Effect::Invoke`**, no kernel change, no new circuit rung: the kernel and the
//! light client keep seeing only the
//! [`SetField`](dregg_app_framework::Effect::SetField) /
//! [`EmitEvent`](dregg_app_framework::Effect::EmitEvent) effects they already enforce
//! and witness. The one extra fact — that an invoked method is a member of the cell's
//! interface — is decided by the SAME verified DFA router
//! ([`InterfaceDescriptor::route_method`]) the protocol already uses.
//!
//! ## A TWO-CELL service object
//!
//! Privacy-voting is two cells (the [`crate`] AX1 floor): a POLL cell (the public
//! tally board — `QUESTION_HASH` `WriteOnce`, three `Monotonic` tallies, `CLOSED`
//! `WriteOnce`) and a per-voter BALLOT cell (`POLL_REF` `WriteOnce`, `VOTE`
//! `WriteOnce` — one vote per ballot). [`VotingService`] bundles BOTH cells and
//! routes each method to the cell it acts on: `cast_vote` targets the BALLOT, the
//! other mutators target the POLL. One published [`InterfaceDescriptor`] names all
//! five methods; the per-method target is the service handle's job.
//!
//! ## The published interface (the lifecycle as typed methods)
//!
//! | method         | target | semantics                | auth        | desugars to |
//! |----------------|--------|--------------------------|-------------|-------------|
//! | `open_poll`    | poll   | [`Semantics::Replayable`]| `Signature` | `SetField(QUESTION_HASH)` + `EmitEvent(poll-opened)` |
//! | `cast_vote`    | ballot | [`Semantics::Replayable`]| `Signature` | `SetField(POLL_REF, VOTE)` + `EmitEvent(vote-cast)` |
//! | `record_tally` | poll   | [`Semantics::Replayable`]| `Signature` | `SetField(tally_slot)` + `SetField(ballots_slot)` + ballot-set `Cleartext` witness + `EmitEvent(vote-cast)` |
//! | `close_poll`   | poll   | [`Semantics::Replayable`]| `Signature` | `SetField(CLOSED)` + `EmitEvent(poll-closed)` |
//! | `view`         | poll   | [`Semantics::Serviced`]  | `None`      | — (the named OFE seam: a pure read, no turn) |
//!
//! The four mutators are **replayable**: they desugar (via `invoke()`) to a verified
//! turn whose post-state the executor checks against the cell's installed
//! [`CellProgram`](dregg_cell::program::CellProgram) (the SAME `always(...)` programs
//! the AX1 floor and the AX2 deos surface install). `view` is **serviced**: the
//! poll's committed tally state IS the answer (it rides the OFE cross-cell-read), so
//! `invoke()` refuses to desugar it and names the seam honestly rather than faking a
//! write.
//!
//! ## The verified guarantee (the program bites)
//!
//! The cap-gate (`Signature` on every mutator) is enforced twice over: at the
//! `invoke()` front door (an unauthorized caller is refused before any turn is built
//! — anti-ghost) and again by the executor (the desugared turn carries a real
//! signature the kernel verifies). The voting teeth re-enforce on the
//! invoke()-desugared turns exactly as on the floor: a SECOND `cast_vote` is an
//! EXECUTOR refusal on `WriteOnce(VOTE)`, a tally REWIND is a refusal on
//! `Monotonic(TALLY_*)`, a poll RE-OPEN is a refusal on `WriteOnce(CLOSED)` — real
//! protocol-layer refusals, not userspace checks.

use dregg_app_framework::{
    AppCipherclerk, CellId, Effect, Event, FieldElement, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, Turn, field_from_u64, invoke_with_descriptor, symbol,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;

use crate::{
    CLOSED_MARKER, CLOSED_SLOT, POLL_REF_SLOT, QUESTION_HASH_SLOT, VOTE_SLOT, poll_ref,
    question_hash, tally_slot_for_choice,
};

// =============================================================================
// Method names
// =============================================================================

/// The `open_poll` method — a [`Semantics::Replayable`], `Signature`-gated mutator
/// on the POLL cell: bind `QUESTION_HASH` (`WriteOnce`), emit `poll-opened`.
pub const METHOD_OPEN_POLL: &str = "open_poll";
/// The `cast_vote` method — a [`Semantics::Replayable`], `Signature`-gated mutator
/// on the BALLOT cell: bind `POLL_REF` + `VOTE` (both `WriteOnce` — one vote per
/// ballot), emit `vote-cast`.
pub const METHOD_CAST_VOTE: &str = "cast_vote";
/// The `record_tally` method — a [`Semantics::Replayable`], `Signature`-gated mutator
/// on the POLL cell: advance the matching `Monotonic` tally slot, emit `vote-cast`.
pub const METHOD_RECORD_TALLY: &str = "record_tally";
/// The `close_poll` method — a [`Semantics::Replayable`], `Signature`-gated mutator
/// on the POLL cell: set `CLOSED` (`WriteOnce`, one-way), emit `poll-closed`.
pub const METHOD_CLOSE_POLL: &str = "close_poll";
/// The `view` method — a [`Semantics::Serviced`] read (the named OFE seam): read the
/// poll's committed tally board. Never desugared.
pub const METHOD_VIEW: &str = "view";

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The voting service's first-class typed interface** — the five methods it
/// publishes, with their auth and replayable-vs-serviced semantics.
///
/// The richer-than-derived descriptor: `derive_replayable` would make every method
/// `Replayable`/`None`, but voting wants its four mutators `Signature`-gated and
/// `view` marked `Serviced`. An app registers THIS in an [`InterfaceRegistry`] so the
/// Service Explorer resolves the real auth + seam shape, not the permissive derived
/// default.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // open_poll(question_hash): open the poll on the POLL cell.
        mutator(METHOD_OPEN_POLL, 1),
        // cast_vote(poll_ref, choice): one vote on the BALLOT cell.
        mutator(METHOD_CAST_VOTE, 2),
        // record_tally(choice, new_tally): advance a tally on the POLL cell.
        mutator(METHOD_RECORD_TALLY, 2),
        // close_poll(): close the poll on the POLL cell (one-way).
        mutator(METHOD_CLOSE_POLL, 0),
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// Register the voting service's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults before
/// falling back to derive-from-program. After this, the explorer resolves the
/// service's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed voting service** — bundles the POLL + BALLOT cells with
/// the published interface, and builds method invocations through the `invoke()`
/// front door, routing each method to the cell it acts on.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it through
/// an executor ([`dregg_app_framework::EmbeddedExecutor::submit_turn`], a node
/// `/turns/submit`, …) to actually commit. A refusal at the front door (unknown
/// method, insufficient authority, a serviced seam) is surfaced as an
/// [`InvokeRefused`] before any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct VotingService {
    /// The POLL cell (the public tally board): `open_poll` / `record_tally` /
    /// `close_poll` / `view` target this.
    pub poll: CellId,
    /// The BALLOT cell (the per-voter capability): `cast_vote` targets this.
    pub ballot: CellId,
    /// The service's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl VotingService {
    /// A handle to the `poll` + `ballot` cells, carrying the published
    /// [`interface_descriptor`].
    pub fn new(poll: CellId, ballot: CellId) -> Self {
        VotingService {
            poll,
            ballot,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `open_poll(question)`** on the POLL cell — bind `QUESTION_HASH`
    /// (`WriteOnce`, admitted from zero on a fresh poll), emit `poll-opened`. Routes
    /// through the verified DFA, cap-gates on `Signature`, and desugars to the
    /// underlying `SetField` + `EmitEvent` targeting the `open_poll` method symbol.
    pub fn open_poll(
        &self,
        cipherclerk: &AppCipherclerk,
        question: &str,
        authority: InvokeAuthority,
    ) -> Result<Turn, VotingServiceError> {
        let q = question_hash(question);
        let effects = vec![
            set(self.poll, QUESTION_HASH_SLOT, q),
            Effect::EmitEvent {
                cell: self.poll,
                event: Event::new(symbol("poll-opened"), vec![q]),
            },
        ];
        self.invoke(
            cipherclerk,
            self.poll,
            METHOD_OPEN_POLL,
            vec![q],
            effects,
            authority,
        )
    }

    /// **Invoke `cast_vote(choice)`** on the BALLOT cell — bind `POLL_REF`
    /// (`WriteOnce`, the poll this ballot votes in) + `VOTE` (`WriteOnce`, the
    /// one-vote-per-ballot tooth), emit `vote-cast`. The poll-ref is recomputed from
    /// the service's poll cell ([`poll_ref`]). A SECOND `cast_vote` rewriting `VOTE`
    /// is an EXECUTOR refusal (`WriteOnce(VOTE)`).
    pub fn cast_vote(
        &self,
        cipherclerk: &AppCipherclerk,
        choice: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, VotingServiceError> {
        let pr = poll_ref(self.poll);
        let choice_field = field_from_u64(choice);
        let effects = vec![
            set(self.ballot, POLL_REF_SLOT, pr),
            set(self.ballot, VOTE_SLOT, choice_field),
            Effect::EmitEvent {
                cell: self.ballot,
                event: Event::new(symbol("vote-cast"), vec![pr, choice_field]),
            },
        ];
        self.invoke(
            cipherclerk,
            self.ballot,
            METHOD_CAST_VOTE,
            vec![pr, choice_field],
            effects,
            authority,
        )
    }

    /// **Invoke `record_tally(choice, new_tally)`** on the POLL cell — set the
    /// matching tally slot ([`tally_slot_for_choice`]) to `new_tally` (the
    /// post-increment count the caller read off the poll: old + 1), commit the
    /// backing distinct ballot set into the choice's ballot-set commitment slot,
    /// EXHIBIT it as the turn's `Cleartext` witness, and emit `vote-cast`.
    /// The poll's `Monotonic(TALLY_*)` caveat refuses any value below the current
    /// tally, and the ballot-binding `CountGe` gate refuses a witness-less or
    /// zero-ballot tally move (both EXECUTOR refusals, fail-closed).
    ///
    /// `ballots` is the FULL distinct set of ballot-cell ids counted into this
    /// choice's tally so far, INCLUDING the newly-counted one.
    pub fn record_tally(
        &self,
        cipherclerk: &AppCipherclerk,
        choice: u64,
        new_tally: u64,
        ballots: &std::collections::BTreeSet<[u8; 32]>,
        authority: InvokeAuthority,
    ) -> Result<Turn, VotingServiceError> {
        let choice_field = field_from_u64(choice);
        let tally = field_from_u64(new_tally);
        let slot = tally_slot_for_choice(choice);
        let effects = vec![
            set(self.poll, slot, tally),
            set(
                self.poll,
                crate::ballots_slot_for_choice(choice),
                dregg_cell::count_ge_set_commitment(ballots),
            ),
            Effect::EmitEvent {
                cell: self.poll,
                event: Event::new(symbol("vote-cast"), vec![choice_field]),
            },
        ];
        dregg_app_framework::invoke_with_descriptor_with_witnesses(
            cipherclerk,
            self.poll,
            &self.descriptor,
            METHOD_RECORD_TALLY,
            vec![choice_field, tally],
            effects,
            authority,
            vec![crate::ballot_set_exhibit(ballots)],
        )
        .map_err(VotingServiceError::Refused)
    }

    /// **Invoke `close_poll()`** on the POLL cell — set `CLOSED` (`WriteOnce`,
    /// one-way), emit `poll-closed`. A RE-OPEN (`CLOSED` 1 → 0) is an EXECUTOR refusal
    /// (`WriteOnce(CLOSED)`).
    pub fn close_poll(
        &self,
        cipherclerk: &AppCipherclerk,
        authority: InvokeAuthority,
    ) -> Result<Turn, VotingServiceError> {
        let marker = field_from_u64(CLOSED_MARKER);
        let effects = vec![
            set(self.poll, CLOSED_SLOT, marker),
            Effect::EmitEvent {
                cell: self.poll,
                event: Event::new(symbol("poll-closed"), vec![marker]),
            },
        ];
        self.invoke(
            cipherclerk,
            self.poll,
            METHOD_CLOSE_POLL,
            vec![],
            effects,
            authority,
        )
    }

    /// **Attempt to invoke `view()`** on the POLL cell — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `view` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read (the poll's committed tally board), not a
    /// replay desugar. This method exists to make the seam legible (and testable): a
    /// serviced read is not a turn, and `invoke()` will not pretend otherwise. To
    /// actually READ the tally, read the committed state at the poll's slots
    /// ([`TALLY_YES_SLOT`](crate::TALLY_YES_SLOT), …).
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, VotingServiceError> {
        self.invoke(
            cipherclerk,
            self.poll,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door against
    /// this service's published descriptor, targeting `target` (the cell the method
    /// acts on — the BALLOT for `cast_vote`, the POLL otherwise).
    #[allow(clippy::too_many_arguments)]
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        target: CellId,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, VotingServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            target,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(VotingServiceError::Refused)
    }
}

/// A `SetField` effect on `cell`.
fn set(cell: CellId, index: usize, value: FieldElement) -> Effect {
    Effect::SetField {
        cell,
        index: index as u64,
        value,
    }
}

/// Why a [`VotingService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VotingServiceError {
    /// The `invoke()` front door refused (unknown method, insufficient authority, or
    /// a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for VotingServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VotingServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for VotingServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    fn svc(cclerk: &AppCipherclerk) -> VotingService {
        let poll = cclerk.cell_id();
        let ballot = crate::ballot_cell_id(&cclerk.public_key().0);
        VotingService::new(poll, ballot)
    }

    #[test]
    fn interface_publishes_five_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 5);
        assert!(iface.verify_id());

        for m in [
            METHOD_OPEN_POLL,
            METHOD_CAST_VOTE,
            METHOD_RECORD_TALLY,
            METHOD_CLOSE_POLL,
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
    fn the_published_interface_names_the_whole_lifecycle() {
        let iface = interface_descriptor();
        for m in [
            METHOD_OPEN_POLL,
            METHOD_CAST_VOTE,
            METHOD_RECORD_TALLY,
            METHOD_CLOSE_POLL,
            METHOD_VIEW,
        ] {
            assert!(iface.method(&method_symbol(m)).is_some(), "{m} published");
        }
    }

    #[test]
    fn unauthorized_cast_vote_refused_at_the_front_door() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let service = svc(&cclerk);
        // `cast_vote` needs `Signature`; a `None` holder is refused before any turn.
        assert!(matches!(
            service.cast_vote(&cclerk, crate::VOTE_YES, InvokeAuthority::None),
            Err(VotingServiceError::Refused(InvokeRefused::Unauthorized {
                required: AuthRequired::Signature,
                ..
            }))
        ));
    }

    #[test]
    fn view_is_a_serviced_seam_never_desugared() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let service = svc(&cclerk);
        assert!(matches!(
            service.view(&cclerk),
            Err(VotingServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }
}
