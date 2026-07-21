//! # polis — the council governance lifecycle as a SERVICE CELL on the
//! `invoke()` front door.
//!
//! The third axis (AX3) of a modern starbridge-app: the council
//! propose → approve → certify → execute lifecycle re-expressed as a
//! CELLS-AS-SERVICE-OBJECTS citizen (after the `bounty-board` /
//! `governed-namespace` exemplars). It publishes a first-class, typed
//! [`InterfaceDescriptor`] and drives the lifecycle through the
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
//! ## Not a library module — the package-cycle dance
//!
//! Unlike `bounty-board`/`governed-namespace` (whose service face is a plain
//! library module), polis CANNOT take a normal `dregg-app-framework` edge:
//! `dregg-sdk` depends on `starbridge-polis` (it re-exports the pure cell
//! programs) and `dregg-app-framework` depends on `dregg-sdk`, so a `polis →
//! app-framework` edge would close the illegal package cycle Cargo rejects. So —
//! exactly like the deos surface (`src/deos.rs`) — this file is compiled INTO THE
//! TEST BINARIES via `#[path = "../src/service.rs"]` (see `tests/service.rs`),
//! where the framework dev-dependency is in scope. The pure library it drives is
//! reached by its external name `starbridge_polis::…` (NOT `crate::…`).
//!
//! ## Non-degrading: the SAME canonical council program re-enforces
//!
//! The service installs the IDENTICAL canonical
//! [`council_cell_program`](starbridge_polis::council::council_cell_program) the
//! [`council_factory_descriptor`](starbridge_polis::council::council_factory_descriptor)
//! bakes into every factory-born proposal cell. So the lifecycle teeth re-enforce
//! on every invoke()-desugared turn exactly as they do on a factory-born cell:
//!
//! | method    | semantics                | auth        | desugars to (the executor re-enforces) |
//! |-----------|--------------------------|-------------|----------------------------------------|
//! | `propose` | [`Semantics::Replayable`]| `Signature` | DRAFT→PROPOSED, stage hash + publish member-commit |
//! | `approve` | [`Semantics::Replayable`]| `Signature` | flip member `i`'s `{0,1}` `Monotonic` approval bit |
//! | `certify` | [`Semantics::Replayable`]| `Signature` | PROPOSED→APPROVED, arm flag (`AffineLe`: `Σ ≥ M`) |
//! | `reject`  | [`Semantics::Replayable`]| `Signature` | PROPOSED→REJECTED (terminal) |
//! | `execute` | [`Semantics::Replayable`]| `Signature` | APPROVED→EXECUTED (terminal; demands flag) |
//! | `view`    | [`Semantics::Serviced`]  | `None`      | — (the named OFE seam: a pure read, no turn) |
//!
//! The five mutators are **replayable**: they desugar (via `invoke()`) to a
//! verified turn whose post-state the executor checks against the council
//! [`CellProgram`]. `view` is **serviced**: the proposal's committed machine IS
//! the answer (it rides the OFE cross-cell-read,
//! `crossCellRead_refines_observedField`, not a replay), so `invoke()` refuses to
//! desugar it and names the seam honestly rather than faking a write.
//!
//! ## The verified guarantee (the program bites)
//!
//! The cap-gate (`Signature` on every mutator) is enforced twice over: at the
//! `invoke()` front door (an unauthorized caller is refused before any turn is
//! built — anti-ghost) and again by the executor (the desugared turn carries a
//! real signature the kernel verifies). The M-of-N gate is the verified executor
//! tooth: `certify` arms the flag only when `Σ approvals >= M`
//! (`AffineLe`), an un-approve is a `Monotonic` refusal, and the terminal
//! REJECTED/EXECUTED states have no outgoing transition row — all REAL executor
//! refusals on the invoke()-desugared turn, not userspace checks.

use dregg_app_framework::{
    AppCipherclerk, CellId, Effect, EmbeddedExecutor, Event, FieldElement, InterfaceRegistry,
    InvokeAuthority, InvokeRefused, Turn, field_from_u64, invoke_with_descriptor, symbol,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::program::CellProgram;

use starbridge_polis::STATE_SLOT;
use starbridge_polis::council::{
    self, APPROVED_FLAG_SLOT, CouncilCharter, FIRST_APPROVAL_SLOT, MEMBERS_COMMIT_SLOT,
    METHOD_APPROVE, METHOD_CERTIFY, METHOD_EXECUTE, METHOD_PROPOSE, METHOD_REJECT, METHOD_VIEW,
    PROPOSAL_HASH_SLOT, STATE_APPROVED, STATE_EXECUTED, STATE_PROPOSED, STATE_REJECTED,
};

// =============================================================================
// The cell program the runtime faces install (the canonical council program)
// =============================================================================

/// The [`CellProgram`] the council SERVICE / REACTOR faces install. This RETURNS the
/// council module's factory-baked cell program verbatim (see the body) — it is not a
/// re-authored peer of it, so every invoke()-desugared turn is re-enforced by the
/// identical lifecycle teeth (the `AllowedTransitions` machine, the `AffineLe` threshold
/// gate, the `Monotonic` approval bits, the `WriteOnce` staged hash) and the service face
/// cannot diverge from the constructor contract. The equality is asserted (not merely
/// documented) by `the_service_program_is_the_canonical_council_program`.
pub fn council_service_program(charter: &CouncilCharter) -> CellProgram {
    council::council_cell_program(charter).expect("the charter validates (caller checked)")
}

// =============================================================================
// Effect bodies (shared by the service handle AND the reactor)
// =============================================================================

/// **`propose` effects** — DRAFT → PROPOSED: stage the action hash
/// (`WriteOnce`), publish the membership commitment (pinned once out of DRAFT),
/// step the state-code to PROPOSED, and emit `council-proposed`.
pub fn propose_effects(
    cell: CellId,
    proposal_hash: FieldElement,
    members_commit: FieldElement,
) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: STATE_SLOT as u64,
            value: field_from_u64(STATE_PROPOSED),
        },
        Effect::SetField {
            cell,
            index: PROPOSAL_HASH_SLOT as u64,
            value: proposal_hash,
        },
        Effect::SetField {
            cell,
            index: MEMBERS_COMMIT_SLOT as u64,
            value: members_commit,
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("council-proposed"), vec![proposal_hash]),
        },
    ]
}

/// **`approve` effects** — flip member `member_index`'s `{0,1}` `Monotonic`
/// approval bit to 1, and emit `council-approved` carrying
/// `[member_index, running_count]` so the auto-certify reactor (the AX5
/// [`crate::reactor`]) can arm the threshold straight off the observed turn.
pub fn approve_effects(cell: CellId, member_index: usize, running_count: u64) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: FIRST_APPROVAL_SLOT as u64 + member_index,
            value: field_from_u64(1),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(
                symbol("council-approved"),
                vec![
                    field_from_u64(member_index as u64),
                    field_from_u64(running_count),
                ],
            ),
        },
    ]
}

/// **`certify` effects** — PROPOSED → APPROVED: arm the threshold-certification
/// flag and step the state-code. The executor's `AffineLe { M·flag − Σ ≤ 0 }`
/// re-enforces that the flag arms only with `Σ approvals >= M`. This is the ONE
/// coherent transition both the service [`CouncilService::certify`] AND the
/// reactor's auto-certify reaction desugar to.
pub fn certify_effects(cell: CellId) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: APPROVED_FLAG_SLOT as u64,
            value: field_from_u64(1),
        },
        Effect::SetField {
            cell,
            index: STATE_SLOT as u64,
            value: field_from_u64(STATE_APPROVED),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("council-certified"), vec![]),
        },
    ]
}

/// **`reject` effects** — PROPOSED → REJECTED (terminal, inert).
pub fn reject_effects(cell: CellId) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: STATE_SLOT as u64,
            value: field_from_u64(STATE_REJECTED),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("council-rejected"), vec![]),
        },
    ]
}

/// **`execute` effects** — APPROVED → EXECUTED (terminal). The executor demands
/// the certified flag (`when_state(EXECUTED, flag == 1)`); a re-execute is a
/// no-row `AllowedTransitions` refusal.
pub fn execute_effects(cell: CellId) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: STATE_SLOT as u64,
            value: field_from_u64(STATE_EXECUTED),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("council-executed"), vec![]),
        },
    ]
}

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The council's first-class typed interface** — the six methods it publishes,
/// with their auth and replayable-vs-serviced semantics.
///
/// This is the richer-than-derived descriptor: `derive_replayable` would make
/// every method `Replayable`/`None`, but the council wants its five mutators
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
        // propose(hash): DRAFT → PROPOSED.
        mutator(METHOD_PROPOSE, 1),
        // approve(member_index, running_count): flip a member's approval bit.
        mutator(METHOD_APPROVE, 2),
        // certify(): PROPOSED → APPROVED (Σ approvals >= M).
        mutator(METHOD_CERTIFY, 0),
        // reject(): PROPOSED → REJECTED.
        mutator(METHOD_REJECT, 0),
        // execute(): APPROVED → EXECUTED.
        mutator(METHOD_EXECUTE, 0),
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// Register the council's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults
/// before falling back to derive-from-program. After this, the explorer resolves
/// the council's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed council proposal cell** — bundles the proposal cell
/// with its charter (the published membership/threshold) and its typed
/// interface, and builds method invocations through the `invoke()` front door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it
/// through an executor ([`EmbeddedExecutor::submit_turn`], a node `/turns/submit`,
/// …) to actually commit. A refusal at the front door (unknown method,
/// insufficient authority, a serviced seam) is surfaced as an [`InvokeRefused`]
/// before any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct CouncilService {
    /// The council proposal cell this handle drives.
    pub cell: CellId,
    /// The published charter — supplies the membership commitment (`propose`
    /// publishes it) and the member-index bound (`approve` validates it).
    pub charter: CouncilCharter,
    /// The council's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl CouncilService {
    /// A handle to the proposal cell `cell` under `charter`, carrying the
    /// council's published [`interface_descriptor`].
    pub fn new(cell: CellId, charter: CouncilCharter) -> Self {
        CouncilService {
            cell,
            charter,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `propose(proposal_hash)`** — DRAFT → PROPOSED: stage the action
    /// hash (`WriteOnce`, admitted from zero on this first turn) and publish the
    /// charter's membership commitment. Routes through the verified DFA, cap-gates
    /// on `Signature`, and desugars to [`propose_effects`].
    pub fn propose(
        &self,
        cipherclerk: &AppCipherclerk,
        proposal_hash: FieldElement,
        authority: InvokeAuthority,
    ) -> Result<Turn, CouncilServiceError> {
        let effects = propose_effects(self.cell, proposal_hash, self.charter.members_commitment());
        self.invoke(
            cipherclerk,
            METHOD_PROPOSE,
            vec![proposal_hash],
            effects,
            authority,
        )
    }

    /// **Invoke `approve(member_index, running_count)`** — flip member
    /// `member_index`'s approval bit, carrying the running approval count for the
    /// AX5 reactor. A member index outside the charter is refused before any turn
    /// is built. Desugars to [`approve_effects`]; the executor re-enforces the
    /// `Monotonic` / `{0,1}` / `BoundedBy` approval-slot teeth.
    pub fn approve(
        &self,
        cipherclerk: &AppCipherclerk,
        member_index: usize,
        running_count: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, CouncilServiceError> {
        if member_index >= self.charter.members.len() {
            return Err(CouncilServiceError::BadMember {
                index: member_index,
                members: self.charter.members.len(),
            });
        }
        let effects = approve_effects(self.cell, member_index, running_count);
        self.invoke(
            cipherclerk,
            METHOD_APPROVE,
            vec![
                field_from_u64(member_index as u64),
                field_from_u64(running_count),
            ],
            effects,
            authority,
        )
    }

    /// **Invoke `certify()`** — PROPOSED → APPROVED: arm the threshold flag. A
    /// certify with too few approvals is an executor refusal (`AffineLe`).
    /// Desugars to [`certify_effects`] — the SAME body the reactor's auto-certify
    /// reaction produces.
    pub fn certify(
        &self,
        cipherclerk: &AppCipherclerk,
        authority: InvokeAuthority,
    ) -> Result<Turn, CouncilServiceError> {
        let effects = certify_effects(self.cell);
        self.invoke(cipherclerk, METHOD_CERTIFY, vec![], effects, authority)
    }

    /// **Invoke `reject()`** — PROPOSED → REJECTED (terminal). Desugars to
    /// [`reject_effects`].
    pub fn reject(
        &self,
        cipherclerk: &AppCipherclerk,
        authority: InvokeAuthority,
    ) -> Result<Turn, CouncilServiceError> {
        let effects = reject_effects(self.cell);
        self.invoke(cipherclerk, METHOD_REJECT, vec![], effects, authority)
    }

    /// **Invoke `execute()`** — APPROVED → EXECUTED (terminal). A re-execute is a
    /// no-row `AllowedTransitions` refusal. Desugars to [`execute_effects`].
    pub fn execute(
        &self,
        cipherclerk: &AppCipherclerk,
        authority: InvokeAuthority,
    ) -> Result<Turn, CouncilServiceError> {
        let effects = execute_effects(self.cell);
        self.invoke(cipherclerk, METHOD_EXECUTE, vec![], effects, authority)
    }

    /// **Attempt to invoke `view()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `view` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read (the proposal's committed machine), not
    /// a replay desugar. This method exists to make the seam legible (and
    /// testable): a serviced read is not a turn, and `invoke()` will not pretend
    /// otherwise. To actually READ the council, decode the committed state via
    /// [`council::inspect_council`].
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, CouncilServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door
    /// against this council's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, CouncilServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(CouncilServiceError::Refused)
    }
}

/// **Seed a council proposal cell for the SERVICE / REACTOR runtime faces** —
/// install the canonical [`council_service_program`] on the executor's agent
/// cell. A factory-born proposal cell mints empty (all-zero = DRAFT, the council
/// birth state), so no genesis state write is needed: the cell is a real DRAFT
/// baseline against which `propose` opens a proposal, `approve` advances the
/// tally, and `certify` / `execute` carry it through.
pub fn seed_council(executor: &EmbeddedExecutor, charter: &CouncilCharter) {
    let cell = executor.cell_id();
    executor.install_program(cell, council_service_program(charter));
}

/// Why a [`CouncilService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CouncilServiceError {
    /// A member index outside the charter's membership — fail-closed before any
    /// turn is built.
    BadMember {
        /// The out-of-range index.
        index: usize,
        /// The charter's membership size.
        members: usize,
    },
    /// The `invoke()` front door refused (unknown method, insufficient authority,
    /// or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for CouncilServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CouncilServiceError::BadMember { index, members } => {
                write!(f, "member index {index} out of range ({members} members)")
            }
            CouncilServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for CouncilServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    fn charter_2of3() -> CouncilCharter {
        CouncilCharter::new(
            vec![
                CellId::from_bytes([0x11; 32]),
                CellId::from_bytes([0x22; 32]),
                CellId::from_bytes([0x33; 32]),
            ],
            2,
        )
    }

    #[test]
    fn interface_publishes_six_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 6);
        assert!(iface.verify_id());

        for m in [
            METHOD_PROPOSE,
            METHOD_APPROVE,
            METHOD_CERTIFY,
            METHOD_REJECT,
            METHOD_EXECUTE,
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

    /// THE DRIVEN AGREEMENT CHECK (the anti-mirror canary): the runtime face installs the
    /// IDENTICAL program the factory bakes into a factory-born proposal cell — because it
    /// RETURNS it verbatim, not a re-authored copy. Canary: re-author
    /// `council_service_program` to any divergent program (a dropped or added constraint)
    /// and this equality goes RED.
    #[test]
    fn the_service_program_is_the_canonical_council_program() {
        let c = charter_2of3();
        assert_eq!(
            council_service_program(&c),
            council::council_cell_program(&c).unwrap()
        );
    }

    #[test]
    fn a_bad_member_index_is_rejected_before_any_turn() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = CouncilService::new(cclerk.cell_id(), charter_2of3());
        assert!(matches!(
            svc.approve(&cclerk, 9, 1, InvokeAuthority::Signature),
            Err(CouncilServiceError::BadMember {
                index: 9,
                members: 3
            })
        ));
    }

    #[test]
    fn unauthorized_certify_refused_at_the_front_door() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = CouncilService::new(cclerk.cell_id(), charter_2of3());
        // `certify` needs `Signature`; a `None` holder is refused before any turn.
        assert!(matches!(
            svc.certify(&cclerk, InvokeAuthority::None),
            Err(CouncilServiceError::Refused(
                InvokeRefused::Unauthorized { .. }
            ))
        ));
    }

    #[test]
    fn view_is_a_serviced_seam_never_desugared() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = CouncilService::new(cclerk.cell_id(), charter_2of3());
        assert!(matches!(
            svc.view(&cclerk),
            Err(CouncilServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }
}
