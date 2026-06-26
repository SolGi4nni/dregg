//! # governed-namespace — the governance lifecycle as a SERVICE CELL on the
//! `invoke()` front door.
//!
//! The third axis (AX3) of a modern starbridge-app: the propose → vote → commit
//! governance lifecycle re-expressed as a CELLS-AS-SERVICE-OBJECTS citizen (after
//! the `bounty-board` / `subscription` exemplars). A new `service` module on the
//! existing crate: it publishes a first-class, typed [`InterfaceDescriptor`] and
//! drives the lifecycle through the [`dregg_app_framework::invoke`] front door —
//! the userspace method-dispatch layer that sits *slightly above* the effect-VM and
//! desugars a method call to the ordinary verified effects it names. There is **no
//! `Effect::Invoke`**, no kernel change, no new circuit rung: the kernel and the
//! light client keep seeing only the
//! [`SetField`](dregg_app_framework::Effect::SetField) /
//! [`EmitEvent`](dregg_app_framework::Effect::EmitEvent) effects they already
//! enforce and witness. The one extra fact — that an invoked method is a member of
//! the cell's interface — is decided by the SAME verified DFA router
//! ([`InterfaceDescriptor::route_method`]) the protocol already uses.
//!
//! ## Which program backs the runtime faces
//!
//! The service installs/assumes [`governance_service_program`] — the FLAT
//! constitutional invariants the [`crate::governance_factory_descriptor`] bakes
//! into its `state_constraints` (`WriteOnce` committee-root/threshold, `Monotonic`
//! version/dispute-window, `Immutable` reserved slots). This is literally the
//! descriptor's own `state_constraints` lifted into a [`CellProgram::Predicate`], so
//! the service face can never diverge from the constructor contract the factory
//! commits to.
//!
//! The full operation-scoped [`crate::governance_program`] `Cases` shape (which adds
//! the per-method `SenderAuthorized` committee membership and the
//! `commit_table_update` `Authorization::Custom` threshold-sig) is the AIR-bound AX1
//! program pinned by the child VK in the factory descriptor. The runtime faces stay
//! on the flat invariants so they are end-to-end testable without wrestling
//! `SenderAuthorized` Merkle roots — and so a `version` ROLLBACK (`Monotonic`) and a
//! committee/threshold REBIND (`WriteOnce`) still bite as real executor refusals on
//! every invoke-desugared turn.
//!
//! ## The published interface (the lifecycle as typed methods)
//!
//! | method                 | semantics                | auth        | args                          |
//! |------------------------|--------------------------|-------------|-------------------------------|
//! | `propose_table_update` | [`Semantics::Replayable`]| `Signature` | `(proposed_root, window)`     |
//! | `vote_on_proposal`     | [`Semantics::Replayable`]| `Signature` | `(tally, proposed_root, ver)` |
//! | `commit_table_update`  | [`Semantics::Replayable`]| `Signature` | `(new_root, new_version)`     |
//! | `register_service`     | [`Semantics::Replayable`]| `Signature` | `(path_hash, target)`         |
//! | `view`                 | [`Semantics::Serviced`]  | `None`      | `()`                          |
//!
//! The four mutators are **replayable**: they desugar (via `invoke()`) to a verified
//! turn whose post-state the executor checks against [`governance_service_program`].
//! `view` is **serviced**: the namespace cell's committed state (live route-table
//! root + version) IS the answer (it rides the OFE cross-cell-read), so `invoke()`
//! refuses to desugar it and names the seam honestly rather than faking a write.
//!
//! The method symbols are the SAME strings the executor's `MethodIs`-guarded cases
//! and the deos surface key off (`propose_table_update`, …), so the card (AX4), the
//! service (AX3), and the reactor (AX5) all speak the one lifecycle.

use dregg_app_framework::{
    AppCipherclerk, CellId, Effect, Event, FieldElement, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, Turn, field_from_bytes, field_from_u64, invoke_with_descriptor, symbol,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::program::CellProgram;

use crate::{
    DISPUTE_WINDOW_HEIGHT_SLOT, PENDING_PROPOSAL_ROOT_SLOT, ROUTE_TABLE_ROOT_SLOT, VERSION_SLOT,
    cell_id_field, governance_factory_descriptor,
};

// =============================================================================
// Method names
// =============================================================================

/// The `propose_table_update` method — a [`Semantics::Replayable`],
/// `Signature`-gated mutator: a committee member opens a proposal (push the
/// dispute window forward, reset the vote tally).
pub const METHOD_PROPOSE: &str = "propose_table_update";
/// The `vote_on_proposal` method — a [`Semantics::Replayable`], `Signature`-gated
/// mutator: a committee member tallies a vote (advance the running count, carry
/// the proposed root + target version for the auto-committer).
pub const METHOD_VOTE: &str = "vote_on_proposal";
/// The `commit_table_update` method — a [`Semantics::Replayable`],
/// `Signature`-gated mutator: enact the swap (`route_table_root := new_root`,
/// `version := new_version`, clear the tally).
pub const METHOD_COMMIT: &str = "commit_table_update";
/// The `register_service` method — a [`Semantics::Replayable`], `Signature`-gated
/// mutator: publish a service mount under the live route table (event-bearing
/// only; freezes every governance slot).
pub const METHOD_REGISTER: &str = "register_service";
/// The `view` method — a [`Semantics::Serviced`] read (the named OFE seam): read
/// the namespace's committed route-table root + version. Never desugared.
pub const METHOD_VIEW: &str = "view";

// =============================================================================
// The cell program the runtime faces install (the descriptor's own invariants)
// =============================================================================

/// The cell program the governed-namespace SERVICE face installs/assumes — the
/// FLAT constitutional invariants the [`crate::governance_factory_descriptor`]
/// bakes into its `state_constraints`, lifted into a [`CellProgram::Predicate`].
///
/// Reading the descriptor's own field guarantees the service face cannot diverge
/// from the constructor contract: `WriteOnce` committee-root/threshold, `Monotonic`
/// version/dispute-window, `Immutable` reserved slots all re-enforce on every
/// invoke-desugared turn. The full operation-scoped [`crate::governance_program`]
/// `Cases` (the `SenderAuthorized` + `Authorization::Custom` shape) is the AIR-bound
/// AX1 program pinned by the child VK; see the module docs.
pub fn governance_service_program() -> CellProgram {
    CellProgram::Predicate(governance_factory_descriptor().state_constraints)
}

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The governed-namespace's first-class typed interface** — the five methods it
/// publishes, with their auth and replayable-vs-serviced semantics.
///
/// This is the richer-than-derived descriptor: `derive_replayable` would make every
/// method `Replayable`/`None`, but the namespace wants its four mutators
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
        // propose_table_update(proposed_root, dispute_window): open a proposal.
        mutator(METHOD_PROPOSE, 2),
        // vote_on_proposal(tally, proposed_root, new_version): tally a vote.
        mutator(METHOD_VOTE, 3),
        // commit_table_update(new_root, new_version): enact the swap.
        mutator(METHOD_COMMIT, 2),
        // register_service(path_hash, target): publish a service mount.
        mutator(METHOD_REGISTER, 2),
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// Register the namespace's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults before
/// falling back to derive-from-program. After this, the explorer resolves the
/// namespace's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// Effect bodies (shared by the service handle AND the reactor)
// =============================================================================

/// **`propose` effects** — open a proposal: push `DISPUTE_WINDOW_HEIGHT` forward
/// (`Monotonic`), reset the running vote tally in `PENDING_PROPOSAL_ROOT` to zero,
/// and emit `proposal-opened` carrying the proposed route-table root + window.
pub fn propose_effects(
    cell: CellId,
    proposed_root: FieldElement,
    dispute_window: u64,
) -> Vec<Effect> {
    let window_f = field_from_u64(dispute_window);
    vec![
        Effect::SetField {
            cell,
            index: DISPUTE_WINDOW_HEIGHT_SLOT as usize,
            value: window_f,
        },
        Effect::SetField {
            cell,
            index: PENDING_PROPOSAL_ROOT_SLOT as usize,
            value: field_from_u64(0),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("proposal-opened"), vec![proposed_root, window_f]),
        },
    ]
}

/// **`vote` effects** — tally a vote: write the new running count `new_tally` into
/// `PENDING_PROPOSAL_ROOT` (the quorum counter the reactor reads), and emit
/// `vote-cast` carrying `[tally, proposed_root, new_version]` so the auto-committer
/// (the AX5 [`crate::reactor`]) can enact the swap straight off the observed turn.
pub fn vote_effects(
    cell: CellId,
    new_tally: u64,
    proposed_root: FieldElement,
    new_version: u64,
) -> Vec<Effect> {
    let tally_f = field_from_u64(new_tally);
    vec![
        Effect::SetField {
            cell,
            index: PENDING_PROPOSAL_ROOT_SLOT as usize,
            value: tally_f,
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(
                symbol("vote-cast"),
                vec![tally_f, proposed_root, field_from_u64(new_version)],
            ),
        },
    ]
}

/// **`commit` effects** — the atomic swap: `route_table_root := new_root`,
/// `version := new_version` (`Monotonic`, the swap's whole point is to bump it),
/// clear the tally in `PENDING_PROPOSAL_ROOT`, and emit `table-committed`. This is
/// the ONE coherent transition both the service [`GovernanceService::commit`] AND
/// the reactor's [`crate::reactor`] reaction desugar to — so the kernel / circuit
/// see only what they already know, and the executor re-enforces the invariants.
pub fn commit_effects(cell: CellId, new_root: FieldElement, new_version: u64) -> Vec<Effect> {
    let version_f = field_from_u64(new_version);
    vec![
        Effect::SetField {
            cell,
            index: ROUTE_TABLE_ROOT_SLOT as usize,
            value: new_root,
        },
        Effect::SetField {
            cell,
            index: VERSION_SLOT as usize,
            value: version_f,
        },
        Effect::SetField {
            cell,
            index: PENDING_PROPOSAL_ROOT_SLOT as usize,
            value: [0u8; 32],
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("table-committed"), vec![new_root, version_f]),
        },
    ]
}

/// **`register_service` effects** — publish a service mount: a single
/// `service-registered` event carrying `[path_hash, target_cell]`. Event-bearing
/// only; the namespace's governance slots are untouched.
pub fn register_effects(cell: CellId, path: &str, target: CellId) -> Vec<Effect> {
    vec![Effect::EmitEvent {
        cell,
        event: Event::new(
            symbol("service-registered"),
            vec![field_from_bytes(path.as_bytes()), cell_id_field(target)],
        ),
    }]
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed governed-namespace cell** — bundles the namespace cell
/// with its published interface, and builds method invocations through the
/// `invoke()` front door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it through
/// an executor ([`dregg_app_framework::EmbeddedExecutor::submit_turn`], a node
/// `/turns/submit`, …) to actually commit. A refusal at the front door (unknown
/// method, insufficient authority, a serviced seam) is surfaced as an
/// [`InvokeRefused`] before any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct GovernanceService {
    /// The namespace cell this handle drives.
    pub cell: CellId,
    /// The namespace's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl GovernanceService {
    /// A handle to the namespace cell `cell`, carrying the namespace's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        GovernanceService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `propose_table_update(proposed_root, dispute_window)`** — open a
    /// proposal: push the dispute window forward (`Monotonic`) and reset the vote
    /// tally. Routes through the verified DFA, cap-gates on `Signature`, and
    /// desugars to [`propose_effects`].
    pub fn propose(
        &self,
        cipherclerk: &AppCipherclerk,
        proposed_root: FieldElement,
        dispute_window: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, GovernanceServiceError> {
        let effects = propose_effects(self.cell, proposed_root, dispute_window);
        self.invoke(
            cipherclerk,
            METHOD_PROPOSE,
            vec![proposed_root, field_from_u64(dispute_window)],
            effects,
            authority,
        )
    }

    /// **Invoke `vote_on_proposal(new_tally, proposed_root, new_version)`** — tally
    /// a vote: write the running count and carry the proposed root + target version
    /// so the AX5 reactor can auto-commit once the count crosses quorum. Desugars to
    /// [`vote_effects`].
    pub fn vote(
        &self,
        cipherclerk: &AppCipherclerk,
        new_tally: u64,
        proposed_root: FieldElement,
        new_version: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, GovernanceServiceError> {
        let effects = vote_effects(self.cell, new_tally, proposed_root, new_version);
        self.invoke(
            cipherclerk,
            METHOD_VOTE,
            vec![
                field_from_u64(new_tally),
                proposed_root,
                field_from_u64(new_version),
            ],
            effects,
            authority,
        )
    }

    /// **Invoke `commit_table_update(new_root, new_version)`** — enact the atomic
    /// swap. A no-advance / rewound `new_version` is an executor refusal
    /// (`Monotonic(VERSION)`). Desugars to [`commit_effects`] — the SAME body the
    /// reactor's auto-commit reaction produces.
    pub fn commit(
        &self,
        cipherclerk: &AppCipherclerk,
        new_root: FieldElement,
        new_version: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, GovernanceServiceError> {
        let effects = commit_effects(self.cell, new_root, new_version);
        self.invoke(
            cipherclerk,
            METHOD_COMMIT,
            vec![new_root, field_from_u64(new_version)],
            effects,
            authority,
        )
    }

    /// **Invoke `register_service(path, target)`** — publish a service mount under
    /// the live route table (event-bearing). Desugars to [`register_effects`].
    pub fn register_service(
        &self,
        cipherclerk: &AppCipherclerk,
        path: &str,
        target: CellId,
        authority: InvokeAuthority,
    ) -> Result<Turn, GovernanceServiceError> {
        if path.is_empty() {
            return Err(GovernanceServiceError::EmptyField);
        }
        let effects = register_effects(self.cell, path, target);
        self.invoke(
            cipherclerk,
            METHOD_REGISTER,
            vec![field_from_bytes(path.as_bytes()), cell_id_field(target)],
            effects,
            authority,
        )
    }

    /// **Attempt to invoke `view()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `view` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read (the namespace's committed route-table
    /// root + version), not a replay desugar. This method exists to make the seam
    /// legible (and testable): a serviced read is not a turn, and `invoke()` will
    /// not pretend otherwise. To actually READ the namespace, read the committed
    /// state at its slots ([`crate::ROUTE_TABLE_ROOT_SLOT`], …).
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, GovernanceServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door against
    /// this namespace's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, GovernanceServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(GovernanceServiceError::Refused)
    }
}

/// **Seed a namespace cell for the SERVICE / REACTOR runtime faces** — install
/// [`governance_service_program`] (the descriptor's own flat invariants) and bind a
/// quiescent constitutional genesis directly into the embedded ledger: committee
/// root + `threshold` (`WriteOnce`, frozen after), `version`, `route_table_root`,
/// `pending_proposal_root := 0` (no tally yet), `dispute_window := 0`.
///
/// After seeding, the board is a real `(old, new)` baseline against which `propose`
/// opens a proposal, `vote` advances the tally, and `commit` swaps the table.
/// Returns the seeded `version`.
pub fn seed_namespace(
    executor: &dregg_app_framework::EmbeddedExecutor,
    threshold: u64,
    version: u64,
    route_table_root: FieldElement,
) -> u64 {
    use crate::{GOVERNANCE_COMMITTEE_ROOT_SLOT, THRESHOLD_SLOT};
    let cell = executor.cell_id();
    executor.install_program(cell, governance_service_program());
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state.set_field(
                GOVERNANCE_COMMITTEE_ROOT_SLOT as usize,
                field_from_bytes(b"committee-v0"),
            );
            c.state
                .set_field(THRESHOLD_SLOT as usize, field_from_u64(threshold));
            c.state
                .set_field(VERSION_SLOT as usize, field_from_u64(version));
            c.state
                .set_field(ROUTE_TABLE_ROOT_SLOT as usize, route_table_root);
            c.state
                .set_field(PENDING_PROPOSAL_ROOT_SLOT as usize, field_from_u64(0));
            c.state
                .set_field(DISPUTE_WINDOW_HEIGHT_SLOT as usize, field_from_u64(0));
        }
    });
    version
}

/// Why a [`GovernanceService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GovernanceServiceError {
    /// A required text field (the registration path) was empty.
    EmptyField,
    /// The `invoke()` front door refused (unknown method, insufficient authority,
    /// or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for GovernanceServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GovernanceServiceError::EmptyField => {
                write!(f, "a required text field must be non-empty")
            }
            GovernanceServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for GovernanceServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    #[test]
    fn interface_publishes_five_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 5);
        assert!(iface.verify_id());

        for m in [METHOD_PROPOSE, METHOD_VOTE, METHOD_COMMIT, METHOD_REGISTER] {
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
    fn the_published_interface_names_the_lifecycle_vocabulary() {
        let iface = interface_descriptor();
        for m in [
            METHOD_PROPOSE,
            METHOD_VOTE,
            METHOD_COMMIT,
            METHOD_REGISTER,
            METHOD_VIEW,
        ] {
            assert!(iface.method(&method_symbol(m)).is_some(), "{m} published");
        }
    }

    #[test]
    fn the_service_program_is_the_descriptors_own_invariants() {
        // Non-divergence: the runtime face's program is LITERALLY the descriptor's
        // baked `state_constraints` — it cannot drift from the constructor contract.
        let prog = governance_service_program();
        match prog {
            CellProgram::Predicate(cs) => {
                assert_eq!(cs, governance_factory_descriptor().state_constraints);
            }
            other => panic!("expected Predicate, got {other:?}"),
        }
    }

    #[test]
    fn empty_registration_path_rejected_before_any_turn() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = GovernanceService::new(cclerk.cell_id());
        assert!(matches!(
            svc.register_service(&cclerk, "", cclerk.cell_id(), InvokeAuthority::Signature),
            Err(GovernanceServiceError::EmptyField)
        ));
    }

    #[test]
    fn unauthorized_commit_refused_at_the_front_door() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = GovernanceService::new(cclerk.cell_id());
        // `commit` needs `Signature`; a `None` holder is refused before any turn.
        assert!(matches!(
            svc.commit(
                &cclerk,
                field_from_bytes(b"new-table"),
                2,
                InvokeAuthority::None
            ),
            Err(GovernanceServiceError::Refused(
                InvokeRefused::Unauthorized { .. }
            ))
        ));
    }

    #[test]
    fn view_is_a_serviced_seam_never_desugared() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = GovernanceService::new(cclerk.cell_id());
        assert!(matches!(
            svc.view(&cclerk),
            Err(GovernanceServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }
}
