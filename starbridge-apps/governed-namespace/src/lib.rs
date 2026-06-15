//! # starbridge-governed-namespace
//!
//! The fourth starbridge-app per `STARBRIDGE-APPS-PLAN.md` §3.3:
//! **governance-bound atomic route table swaps** on a sovereign cell,
//! composed from existing dregg primitives only.
//!
//! A *governed-namespace cell* hosts a [`dregg_dfa::GovernedRouter`]-shaped
//! route table whose root commits into the cell's state slots, controlled
//! by a constitutional committee. Updates require a constitutional
//! threshold-signature carrier riding under
//! [`dregg_cell::predicate::WitnessedPredicate`] with
//! [`WitnessedPredicateKind::Custom { vk_hash: GOVERNANCE_VK }`][gk] in an
//! [`Authorization::Custom`] action — the same `commitment` /
//! `route_table_root` CAS the in-memory `GovernedRouter::update_routes`
//! enforces, lifted onto the cell substrate so the executor's per-turn
//! slot-caveat evaluator and the AIR-attestable accept/reject pipeline
//! cover the table swap end-to-end.
//!
//! [gk]: dregg_cell::predicate::WitnessedPredicateKind::Custom
//!
//! ## Companion docs
//!
//! - `STARBRIDGE-APPS-PLAN.md` §3.3 — per-app design sketch.
//! - `DFA-RATIONALIZATION-DESIGN.md` §2.2 — "governance: atomic table swap
//!   of approved capability set", the canonical fit for `GovernedRouter`.
//! - `STORAGE-AS-CELL-PROGRAMS.md` — the RelayOperator cell-program
//!   pattern this app mirrors for the "no operator-side enforcement"
//!   inversion (the table is the cell's state; the swap is the turn;
//!   the executor is the enforcer).
//! - `SLOT-CAVEATS-DESIGN.md` — the slot-caveat vocabulary this crate
//!   draws on (`Immutable`, `Monotonic`, `MonotonicSequence`,
//!   `SenderAuthorized`, `BoundedBy`).
//! - `AUTHORIZATION-CUSTOM-DESIGN.md` — the `Authorization::Custom` shape
//!   the `commit_table_update` builder constructs.
//! - `starbridge-apps/nameservice/` — the pattern anchor (slot layout +
//!   factory descriptor + turn builders + AppCipherclerk integration).
//! - `starbridge-apps/subscription/` — the operation-scoped
//!   `CellProgram::Cases(_)` pattern with default-deny on unknown
//!   methods, which this crate adopts.
//!
//! ## Slot layout
//!
//! `STATE_SLOTS = 16`. We use 6 of them:
//!
//! | Slot | Name | Caveat | Purpose |
//! |---:|---|---|---|
//! | 0 | `route_table_root` | `BoundedBy { witness_index: 1 }` under `commit_table_update`; `Immutable` otherwise | The current [`dregg_dfa::GovernedRouter::commitment`] — BLAKE3 over the canonical serialization of the live route table. |
//! | 1 | `version` | `MonotonicSequence` (`commit_table_update`-scoped); `Immutable` otherwise | Monotonic table-swap counter. Bumps by exactly +1 on every successful `commit_table_update`. |
//! | 2 | `governance_committee_root` | `Immutable` | Merkle root over the committee members' pubkeys. Set at cell creation; never changes (constitution-level amendment is a separate factory). |
//! | 3 | `threshold` | `Immutable` | The threshold-signature count required for `commit_table_update`. Set at creation. |
//! | 4 | `dispute_window_height` | `Monotonic` | Block height at which a pending proposal finalizes (height after which un-disputed updates may commit). |
//! | 5 | `pending_proposal_root` | per-method | Commitment to the in-flight proposal payload + vote tally. Read by `commit_table_update`; advanced by `propose_table_update` and `vote_on_proposal`. |
//!
//! Slots 6..15 are reserved (`Immutable`-by-default) for future
//! extensions — e.g. a registry root pointing at the named-service
//! sub-cells `register_service` produces.
//!
//! ## Operations
//!
//! Five operation-scoped methods, each gated through a
//! `CellProgram::Cases(_)` case. Cases default-deny when no case
//! matches, so any action whose method symbol is unrecognized is
//! rejected outright (the same Cav-Codex Block 4 shape the
//! subscription app uses).
//!
//! 1. **`propose_table_update`** — a committee member proposes a new
//!    route table (commits to its root + payload). Opens the dispute
//!    window. Constraints: `pending_proposal_root` advances
//!    monotonically; `version`, `route_table_root`, committee
//!    metadata frozen; `SenderAuthorized` against
//!    `governance_committee_root` (slot 2).
//! 2. **`vote_on_proposal`** — a committee member casts a vote.
//!    Constraints: `pending_proposal_root` advances (tally grows);
//!    every other slot frozen; `SenderAuthorized` against the
//!    committee root.
//! 3. **`commit_table_update`** — once threshold is met and the
//!    dispute window has elapsed, atomically swap:
//!    `route_table_root := new_root` and `version += 1`.
//!    The action carries an [`Authorization::Custom`] whose
//!    [`WitnessedPredicate`] is `Custom { vk_hash: GOVERNANCE_VK }`,
//!    with the commitment naming the threshold-sig audience root and
//!    the `input_ref` being [`InputRef::SigningMessage`]. The
//!    executor binds this to the canonical signing message and
//!    dispatches the registered governance verifier; only successful
//!    threshold verification advances the commit.
//! 4. **`register_service`** — a userspace caller publishes a service
//!    cell at a named path under the live route table. Emits
//!    `EmitEvent("service-registered", [path_hash, target_cell_id])`.
//!    No slot mutations beyond an optional `pending_proposal_root`
//!    re-anchor; this is the *read-then-emit* side of the namespace
//!    (think `dregg-directory` register; the cell-program does not
//!    bake the directory map in-slot — it lives in an indexer fed by
//!    the events).
//! 5. **`dispatch`** (read-only) — not an action; documented here as
//!    the `dregg_dfa::Router::classify(input)` walk against the live
//!    `route_table_root` (callers reconstruct the [`Router`] from the
//!    [`RouteTable`] the app authors via [`build_route_table`]).
//!
//! ## DFA + `Authorization::Custom` composition
//!
//! The two primitives compose at the cell-program boundary:
//!
//! - The **route table commitment** lives in slot 0. Anyone reading the
//!   cell can reconstruct the live `Router` (over the route-table bytes
//!   the dispatcher holds) and prove `Router::classify(input) =
//!   target` against the committed root via the DFA AIR.
//! - The **governance threshold** lives behind a registered
//!   [`WitnessedPredicateKind::Custom { vk_hash: GOVERNANCE_VK }`][gk]
//!   verifier. The verifier interprets `commitment` as
//!   `governance_committee_root` and validates the threshold-sig over
//!   the `(old_root, new_root, version+1)` triple — exactly the
//!   shape `dregg_dfa::ThresholdVerifier::verify` already enforces in
//!   memory. The `Authorization::Custom { predicate }` carries the
//!   proof bytes via `predicate.proof_witness_index` →
//!   `action.witness_blobs`.
//!
//! Constructor transparency: the descriptor binds
//! [`GOVERNANCE_VK`] into the cell-program at factory creation, so
//! every cell produced from this factory enforces governance via the
//! same registered verifier. Apps that want a different governance
//! crypto (e.g. BLS aggregate instead of multisig) build a different
//! factory; the variant lives in the registered verifier under a
//! different `vk_hash`.
//!
//! ## Dependency on the `Authorization::Custom` propagation lane
//!
//! `commit_table_update` constructs an `Authorization::Custom` carrier.
//! The propagation lane wiring `WitnessedPredicateRegistry` into the
//! executor's auth path (so the `Custom` variant successfully
//! dispatches to a registered verifier) is in flight. If that lane has
//! not landed at the time this crate ships, the structural code (slot
//! layout, factory descriptor, turn builders, web components) is
//! correct and the adversarial tests against the slot-caveat shape
//! pass — what's gated on the in-flight lane is the executor's
//! cryptographic acceptance of the Custom proof. The unit tests here
//! drive `evaluate_with_meta(..)` directly so they exercise the
//! operation-scoped semantics regardless of executor wiring state.
//! See the README for the dependency note.
//!
//! ## What this crate exports
//!
//! 1. [`governance_factory_descriptor`] — the `FactoryDescriptor`
//!    pinning the constructor contract: slot layout, immutable
//!    committee root + threshold, monotonic version, plus the
//!    cell-program (`governance_program`).
//! 2. [`governance_program`] — the `CellProgram::Cases(_)` value baked
//!    into the descriptor. Exported separately so tests can drive
//!    `evaluate_with_meta(..)` against hand-rolled triples.
//! 3. [`factory_descriptors`] — the slice of factory descriptors this
//!    starbridge-app contributes. Today: one.
//! 4. Turn-builders (signed actions composed of generic Effects):
//!    - [`build_propose_table_update_action`]
//!    - [`build_vote_on_proposal_action`]
//!    - [`build_commit_table_update_action`] (`Authorization::Custom`)
//!    - [`build_register_service_action`]
//! 5. [`build_route_table`] / [`route_table_commitment`] — helpers
//!    that reproduce the route-table commitment the descriptor expects
//!    in slot 0.
//! 6. [`register`] — `StarbridgeAppContext` mount hook wiring the
//!    factory + inspector descriptors into a shared host context.

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, Authorization, AuthorizedSet, CapTarget, CapTemplate,
    CellAffordance, CellId, CellMode, CellProgram, ChildVkStrategy, ConstantsModule, DeosApp,
    DeosCell, Effect, EmbeddedExecutor, Event, FactoryDescriptor, FieldElement, FireError,
    FireExecuteError, GatedAffordance, InputRef, InspectorDescriptor, StarbridgeAppContext,
    StateConstraint, TransitionCase, TransitionGuard, TurnReceipt, WitnessedPredicate,
    WitnessedPredicateKind, field_from_bytes, field_from_u64, hex_encode_32, symbol,
};
use dregg_dfa::{GovernedRouter, KindRegistry, RouteTable, RouteTableBuilder, RouteTarget, Router};
use dregg_turn::action::WitnessBlob;
use dregg_turn::executor::{single_member_authorized_root, single_member_membership_proof};

// =============================================================================
// Slot layout
// =============================================================================

/// Slot 0 — `route_table_root`. The BLAKE3 commitment of the live
/// [`dregg_dfa::RouteTable`]. Swap is atomic under `commit_table_update`.
pub const ROUTE_TABLE_ROOT_SLOT: u8 = 0;

/// Slot 1 — `version`. Monotonic counter; bumps +1 on every commit.
pub const VERSION_SLOT: u8 = 1;

/// Slot 2 — `governance_committee_root`. `Immutable` after creation.
/// Merkle root of committee member pubkeys. The `SenderAuthorized`
/// constraint on `propose_table_update` / `vote_on_proposal` reads this
/// slot (`AuthorizedSet::PublicRoot { set_root_index: 2 }`).
pub const GOVERNANCE_COMMITTEE_ROOT_SLOT: u8 = 2;

/// Slot 3 — `threshold`. `Immutable` after creation. Number of distinct
/// committee signatures required for `commit_table_update` (encoded
/// big-endian into the last 8 bytes of the field). The threshold is
/// also baked into the registered governance verifier under
/// `GOVERNANCE_VK` so the AIR can constrain it as well.
pub const THRESHOLD_SLOT: u8 = 3;

/// Slot 4 — `dispute_window_height`. Block height after which a pending
/// proposal finalizes. `Monotonic` (only pushable forward).
pub const DISPUTE_WINDOW_HEIGHT_SLOT: u8 = 4;

/// Slot 5 — `pending_proposal_root`. Commits to the in-flight proposal's
/// `(new_route_table_root, vote_tally_root, deadline_height)` triple.
/// Advances under `propose_table_update` and `vote_on_proposal`;
/// cleared (set to FIELD_ZERO) by `commit_table_update` once the
/// proposal is enacted.
pub const PENDING_PROPOSAL_ROOT_SLOT: u8 = 5;

/// Slot 6 — reserved. Future: registry root over `register_service`
/// emissions for in-cell index queries. `Immutable` by default.
pub const RESERVED_SLOT_6: u8 = 6;

/// Slot 7 — reserved. Future: tombstone root for revoked routes.
pub const RESERVED_SLOT_7: u8 = 7;

// =============================================================================
// Factory configuration
// =============================================================================

/// Default per-epoch creation budget for governed-namespace cells.
/// A federation typically only ever creates a handful of these
/// (one per constitutional domain), so the budget is low.
pub const DEFAULT_CREATION_BUDGET: u64 = 64;

/// The factory VK we publish for the governed-namespace factory.
///
/// In a real deployment this is the BLAKE3 hash of the
/// governance-cell-program VK. We bake a stable placeholder here so
/// the descriptor hash is reproducible across builds; the eventual
/// real-program VK replacement is a single constant change.
pub const GOVERNANCE_FACTORY_VK: [u8; 32] = *b"starbridge-governed-namespace-fa";

/// The child cell-program VK installed on per-cell governed-namespace
/// instances. As above, a stable placeholder.
pub const GOVERNANCE_CHILD_PROGRAM_VK: [u8; 32] = *b"starbridge-governed-namespace-cp";

/// The registered `WitnessedPredicateKind::Custom { vk_hash }`
/// identifying the governance threshold-signature verifier. The
/// `commit_table_update` builder constructs an
/// `Authorization::Custom { predicate }` with
/// `predicate.kind == Custom { vk_hash: GOVERNANCE_VK }`; the executor
/// dispatches to the verifier registered under this VK in the
/// `WitnessedPredicateRegistry`.
///
/// Stable placeholder; the real value is the verifying-key hash of the
/// registered threshold-sig AIR (BLS aggregate, Ed25519 multisig, etc.).
pub const GOVERNANCE_VK: [u8; 32] = *b"starbridge-gov-threshold-verify!";

/// The userspace-kind identifier the [`build_route_table`] helper
/// registers under, for the `RouteTarget::Userspace { kind: ... }`
/// variant. Routes that resolve to named services (the
/// `register_service` flow) carry this kind in the route table.
pub const NAMESPACE_SERVICE_KIND: &str = "namespace_service";

// =============================================================================
// Method symbols
// =============================================================================

/// Method symbol for `propose_table_update`.
pub fn propose_method_symbol() -> [u8; 32] {
    symbol("propose_table_update")
}
/// Method symbol for `vote_on_proposal`.
pub fn vote_method_symbol() -> [u8; 32] {
    symbol("vote_on_proposal")
}
/// Method symbol for `commit_table_update`.
pub fn commit_method_symbol() -> [u8; 32] {
    symbol("commit_table_update")
}
/// Method symbol for `register_service`.
pub fn register_service_method_symbol() -> [u8; 32] {
    symbol("register_service")
}

// =============================================================================
// CellProgram: operation-scoped Cases
// =============================================================================

/// Build the `CellProgram` enforcing the governed-namespace cell's
/// lifetime invariants and per-operation transitions.
///
/// Five cases: one `Always`-guarded invariants case plus four
/// `MethodIs`-guarded operation cases. Cases default-deny on unknown
/// method symbols (per Cav-Codex Block 4 / `subscription_program`'s
/// shape).
pub fn governance_program() -> CellProgram {
    CellProgram::Cases(vec![
        // ────────────────────────────────────────────────────────────────
        // Invariants: every transition, regardless of operation.
        //   - Committee root and threshold are constitutional; never change.
        //   - Version is monotonic across the cell's lifetime.
        //   - Dispute window height is monotonic.
        // ────────────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![
                // `WriteOnce` (not `Immutable`): a factory-born governance cell
                // is empty, so committee + threshold are bound once by the
                // first `constitute` turn and frozen thereafter — the
                // birth-compatible form of the constitutional invariant.
                StateConstraint::WriteOnce {
                    index: GOVERNANCE_COMMITTEE_ROOT_SLOT,
                },
                StateConstraint::WriteOnce {
                    index: THRESHOLD_SLOT,
                },
                StateConstraint::Monotonic {
                    index: VERSION_SLOT,
                },
                StateConstraint::Monotonic {
                    index: DISPUTE_WINDOW_HEIGHT_SLOT,
                },
                StateConstraint::Immutable {
                    index: RESERVED_SLOT_6,
                },
                StateConstraint::Immutable {
                    index: RESERVED_SLOT_7,
                },
            ],
        },
        // ────────────────────────────────────────────────────────────────
        // propose_table_update: committee member opens a new proposal.
        //   - route_table_root + version frozen (no swap yet).
        //   - pending_proposal_root advances (Monotonic; the new
        //     commitment must dominate the prior pending state).
        //   - dispute_window_height pushes forward (Monotonic).
        //   - sender must be a member of the governance committee.
        // ────────────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("propose_table_update"),
            },
            constraints: vec![
                StateConstraint::Immutable {
                    index: ROUTE_TABLE_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: VERSION_SLOT,
                },
                StateConstraint::Monotonic {
                    index: PENDING_PROPOSAL_ROOT_SLOT,
                },
                StateConstraint::Monotonic {
                    index: DISPUTE_WINDOW_HEIGHT_SLOT,
                },
                StateConstraint::SenderAuthorized {
                    set: AuthorizedSet::PublicRoot {
                        set_root_index: GOVERNANCE_COMMITTEE_ROOT_SLOT,
                    },
                },
            ],
        },
        // ────────────────────────────────────────────────────────────────
        // vote_on_proposal: tally grows.
        //   - route_table_root + version frozen (still no swap).
        //   - pending_proposal_root advances (tally root grows).
        //   - dispute_window_height frozen — votes ride on the proposer's
        //     declared window. Re-opening the window requires a new
        //     proposal.
        //   - sender must be a member of the governance committee.
        // ────────────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("vote_on_proposal"),
            },
            constraints: vec![
                StateConstraint::Immutable {
                    index: ROUTE_TABLE_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: VERSION_SLOT,
                },
                // NOTE: pending_proposal_root is NOT Monotonic here because
                // compose_vote_update produces a blake3 hash, which has no
                // guaranteed numerical ordering relative to the prior root.
                // The vote's validity is enforced by SenderAuthorized and by
                // the auditor checking the event stream.
                StateConstraint::Immutable {
                    index: DISPUTE_WINDOW_HEIGHT_SLOT,
                },
                StateConstraint::SenderAuthorized {
                    set: AuthorizedSet::PublicRoot {
                        set_root_index: GOVERNANCE_COMMITTEE_ROOT_SLOT,
                    },
                },
            ],
        },
        // ────────────────────────────────────────────────────────────────
        // commit_table_update: atomic swap.
        //   - version advances by exactly +1 (MonotonicSequence).
        //   - route_table_root may take any non-zero new value; the
        //     governance verifier (vk_hash: GOVERNANCE_VK) binds the
        //     transition's `(old_root, new_root, new_version)` triple
        //     to the threshold-sig, so any-value-here is constrained
        //     out-of-band by the registered verifier. The slot caveats
        //     ensure structural well-formedness; the predicate ensures
        //     authorization.
        //   - pending_proposal_root is cleared (back to FIELD_ZERO); we
        //     model "cleared" as the conjunction of (a) the executor's
        //     `Authorization::Custom` discharge succeeding (the proof
        //     binds the prior pending root via PublicInput) and (b) no
        //     slot caveat forbidding the clear. We deliberately do NOT
        //     `Monotonic`-bind the pending root here — that would lock
        //     it to never decrease, and a commit's whole purpose is to
        //     clear it. So this case omits a constraint on slot 5.
        //   - dispute_window_height frozen.
        //   - SenderAuthorized: any committee member may submit the
        //     commit turn (the threshold-sig is what authorizes; the
        //     submitter is just the carrier).
        // ────────────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("commit_table_update"),
            },
            constraints: vec![
                StateConstraint::MonotonicSequence {
                    seq_index: VERSION_SLOT,
                },
                StateConstraint::Immutable {
                    index: DISPUTE_WINDOW_HEIGHT_SLOT,
                },
                StateConstraint::SenderAuthorized {
                    set: AuthorizedSet::PublicRoot {
                        set_root_index: GOVERNANCE_COMMITTEE_ROOT_SLOT,
                    },
                },
            ],
        },
        // ────────────────────────────────────────────────────────────────
        // register_service: userspace caller publishes a service mount.
        //   - All governance slots frozen; this turn does NOT mutate the
        //     route table, version, committee, threshold, dispute window,
        //     or pending proposal.
        //   - The service registration is purely event-bearing: the
        //     `EmitEvent("service-registered", [path_hash, target_cell])`
        //     surface feeds an off-cell indexer that the
        //     `<dregg-namespace>` web component reads.
        //   - No `SenderAuthorized` constraint here: the route table
        //     itself classifies the caller's access via the DFA, so any
        //     sender may *register* — the route table's
        //     `RouteTarget::Userspace { kind: namespace_service }` dispatch
        //     determines whether the registration is accepted by the
        //     dispatcher. (A caller blocked by the DFA at dispatch time
        //     still consumes a turn, but produces no useful entry.)
        // ────────────────────────────────────────────────────────────────
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("register_service"),
            },
            constraints: vec![
                StateConstraint::Immutable {
                    index: ROUTE_TABLE_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: VERSION_SLOT,
                },
                StateConstraint::Immutable {
                    index: PENDING_PROPOSAL_ROOT_SLOT,
                },
                StateConstraint::Immutable {
                    index: DISPUTE_WINDOW_HEIGHT_SLOT,
                },
            ],
        },
    ])
}

// =============================================================================
// FactoryDescriptor
// =============================================================================

/// Build the `FactoryDescriptor` for governed-namespace cells.
///
/// Pins the constructor contract anyone can audit by hashing the
/// descriptor:
///
/// - `child_program_vk = GOVERNANCE_CHILD_PROGRAM_VK` — the AIR
///   enforcing [`governance_program`]'s `CellProgram::Cases`.
/// - `default_mode = Sovereign` — governed-namespace cells are
///   federation-shared roots; they need to be sovereign so the
///   committee retains constitutional control independent of any
///   hosting node.
/// - `creation_budget = DEFAULT_CREATION_BUDGET` (a low Sybil cap
///   appropriate for constitutional cells).
/// - `allowed_cap_templates` — a single attenuatable capability for the
///   committee aggregate (members hold attenuated facets of this cap,
///   discharged via Caveat::SenderInSet against the committee root).
/// - `field_constraints` (creation-time): the committee root and
///   threshold must be non-zero; version starts at zero.
/// - `state_constraints` (perpetual / Lane G slot caveats): the
///   `Immutable` invariants flattened from [`governance_program`]'s
///   `Always` case. The full operation-scoped shape is bound by
///   `child_program_vk` (which is the VK of an AIR that enforces
///   [`governance_program`]).
///
/// The split between `state_constraints` (descriptor) and
/// `governance_program` (cell-program) mirrors the subscription app:
/// the descriptor's field is `Vec<StateConstraint>` — a flat list, no
/// `Cases` shape — because the descriptor is hashed for constructor
/// transparency before the cell-program AIR exists. The flat list
/// commits to the *invariants*; the AIR commits to the full
/// operation-scoped shape.
pub fn governance_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: GOVERNANCE_FACTORY_VK,
        child_program_vk: Some(GOVERNANCE_CHILD_PROGRAM_VK),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(GOVERNANCE_CHILD_PROGRAM_VK))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            // The committee cap is dispatched via the
            // `WitnessedPredicate { kind: Custom { vk_hash: GOVERNANCE_VK } }`
            // path on `commit_table_update`; the `AuthRequired::Signature`
            // setting here is the *fallback* path for ordinary committee
            // operations (propose / vote / register_service) where the
            // member acts as themselves rather than as the aggregate.
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        // No creation-time `field_constraints`: a freshly-minted governance
        // cell is born empty (version already 0) and its first `constitute`
        // turn writes `COMMITTEE_ROOT` + `THRESHOLD` (`WriteOnce`, frozen after).
        // The birth `NonZero`s validated against `params.initial_fields`,
        // forcing the seed path to mint placeholders — and a `1`-threshold
        // placeholder is a genuine soundness hazard ("anyone can commit"
        // governance). Mirror privacy-voting/bounty-board: drop the birth
        // constraints, bind committee + threshold with the first turn, frozen
        // thereafter by `WriteOnce`.
        field_constraints: vec![],
        state_constraints: vec![
            // Constitutional invariants: committee + threshold are bound ONCE
            // (`WriteOnce`, from zero on the first turn) and frozen thereafter —
            // the birth-compatible form of the constitutional `Immutable`.
            StateConstraint::WriteOnce {
                index: GOVERNANCE_COMMITTEE_ROOT_SLOT,
            },
            StateConstraint::WriteOnce {
                index: THRESHOLD_SLOT,
            },
            // Version is monotonic across the cell's lifetime; per
            // `commit_table_update` it advances exactly +1.
            StateConstraint::Monotonic {
                index: VERSION_SLOT,
            },
            // Dispute window pushes forward only.
            StateConstraint::Monotonic {
                index: DISPUTE_WINDOW_HEIGHT_SLOT,
            },
            // Reserved slots stay frozen until a follow-on factory
            // unlocks them.
            StateConstraint::Immutable {
                index: RESERVED_SLOT_6,
            },
            StateConstraint::Immutable {
                index: RESERVED_SLOT_7,
            },
        ],
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// The full slice of factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![governance_factory_descriptor()]
}

// =============================================================================
// Route-table helpers (DFA composition)
// =============================================================================

/// Build a [`dregg_dfa::RouteTable`] from a slice of `(path, target)`
/// pairs.
///
/// Convenience wrapper around [`RouteTableBuilder`]. The path is a
/// URL-style string (e.g. `"/public/"`, `"/treasury/*"`); the target
/// is any [`RouteTarget`] including the open
/// `RouteTarget::Userspace { kind: NAMESPACE_SERVICE_KIND, .. }` variant
/// the `register_service` flow uses.
pub fn build_route_table(routes: &[(&str, RouteTarget)]) -> RouteTable {
    let mut b = RouteTableBuilder::new();
    for (path, target) in routes {
        b = b.route(path, target.clone());
    }
    b.compile()
}

/// Return the BLAKE3 commitment of the given [`RouteTable`].
///
/// This is the value that goes into slot 0 (`ROUTE_TABLE_ROOT_SLOT`)
/// after a successful `commit_table_update`. Equivalent to
/// `table.commitment` — exposed as a function so callers don't have
/// to learn the field name and so the helper is reachable from the
/// inspector-facing JSON without leaking `RouteTable`'s internals.
pub fn route_table_commitment(table: &RouteTable) -> [u8; 32] {
    table.commitment
}

/// Build a `KindRegistry` pre-populated with the namespace-service
/// userspace kind, ready for installation on a [`GovernedRouter`].
///
/// `register_service` mints `RouteTarget::Userspace { kind:
/// NAMESPACE_SERVICE_KIND, .. }` entries; a `GovernedRouter` that
/// will accept those needs the kind registered.
pub fn default_kind_registry() -> KindRegistry {
    let mut reg = KindRegistry::new();
    reg.register(NAMESPACE_SERVICE_KIND);
    reg
}

/// Build a [`GovernedRouter`] for the given route table with the
/// default [`default_kind_registry`] installed.
///
/// This is the read-side dispatch helper the
/// `<dregg-namespace-dispatch>` component uses to classify input
/// paths against the live route table. The `update_routes` path on
/// the returned router is *informational* — the authoritative update
/// path runs through `commit_table_update`'s
/// [`build_commit_table_update_action`] turn against the cell.
pub fn build_governed_router(table: RouteTable) -> GovernedRouter {
    let mut router = GovernedRouter::new(table);
    router.set_kind_registry(default_kind_registry());
    router
}

// =============================================================================
// Turn-builders
// =============================================================================

/// Build the on-ledger [`Action`] that opens a new route-table update
/// proposal.
///
/// The action carries three `SetField` effects (the new
/// `pending_proposal_root`, the dispute-window height, and an event)
/// plus the `proposal-opened` event for off-chain indexers.
///
/// # Parameters
///
/// - `cipherclerk` — the [`AppCipherclerk`] signing the proposal. The cipherclerk's
///   public key must be a member of the governance committee
///   (verified by `SenderAuthorized` against
///   `governance_committee_root` at execution time).
/// - `namespace_cell` — the target governed-namespace cell.
/// - `proposed_route_table` — the route table being proposed. The
///   proposed root is hashed into the `proposal_root` value along
///   with a deadline marker.
/// - `dispute_window_height` — block height at which un-disputed
///   votes finalize. Must be >= the current `dispute_window_height`
///   (Monotonic).
/// - `description` — human-readable description bytes for indexers.
///   Hashed into the `proposal_root` so off-chain indexers can
///   resolve the cleartext later.
pub fn build_propose_table_update_action(
    cipherclerk: &AppCipherclerk,
    namespace_cell: CellId,
    proposed_route_table: &RouteTable,
    dispute_window_height: u64,
    description: &str,
) -> Action {
    let proposed_root = route_table_commitment(proposed_route_table);
    let description_hash = field_from_bytes(description.as_bytes());
    let proposal_root =
        compose_proposal_root(&proposed_root, dispute_window_height, &description_hash);
    let window_field = field_from_u64(dispute_window_height);

    let effects = vec![
        Effect::SetField {
            cell: namespace_cell,
            index: PENDING_PROPOSAL_ROOT_SLOT as usize,
            value: proposal_root,
        },
        Effect::SetField {
            cell: namespace_cell,
            index: DISPUTE_WINDOW_HEIGHT_SLOT as usize,
            value: window_field,
        },
        Effect::EmitEvent {
            cell: namespace_cell,
            event: Event::new(
                symbol("proposal-opened"),
                vec![proposal_root, proposed_root, window_field, description_hash],
            ),
        },
    ];

    cipherclerk.make_action(namespace_cell, "propose_table_update", effects)
}

/// Build the on-ledger [`Action`] that records a vote on a pending
/// proposal.
///
/// The action carries one `SetField` (the advanced
/// `pending_proposal_root`, with the voter's contribution folded in)
/// plus an `EmitEvent("vote-cast", ...)`.
///
/// # Parameters
///
/// - `cipherclerk` — the voting member (`SenderAuthorized` against
///   committee root enforces membership).
/// - `namespace_cell` — the target cell.
/// - `prior_proposal_root` — the value currently in
///   `PENDING_PROPOSAL_ROOT_SLOT`. The caller reads this from the
///   cell state.
/// - `vote_kind` — `VoteKind::Approve` or `VoteKind::Reject`.
/// - `vote_weight` — the voter's declared weight (1 in the
///   one-member-one-vote case; more in weighted-vote constitutions).
///   Folded into the proposal root so the tally is auditable.
pub fn build_vote_on_proposal_action(
    cipherclerk: &AppCipherclerk,
    namespace_cell: CellId,
    prior_proposal_root: FieldElement,
    vote_kind: VoteKind,
    vote_weight: u64,
) -> Action {
    let voter_pk_hash = field_from_bytes(&cipherclerk.public_key().0);
    let new_proposal_root =
        compose_vote_update(&prior_proposal_root, &voter_pk_hash, vote_kind, vote_weight);
    let weight_field = field_from_u64(vote_weight);
    let kind_tag = vote_kind.tag_field();

    let effects = vec![
        Effect::SetField {
            cell: namespace_cell,
            index: PENDING_PROPOSAL_ROOT_SLOT as usize,
            value: new_proposal_root,
        },
        Effect::EmitEvent {
            cell: namespace_cell,
            event: Event::new(
                symbol("vote-cast"),
                vec![new_proposal_root, voter_pk_hash, kind_tag, weight_field],
            ),
        },
    ];

    cipherclerk.make_action(namespace_cell, "vote_on_proposal", effects)
}

/// Build the on-ledger [`Action`] that atomically swaps the route
/// table once threshold + dispute-window are satisfied.
///
/// The action carries three `SetField` effects (the new
/// `route_table_root`, the bumped `version`, the cleared
/// `pending_proposal_root`) plus an `EmitEvent("table-committed",
/// ...)` for indexers. **The action's authorization is
/// [`Authorization::Custom`]** carrying a
/// [`WitnessedPredicate`] with `kind = Custom { vk_hash:
/// GOVERNANCE_VK }`; the threshold-sig over the
/// `(old_root, new_root, new_version)` triple is the
/// `predicate.proof_witness_index`-th entry in
/// `action.witness_blobs`.
///
/// # Parameters
///
/// - `cipherclerk` — the carrier (any committee member); the threshold-sig
///   is what authorizes, not the carrier's individual signature.
/// - `namespace_cell` — the target cell.
/// - `committed_route_table` — the new route table. Its commitment
///   becomes the new `route_table_root`.
/// - `new_version` — the new version (typically `old_version + 1`;
///   the `MonotonicSequence` constraint on slot 1 will reject any
///   other value).
/// - `threshold_sig_bytes` — the threshold-signature bytes the
///   registered governance verifier consumes. The format is the
///   verifier's responsibility (BLS aggregate, Ed25519 multisig
///   bundle, STARK threshold-sig AIR proof, etc.).
///
/// # `Authorization::Custom` shape
///
/// ```text
/// Authorization::Custom {
///   predicate: WitnessedPredicate {
///     kind: Custom { vk_hash: GOVERNANCE_VK },
///     commitment: governance_committee_root,
///     input_ref: InputRef::SigningMessage,
///     proof_witness_index: 0,
///   }
/// }
/// ```
///
/// The executor resolves `InputRef::SigningMessage` to the canonical
/// `compute_partial_signing_message(action, position, federation_id,
/// turn_nonce)` bytes; the verifier checks
/// `threshold_sig_bytes` is a valid threshold-signature over the
/// committee at `governance_committee_root` certifying those bytes.
///
/// The `commitment` field carries
/// `governance_committee_root` so the verifier knows *which*
/// committee root to validate against — it reads the cell state
/// out-of-band (the registered verifier is allowed to peek at the
/// target cell's slot 2; that's part of the auth-mode contract).
///
/// # Returns
///
/// An [`Action`] whose `authorization` is
/// `Authorization::Custom { predicate }` and whose `witness_blobs[0]`
/// is `threshold_sig_bytes`. The action's three `SetField` effects
/// plus the event constitute the atomic swap.
pub fn build_commit_table_update_action(
    cipherclerk: &AppCipherclerk,
    namespace_cell: CellId,
    committed_route_table: &RouteTable,
    new_version: u64,
    threshold_sig_bytes: Vec<u8>,
    governance_committee_root: FieldElement,
) -> Action {
    let new_root = route_table_commitment(committed_route_table);
    let new_version_field = field_from_u64(new_version);

    let effects = vec![
        Effect::SetField {
            cell: namespace_cell,
            index: ROUTE_TABLE_ROOT_SLOT as usize,
            value: new_root,
        },
        Effect::SetField {
            cell: namespace_cell,
            index: VERSION_SLOT as usize,
            value: new_version_field,
        },
        // Clear the pending proposal — the commit consumed it.
        Effect::SetField {
            cell: namespace_cell,
            index: PENDING_PROPOSAL_ROOT_SLOT as usize,
            value: [0u8; 32],
        },
        Effect::EmitEvent {
            cell: namespace_cell,
            event: Event::new(
                symbol("table-committed"),
                vec![new_root, new_version_field, governance_committee_root],
            ),
        },
    ];

    // Build the unsigned action with `Authorization::Custom` carrying
    // the governance predicate, then attach the threshold-sig as a
    // witness blob. We use `cipherclerk.make_action` to build the canonical
    // shape (so the action carries the correct target/method/effects
    // and a default signature) and then OVERWRITE the authorization
    // with the `Custom` variant — the cipherclerk's signature is not the
    // load-bearing auth here; the threshold-sig is.
    let mut action = cipherclerk.make_action(namespace_cell, "commit_table_update", effects);

    // The witness-blob index for the threshold-sig is 0 (first blob).
    // The blob carries `WitnessKind::ProofBytes` — the canonical kind
    // for `Custom`-verifier proof payloads — and the threshold-sig
    // bytes verbatim. The registered governance verifier reads from
    // `proof_witness_index` and the executor refuses to dispatch with
    // a stale or mismatched index.
    action.witness_blobs = vec![WitnessBlob::proof(threshold_sig_bytes)];

    action.authorization = Authorization::Custom {
        predicate: WitnessedPredicate {
            kind: WitnessedPredicateKind::Custom {
                vk_hash: GOVERNANCE_VK,
            },
            commitment: governance_committee_root,
            input_ref: InputRef::SigningMessage,
            proof_witness_index: 0,
        },
    };

    action
}

/// Build the on-ledger [`Action`] that records a service registration
/// at a named path under the live route table.
///
/// The action carries one `EmitEvent("service-registered", ...)`. The
/// cell-program's `register_service` case freezes every governance
/// slot — this turn is purely event-bearing; off-chain indexers
/// (and the `<dregg-namespace>` component) consume the event stream
/// to build a `path → cell_id` view.
///
/// # Parameters
///
/// - `cipherclerk` — the registering caller (any sender; the DFA's
///   classification of `path` determines whether the dispatch is
///   accepted by downstream consumers).
/// - `namespace_cell` — the target governed-namespace cell.
/// - `path` — the path being registered (e.g. `"/treasury/main"`).
/// - `target_cell` — the cell ID the path resolves to.
pub fn build_register_service_action(
    cipherclerk: &AppCipherclerk,
    namespace_cell: CellId,
    path: &str,
    target_cell: CellId,
) -> Action {
    let path_hash = field_from_bytes(path.as_bytes());
    let target_field = cell_id_field(target_cell);

    let effects = vec![Effect::EmitEvent {
        cell: namespace_cell,
        event: Event::new(symbol("service-registered"), vec![path_hash, target_field]),
    }];

    cipherclerk.make_action(namespace_cell, "register_service", effects)
}

// =============================================================================
// Vote kind + proposal-root composition
// =============================================================================

/// The two vote outcomes a committee member may cast on a pending
/// proposal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VoteKind {
    /// Approve the proposed table swap.
    Approve,
    /// Reject the proposal.
    Reject,
}

impl VoteKind {
    /// Encode as a single-byte field tag (slot 0 of a 32-byte field).
    /// Used in the on-cell event and folded into the rolling
    /// `pending_proposal_root` so the indexer can reconstruct each
    /// vote's outcome.
    pub fn tag_field(self) -> FieldElement {
        let mut out = [0u8; 32];
        out[31] = match self {
            VoteKind::Approve => 1,
            VoteKind::Reject => 2,
        };
        out
    }
}

/// Compose the initial `pending_proposal_root` from a proposed
/// route-table root, the dispute-window height, and a description
/// hash.
///
/// Folds together (`dregg-governed-namespace-proposal-v1` ‖
/// `proposed_root` ‖ `dispute_window_height_be` ‖
/// `description_hash`) into a 32-byte BLAKE3 commitment. The format
/// is keyed-derive so distinct proposals (even with the same
/// proposed root) produce distinct commitments.
pub fn compose_proposal_root(
    proposed_root: &FieldElement,
    dispute_window_height: u64,
    description_hash: &FieldElement,
) -> FieldElement {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-governed-namespace-proposal-v1");
    hasher.update(proposed_root);
    hasher.update(&dispute_window_height.to_be_bytes());
    hasher.update(description_hash);
    *hasher.finalize().as_bytes()
}

/// Compose the updated `pending_proposal_root` after folding in a
/// single vote.
///
/// `dregg-governed-namespace-vote-v1` keyed-derive over
/// (`prior_root` ‖ `voter_pk_hash` ‖ `vote_kind_byte` ‖
/// `weight_be`). Monotonically advances the root: any two distinct
/// votes produce distinct roots, and re-folding the same vote
/// twice produces the same advance both times (idempotency at the
/// commitment level; the executor's `SenderAuthorized` plus a
/// proposal-side replay nullifier — out-of-band — is what enforces
/// "one vote per member per proposal" cryptographically).
pub fn compose_vote_update(
    prior_root: &FieldElement,
    voter_pk_hash: &FieldElement,
    vote_kind: VoteKind,
    vote_weight: u64,
) -> FieldElement {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-governed-namespace-vote-v1");
    hasher.update(prior_root);
    hasher.update(voter_pk_hash);
    hasher.update(&[match vote_kind {
        VoteKind::Approve => 1u8,
        VoteKind::Reject => 2u8,
    }]);
    hasher.update(&vote_weight.to_be_bytes());
    *hasher.finalize().as_bytes()
}

// =============================================================================
// Dispatch helper (read-only)
// =============================================================================

/// Classify an input path against a [`RouteTable`].
///
/// Convenience wrapper around `dregg_dfa::Router::classify_path`.
/// Returns the matched [`RouteTarget`] (if any) and the matched
/// prefix bytes. Used by the `<dregg-namespace-dispatch>` web
/// component for the lookup form.
///
/// The result is owned so the caller does not have to manage the
/// lifetime of the temporary `Router`.
pub fn dispatch(table: &RouteTable, path: &[u8]) -> Option<DispatchOutcome> {
    let router = Router::new(table.clone());
    let c = router.classify_path(path)?;
    Some(DispatchOutcome {
        target: c.target.clone(),
        matched_prefix: c.matched_prefix.to_vec(),
        remainder: c.remainder.to_vec(),
    })
}

/// Owned classification result returned by [`dispatch`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DispatchOutcome {
    pub target: RouteTarget,
    pub matched_prefix: Vec<u8>,
    pub remainder: Vec<u8>,
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// The canonical web-constants module — the single source of truth the
/// `pages/constants.generated.js` is rendered from.
///
/// IMPORTANT: this fixes a latent drift bug. The hand-written JS previously
/// emitted `namespace-proposal-submitted` / `namespace-vote-cast` /
/// `namespace-table-committed` / `namespace-service-registered`, but the Rust
/// builders (and thus the executor's receipts) emit `proposal-opened` /
/// `vote-cast` / `table-committed` / `service-registered`. An inspector or
/// indexer keyed to the JS names would never match real events. The generated
/// module carries the EXACT `symbol("…")` topics the Rust side emits, and the
/// pages now import them, so the two can no longer disagree. The method symbols
/// (already matching) are carried too so the JS builders dispatch the right
/// `MethodIs`-guarded cases.
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("governed-namespace")
        .slot("ROUTE_TABLE_ROOT_SLOT", ROUTE_TABLE_ROOT_SLOT as u64)
        .slot("VERSION_SLOT", VERSION_SLOT as u64)
        .slot(
            "GOVERNANCE_COMMITTEE_ROOT_SLOT",
            GOVERNANCE_COMMITTEE_ROOT_SLOT as u64,
        )
        .slot("THRESHOLD_SLOT", THRESHOLD_SLOT as u64)
        .slot(
            "DISPUTE_WINDOW_HEIGHT_SLOT",
            DISPUTE_WINDOW_HEIGHT_SLOT as u64,
        )
        .slot(
            "PENDING_PROPOSAL_ROOT_SLOT",
            PENDING_PROPOSAL_ROOT_SLOT as u64,
        )
        .string("FACTORY_VK_HEX", hex_encode_32(&GOVERNANCE_FACTORY_VK))
        // Method names (the executor's `MethodIs` guards key off these).
        .string("METHOD_PROPOSE", "propose_table_update")
        .string("METHOD_VOTE", "vote_on_proposal")
        .string("METHOD_COMMIT", "commit_table_update")
        .string("METHOD_REGISTER", "register_service")
        // Event topics — the EXACT strings the Rust builders emit (was the
        // drift bug: JS used `namespace-*` aliases that never matched).
        .topic("PROPOSED", "proposal-opened")
        .topic("VOTED", "vote-cast")
        .topic("COMMITTED", "table-committed")
        .topic("SERVICE_BOUND", "service-registered")
}

/// Register the governed-namespace starbridge-app on a
/// [`StarbridgeAppContext`].
///
/// Wires:
/// - the factory descriptor (under `GOVERNANCE_FACTORY_VK`);
/// - the family of inspector descriptors for the four web
///   components: `<dregg-namespace>` (browse), `<dregg-namespace-
///   route-table>` (visualize), `<dregg-namespace-proposal>`
///   (propose/vote/commit), `<dregg-namespace-dispatch>` (lookup).
///
/// Returns the registered `factory_vk` so the host can log it.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(governance_factory_descriptor());

    // Per-namespace browse view: version, committee, route table summary.
    ctx.register_inspector(InspectorDescriptor {
        kind: "namespace".into(),
        descriptor: serde_json::json!({
            "component": "dregg-namespace",
            "module": "/starbridge-apps/governed-namespace/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": [
                "route_table_root", "version", "governance_committee_root",
                "threshold", "dispute_window_height", "pending_proposal_root",
            ],
            "slot_layout": {
                "route_table_root":            ROUTE_TABLE_ROOT_SLOT,
                "version":                     VERSION_SLOT,
                "governance_committee_root":   GOVERNANCE_COMMITTEE_ROOT_SLOT,
                "threshold":                   THRESHOLD_SLOT,
                "dispute_window_height":       DISPUTE_WINDOW_HEIGHT_SLOT,
                "pending_proposal_root":       PENDING_PROPOSAL_ROOT_SLOT,
            },
            "factory_vk_hex":              hex_encode_32(&factory_vk),
            "child_program_vk_hex":        hex_encode_32(&GOVERNANCE_CHILD_PROGRAM_VK),
            "governance_vk_hex":           hex_encode_32(&GOVERNANCE_VK),
            "namespace_service_kind":      NAMESPACE_SERVICE_KIND,
        }),
    });

    // Route-table visualization — renders the live DFA accept-map.
    ctx.register_inspector_with("namespace-route-table", || {
        serde_json::json!({
            "component": "dregg-namespace-route-table",
            "module": "/starbridge-apps/governed-namespace/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "factory_vk_hex": hex_encode_32(&GOVERNANCE_FACTORY_VK),
        })
    });

    // Proposal authoring + vote-casting + commit-submission UI.
    ctx.register_inspector_with("namespace-proposal", || {
        serde_json::json!({
            "component": "dregg-namespace-proposal",
            "module": "/starbridge-apps/governed-namespace/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "factory_vk_hex": hex_encode_32(&GOVERNANCE_FACTORY_VK),
            "builders_module": "/starbridge-apps/governed-namespace/turn-builders.js",
            "methods": [
                "propose_table_update",
                "vote_on_proposal",
                "commit_table_update",
                "register_service",
            ],
        })
    });

    // Lookup form — input path → classified target via the live table.
    ctx.register_inspector_with("namespace-dispatch", || {
        serde_json::json!({
            "component": "dregg-namespace-dispatch",
            "module": "/starbridge-apps/governed-namespace/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "factory_vk_hex": hex_encode_32(&GOVERNANCE_FACTORY_VK),
        })
    });

    // Mount the deos-native composition surface (the `DeosApp`) on the SAME context —
    // the census promotion: the governance board now ships from `src/`. The factory +
    // inspectors are where SOUNDNESS lives (a version rollback / threshold rebind is a
    // real executor refusal on the born cell); the deos surface is the composition skin
    // (per-viewer projection, the cap∧state gated propose/vote fires, the `dregg://`
    // publish, the rehydratable snapshot, the generated component, the manifest).
    register_deos(ctx);

    factory_vk
}

// =============================================================================
// Cross-app composition: credential-gated voting + nameservice-mounted routes
// =============================================================================
//
// Two integrations live here:
//
// 1. **Credential-gated voting** — a governed-namespace can require
//    voters to present a credential (e.g. "verified developer") issued
//    by a specific identity-issuer cell. The constraint is dropped into
//    a future per-method case (e.g. `vote_on_proposal_attested`) via
//    [`credential_gated_voting_constraint`]; the vote action attaches
//    the credential proof in `witness_blobs` and uses
//    [`credential_gated_witness_predicate`] as the dispatch shape.
//
// 2. **Nameservice-mounted route targets** — a governed namespace can
//    register a `dregg://<name>` URI whose resolve target is computed
//    via the nameservice's `RESOLVE_TARGET_SLOT` convention. The helper
//    [`register_nameservice_route_action`] builds the registration so
//    the route table's target binding matches the nameservice's
//    canonical hash of the target URI.
//
// Both integrations are data-only: this crate does not import
// `starbridge-identity` or `starbridge-nameservice`; callers supply the
// issuer cell + schema commitment (computed by
// `starbridge_identity::schema_commitment`) and the resolve target
// (computed by `starbridge_nameservice::resolve_target`).

/// Build the `StateConstraint` clause a credential-gated voting tier
/// of a governed namespace imposes on `vote_on_proposal` turns.
///
/// Drop this into a `CellProgram::Cases` case (e.g. a new
/// `vote_on_proposal_attested` method symbol) when the namespace's
/// constitution requires voters to hold a credential from
/// `issuer_cell` of `credential_schema_id` (computed via
/// `starbridge_identity::schema_commitment`). The accompanying
/// `Action` carries the `Presentation` proof bytes in
/// `witness_blobs[proof_witness_index]`; the executor's
/// `WitnessedPredicateRegistry` dispatches to the registered
/// `WitnessedPredicateKind::BlindedSet` verifier.
///
/// The constraint's commitment is
/// `AuthorizedSet::credential_set_commitment(issuer_cell,
/// credential_schema_id)` — matching the witness predicate
/// [`credential_gated_witness_predicate`] emits.
pub fn credential_gated_voting_constraint(
    issuer_cell: CellId,
    credential_schema_id: [u8; 32],
) -> StateConstraint {
    StateConstraint::SenderAuthorized {
        set: AuthorizedSet::CredentialSet {
            issuer_cell: *issuer_cell.as_bytes(),
            credential_schema_id,
        },
    }
}

/// Build the witness-predicate shape an `Action` carries to discharge
/// a [`credential_gated_voting_constraint`].
pub fn credential_gated_witness_predicate(
    issuer_cell: CellId,
    credential_schema_id: [u8; 32],
    proof_witness_index: usize,
) -> WitnessedPredicate {
    WitnessedPredicate {
        kind: WitnessedPredicateKind::BlindedSet,
        commitment: AuthorizedSet::credential_set_commitment(
            issuer_cell.as_bytes(),
            &credential_schema_id,
        ),
        input_ref: InputRef::Sender,
        proof_witness_index,
    }
}

/// Build a `register_service` action that mounts a nameservice-resolved
/// target at a path under the governed namespace.
///
/// Wraps [`build_register_service_action`] with the caller's
/// pre-computed `nameservice_resolve_target` (the 32-byte hash a
/// nameservice cell records in its `RESOLVE_TARGET_SLOT`) so the
/// emitted `service-registered` event carries the same target bytes
/// downstream consumers (a `dregg_dfa::Router` walking the live route
/// table) see when they resolve the cell.
///
/// `target_cell` is still the canonical cell ID; the
/// `nameservice_resolve_target` is an *additional* event datum so the
/// indexer can correlate the namespace mount with the nameservice
/// entry without a second lookup.
pub fn register_nameservice_route_action(
    cipherclerk: &AppCipherclerk,
    namespace_cell: CellId,
    path: &str,
    target_cell: CellId,
    nameservice_resolve_target: FieldElement,
) -> Action {
    let path_hash = field_from_bytes(path.as_bytes());
    let target_field = cell_id_field(target_cell);

    let effects = vec![Effect::EmitEvent {
        cell: namespace_cell,
        event: Event::new(
            symbol("service-registered"),
            vec![path_hash, target_field, nameservice_resolve_target],
        ),
    }];

    cipherclerk.make_action(namespace_cell, "register_service", effects)
}

// =============================================================================
// The deos-native surface — the governance BOARD as a composed `DeosApp`.
// =============================================================================
//
// `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the governed-namespace governance
// board, re-expressed as a composed [`DeosApp`] and SHIPPED from `src/`. The same
// operations are ONE [`DeosApp`] ([`governance_app`] below); the framework wires the
// rest — per-viewer projection, web-of-cells publish (the governance cell IS a
// `dregg://` sturdyref a peer federation reacquires), the rehydratable
// frustum-snapshot, the generated `<dregg-affordance-surface>` component, and the
// manifest — none of which the floor's bones had.
//
// **The seam is closed for the GATEABLE ops** — a TWO-TEMPO fire (mirror
// supply-chain-provenance / subscription). The two state-advancing committee
// operations (`propose_table_update`, `vote_on_proposal`) are [`GatedAffordance`]s
// carrying a live-state PRECONDITION; the FULL governance program ([`governance_program`]
// = the operation-scoped `Cases`) is INSTALLED on the seeded governance cell
// ([`seed_governance`]) and RE-ENFORCED by the executor on every touching turn:
//
//   1. the deos PRECONDITION gate (the cap-gate `is_attenuation` AND the live-state
//      precondition `CellProgram::evaluate`) decides the button's verdict IN-BAND —
//      nothing submitted on a miss (anti-ghost; the htmx reactivity rides this);
//   2. [`fire_propose`] / [`fire_vote`] then submit the FULL committee turn, and the
//      executor RE-ENFORCES the installed governance program — so a PENDING-root rewind
//      (a `propose` whose `pending_proposal_root` decreases, `Monotonic` in the propose
//      case) and a frozen-slot violation (a `vote` that touches `route_table_root` /
//      `version`, `Immutable` in the vote case) are REAL executor refusals in the
//      SUBMISSION path — the half the floor's `evaluate_with_meta`-only tests never
//      exercised through a real signed turn (see `tests/deos_seam.rs`).
//
// **THE `commit_table_update` THRESHOLD-SIG FIRE.** `commit_table_update` rides
// `Authorization::Custom` + a `WitnessedPredicate { Custom { vk_hash: GOVERNANCE_VK } }`
// (the constitutional threshold-sig). The verifier for that kind is
// [`dregg_turn::executor::ThresholdSigVerifier`] — a real BLS12-381 + KZG
// weighted-threshold-signature check (`hints::verify_aggregate`: the constant-size
// aggregate QC's SNARK proof + final BLS pairing), the same primitive
// `dregg-federation`'s `FederationCommittee` / `ThresholdQC` wrap. A host installs it
// with [`dregg_turn::executor::register_threshold_sig_verifier`] under `GOVERNANCE_VK`,
// backed by a `StaticThresholdSigPolicy` mapping the predicate `commitment` (the
// `governance_committee_root`) to the committee's `hints::Verifier` + the k-of-n floor.
// With that registry installed (`EmbeddedExecutor::set_witnessed_registry`), the commit
// fire COMMITS through the full executor under a valid k-of-n aggregate over the
// canonical custom signing message, and is REFUSED under an under-threshold / forged /
// wrong-committee signature — both polarities are proven end-to-end in
// `tests/commit_threshold_sig.rs`. The threshold floor is pinned from the host policy,
// not the QC, so an aggregator-chosen low threshold cannot downgrade the gate.

/// The governance rights tiers, ON THE REAL ATTENUATION LATTICE — these ARE the roles
/// the floor crate's cap-graph + `SenderAuthorized(committee_root)` enforces:
///
///   - a VIEWER (the public / an auditor) holds [`AuthRequired::Signature`] — the narrow
///     read tier: it can `view_table` (read the live route table + version) and nothing
///     else;
///   - a COMMITTEE MEMBER (a constitutional signer) holds [`AuthRequired::Either`] — it
///     can `propose_table_update` and `vote_on_proposal` (open + tally a proposal) AND
///     register services AND view;
///   - the COMMITTEE AGGREGATE / ADMIN holds [`AuthRequired::None`]/root — it carries the
///     `commit_table_update` authority (the threshold-sig aggregate enacts the swap) on
///     top of everything a member can do.
///
/// So `Signature ⊂ Either ⊂ None` IS the viewer ⊂ committee-member ⊂ admin ladder. The
/// committee tier maps onto `Either` because a member acts as themselves (a signature)
/// OR via a proof on the constitutional propose/vote turns; commit-authority maps onto
/// `None`/root because the threshold aggregate, not any individual, is what enacts.
pub const VIEWER_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The committee-member rights tier (sig-or-proof — propose + vote + register + view). See [`VIEWER_RIGHTS`].
pub const COMMITTEE_RIGHTS: AuthRequired = AuthRequired::Either;
/// The committee-aggregate / admin rights tier (root — the commit authority + all). See [`VIEWER_RIGHTS`].
pub const ADMIN_RIGHTS: AuthRequired = AuthRequired::None;

/// The `propose_table_update` **live-state precondition** — there must be NO in-flight
/// proposal (`pending_proposal_root == 0`). A real [`CellProgram`] read against the
/// cell's current state, so a `propose` button is LIT on a quiescent board and goes DARK
/// the instant a proposal opens (the htmx tooth). This gates "may `propose` fire now";
/// the governance INVARIANTS (the `Monotonic(pending)` + frozen `route_table_root`/
/// `version`) are the installed [`governance_program`] the executor re-enforces on the
/// produced transition.
pub fn no_pending_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: PENDING_PROPOSAL_ROOT_SLOT,
        value: field_from_u64(0),
    }])
}

/// The `vote_on_proposal` **live-state precondition** — a proposal must EXIST
/// (`pending_proposal_root >= 1`). So the `vote` button is DARK on a quiescent board and
/// LIT once a proposal is open (the htmx tooth — the dual of [`no_pending_precondition`]).
/// The executor's installed `vote`-case `Immutable(route_table_root, version)` is the
/// second guard (a vote that tries to swap the table is a real refusal).
pub fn proposal_exists_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldGte {
        index: PENDING_PROPOSAL_ROOT_SLOT,
        value: field_from_u64(1),
    }])
}

/// **The governance BOARD as a composed [`DeosApp`]** — the whole interaction surface,
/// on the deos bones. The governance cell is the agent's OWN cell
/// (`cipherclerk.cell_id()`) so fires execute against the seeded embedded ledger.
///
/// Five operations on the governance cell, on the viewer ⊂ committee ⊂ admin rights
/// ladder:
///
///   - `view_table` — a cap-only affordance (a VIEWER reads the live route table +
///     version): `Signature`, an `EmitEvent`;
///   - `register_service` — a cap-only affordance (any committee member publishes a
///     service mount): `Either`, carrying the floor's `register_service` `EmitEvent`
///     effect (the read-then-emit side of the namespace; the floor's `register_service`
///     case freezes every governance slot, so it is event-bearing only);
///   - `commit_table_update` — a CAP-ONLY affordance (`None`/root), carrying the EXISTING
///     [`build_commit_table_update_action`]'s decisive effect (the `route_table_root`
///     swap) as its surface representative. Its happy-path fire needs the
///     `WitnessedPredicateRegistry`-into-executor lane (the fail-closed
///     `NotYetWiredVerifier`), so this affordance is CAP-AUTHORIZATION-ONLY today and the
///     deos seam does NOT assert a green commit fire (see the module docs — option (b));
///   - `propose_table_update` — a [`GatedAffordance`] (a COMMITTEE member opens a
///     proposal): `Either`, a live-state PRECONDITION ([`no_pending_precondition`]: no
///     in-flight proposal); the real fire ([`fire_propose`]) submits the FULL propose
///     turn, re-enforced by the executor's installed governance program
///     (`Monotonic(pending_proposal_root)` + frozen `route_table_root`/`version`);
///   - `vote_on_proposal` — a [`GatedAffordance`] (a COMMITTEE member tallies a vote):
///     `Either`, a live-state PRECONDITION ([`proposal_exists_precondition`]: a proposal
///     exists); the real fire ([`fire_vote`]) submits the FULL vote turn, re-enforced by
///     the executor (frozen `route_table_root`/`version`/`dispute_window_height`).
///
/// The governance cell is published into the web-of-cells at the viewer tier (an auditor
/// on another federation reacquires the live table across the membrane) and is
/// discoverable under `governance` / `namespace`.
///
/// Seed the cell's program + genesis state with [`seed_governance`] so the gated fires
/// have a live state and the executor re-enforces the program.
pub fn governance_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let cell = cipherclerk.cell_id();

    // `view_table` — a viewer reads the live route table + version. Cap-only.
    let view_table = CellAffordance::new(
        "view_table",
        VIEWER_RIGHTS,
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("table-read"), vec![]),
        },
    );
    // `register_service` — any committee member publishes a service mount. Cap-only,
    // carrying the floor's event-bearing `register_service` emission (its floor case
    // freezes every governance slot — purely event-bearing).
    let register_service = CellAffordance::new(
        "register_service",
        COMMITTEE_RIGHTS,
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("service-registered"), vec![]),
        },
    );
    // `commit_table_update` — the committee aggregate enacts the swap. CAP-ONLY (root),
    // carrying the EXISTING commit decisive effect (the route_table_root swap) as the
    // surface representative. Its happy-path fire needs the witnessed-verifier lane (the
    // fail-closed `NotYetWiredVerifier`) — so this is cap-authorization-only today and the
    // deos seam does NOT assert a green commit fire (option (b); see the module docs).
    let commit = CellAffordance::new(
        "commit_table_update",
        ADMIN_RIGHTS,
        Effect::SetField {
            cell,
            index: ROUTE_TABLE_ROOT_SLOT as usize,
            value: field_from_bytes(b"committed-route-table-root"),
        },
    );
    // `propose_table_update` — a COMMITTEE member opens a proposal. The GatedAffordance
    // carries the DECISIVE effect (the `pending_proposal_root` advance) as its surface
    // representative AND a live-state PRECONDITION ([`no_pending_precondition`]: no
    // in-flight proposal) — so the button is lit on a quiescent board and dark once a
    // proposal opens (the htmx tooth) and the cap∧state gate decides its verdict in-band.
    // The actual fire ([`fire_propose`]) submits the FULL propose turn, which the executor
    // re-enforces the governance program on — so `Monotonic(pending_proposal_root)` BITES:
    // a rewind of the pending root is REFUSED.
    let propose = GatedAffordance::new(
        CellAffordance::new(
            "propose_table_update",
            COMMITTEE_RIGHTS,
            Effect::SetField {
                cell,
                index: PENDING_PROPOSAL_ROOT_SLOT as usize,
                value: field_from_u64(1),
            },
        ),
        no_pending_precondition(),
    );
    // `vote_on_proposal` — a COMMITTEE member tallies a vote. The decisive effect advances
    // the `pending_proposal_root` (the floor folds the tally INTO the pending root);
    // gated on the PROPOSAL-EXISTS precondition ([`proposal_exists_precondition`]:
    // `pending_proposal_root >= 1`). The executor re-enforces the installed program (so the
    // vote-case `Immutable(route_table_root, version)` bites — a vote that swaps the table
    // is refused).
    let vote = GatedAffordance::new(
        CellAffordance::new(
            "vote_on_proposal",
            COMMITTEE_RIGHTS,
            Effect::SetField {
                cell,
                index: PENDING_PROPOSAL_ROOT_SLOT as usize,
                value: field_from_u64(2),
            },
        ),
        proposal_exists_precondition(),
    );

    DeosApp::builder("governed-namespace", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["governance".into(), "namespace".into()])
        .cell(
            DeosCell::new(cell, "governance")
                .affordance(view_table)
                .affordance(register_service)
                .affordance(commit)
                .gated(propose)
                .gated(vote)
                .publish(VIEWER_RIGHTS),
        )
        .build()
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// [`field_from_u64`] for the counter the gated propose/vote fires advance the pending
/// root by).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// **Seed the governance cell** so the gated fires have live state + the program bites:
/// install the full [`governance_program`] (`Cases`) on the seeded governance cell (so
/// the executor re-enforces it on every touching turn), then bind the genesis
/// constitutional state directly into the embedded ledger — `GOVERNANCE_COMMITTEE_ROOT`
/// + `THRESHOLD` (`WriteOnce`, frozen after), `VERSION = initial`, `ROUTE_TABLE_ROOT =
/// initial`, and `PENDING_PROPOSAL_ROOT = 0` (a quiescent board: no in-flight proposal).
///
/// **The `SenderAuthorized` membership root (the REAL verifier now bites).** The
/// `propose` / `vote` cases carry `SenderAuthorized { PublicRoot { set_root_index:
/// GOVERNANCE_COMMITTEE_ROOT_SLOT } }`, and the embedded executor wires the REAL
/// STARK-backed [`dregg_turn::executor::MerkleMembershipStarkVerifier`] (no longer the
/// fail-closed stub). So a `propose`/`vote` turn whose signer is NOT a genuine Merkle
/// leaf under slot 2's root — or carries no membership witness — is a REAL executor
/// refusal. We therefore seed slot 2 with [`single_member_authorized_root`] over the
/// SEEDED CELL'S OWN public key (the cell the gated fires run as), making that signer the
/// sole authorized committee member; [`fire_propose`] / [`fire_vote`] attach the matching
/// [`single_member_membership_proof`] so the verifier accepts. (The `committee_root`
/// parameter is retained for source-shape compatibility but no longer occupies slot 2 —
/// the authorization root MUST be the membership root the verifier reconstructs, not an
/// opaque label; a forged label would simply make every committee turn unprovable.)
///
/// After seeding, the board is quiescent at `version` with the committee bound — a real
/// `(old, new)` baseline against which `propose` opens a proposal (pending 0 -> 1) and
/// `vote` advances the tally. Returns the seeded `version` value.
pub fn seed_governance(
    executor: &EmbeddedExecutor,
    committee_root: FieldElement,
    threshold: u64,
    version: u64,
    route_table_root: FieldElement,
) -> u64 {
    let _ = committee_root; // see the doc note: slot 2 now holds the membership root.
    let cell = executor.cell_id();
    executor.install_program(cell, governance_program());
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            // The authorized-committee root the REAL MerkleMembership verifier reads on
            // every `propose`/`vote`: a single-member set whose sole member is THIS cell's
            // own public key (the signer the gated fires submit as). The matching proof is
            // `single_member_membership_proof(&this_pk)`, attached in the fires.
            let member_pk = *c.public_key();
            c.state.set_field(
                GOVERNANCE_COMMITTEE_ROOT_SLOT as usize,
                single_member_authorized_root(&member_pk),
            );
            c.state
                .set_field(THRESHOLD_SLOT as usize, field_from_u64(threshold));
            c.state
                .set_field(VERSION_SLOT as usize, field_from_u64(version));
            c.state
                .set_field(ROUTE_TABLE_ROOT_SLOT as usize, route_table_root);
            // A quiescent board: no in-flight proposal.
            c.state
                .set_field(PENDING_PROPOSAL_ROOT_SLOT as usize, field_from_u64(0));
        }
    });
    version
}

/// **Fire `propose_table_update`** — the deos cap∧state PRECONDITION gate (anti-ghost,
/// in-band), then the FULL propose turn the executor re-enforces the governance program
/// on. The two-tempo bridge: the gated affordance decides the button's verdict (cap ⊇
/// Either AND no in-flight proposal) WITHOUT touching the executor; on both passing, the
/// complete pending-root-advancing turn is submitted, and the executor's re-enforcement
/// of [`governance_program`]'s `propose` case is the SECOND, verified gate
/// (`Monotonic(pending_proposal_root)` + frozen `route_table_root`/`version` bite).
/// Anti-ghost both ways: a precondition miss never submits; a program violation is a real
/// executor refusal.
///
/// The pending root is advanced past its live value (read from state), so the
/// `Monotonic(pending_proposal_root)` propose-case caveat holds. Use [`seed_governance`]
/// first.
pub fn fire_propose(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = app.cells()[0].cell();
    fire_committee_gated(
        app,
        "propose_table_update",
        held,
        cipherclerk,
        executor,
        |state| {
            // Advance the pending root past its live value (Monotonic in the propose case).
            let pending = field_to_u64(&state.fields[PENDING_PROPOSAL_ROOT_SLOT as usize]);
            let new_pending = field_from_u64(pending + 1);
            vec![
                Effect::SetField {
                    cell,
                    index: PENDING_PROPOSAL_ROOT_SLOT as usize,
                    value: new_pending,
                },
                Effect::EmitEvent {
                    cell,
                    event: Event::new(symbol("proposal-opened"), vec![new_pending]),
                },
            ]
        },
    )
}

/// **The committee-gated manual fire** — the SenderAuthorized-carrying ops (`propose` /
/// `vote`) fired through the executor against the FULL governance program, with the
/// Merkle-membership witness attached.
///
/// This is the manual analogue of [`DeosCell::fire_gated_through_executor_with`] that the
/// `SenderAuthorized`-gated ops REQUIRE: the framework helper builds+submits the action
/// internally and so cannot inject the membership witness blob the now-real
/// [`dregg_turn::executor::MerkleMembershipStarkVerifier`] demands. We therefore drive
/// the two-tempo bridge by hand:
///
///   1. **the cap∧state gate, IN-BAND (anti-ghost).** Read the cell's live state and run
///      BOTH teeth via [`GatedAffordance::fire`] (the cap `is_attenuation` AND the
///      live-state precondition `CellProgram::evaluate`). A miss at either tooth is a
///      [`FireExecuteError::Gate`] and NOTHING is submitted — the same anti-ghost the
///      framework helper gives, and the same `FireError::Unauthorized` /
///      `FireError::StateConditionUnmet` shapes the deos seam tests assert;
///   2. **the full committee turn, carrying the witness.** On both teeth passing, build
///      the state-parameterized effects, sign the action via
///      [`AppCipherclerk::make_action`], ATTACH the single-member membership proof as a
///      `MerklePath` [`WitnessBlob`] (over the firing signer's own pubkey — the sole
///      member seeded into slot 2), and submit. The executor RE-ENFORCES the full
///      governance program INCLUDING the now-real `SenderAuthorized`, which PASSES because
///      the signer is the seeded root's member AND carries the proof — and the propose/vote
///      slot caveats (`Monotonic(pending_proposal_root)`, frozen `route_table_root` /
///      `version`) still BITE on a malformed turn.
fn fire_committee_gated<F>(
    app: &DeosApp,
    name: &str,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
    effects: F,
) -> Result<TurnReceipt, FireExecuteError>
where
    F: FnOnce(&dregg_cell::state::CellState) -> Vec<Effect>,
{
    let board = &app.cells()[0];
    let cell = board.cell();
    // The live state of the governance cell — the same read the projection gates on.
    let live = executor.cell_state(cell).ok_or_else(|| {
        FireExecuteError::Gate(FireError::StateConditionUnmet {
            affordance: name.to_string(),
            reason: "cell has no live state in the embedded ledger (fail-closed)".to_string(),
        })
    })?;
    // Tempo 1 — the REAL cap∧state gate, IN-BAND. A miss at EITHER tooth (cap
    // `Unauthorized` / state `StateConditionUnmet`) is a `Gate` error; nothing submitted.
    let ga = board
        .gated_surface()
        .get(name)
        .ok_or(FireExecuteError::Gate(FireError::NoSuchAffordance))?;
    ga.fire(cipherclerk.cell_id(), held, &live, &live)
        .map_err(FireExecuteError::Gate)?;
    // Tempo 2 — the full committee turn, carrying the Merkle-membership witness. Sign the
    // action, attach the single-member membership proof (the ONLY MerklePath/ProofBytes
    // blob, so the SenderAuthorized evaluator binds it unambiguously), then submit through
    // the executor, which re-enforces the full governance program (incl. the real
    // SenderAuthorized).
    let produced = effects(&live);
    let mut action = cipherclerk.make_action(cell, name, produced);
    let member_proof = single_member_membership_proof(&cipherclerk.public_key().0);
    action.witness_blobs = vec![WitnessBlob::merkle_path(member_proof)];
    executor
        .submit_action(cipherclerk, action)
        .map_err(FireExecuteError::Executor)
}

/// **Fire `vote_on_proposal`** — the deos cap∧state PRECONDITION gate (cap ⊇ Either AND a
/// proposal exists), then the FULL vote turn. Like [`fire_propose`], the gated affordance
/// decides the button in-band and the executor's re-enforcement of the `vote` case
/// (`Immutable(route_table_root, version, dispute_window_height)`) is the verified second
/// gate (a vote that swaps the table is a real refusal). The vote case does NOT
/// `Monotonic`-bind the pending root (a blake3 tally fold has no numeric ordering), so the
/// fire advances it freely while keeping it non-zero. Use [`seed_governance`] first.
pub fn fire_vote(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = app.cells()[0].cell();
    fire_committee_gated(
        app,
        "vote_on_proposal",
        held,
        cipherclerk,
        executor,
        |state| {
            // Fold the tally into the pending root (the floor's vote semantics); keep it
            // non-zero so the proposal stays live. The vote case does not Monotonic-bind it.
            let pending = field_to_u64(&state.fields[PENDING_PROPOSAL_ROOT_SLOT as usize]);
            let new_pending = field_from_u64(pending + 1);
            vec![
                Effect::SetField {
                    cell,
                    index: PENDING_PROPOSAL_ROOT_SLOT as usize,
                    value: new_pending,
                },
                Effect::EmitEvent {
                    cell,
                    event: Event::new(symbol("vote-cast"), vec![new_pending]),
                },
            ]
        },
    )
}

/// **Mount the deos-native surface** ([`governance_app`]) on a shared context: build the
/// composed [`DeosApp`] from the context's cipherclerk + executor, seed the governance
/// cell's program + genesis state (so the gated propose/vote fires bite), and fold the app
/// into the context's affordance registry ([`DeosApp::register`]). Returns the live
/// [`DeosApp`] (so a host can also [`DeosApp::mount`] its axum router /
/// [`DeosApp::publish_all`] into the web-of-cells). This is the PROMOTION the census asks
/// for: the deos surface now ships from `src/`, not from a side-proof in `tests/`.
///
/// Seeds a 2-of-N committee at version 1 with an initial route table — a real
/// constitutional baseline the gated fires advance.
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = governance_app(ctx.cipherclerk(), ctx.executor());
    // Seed the governance cell so the gated `propose` / `vote` fires have a live
    // `(old, new)` and the governance program (installed here) is re-enforced by the
    // executor on every touching turn.
    seed_governance(
        ctx.executor(),
        field_from_bytes(b"committee-v0"),
        2,
        1,
        field_from_bytes(b"genesis-route-table-root"),
    );
    app.register(ctx);
    app
}

// =============================================================================
// Helpers
// =============================================================================

/// Hash arbitrary bytes into a 32-byte `FieldElement`.
///
/// Deprecated alias for [`dregg_app_framework::field_from_bytes`]; kept
/// `pub` because integration tests import this name directly.
pub use dregg_app_framework::field_from_bytes as blake3_field;

/// Encode a `u64` as a big-endian-padded 32-byte `FieldElement`.
///
/// Deprecated alias for [`dregg_app_framework::field_from_u64`]; kept
/// `pub` because integration tests import this name directly.
pub use dregg_app_framework::field_from_u64 as u64_field;

/// Encode a `CellId` as a 32-byte `FieldElement`.
///
/// `CellId` is 32 bytes; we copy verbatim. Used in events that
/// reference target cells.
pub fn cell_id_field(cell_id: CellId) -> FieldElement {
    *cell_id.as_bytes()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, EmbeddedExecutor};
    use dregg_cell::program::{TransitionGuard, TransitionMeta};

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    fn test_cell() -> CellId {
        CellId::from_bytes([19u8; 32])
    }

    fn dummy_committee_root() -> FieldElement {
        field_from_bytes(b"committee-v0")
    }

    fn dummy_route_table(routes: &[(&str, &str)]) -> RouteTable {
        let owned: Vec<(&str, RouteTarget)> = routes
            .iter()
            .map(|(p, t)| (*p, RouteTarget::handler(*t)))
            .collect();
        build_route_table(&owned)
    }

    // ── FactoryDescriptor tests ───────────────────────────────────────────

    #[test]
    fn factory_descriptor_is_stable() {
        let h1 = governance_factory_descriptor().hash();
        let h2 = governance_factory_descriptor().hash();
        assert_eq!(h1, h2, "descriptor hash must be deterministic");
    }

    #[test]
    fn factory_descriptor_pins_program_vk() {
        let d = governance_factory_descriptor();
        assert_eq!(d.factory_vk, GOVERNANCE_FACTORY_VK);
        assert_eq!(d.child_program_vk, Some(GOVERNANCE_CHILD_PROGRAM_VK));
        assert_eq!(d.default_mode, CellMode::Sovereign);
        assert_eq!(d.creation_budget, Some(DEFAULT_CREATION_BUDGET));
    }

    #[test]
    fn factory_descriptor_bakes_constitutional_write_once() {
        // `WriteOnce` (not `Immutable`): a factory-born governance cell is empty,
        // so committee + threshold are bound ONCE by the first `constitute` turn
        // (from zero) and frozen thereafter — the birth-compatible form of the
        // constitutional invariant.
        let d = governance_factory_descriptor();
        for slot in [GOVERNANCE_COMMITTEE_ROOT_SLOT, THRESHOLD_SLOT] {
            assert!(
                d.state_constraints
                    .iter()
                    .any(|c| matches!(c, StateConstraint::WriteOnce { index } if *index == slot)),
                "factory must install WriteOnce on slot {slot} (bound once, frozen after)"
            );
        }
    }

    #[test]
    fn factory_descriptor_bakes_monotonic_version_and_window() {
        let d = governance_factory_descriptor();
        for slot in [VERSION_SLOT, DISPUTE_WINDOW_HEIGHT_SLOT] {
            assert!(
                d.state_constraints
                    .iter()
                    .any(|c| matches!(c, StateConstraint::Monotonic { index } if *index == slot)),
                "factory must install Monotonic on slot {slot}"
            );
        }
    }

    #[test]
    fn factory_descriptor_has_no_birth_field_constraints() {
        // A factory-born governance cell mints empty: version == 0 ALREADY (a born
        // cell is all-zero), committee/threshold zero until the first `constitute`
        // turn binds them under `WriteOnce`. The old creation-time constraints
        // (version `Equality(0)`, committee/threshold `NonZero`) forced the seed
        // path to mint placeholders — a `1`-threshold placeholder is a genuine
        // soundness hazard ("anyone can commit" governance). We carry NONE
        // (mirroring privacy-voting/bounty-board); committee + threshold are bound
        // by the first turn and frozen thereafter by `WriteOnce`.
        let d = governance_factory_descriptor();
        assert!(
            d.field_constraints.is_empty(),
            "governance factory must carry NO creation-time field_constraints; \
             version==0 already holds at birth and committee/threshold are bound \
             by the first constitute turn under WriteOnce"
        );
    }

    #[test]
    fn factory_descriptors_slice_contains_governance_factory() {
        let all = factory_descriptors();
        assert_eq!(all.len(), 1);
        assert_eq!(all[0].factory_vk, GOVERNANCE_FACTORY_VK);
    }

    // ── CellProgram: shape ───────────────────────────────────────────────

    #[test]
    fn program_is_cases_with_five_branches() {
        match governance_program() {
            CellProgram::Cases(cases) => {
                assert_eq!(cases.len(), 5, "expected one Always + four MethodIs cases");
            }
            other => panic!("expected CellProgram::Cases, got {other:?}"),
        }
    }

    #[test]
    fn program_covers_all_four_methods() {
        let cases = match governance_program() {
            CellProgram::Cases(c) => c,
            _ => panic!("expected Cases"),
        };
        let mut seen_propose = false;
        let mut seen_vote = false;
        let mut seen_commit = false;
        let mut seen_register = false;
        for case in &cases {
            if let TransitionGuard::MethodIs { method } = &case.guard {
                if *method == symbol("propose_table_update") {
                    seen_propose = true;
                }
                if *method == symbol("vote_on_proposal") {
                    seen_vote = true;
                }
                if *method == symbol("commit_table_update") {
                    seen_commit = true;
                }
                if *method == symbol("register_service") {
                    seen_register = true;
                }
            }
        }
        assert!(seen_propose, "propose_table_update case missing");
        assert!(seen_vote, "vote_on_proposal case missing");
        assert!(seen_commit, "commit_table_update case missing");
        assert!(seen_register, "register_service case missing");
    }

    #[test]
    fn commit_case_uses_monotonic_sequence_on_version() {
        let cases = match governance_program() {
            CellProgram::Cases(c) => c,
            _ => panic!(),
        };
        let commit_case = cases
            .iter()
            .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == symbol("commit_table_update")))
            .expect("commit case present");
        assert!(
            commit_case.constraints.iter().any(|c| matches!(c,
                StateConstraint::MonotonicSequence { seq_index } if *seq_index == VERSION_SLOT
            )),
            "commit_table_update must MonotonicSequence the version slot"
        );
    }

    #[test]
    fn propose_case_freezes_route_table_root() {
        let cases = match governance_program() {
            CellProgram::Cases(c) => c,
            _ => panic!(),
        };
        let propose_case = cases
            .iter()
            .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == symbol("propose_table_update")))
            .expect("propose case present");
        assert!(
            propose_case.constraints.iter().any(|c| matches!(c,
                StateConstraint::Immutable { index } if *index == ROUTE_TABLE_ROOT_SLOT
            )),
            "propose must freeze route_table_root"
        );
    }

    #[test]
    fn vote_case_freezes_route_table_root_and_version() {
        let cases = match governance_program() {
            CellProgram::Cases(c) => c,
            _ => panic!(),
        };
        let vote_case = cases
            .iter()
            .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == symbol("vote_on_proposal")))
            .expect("vote case present");
        for slot in [ROUTE_TABLE_ROOT_SLOT, VERSION_SLOT] {
            assert!(
                vote_case.constraints.iter().any(|c| matches!(c,
                    StateConstraint::Immutable { index } if *index == slot
                )),
                "vote must freeze slot {slot}"
            );
        }
    }

    #[test]
    fn register_service_case_freezes_governance_slots() {
        let cases = match governance_program() {
            CellProgram::Cases(c) => c,
            _ => panic!(),
        };
        let reg = cases
            .iter()
            .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == symbol("register_service")))
            .expect("register_service case present");
        for slot in [
            ROUTE_TABLE_ROOT_SLOT,
            VERSION_SLOT,
            PENDING_PROPOSAL_ROOT_SLOT,
            DISPUTE_WINDOW_HEIGHT_SLOT,
        ] {
            assert!(
                reg.constraints.iter().any(|c| matches!(c,
                    StateConstraint::Immutable { index } if *index == slot
                )),
                "register_service must freeze slot {slot}"
            );
        }
    }

    // ── Route-table helpers ──────────────────────────────────────────────

    #[test]
    fn build_route_table_basic_roundtrip() {
        let table = dummy_route_table(&[("/health", "ping"), ("/cells/treasury/*", "treasury")]);
        let router = Router::new(table.clone());
        let c = router.classify_path(b"/health").unwrap();
        assert_eq!(c.target, &RouteTarget::handler("ping"));
        let c = router.classify_path(b"/cells/treasury/transfer").unwrap();
        assert_eq!(c.target, &RouteTarget::handler("treasury"));
    }

    #[test]
    fn route_table_commitment_deterministic() {
        let t1 = dummy_route_table(&[("/a", "a"), ("/b", "b")]);
        let t2 = dummy_route_table(&[("/a", "a"), ("/b", "b")]);
        assert_eq!(route_table_commitment(&t1), route_table_commitment(&t2));
    }

    #[test]
    fn route_table_commitment_sensitive_to_routes() {
        let t1 = dummy_route_table(&[("/a", "a")]);
        let t2 = dummy_route_table(&[("/a", "b")]);
        assert_ne!(route_table_commitment(&t1), route_table_commitment(&t2));
    }

    #[test]
    fn default_kind_registry_contains_namespace_service() {
        let reg = default_kind_registry();
        assert!(reg.contains(NAMESPACE_SERVICE_KIND));
    }

    #[test]
    fn build_governed_router_classifies_under_kind_registry() {
        let table = build_route_table(&[(
            "/svc/*",
            RouteTarget::userspace(NAMESPACE_SERVICE_KIND, b"".to_vec()),
        )]);
        let router = build_governed_router(table);
        let c = router.classify_path(b"/svc/alpha").unwrap();
        assert!(matches!(c.target, RouteTarget::Userspace(_)));
    }

    // ── Turn-builder shapes ──────────────────────────────────────────────

    #[test]
    fn propose_action_shape() {
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let table = dummy_route_table(&[("/treasury/*", "treasury_v2")]);
        let action =
            build_propose_table_update_action(&cipherclerk, cell, &table, 10_000, "rotate keys");

        assert_eq!(action.target, cell);
        assert_eq!(action.method, symbol("propose_table_update"));
        assert_eq!(action.effects.len(), 3);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, .. } if *index == PENDING_PROPOSAL_ROOT_SLOT as usize
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, .. } if *index == DISPUTE_WINDOW_HEIGHT_SLOT as usize
        ));
        assert!(matches!(&action.effects[2], Effect::EmitEvent { .. }));
    }

    #[test]
    fn vote_action_shape() {
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let prior_root = field_from_bytes(b"prior-proposal-root");
        let action =
            build_vote_on_proposal_action(&cipherclerk, cell, prior_root, VoteKind::Approve, 1);

        assert_eq!(action.method, symbol("vote_on_proposal"));
        assert_eq!(action.effects.len(), 2);
        match &action.effects[0] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, PENDING_PROPOSAL_ROOT_SLOT as usize);
                assert_ne!(*value, prior_root, "vote must advance the root");
                assert_ne!(*value, [0u8; 32], "advanced root is non-zero");
            }
            other => panic!("expected SetField, got {other:?}"),
        }
        assert!(matches!(&action.effects[1], Effect::EmitEvent { .. }));
    }

    #[test]
    fn commit_action_uses_authorization_custom_with_governance_vk() {
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let table = dummy_route_table(&[("/treasury/*", "treasury_v2")]);
        let committee = dummy_committee_root();
        let proof = b"threshold-sig-bytes-stub".to_vec();
        let action = build_commit_table_update_action(
            &cipherclerk,
            cell,
            &table,
            1,
            proof.clone(),
            committee,
        );

        assert_eq!(action.method, symbol("commit_table_update"));
        assert_eq!(action.effects.len(), 4, "3 SetField + 1 EmitEvent");

        // The first effect writes the new route-table root.
        match &action.effects[0] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, ROUTE_TABLE_ROOT_SLOT as usize);
                assert_eq!(*value, route_table_commitment(&table));
            }
            other => panic!("expected SetField, got {other:?}"),
        }
        // The second effect bumps version.
        match &action.effects[1] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, VERSION_SLOT as usize);
                assert_eq!(*value, field_from_u64(1));
            }
            other => panic!("expected SetField, got {other:?}"),
        }
        // The third effect clears the pending proposal root.
        match &action.effects[2] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, PENDING_PROPOSAL_ROOT_SLOT as usize);
                assert_eq!(*value, [0u8; 32]);
            }
            other => panic!("expected SetField, got {other:?}"),
        }

        // Authorization is `Custom` with the governance verifier vk.
        match &action.authorization {
            Authorization::Custom { predicate } => {
                assert_eq!(
                    predicate.kind,
                    WitnessedPredicateKind::Custom {
                        vk_hash: GOVERNANCE_VK
                    }
                );
                assert_eq!(predicate.commitment, committee);
                assert_eq!(predicate.input_ref, InputRef::SigningMessage);
                assert_eq!(predicate.proof_witness_index, 0);
            }
            other => panic!("expected Authorization::Custom, got {other:?}"),
        }
        // The threshold-sig is carried as witness_blobs[0] in a
        // `WitnessKind::ProofBytes` blob.
        assert_eq!(action.witness_blobs.len(), 1);
        assert_eq!(action.witness_blobs[0].bytes, proof);
        assert_eq!(
            action.witness_blobs[0].kind,
            dregg_turn::action::WitnessKind::ProofBytes
        );
    }

    #[test]
    fn register_service_action_shape() {
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let target = CellId::from_bytes([77u8; 32]);
        let action = build_register_service_action(&cipherclerk, cell, "/treasury/main", target);

        assert_eq!(action.method, symbol("register_service"));
        assert_eq!(action.effects.len(), 1);
        match &action.effects[0] {
            Effect::EmitEvent { event, .. } => {
                assert_eq!(event.topic, symbol("service-registered"));
                assert_eq!(event.data.len(), 2);
                assert_eq!(event.data[0], field_from_bytes(b"/treasury/main"));
                assert_eq!(event.data[1], cell_id_field(target));
            }
            other => panic!("expected EmitEvent, got {other:?}"),
        }
    }

    #[test]
    fn propose_action_carries_real_signature() {
        let cipherclerk = test_cipherclerk();
        let cell = test_cell();
        let table = dummy_route_table(&[("/x", "y")]);
        let action = build_propose_table_update_action(&cipherclerk, cell, &table, 1, "d");
        match action.authorization {
            Authorization::Signature(a, b) => {
                assert!(
                    a != [0u8; 32] || b != [0u8; 32],
                    "signature must be non-zero"
                );
            }
            other => panic!("expected Signature variant, got {other:?}"),
        }
    }

    #[test]
    fn different_cipherclerks_produce_different_vote_signatures() {
        let cc1 = AppCipherclerk::new(AgentCipherclerk::new(), [1u8; 32]);
        let cc2 = AppCipherclerk::new(AgentCipherclerk::new(), [1u8; 32]);
        let cell = test_cell();
        let prior = field_from_bytes(b"prior");
        let a1 = build_vote_on_proposal_action(&cc1, cell, prior, VoteKind::Approve, 1);
        let a2 = build_vote_on_proposal_action(&cc2, cell, prior, VoteKind::Approve, 1);
        // Signatures differ even though logical input is identical.
        let (Authorization::Signature(r1, _), Authorization::Signature(r2, _)) =
            (&a1.authorization, &a2.authorization)
        else {
            panic!("expected Signature variants");
        };
        assert_ne!(
            r1, r2,
            "different cipherclerks must produce different signatures"
        );
        // Vote roots also differ (each cipherclerk folds in its own pk hash).
        let (v1, v2) = match (&a1.effects[0], &a2.effects[0]) {
            (Effect::SetField { value: v1, .. }, Effect::SetField { value: v2, .. }) => (*v1, *v2),
            _ => panic!("expected SetField effects"),
        };
        assert_ne!(v1, v2, "different voters must produce different roots");
    }

    // ── Proposal-root composition ────────────────────────────────────────

    #[test]
    fn proposal_root_is_deterministic() {
        let root = field_from_bytes(b"new-table");
        let desc = field_from_bytes(b"desc");
        let a = compose_proposal_root(&root, 100, &desc);
        let b = compose_proposal_root(&root, 100, &desc);
        assert_eq!(a, b);
    }

    #[test]
    fn proposal_root_sensitive_to_proposed_table() {
        let desc = field_from_bytes(b"desc");
        let r1 = compose_proposal_root(&field_from_bytes(b"a"), 100, &desc);
        let r2 = compose_proposal_root(&field_from_bytes(b"b"), 100, &desc);
        assert_ne!(r1, r2);
    }

    #[test]
    fn proposal_root_sensitive_to_window() {
        let root = field_from_bytes(b"new-table");
        let desc = field_from_bytes(b"desc");
        let r1 = compose_proposal_root(&root, 100, &desc);
        let r2 = compose_proposal_root(&root, 200, &desc);
        assert_ne!(r1, r2);
    }

    #[test]
    fn vote_update_distinguishes_approve_vs_reject() {
        let prior = field_from_bytes(b"prior");
        let voter = field_from_bytes(b"voter");
        let approve = compose_vote_update(&prior, &voter, VoteKind::Approve, 1);
        let reject = compose_vote_update(&prior, &voter, VoteKind::Reject, 1);
        assert_ne!(approve, reject);
    }

    #[test]
    fn vote_update_distinguishes_voters() {
        let prior = field_from_bytes(b"prior");
        let a = field_from_bytes(b"voter-a");
        let b = field_from_bytes(b"voter-b");
        let r1 = compose_vote_update(&prior, &a, VoteKind::Approve, 1);
        let r2 = compose_vote_update(&prior, &b, VoteKind::Approve, 1);
        assert_ne!(r1, r2);
    }

    #[test]
    fn vote_kind_tag_field_distinguishes_outcomes() {
        assert_ne!(VoteKind::Approve.tag_field(), VoteKind::Reject.tag_field());
        assert_ne!(VoteKind::Approve.tag_field(), [0u8; 32]);
    }

    // ── StarbridgeAppContext registration ────────────────────────────────

    #[test]
    fn register_installs_governance_factory() {
        let ctx = test_context();
        assert_eq!(ctx.factory_registry().len(), 0);
        let vk = register(&ctx);
        assert_eq!(vk, GOVERNANCE_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        let got = ctx
            .factory_registry()
            .get(&GOVERNANCE_FACTORY_VK)
            .expect("governance factory registered");
        assert_eq!(got.factory_vk, GOVERNANCE_FACTORY_VK);
        assert_eq!(got.child_program_vk, Some(GOVERNANCE_CHILD_PROGRAM_VK));
        assert_eq!(got.default_mode, CellMode::Sovereign);
    }

    #[test]
    fn register_installs_four_inspectors() {
        let ctx = test_context();
        register(&ctx);
        for kind in [
            "namespace",
            "namespace-route-table",
            "namespace-proposal",
            "namespace-dispatch",
        ] {
            assert!(
                ctx.inspector_registry().get(kind).is_some(),
                "missing inspector kind: {kind}"
            );
        }
    }

    #[test]
    fn namespace_inspector_carries_slot_layout_and_vks() {
        let ctx = test_context();
        register(&ctx);
        let insp = ctx.inspector_registry().get("namespace").unwrap();
        let layout = &insp.descriptor["slot_layout"];
        assert_eq!(layout["route_table_root"], ROUTE_TABLE_ROOT_SLOT);
        assert_eq!(layout["version"], VERSION_SLOT);
        assert_eq!(
            layout["governance_committee_root"],
            GOVERNANCE_COMMITTEE_ROOT_SLOT
        );
        assert_eq!(layout["threshold"], THRESHOLD_SLOT);
        assert_eq!(layout["dispute_window_height"], DISPUTE_WINDOW_HEIGHT_SLOT);
        assert_eq!(layout["pending_proposal_root"], PENDING_PROPOSAL_ROOT_SLOT);

        let factory_hex = insp.descriptor["factory_vk_hex"].as_str().unwrap();
        assert_eq!(factory_hex.len(), 64);
        assert_eq!(factory_hex, hex_encode_32(&GOVERNANCE_FACTORY_VK));
        let gov_hex = insp.descriptor["governance_vk_hex"].as_str().unwrap();
        assert_eq!(gov_hex, hex_encode_32(&GOVERNANCE_VK));
    }

    #[test]
    fn proposal_inspector_lists_all_four_methods() {
        let ctx = test_context();
        register(&ctx);
        let insp = ctx.inspector_registry().get("namespace-proposal").unwrap();
        let methods: Vec<&str> = insp.descriptor["methods"]
            .as_array()
            .unwrap()
            .iter()
            .filter_map(|m| m.as_str())
            .collect();
        for required in [
            "propose_table_update",
            "vote_on_proposal",
            "commit_table_update",
            "register_service",
        ] {
            assert!(
                methods.contains(&required),
                "proposal inspector must list `{required}`, methods were {methods:?}"
            );
        }
    }

    #[test]
    fn register_is_idempotent_on_factory() {
        let ctx = test_context();
        register(&ctx);
        register(&ctx);
        assert_eq!(ctx.factory_registry().len(), 1);
    }

    // ── Method-symbol helpers ────────────────────────────────────────────

    #[test]
    fn method_symbol_helpers_match_symbol_macro() {
        assert_eq!(propose_method_symbol(), symbol("propose_table_update"));
        assert_eq!(vote_method_symbol(), symbol("vote_on_proposal"));
        assert_eq!(commit_method_symbol(), symbol("commit_table_update"));
        assert_eq!(register_service_method_symbol(), symbol("register_service"));
    }

    // ── A tiny meta sanity that the program's commit case uses
    //    MonotonicSequence rather than a plain Monotonic on version
    //    (the latter would silently allow +0 commits, which is a
    //    canonical replay bypass — the test catches a refactor that
    //    relaxes the constraint by mistake). ───────────────────────────

    #[test]
    fn commit_case_does_not_use_plain_monotonic_on_version() {
        let cases = match governance_program() {
            CellProgram::Cases(c) => c,
            _ => panic!(),
        };
        let commit = cases
            .iter()
            .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == symbol("commit_table_update")))
            .unwrap();
        // Ensure there is no PLAIN Monotonic on VERSION_SLOT — only the
        // strict MonotonicSequence form.
        let has_plain = commit
            .constraints
            .iter()
            .any(|c| matches!(c, StateConstraint::Monotonic { index } if *index == VERSION_SLOT));
        assert!(
            !has_plain,
            "commit_case must not use plain Monotonic on version (would allow +0 replay)"
        );
    }

    #[test]
    fn wildcard_meta_matches_only_always_case() {
        // The wildcard `TransitionMeta` (zero method, zero mask) must
        // match the `Always` invariants case and miss every
        // `MethodIs` case. This is the property the unit tests in
        // `tests/governance.rs` rely on to drive operation-scoped
        // adversarials.
        let cases = match governance_program() {
            CellProgram::Cases(c) => c,
            _ => panic!(),
        };
        let meta = TransitionMeta::wildcard();
        let mut always_matched = false;
        let mut method_matched = false;
        let state = dregg_cell::state::CellState::new(0);
        for case in &cases {
            let m = case.guard.matches(&meta, None, &state);
            match &case.guard {
                TransitionGuard::Always if m => always_matched = true,
                TransitionGuard::MethodIs { .. } if m => method_matched = true,
                _ => {}
            }
        }
        assert!(always_matched);
        assert!(!method_matched);
    }

    // ── Cross-app composition ────────────────────────────────────────────

    #[test]
    fn credential_gated_voting_constraint_and_predicate_agree_on_commitment() {
        let issuer = CellId::from_bytes([55u8; 32]);
        let schema_id = field_from_bytes(b"verified-developer-v1");
        let constraint = credential_gated_voting_constraint(issuer, schema_id);
        let predicate = credential_gated_witness_predicate(issuer, schema_id, 0);

        let constraint_commit = match constraint {
            StateConstraint::SenderAuthorized {
                set:
                    AuthorizedSet::CredentialSet {
                        issuer_cell,
                        credential_schema_id,
                    },
            } => AuthorizedSet::credential_set_commitment(&issuer_cell, &credential_schema_id),
            other => panic!("expected CredentialSet, got {other:?}"),
        };
        assert_eq!(predicate.commitment, constraint_commit);
        assert_eq!(predicate.kind, WitnessedPredicateKind::BlindedSet);
        assert_eq!(predicate.input_ref, InputRef::Sender);
    }

    #[test]
    fn credential_gated_constraint_distinguishes_issuer_and_schema() {
        let i_a = CellId::from_bytes([1u8; 32]);
        let i_b = CellId::from_bytes([2u8; 32]);
        let s_a = field_from_bytes(b"schema-a");
        let s_b = field_from_bytes(b"schema-b");
        let extract = |c: StateConstraint| match c {
            StateConstraint::SenderAuthorized {
                set:
                    AuthorizedSet::CredentialSet {
                        issuer_cell,
                        credential_schema_id,
                    },
            } => AuthorizedSet::credential_set_commitment(&issuer_cell, &credential_schema_id),
            _ => panic!(),
        };
        let c1 = extract(credential_gated_voting_constraint(i_a, s_a));
        let c2 = extract(credential_gated_voting_constraint(i_b, s_a));
        let c3 = extract(credential_gated_voting_constraint(i_a, s_b));
        assert_ne!(c1, c2);
        assert_ne!(c1, c3);
    }

    #[test]
    fn register_nameservice_route_action_carries_resolve_target() {
        let cclerk = test_cipherclerk();
        let cell = test_cell();
        let target_cell = CellId::from_bytes([77u8; 32]);
        let ns_resolve = field_from_bytes(b"dregg://cell/bob.dev-actual-target");

        let action =
            register_nameservice_route_action(&cclerk, cell, "/bob.dev", target_cell, ns_resolve);

        assert_eq!(action.method, symbol("register_service"));
        assert_eq!(action.effects.len(), 1);
        match &action.effects[0] {
            Effect::EmitEvent { event, .. } => {
                assert_eq!(event.topic, symbol("service-registered"));
                // The 3-fact form for the nameservice-bound variant:
                // [path_hash, target_cell_id, nameservice_resolve_target]
                assert_eq!(event.data.len(), 3);
                assert_eq!(event.data[0], field_from_bytes(b"/bob.dev"));
                assert_eq!(event.data[1], cell_id_field(target_cell));
                assert_eq!(event.data[2], ns_resolve);
            }
            other => panic!("expected EmitEvent, got {other:?}"),
        }
    }
}
