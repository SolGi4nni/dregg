//! # Polis builders — the SDK surface for governance cells (council /
//! constitution / forward-certified amendment) and budgeted worker mandates.
//!
//! The cell programs live in [`starbridge_polis`] (per-charter
//! content-addressed [`FactoryDescriptor`]s whose `state_constraints` ARE the
//! state machines); this module builds the turns that drive them, made of
//! SURVIVING verbs only:
//!
//! * [`Effect::CreateCellFromFactory`] — birth the cell,
//! * [`Effect::SetField`] — stage proposals / approve / certify / step the
//!   machine / pin terms,
//! * [`Effect::Transfer`] — fund treasuries and worker slices, pay out,
//! * [`Effect::GrantCapability`] — the one-time adopt self-grant
//!   ([`crate::factories`] pattern; same [`ADOPT_TURN_FEE`]).
//!
//! **The safety is NOT in these builders** — it is in the installed
//! [`dregg_cell::CellProgram`], which the executor re-evaluates on EVERY turn
//! that touches the cell. A caller who hand-writes a turn against a polis
//! cell faces the same program gate (the e2e teeth in
//! `sdk/tests/polis_*_e2e.rs` do exactly that). What the builders add is the
//! ONE sensible turn shape per ceremony step, plus the cross-cell glue the
//! constraint grammar cannot express (documented per-function below and in
//! the `starbridge_polis` lib docs "expressibility gaps").
//!
//! ## Bootstrap lifecycle (every polis cell family)
//!
//! 1. **Plan** — `create_*` builds a [`GovernanceCellPlan`].
//! 2. **Deploy** — `AgentRuntime::deploy_factory(plan.descriptor.clone())`.
//! 3. **Create** — execute `plan.create_effects` (ordinary agent turn).
//! 4. **Fund** — execute `plan.fund_effects`
//!    (`endowment + ADOPT_TURN_FEE` in; exactly `endowment` remains after adopt).
//! 5. **Adopt** — `AgentRuntime::execute_as(plan.cell_id, plan.adopt_effects, ADOPT_TURN_FEE)`.
//! 6. **Drive** — ceremony turns via `AgentRuntime::execute_on(plan.cell_id, ..)`,
//!    each decided by the installed program.

use crate::factories::ADOPT_TURN_FEE;
use dregg_cell::state::FieldElement;
use dregg_cell::{
    AuthRequired, CapabilityRef, CellId, CellMode, FactoryCreationParams, FactoryDescriptor,
    field_from_u64,
};
use dregg_turn::Effect;

pub use starbridge_polis::council::{
    AmendmentTerms, CouncilCharter, CouncilStatus, ProposalState, STATE_APPROVED, STATE_DRAFT,
    STATE_EXECUTED, STATE_PROPOSED, STATE_REJECTED, amendment_factory_descriptor,
    council_factory_descriptor, inspect_council,
};
pub use starbridge_polis::constitution::{
    ConstitutionParams, constitution_factory_descriptor,
};
pub use starbridge_polis::mandate::{
    WorkerMandate, tool_scope_commitment, worker_factory_descriptor,
};
pub use starbridge_polis::{PolisError, party_field};

use starbridge_polis::{STATE_SLOT, constitution, council, mandate};

/// A planned polis cell: the published factory + the three bootstrap turns
/// (create / fund / adopt — see the module docs lifecycle). Ceremony turns
/// are built by the per-family functions below.
#[derive(Clone, Debug)]
pub struct GovernanceCellPlan {
    /// The per-charter content-addressed factory descriptor. Deploy BEFORE
    /// executing [`Self::create_effects`].
    pub descriptor: FactoryDescriptor,
    /// `descriptor.factory_vk`, for convenience.
    pub factory_vk: [u8; 32],
    /// The deterministic id of the cell
    /// (`CellId::derive_raw(owner_pubkey, token_id)`).
    pub cell_id: CellId,
    /// Turn 1 (agent turn): birth the cell from the factory.
    pub create_effects: Vec<Effect>,
    /// Turn 2 (agent turn): one `Transfer` of `endowment + ADOPT_TURN_FEE`
    /// into the cell.
    pub fund_effects: Vec<Effect>,
    /// Turn 3 (cell-agent turn — `execute_as(cell_id, .., ADOPT_TURN_FEE)`):
    /// the cell self-grants the operator a c-list capability on itself.
    pub adopt_effects: Vec<Effect>,
}

/// Shared bootstrap-plan constructor (the [`crate::factories`] shape minus
/// the per-family open turn). `endowment` is what remains in the cell after
/// the adopt turn burns its fee: a council treasury, a worker's budget
/// slice, or 0.
fn bootstrap_plan(
    descriptor: FactoryDescriptor,
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    operator: CellId,
    funder: CellId,
    endowment: u64,
) -> GovernanceCellPlan {
    let factory_vk = descriptor.factory_vk;
    let cell_id = CellId::derive_raw(&owner_pubkey, &token_id);
    let params = FactoryCreationParams {
        mode: CellMode::Hosted,
        program_vk: descriptor.child_program_vk,
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey,
    };
    GovernanceCellPlan {
        factory_vk,
        cell_id,
        create_effects: vec![Effect::CreateCellFromFactory {
            factory_vk,
            owner_pubkey,
            token_id,
            params,
        }],
        fund_effects: vec![Effect::Transfer {
            from: funder,
            to: cell_id,
            amount: endowment + ADOPT_TURN_FEE,
        }],
        adopt_effects: vec![Effect::GrantCapability {
            from: cell_id,
            to: operator,
            cap: CapabilityRef {
                target: cell_id,
                slot: 0, // assigned by the recipient c-list at install
                permissions: AuthRequired::Signature,
                breadstuff: None,
                expires_at: None,
                allowed_effects: None,
                stored_epoch: None,
            },
        }],
        descriptor,
    }
}

fn set(cell: CellId, index: u8, value: FieldElement) -> Effect {
    Effect::SetField {
        cell,
        index: index as usize,
        value,
    }
}

// =============================================================================
// Council — M-of-N proposal cells
// =============================================================================

/// Plan a new proposal cell of `charter`'s council.
///
/// **Safety contract** (enforced by the installed program — see
/// `starbridge_polis::council`): one write-once proposal hash per cell; an
/// approval per member slot, `{0,1}` and monotone; certification
/// (`APPROVED_FLAG := 1`) is admitted only when `Σ approvals >= threshold`
/// (`AffineLe`); APPROVED/EXECUTED demand the certified flag; REJECTED and
/// EXECUTED are terminal with no outgoing transition row (no double
/// execute). `endowment` funds the cell's own balance (a per-proposal
/// treasury the executed action may pay out of); use 0 for pure
/// signaling proposals.
pub fn create_council_proposal(
    charter: &CouncilCharter,
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    operator: CellId,
    funder: CellId,
    endowment: u64,
) -> Result<GovernanceCellPlan, PolisError> {
    Ok(bootstrap_plan(
        council_factory_descriptor(charter)?,
        owner_pubkey,
        token_id,
        operator,
        funder,
        endowment,
    ))
}

/// Derive the council charter the CONSTITUTION prescribes: `members` at the
/// constitutional `council_threshold`. The polis's ordinary governance runs
/// under the constitution this way — the threshold parameter is COPIED into
/// the proposal descriptors at build (the documented cross-cell pattern,
/// `starbridge_polis` gap 2), so anyone can recompute a proposal factory
/// from the published constitution + membership and verify the council is
/// the constitutional one.
pub fn council_charter_from_constitution(
    constitution: &ConstitutionParams,
    members: Vec<CellId>,
) -> CouncilCharter {
    CouncilCharter {
        members,
        threshold: constitution.council_threshold,
    }
}

/// Plan a constitution-governed proposal cell: the charter threshold comes
/// from the constitution ([`council_charter_from_constitution`]) and the
/// proposal treasury is capped by the constitutional `treasury_cap` —
/// fail-closed AT BUILD (the cell balance is sealed from `StateConstraint`,
/// so the cap cannot be a program gate; this builder is the documented
/// enforcement point, and the descriptor it produces is recomputable by any
/// verifier from the published constitution).
pub fn create_council_proposal_under(
    constitution: &ConstitutionParams,
    members: Vec<CellId>,
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    operator: CellId,
    funder: CellId,
    endowment: u64,
) -> Result<GovernanceCellPlan, PolisError> {
    if endowment > constitution.treasury_cap {
        return Err(PolisError::EndowmentExceedsTreasuryCap {
            endowment,
            cap: constitution.treasury_cap,
        });
    }
    create_council_proposal(
        &council_charter_from_constitution(constitution, members),
        owner_pubkey,
        token_id,
        operator,
        funder,
        endowment,
    )
}

/// Build the propose turn: stage `action_hash` (write-once), publish the
/// membership commitment, and step DRAFT → PROPOSED.
///
/// **Safety contract**: the program rejects a second proposal on the same
/// cell (`WriteOnce`), any state step without a staged hash (`BoundedBy`),
/// and a membership commitment differing from the charter literal (pin).
pub fn propose(cell: CellId, charter: &CouncilCharter, action_hash: FieldElement) -> Vec<Effect> {
    vec![
        set(cell, council::PROPOSAL_HASH_SLOT, action_hash),
        set(cell, council::MEMBERS_COMMIT_SLOT, charter.members_commitment()),
        set(cell, STATE_SLOT, field_from_u64(council::STATE_PROPOSED)),
    ]
}

/// Build member `member_index`'s approval turn: set that member's approval
/// slot to 1.
///
/// **Safety contract**: the slot is `{0,1}` and monotone (approve-once; no
/// un-approve), admitted only while a proposal is staged. **Gap 1 (see
/// `starbridge_polis` lib docs)**: the program cannot verify the SIGNER is
/// member `member_index` — slot↔member binding is capability possession +
/// operator discipline; the receipt records the signer for audit.
pub fn approve(
    cell: CellId,
    charter: &CouncilCharter,
    member_index: usize,
) -> Result<Vec<Effect>, PolisError> {
    let slot = charter.approval_slot(member_index)?;
    Ok(vec![set(cell, slot, field_from_u64(1))])
}

/// Build the certification turn: arm the approved flag and step
/// PROPOSED → APPROVED.
///
/// **Safety contract**: the EXECUTOR rejects this turn unless
/// `Σ approvals >= threshold` in the post-state (the `AffineLe` gate) — there
/// is no operator override. Approvals and the flag are monotone, so the
/// threshold remains witnessed by the cell state forever after.
pub fn certify_approval(cell: CellId) -> Vec<Effect> {
    vec![
        set(cell, council::APPROVED_FLAG_SLOT, field_from_u64(1)),
        set(cell, STATE_SLOT, field_from_u64(council::STATE_APPROVED)),
    ]
}

/// Build the execute turn: step APPROVED → EXECUTED **carrying the proposed
/// action's effects in the same turn**, so the receipt binds the action to
/// the proposal cell.
///
/// **Safety contract**: the program admits the step only from APPROVED with
/// the certified flag, exactly once (EXECUTED is terminal/inert). **Gap 3**:
/// the program cannot check `action_effects` hash to the staged
/// `PROPOSAL_HASH` — verifiers recompute it from the receipt; this builder
/// is the one place that assembles the pair.
pub fn execute_proposal(cell: CellId, action_effects: Vec<Effect>) -> Vec<Effect> {
    let mut effects = vec![set(
        cell,
        STATE_SLOT,
        field_from_u64(council::STATE_EXECUTED),
    )];
    effects.extend(action_effects);
    effects
}

/// Build the reject turn: step PROPOSED → REJECTED (terminal, inert).
pub fn reject_proposal(cell: CellId) -> Vec<Effect> {
    vec![set(cell, STATE_SLOT, field_from_u64(council::STATE_REJECTED))]
}

// =============================================================================
// Constitution — per-version parameter cells
// =============================================================================

/// Plan a new constitution version cell.
///
/// **Safety contract**: the parameters are pinned literals for the cell's
/// whole life — parameter mutation is IMPOSSIBLE on this cell; amendment is
/// reissue (see [`create_amendment`]). The factory births exactly one cell;
/// `plan.descriptor.hash()` is this version's identity (what amendments
/// stage and predecessors record as successor).
pub fn create_constitution(
    params: &ConstitutionParams,
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    operator: CellId,
    funder: CellId,
) -> Result<GovernanceCellPlan, PolisError> {
    Ok(bootstrap_plan(
        constitution_factory_descriptor(params)?,
        owner_pubkey,
        token_id,
        operator,
        funder,
        0,
    ))
}

/// Build the activation turn: write the constitutional parameters and step
/// UNINIT → ACTIVE. The program rejects any parameter differing from the
/// descriptor's published literal.
pub fn activate_constitution(cell: CellId, params: &ConstitutionParams) -> Vec<Effect> {
    vec![
        set(cell, constitution::VERSION_SLOT, field_from_u64(params.version)),
        set(
            cell,
            constitution::COUNCIL_THRESHOLD_SLOT,
            field_from_u64(params.council_threshold),
        ),
        set(
            cell,
            constitution::AMENDMENT_DELAY_SLOT,
            field_from_u64(params.amendment_delay),
        ),
        set(cell, constitution::TREASURY_CAP_SLOT, field_from_u64(params.treasury_cap)),
        set(cell, STATE_SLOT, field_from_u64(constitution::STATE_ACTIVE)),
    ]
}

/// Build the supersede turn: record the successor constitution's descriptor
/// hash and step ACTIVE → SUPERSEDED (terminal, inert).
///
/// **Safety contract**: the program demands a nonzero successor hash, writes
/// it at most once, and admits the step exactly once. **Gap 4**: "only after
/// the amendment was enacted" is cross-cell and carried by the receipt
/// chain — run this AFTER [`enact_amendment`] commits, in the same ceremony.
pub fn supersede_constitution(cell: CellId, successor_hash: FieldElement) -> Vec<Effect> {
    vec![
        set(cell, constitution::SUCCESSOR_HASH_SLOT, successor_hash),
        set(cell, STATE_SLOT, field_from_u64(constitution::STATE_SUPERSEDED)),
    ]
}

// =============================================================================
// Amendment — forward-certified constitutional change
// =============================================================================

/// Assemble the [`AmendmentTerms`] for amending `current` (the in-force
/// parameters) into `successor` (the next version's parameters), proposed at
/// `propose_height`.
///
/// This is the ONE place the cross-cell parameter copy happens (**gap 2**):
/// the council threshold and the cooling delay are read from `current` and
/// BAKED into the amendment descriptor's content address —
/// `enact_not_before = propose_height + current.amendment_delay`, and the
/// certifying council is `members` at `current.council_threshold`. Anyone
/// can recompute the descriptor from the published constitution and verify
/// the amendment cell used the constitutional parameters.
pub fn amendment_terms(
    current: &ConstitutionParams,
    successor: &ConstitutionParams,
    members: Vec<CellId>,
    propose_height: u64,
) -> Result<AmendmentTerms, PolisError> {
    let successor_descriptor = constitution_factory_descriptor(successor)?;
    Ok(AmendmentTerms {
        charter: CouncilCharter {
            members,
            threshold: current.council_threshold,
        },
        new_constitution_hash: successor_descriptor.hash(),
        enact_not_before: propose_height + current.amendment_delay,
    })
}

/// Plan the amendment proposal cell.
///
/// **Safety contract**: the council machine (M-of-N certification, terminal
/// EXECUTED/REJECTED) PLUS the staged successor hash pinned as a descriptor
/// literal PLUS the cooling period: ENACT (the EXECUTED step) is rejected
/// before `terms.enact_not_before` (`TemporalGate`) — the program, not the
/// operator, enforces the cooling-off.
pub fn create_amendment(
    terms: &AmendmentTerms,
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    operator: CellId,
    funder: CellId,
) -> Result<GovernanceCellPlan, PolisError> {
    Ok(bootstrap_plan(
        amendment_factory_descriptor(terms)?,
        owner_pubkey,
        token_id,
        operator,
        funder,
        0,
    ))
}

/// Build the amendment's propose turn: stage the (pinned) successor hash.
pub fn propose_amendment(cell: CellId, terms: &AmendmentTerms) -> Vec<Effect> {
    propose(cell, &terms.charter, terms.new_constitution_hash)
}

/// Build the ENACT turn: step APPROVED → EXECUTED, admitted by the program
/// only at `block_height >= terms.enact_not_before` and only once.
///
/// The full enactment ceremony (the receipt chain IS the forward
/// certification) is three turns, in order:
/// 1. `execute_on(amendment, enact_amendment(amendment))` — the gated step;
/// 2. `execute(successor_plan.create_effects)` + bootstrap +
///    `activate_constitution` — birth the staged successor (its descriptor
///    hash equals the amendment's pinned literal);
/// 3. `execute_on(old, supersede_constitution(old, successor_hash))` —
///    retire the predecessor, recording the successor.
pub fn enact_amendment(cell: CellId) -> Vec<Effect> {
    execute_proposal(cell, vec![])
}

// =============================================================================
// Orchestration — budgeted worker mandates
// =============================================================================

/// Plan a worker mandate cell: the worker's budget slice is the cell's own
/// funded balance (`endowment = mandate.slice`), its tool scope and
/// delegating orchestrator are pinned literals.
///
/// **Safety contract**: overspend cannot commit (kernel conservation — the
/// slice IS the balance, funded exactly once here); the mandate terms are
/// pinned; REVOKED is terminal and inert, so a revoked worker's spends are
/// rejected by the EXECUTOR. Every turn on this cell yields a receipt whose
/// cell id resolves to this content-addressed mandate (**gap 6**: per-tool
/// gating is the MCP cap layer's job; the pinned scope is the published
/// audit anchor).
pub fn spawn_worker_mandate(
    mandate: &WorkerMandate,
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    funder: CellId,
) -> Result<GovernanceCellPlan, PolisError> {
    Ok(bootstrap_plan(
        worker_factory_descriptor(mandate)?,
        owner_pubkey,
        token_id,
        mandate.orchestrator,
        funder,
        mandate.slice,
    ))
}

/// Build the activation turn: write the mandate terms and step
/// UNINIT → ACTIVE. The program rejects terms differing from the
/// descriptor's published literals.
pub fn activate_worker(cell: CellId, mandate: &WorkerMandate) -> Vec<Effect> {
    vec![
        set(cell, mandate::SLICE_SLOT, field_from_u64(mandate.slice)),
        set(cell, mandate::TOOL_SCOPE_SLOT, mandate.tool_scope),
        set(cell, mandate::ORCHESTRATOR_SLOT, party_field(mandate.orchestrator)),
        set(cell, mandate::WORKER_TAG_SLOT, mandate.worker_tag),
        set(cell, STATE_SLOT, field_from_u64(mandate::STATE_ACTIVE)),
    ]
}

/// Build a worker spend: one `Transfer` from the worker's slice to `to`.
///
/// **Safety contract**: commits only while ACTIVE (a REVOKED cell has no
/// transition row — even a pure transfer touch is rejected) and only within
/// the remaining balance (conservation). The receipt is the provenance
/// record: `worker` resolves to the content-addressed mandate terms.
pub fn worker_spend(worker: CellId, to: CellId, amount: u64) -> Vec<Effect> {
    vec![Effect::Transfer {
        from: worker,
        to,
        amount,
    }]
}

/// Build the revoke turn: step ACTIVE → REVOKED (terminal, inert),
/// optionally recovering the unspent slice to `recover_to` in the SAME turn
/// (the last turn that can move it — after this the cell is inert and any
/// residue is burned).
pub fn revoke_worker(worker: CellId, recover_to: Option<(CellId, u64)>) -> Vec<Effect> {
    let mut effects = vec![set(
        worker,
        STATE_SLOT,
        field_from_u64(mandate::STATE_REVOKED),
    )];
    if let Some((to, amount)) = recover_to {
        effects.push(Effect::Transfer {
            from: worker,
            to,
            amount,
        });
    }
    effects
}
