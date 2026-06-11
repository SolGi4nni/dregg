//! End-to-end teeth for the polis GOVERNANCE cells (council M-of-N proposal
//! cells / constitution-as-pinned-program / forward-certified amendments) on
//! the REAL executor.
//!
//! These tests drive `AgentRuntime` (the embedded `TurnExecutor`) with turns
//! built by `dregg_sdk::polis` — surviving verbs only (`CreateCellFromFactory`
//! / `SetField` / `Transfer` / the one-time `GrantCapability` adopt
//! self-grant). Every safety property is enforced by the cell program the
//! factory installs (the executor's per-touched-cell program gate), NOT by
//! SDK-side checks: the negative tests hand the executor a well-signed,
//! well-formed turn and assert the EXECUTOR rejects it with
//! `TurnError::ProgramViolation`.
//!
//! The program spec being exercised: `starbridge_polis::{council,
//! constitution}` (see its module docs for the machines and the documented
//! expressibility gaps — what is program-enforced here vs what is carried by
//! capability possession + the receipt chain).

use dregg_cell::{Cell, CellId, field_from_u64};
use dregg_sdk::factories::ADOPT_TURN_FEE;
use dregg_sdk::polis::PolisError;
use dregg_sdk::polis::{
    AmendmentTerms, ConstitutionParams, CouncilCharter, GovernanceCellPlan, ProposalState,
    activate_constitution, amendment_terms, approve, certify_approval,
    council_charter_from_constitution, create_amendment, create_constitution,
    create_council_proposal, create_council_proposal_under, enact_amendment, execute_proposal,
    inspect_council, propose, propose_amendment, reject_proposal, supersede_constitution,
};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, Effect, SdkError, TurnReceipt};
use dregg_turn::TurnError;
use starbridge_polis::STATE_SLOT;
use starbridge_polis::constitution::{
    COUNCIL_THRESHOLD_SLOT, STATE_ACTIVE, STATE_SUPERSEDED, SUCCESSOR_HASH_SLOT,
};
use starbridge_polis::council::{
    APPROVED_FLAG_SLOT, FIRST_APPROVAL_SLOT, PROPOSAL_HASH_SLOT, STATE_APPROVED, STATE_EXECUTED,
    STATE_PROPOSED, STATE_REJECTED,
};

// =============================================================================
// Harness (matches sdk/tests/factory_settlement_e2e.rs)
// =============================================================================

/// A runtime + its agent's cell id + three zero-balance member cells.
///
/// The polis cells are owned by the AGENT's key and the agent is the
/// operator + funder. Members are separate cells: in this harness the
/// operator relays member approvals (gap 1 in the `starbridge_polis` docs —
/// the program cannot bind approval slots to signers; what the tests prove
/// is everything the PROGRAM enforces).
fn harness(domain: &str) -> (AgentRuntime, CellId, Vec<CellId>) {
    let runtime = AgentRuntime::new_simple(AgentCipherclerk::new(), domain);
    let agent = runtime.cell_id();
    let party = |tag: u8| {
        let cell = Cell::with_balance([tag; 32], *blake3::hash(domain.as_bytes()).as_bytes(), 0);
        let id = cell.id();
        runtime
            .ledger()
            .lock()
            .unwrap()
            .insert_cell(cell)
            .expect("fresh party cell");
        id
    };
    let members = vec![party(0xA1), party(0xA2), party(0xA3)];
    (runtime, agent, members)
}

fn agent_pubkey(runtime: &AgentRuntime) -> [u8; 32] {
    runtime
        .cipherclerk()
        .read()
        .unwrap_or_else(|e| e.into_inner())
        .public_key()
        .0
}

fn balance_of(runtime: &AgentRuntime, cell: CellId) -> u64 {
    runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&cell)
        .expect("cell exists")
        .state
        .balance()
}

fn slot_of(runtime: &AgentRuntime, cell: CellId, slot: u8) -> [u8; 32] {
    runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&cell)
        .expect("cell exists")
        .state
        .fields[slot as usize]
}

/// Deploy the plan's factory and run its create + fund + adopt turns.
fn bootstrap(runtime: &mut AgentRuntime, plan: &GovernanceCellPlan) {
    runtime.deploy_factory(plan.descriptor.clone());
    runtime
        .execute(plan.create_effects.clone())
        .expect("create turn (factory birth) must commit");
    runtime
        .execute(plan.fund_effects.clone())
        .expect("fund turn (endowment + adopt fee in) must commit");
    runtime
        .execute_as(plan.cell_id, plan.adopt_effects.clone(), ADOPT_TURN_FEE)
        .expect("adopt turn (operator self-grant) must commit");
}

/// Assert an executor-level cell-program rejection (NOT an SDK-side error).
fn assert_program_violation(result: Result<TurnReceipt, SdkError>, what: &str) {
    match result {
        Err(SdkError::Turn(TurnError::ProgramViolation { .. })) => {}
        Err(other) => panic!("{what}: expected ProgramViolation, got {other:?}"),
        Ok(_) => panic!("{what}: expected the EXECUTOR to reject, but the turn committed"),
    }
}

fn set_field(cell: CellId, slot: u8, value: [u8; 32]) -> Vec<Effect> {
    vec![Effect::SetField {
        cell,
        index: slot as usize,
        value,
    }]
}

fn charter(members: &[CellId], threshold: u64) -> CouncilCharter {
    CouncilCharter {
        members: members.to_vec(),
        threshold,
    }
}

// =============================================================================
// Council — M-of-N proposal cells
// =============================================================================

/// The full happy lifecycle PLUS the threshold tooth: propose → 1 approval →
/// certify REJECTED (1 < M=2) → 2nd approval → certify → execute carries the
/// proposed payout in the same turn; the treasury moves exactly once.
#[test]
fn council_two_of_three_lifecycle_with_threshold_gate() {
    let (mut runtime, agent, members) = harness("polis-council-lifecycle");
    let charter = charter(&members, 2);
    let plan = create_council_proposal(
        &charter,
        agent_pubkey(&runtime),
        [0x01; 32],
        agent,
        agent,
        100,
    )
    .expect("valid charter");
    bootstrap(&mut runtime, &plan);
    assert_eq!(
        balance_of(&runtime, plan.cell_id),
        100,
        "proposal treasury funded"
    );

    // Propose: stage the action hash.
    let action_hash = *blake3::hash(b"pay the grantee 100").as_bytes();
    runtime
        .execute_on(plan.cell_id, propose(plan.cell_id, &charter, action_hash))
        .expect("propose must commit");
    assert_eq!(
        slot_of(&runtime, plan.cell_id, STATE_SLOT),
        field_from_u64(STATE_PROPOSED)
    );

    // One approval is not the threshold: certification is REJECTED BY THE
    // EXECUTOR (the AffineLe gate), not by any SDK check.
    runtime
        .execute_on(plan.cell_id, approve(plan.cell_id, &charter, 0).unwrap())
        .expect("member 0 approval must commit");
    assert_program_violation(
        runtime.execute_on(plan.cell_id, certify_approval(plan.cell_id)),
        "certify with 1 of 2 required approvals",
    );

    // Legibility: read the machine back out of the ledger.
    let fields = runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&plan.cell_id)
        .unwrap()
        .state
        .fields;
    let status = inspect_council(&charter, &fields);
    assert_eq!(status.state, ProposalState::Proposed);
    assert_eq!(status.proposal_hash, action_hash);
    assert!(
        status.members_commit_matches,
        "the cell publishes its charter"
    );
    assert_eq!(status.approvals, vec![true, false, false]);
    assert_eq!((status.approval_count, status.threshold), (1, 2));
    assert!(!status.certified);

    // Second distinct member approves; certification commits.
    runtime
        .execute_on(plan.cell_id, approve(plan.cell_id, &charter, 1).unwrap())
        .expect("member 1 approval must commit");
    runtime
        .execute_on(plan.cell_id, certify_approval(plan.cell_id))
        .expect("certify at threshold must commit");
    assert_eq!(
        slot_of(&runtime, plan.cell_id, STATE_SLOT),
        field_from_u64(STATE_APPROVED)
    );

    // Execute: the EXECUTED step and the proposed action ride one turn.
    let grantee = members[2]; // any payable cell
    runtime
        .execute_on(
            plan.cell_id,
            execute_proposal(
                plan.cell_id,
                vec![Effect::Transfer {
                    from: plan.cell_id,
                    to: grantee,
                    amount: 100,
                }],
            ),
        )
        .expect("execute at APPROVED must commit");
    assert_eq!(
        slot_of(&runtime, plan.cell_id, STATE_SLOT),
        field_from_u64(STATE_EXECUTED)
    );
    assert_eq!(
        balance_of(&runtime, grantee),
        100,
        "treasury paid exactly once"
    );
    assert_eq!(balance_of(&runtime, plan.cell_id), 0);

    // Final legibility check: the executed proposal reads back as such.
    let fields = runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&plan.cell_id)
        .unwrap()
        .state
        .fields;
    let status = inspect_council(&charter, &fields);
    assert_eq!(status.state, ProposalState::Executed);
    assert!(status.certified);
    assert_eq!(status.approval_count, 2);
}

/// The constitution GOVERNS ordinary proposals: the council threshold is the
/// constitutional parameter (copied at build, content-addressed) and the
/// proposal treasury is capped by `treasury_cap` — fail-closed at build.
#[test]
fn constitution_governed_proposal() {
    let (mut runtime, agent, members) = harness("polis-governed-proposal");
    let v1 = params_v1(); // threshold 2, treasury cap 1_000

    // Over the constitutional treasury cap: never becomes a descriptor.
    assert!(matches!(
        create_council_proposal_under(
            &v1,
            members.clone(),
            agent_pubkey(&runtime),
            [0x40; 32],
            agent,
            agent,
            1_001,
        ),
        Err(PolisError::EndowmentExceedsTreasuryCap {
            endowment: 1_001,
            cap: 1_000
        })
    ));

    // Under the cap: the charter is the constitutional one, and the
    // descriptor is recomputable from constitution + membership.
    let plan = create_council_proposal_under(
        &v1,
        members.clone(),
        agent_pubkey(&runtime),
        [0x40; 32],
        agent,
        agent,
        1_000,
    )
    .expect("under the cap");
    let charter = council_charter_from_constitution(&v1, members.clone());
    assert_eq!(charter.threshold, v1.council_threshold);
    assert_eq!(
        plan.descriptor.hash(),
        create_council_proposal(
            &charter,
            agent_pubkey(&runtime),
            [0x40; 32],
            agent,
            agent,
            0
        )
        .unwrap()
        .descriptor
        .hash(),
        "the governed proposal runs the constitutional council's program"
    );
    bootstrap(&mut runtime, &plan);
    runtime
        .execute_on(
            plan.cell_id,
            propose(plan.cell_id, &charter, *blake3::hash(b"act").as_bytes()),
        )
        .expect("propose under the constitution");
    runtime
        .execute_on(plan.cell_id, approve(plan.cell_id, &charter, 0).unwrap())
        .expect("approve");
    // The constitutional threshold (2) gates certification on this cell too.
    assert_program_violation(
        runtime.execute_on(plan.cell_id, certify_approval(plan.cell_id)),
        "certify below the CONSTITUTIONAL threshold",
    );
}

/// No-double-execute: EXECUTED is terminal and inert — a second execute, a
/// state rollback, and even a transfer INTO the executed cell are rejected.
#[test]
fn council_no_double_execute() {
    let (mut runtime, agent, members) = harness("polis-council-double");
    let charter = charter(&members, 1);
    let plan = create_council_proposal(
        &charter,
        agent_pubkey(&runtime),
        [0x02; 32],
        agent,
        agent,
        0,
    )
    .expect("valid charter");
    bootstrap(&mut runtime, &plan);

    runtime
        .execute_on(
            plan.cell_id,
            propose(plan.cell_id, &charter, *blake3::hash(b"act").as_bytes()),
        )
        .expect("propose");
    runtime
        .execute_on(plan.cell_id, approve(plan.cell_id, &charter, 0).unwrap())
        .expect("approve");
    runtime
        .execute_on(plan.cell_id, certify_approval(plan.cell_id))
        .expect("certify");
    runtime
        .execute_on(plan.cell_id, execute_proposal(plan.cell_id, vec![]))
        .expect("first execute commits");

    assert_program_violation(
        runtime.execute_on(plan.cell_id, execute_proposal(plan.cell_id, vec![])),
        "second execute",
    );
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            set_field(plan.cell_id, STATE_SLOT, field_from_u64(STATE_APPROVED)),
        ),
        "rollback to APPROVED after execute",
    );
    assert_program_violation(
        runtime.execute(vec![Effect::Transfer {
            from: agent,
            to: plan.cell_id,
            amount: 1,
        }]),
        "transfer into an executed proposal cell",
    );
}

/// Approval gating teeth: no approval before a proposal is staged
/// (`BoundedBy`), no un-approve (`Monotonic`), and one member approving the
/// same slot twice does NOT reach a 2-of-N threshold (the structural
/// distinct-approver property).
#[test]
fn council_approval_teeth() {
    let (mut runtime, agent, members) = harness("polis-council-approvals");
    let charter = charter(&members, 2);
    let plan = create_council_proposal(
        &charter,
        agent_pubkey(&runtime),
        [0x03; 32],
        agent,
        agent,
        0,
    )
    .expect("valid charter");
    bootstrap(&mut runtime, &plan);

    // Approve before propose: rejected.
    assert_program_violation(
        runtime.execute_on(plan.cell_id, approve(plan.cell_id, &charter, 0).unwrap()),
        "approval before any proposal is staged",
    );

    runtime
        .execute_on(
            plan.cell_id,
            propose(plan.cell_id, &charter, *blake3::hash(b"act").as_bytes()),
        )
        .expect("propose");

    // Member 0 approves twice (idempotent slot write) — still ONE approver.
    runtime
        .execute_on(plan.cell_id, approve(plan.cell_id, &charter, 0).unwrap())
        .expect("first approval");
    runtime
        .execute_on(plan.cell_id, approve(plan.cell_id, &charter, 0).unwrap())
        .expect("re-approving the same slot is a no-op write");
    assert_program_violation(
        runtime.execute_on(plan.cell_id, certify_approval(plan.cell_id)),
        "certify with one DISTINCT approver under M=2",
    );

    // Un-approve: rejected (monotone approval bits).
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            set_field(plan.cell_id, FIRST_APPROVAL_SLOT, [0u8; 32]),
        ),
        "retracting an approval",
    );

    // An approval bit greater than 1: rejected (MemberOf {0,1}).
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            set_field(plan.cell_id, FIRST_APPROVAL_SLOT + 1, field_from_u64(2)),
        ),
        "approval weight stuffing (slot = 2)",
    );
}

/// Non-member approval: with a 2-member charter, the third approval slot is
/// pinned zero — an approval outside the membership CANNOT exist, so the
/// threshold can only be met by charter members.
#[test]
fn council_non_member_approval_rejected() {
    let (mut runtime, agent, members) = harness("polis-council-nonmember");
    let charter = charter(&members[..2], 2);
    let plan = create_council_proposal(
        &charter,
        agent_pubkey(&runtime),
        [0x04; 32],
        agent,
        agent,
        0,
    )
    .expect("valid charter");
    bootstrap(&mut runtime, &plan);
    runtime
        .execute_on(
            plan.cell_id,
            propose(plan.cell_id, &charter, *blake3::hash(b"act").as_bytes()),
        )
        .expect("propose");

    // The would-be "member 2" slot is pinned zero for a 2-member charter.
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            set_field(plan.cell_id, FIRST_APPROVAL_SLOT + 2, field_from_u64(1)),
        ),
        "non-member approval slot write",
    );
    // And the SDK builder refuses the index outright (fail-closed at build).
    assert!(approve(plan.cell_id, &charter, 2).is_err());

    // Arming the flag by brute force without approvals: the AffineLe gate.
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            set_field(plan.cell_id, APPROVED_FLAG_SLOT, field_from_u64(1)),
        ),
        "arming the approved flag with zero approvals",
    );
}

/// One proposal per cell: the staged hash is write-once; a rejected proposal
/// cell is terminal and cannot be revived.
#[test]
fn council_proposal_staging_teeth() {
    let (mut runtime, agent, members) = harness("polis-council-staging");
    let charter = charter(&members, 2);
    let plan = create_council_proposal(
        &charter,
        agent_pubkey(&runtime),
        [0x05; 32],
        agent,
        agent,
        0,
    )
    .expect("valid charter");
    bootstrap(&mut runtime, &plan);
    runtime
        .execute_on(
            plan.cell_id,
            propose(plan.cell_id, &charter, *blake3::hash(b"v1").as_bytes()),
        )
        .expect("propose");

    // Re-staging a different action hash: rejected (WriteOnce).
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            set_field(
                plan.cell_id,
                PROPOSAL_HASH_SLOT,
                *blake3::hash(b"v2").as_bytes(),
            ),
        ),
        "swapping the staged proposal hash",
    );

    // Reject, then the cell is inert.
    runtime
        .execute_on(plan.cell_id, reject_proposal(plan.cell_id))
        .expect("reject commits");
    assert_eq!(
        slot_of(&runtime, plan.cell_id, STATE_SLOT),
        field_from_u64(STATE_REJECTED)
    );
    assert_program_violation(
        runtime.execute_on(plan.cell_id, approve(plan.cell_id, &charter, 0).unwrap()),
        "approval on a rejected proposal",
    );
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            set_field(plan.cell_id, STATE_SLOT, field_from_u64(STATE_PROPOSED)),
        ),
        "reviving a rejected proposal",
    );
}

// =============================================================================
// Constitution + forward-certified amendment
// =============================================================================

fn params_v1() -> ConstitutionParams {
    ConstitutionParams {
        version: 1,
        council_threshold: 2,
        amendment_delay: 50,
        treasury_cap: 1_000,
    }
}

fn params_v2() -> ConstitutionParams {
    ConstitutionParams {
        version: 2,
        council_threshold: 3,
        amendment_delay: 100,
        treasury_cap: 2_000,
    }
}

/// Constitution-as-program: once ACTIVE, every parameter slot is pinned —
/// mutation on the cell is impossible (amendment is reissue, see the full
/// ceremony below).
#[test]
fn constitution_params_immutable() {
    let (mut runtime, agent, _members) = harness("polis-constitution-pin");
    let params = params_v1();
    let plan = create_constitution(&params, agent_pubkey(&runtime), [0x10; 32], agent, agent)
        .expect("valid params");
    bootstrap(&mut runtime, &plan);
    runtime
        .execute_on(plan.cell_id, activate_constitution(plan.cell_id, &params))
        .expect("activation writes the published params");
    assert_eq!(
        slot_of(&runtime, plan.cell_id, STATE_SLOT),
        field_from_u64(STATE_ACTIVE)
    );

    // Tampering with the council threshold: rejected by the program.
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            set_field(plan.cell_id, COUNCIL_THRESHOLD_SLOT, field_from_u64(1)),
        ),
        "lowering the council threshold in place",
    );
    // Writing a successor hash while ACTIVE (no supersede step): rejected.
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            set_field(
                plan.cell_id,
                SUCCESSOR_HASH_SLOT,
                *blake3::hash(b"x").as_bytes(),
            ),
        ),
        "successor hash while still active",
    );
    // A second cell from the SAME constitution descriptor: rejected — the
    // factory's creation budget is 1 (one cell per constitution version).
    let twin = create_constitution(&params, agent_pubkey(&runtime), [0x12; 32], agent, agent)
        .expect("valid params");
    assert!(
        runtime.execute(twin.create_effects.clone()).is_err(),
        "a constitution version is a singleton (creation_budget = 1)"
    );

    // Activating with params that differ from the published literals: the
    // factory's pins also bite on the activation turn itself (fresh version,
    // fresh descriptor).
    let mut v3 = params_v1();
    v3.version = 3;
    let plan2 = create_constitution(&v3, agent_pubkey(&runtime), [0x11; 32], agent, agent)
        .expect("valid params");
    bootstrap(&mut runtime, &plan2);
    let mut lying = v3.clone();
    lying.treasury_cap = 999_999;
    assert_program_violation(
        runtime.execute_on(plan2.cell_id, activate_constitution(plan2.cell_id, &lying)),
        "activating with unpublished parameters",
    );
}

/// THE CEREMONY — forward-certified amendment, end to end, with every tooth:
///
/// 1. constitution v1 ACTIVE (threshold 2, delay 50);
/// 2. amendment cell stakes v2's descriptor hash, charter = v1's threshold,
///    cooling gate = propose-height + v1's delay (all content-addressed);
/// 3. approvals × 2, certification;
/// 4. enact BEFORE the cooling period → EXECUTOR REJECTS (`TemporalGate`);
/// 5. at the gate height: enact commits;
/// 6. v2 is born from exactly the staged descriptor and activated;
/// 7. v1 is superseded recording v2's hash; v1 is then inert;
/// 8. double-enact REJECTED; the operator receipt chain links the whole
///    ceremony (the forward certification).
#[test]
fn amendment_full_ceremony_forward_certified() {
    let (mut runtime, agent, members) = harness("polis-amendment-ceremony");
    runtime.set_block_height(1_000);

    // 1. Constitution v1.
    let v1 = params_v1();
    let v1_plan = create_constitution(&v1, agent_pubkey(&runtime), [0x20; 32], agent, agent)
        .expect("valid params");
    bootstrap(&mut runtime, &v1_plan);
    runtime
        .execute_on(v1_plan.cell_id, activate_constitution(v1_plan.cell_id, &v1))
        .expect("v1 active");

    // 2. The amendment terms: parameters COPIED from v1 at build (the
    // documented cross-cell pattern), all content-addressed.
    let v2 = params_v2();
    let terms: AmendmentTerms = amendment_terms(&v1, &v2, members.clone(), 1_000).expect("terms");
    assert_eq!(terms.charter.threshold, v1.council_threshold);
    assert_eq!(terms.enact_not_before, 1_000 + v1.amendment_delay);
    let amend_plan = create_amendment(&terms, agent_pubkey(&runtime), [0x21; 32], agent, agent)
        .expect("valid amendment");
    bootstrap(&mut runtime, &amend_plan);
    runtime
        .execute_on(
            amend_plan.cell_id,
            propose_amendment(amend_plan.cell_id, &terms),
        )
        .expect("amendment proposed");

    // (The "staging a hash other than the published successor is rejected"
    // tooth is proven at the program level in
    // `starbridge_polis::tests::amendment_pins_staged_hash`.)

    // 3. Approvals × threshold, then certification.
    runtime
        .execute_on(
            amend_plan.cell_id,
            approve(amend_plan.cell_id, &terms.charter, 0).unwrap(),
        )
        .expect("member 0 approves");
    runtime
        .execute_on(
            amend_plan.cell_id,
            approve(amend_plan.cell_id, &terms.charter, 1).unwrap(),
        )
        .expect("member 1 approves");
    runtime
        .execute_on(amend_plan.cell_id, certify_approval(amend_plan.cell_id))
        .expect("certified at threshold");

    // 4. ENACT BEFORE THE COOLING PERIOD: the TemporalGate rejects.
    runtime.set_block_height(1_049);
    assert_program_violation(
        runtime.execute_on(amend_plan.cell_id, enact_amendment(amend_plan.cell_id)),
        "enact at height 1049 < 1050 (cooling period)",
    );

    // 5. At the gate: enact commits.
    runtime.set_block_height(1_050);
    let enact_receipt = runtime
        .execute_on(amend_plan.cell_id, enact_amendment(amend_plan.cell_id))
        .expect("enact at the cooling-gate height");
    assert_eq!(
        slot_of(&runtime, amend_plan.cell_id, STATE_SLOT),
        field_from_u64(STATE_EXECUTED)
    );

    // 6. Birth the successor — exactly the staged descriptor.
    let v2_plan = create_constitution(&v2, agent_pubkey(&runtime), [0x23; 32], agent, agent)
        .expect("valid params");
    assert_eq!(
        v2_plan.descriptor.hash(),
        terms.new_constitution_hash,
        "the successor born IS the one the amendment staged (content address)"
    );
    bootstrap(&mut runtime, &v2_plan);
    runtime
        .execute_on(v2_plan.cell_id, activate_constitution(v2_plan.cell_id, &v2))
        .expect("v2 active");

    // 7. Supersede v1, recording the successor hash. v1 is then inert.
    let supersede_receipt = runtime
        .execute_on(
            v1_plan.cell_id,
            supersede_constitution(v1_plan.cell_id, terms.new_constitution_hash),
        )
        .expect("supersede v1");
    assert_eq!(
        slot_of(&runtime, v1_plan.cell_id, STATE_SLOT),
        field_from_u64(STATE_SUPERSEDED)
    );
    assert_eq!(
        slot_of(&runtime, v1_plan.cell_id, SUCCESSOR_HASH_SLOT),
        terms.new_constitution_hash
    );
    assert_program_violation(
        runtime.execute_on(
            v1_plan.cell_id,
            set_field(v1_plan.cell_id, STATE_SLOT, field_from_u64(STATE_ACTIVE)),
        ),
        "resurrecting the superseded constitution",
    );

    // 8. Double-enact: the amendment cell is terminal.
    assert_program_violation(
        runtime.execute_on(amend_plan.cell_id, enact_amendment(amend_plan.cell_id)),
        "double enact",
    );

    // The forward certification: the supersede receipt chains back to the
    // enact receipt through the operator's receipt chain (enact → v2 create
    // → v2 fund → v2 activate → supersede; the adopt turn belongs to the
    // cell's own history). Walk previous_receipt_hash links.
    let chain = runtime
        .cipherclerk()
        .read()
        .unwrap_or_else(|e| e.into_inner())
        .receipt_chain()
        .to_vec();
    let pos = |r: &TurnReceipt| {
        chain
            .iter()
            .position(|c| c.receipt_hash() == r.receipt_hash())
            .expect("ceremony receipt is on the operator chain")
    };
    let (enact_pos, supersede_pos) = (pos(&enact_receipt), pos(&supersede_receipt));
    assert!(
        enact_pos < supersede_pos,
        "enact must precede supersede on the chain"
    );
    for w in chain[enact_pos..=supersede_pos].windows(2) {
        assert_eq!(
            w[1].previous_receipt_hash,
            Some(w[0].receipt_hash()),
            "the ceremony receipts are hash-chained (forward certification)"
        );
    }
}

/// The threshold tooth on the amendment path: without M approvals the
/// certification (and hence enactment) is impossible, even past the gate.
#[test]
fn amendment_enact_without_threshold_rejected() {
    let (mut runtime, agent, members) = harness("polis-amendment-no-threshold");
    runtime.set_block_height(1_000);
    let v1 = params_v1();
    let terms = amendment_terms(&v1, &params_v2(), members, 1_000).expect("terms");
    let plan = create_amendment(&terms, agent_pubkey(&runtime), [0x30; 32], agent, agent)
        .expect("valid amendment");
    bootstrap(&mut runtime, &plan);
    runtime
        .execute_on(plan.cell_id, propose_amendment(plan.cell_id, &terms))
        .expect("proposed");
    runtime
        .execute_on(
            plan.cell_id,
            approve(plan.cell_id, &terms.charter, 0).unwrap(),
        )
        .expect("one approval");

    runtime.set_block_height(2_000); // far past the cooling gate
    assert_program_violation(
        runtime.execute_on(plan.cell_id, certify_approval(plan.cell_id)),
        "certify with 1 of 2 approvals",
    );
    // Brute-force EXECUTED from PROPOSED: no transition row.
    assert_program_violation(
        runtime.execute_on(
            plan.cell_id,
            set_field(plan.cell_id, STATE_SLOT, field_from_u64(STATE_EXECUTED)),
        ),
        "enact directly from PROPOSED",
    );
}
