//! THE POLIS AS A MULTI-INHABITANT SHARED GOVERNANCE WORLD, proven by RUNNING.
//!
//! A council of N **distinct inhabitants** — each a sovereign principal with its
//! OWN cipherclerk / signing key / cap-root, all joining ONE shared ledger — forms
//! an actor-bound `CouncilCharter` (membership + per-member signing key baked into
//! the cell's content-addressed program). One inhabitant PROPOSES (a real verified
//! DRAFT→PROPOSED turn); the others VOTE (real cap-gated turns, each authenticated
//! as a council member via the program's `SenderIs{member_key_i}` clause — the
//! deployed equivalent of the `SenderAuthorized` + membership-witness pattern); and
//! the M-of-N quorum gates the outcome BY CONSTRUCTION: the proposal cell advances
//! to APPROVED only at quorum (`AffineLe { M·flag − Σ approvals ≤ 0 }`), a
//! below-quorum certification is REFUSED by the executor, and a non-member vote is
//! REFUSED by the executor.
//!
//! Every governance step is a REAL verified turn on the embedded `TurnExecutor`
//! (`AgentRuntime`), and every safety property below is enforced by the cell
//! PROGRAM the factory installs — NOT by any SDK-side check. The negative cases
//! hand the executor a well-signed, well-formed turn and assert it rejects with
//! `TurnError::ProgramViolation`.
//!
//! THE POLIS FLOOR — *no subject's exit is foreclosed by the council's actions*.
//! What is EXECUTOR-ENFORCED here: the council's content-addressed descriptor
//! grants only a `CapTarget::SelfCell` template, and the installed program's
//! `state_constraints` bind ONLY the proposal cell's 16 slots. So no council turn
//! — proposal, vote, certify, or execute — can reach into a non-member subject's
//! OWN sovereign cell: the subject's balance, state, and exit (its ability to act
//! / move its funds) are untouched by anything the council does. We demonstrate
//! this by RUNNING: a non-member subject's cell is read before and after the full
//! M-of-N ceremony, and the subject independently spends from its own cell AFTER
//! the council has ACCEPTED — the council never foreclosed the subject's exit.
//! (The whole-world model-level statement — `polis_safety`, every controller
//! bounded by the floor for ALL subjects — lives in `metatheory/.../Polis.lean`
//! and is NOT what this test claims; this test demonstrates the DEPLOYED Rust
//! governance running, with the floor executor-enforced for this concrete world.)

use std::sync::{Arc, RwLock};

use dregg_cell::{AuthRequired, Cell, CapabilityRef, CellId, field_from_u64};
use dregg_sdk::factories::ADOPT_TURN_FEE;
use dregg_sdk::polis::{
    CouncilCharter, ProposalState, approve, certify_approval, create_council_proposal,
    execute_proposal, inspect_council, propose,
};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, Effect, SdkError};
use dregg_turn::{TurnError, TurnReceipt};
use starbridge_polis::STATE_SLOT;
use starbridge_polis::council::{APPROVED_FLAG_SLOT, STATE_APPROVED, STATE_PROPOSED};

/// A single inhabitant of the polis: a sovereign principal with its own
/// cipherclerk / signing key / cap-root, sharing ONE ledger with the others.
struct Inhabitant {
    runtime: AgentRuntime,
}

impl Inhabitant {
    fn cell(&self) -> CellId {
        self.runtime.cell_id()
    }
    fn pubkey(&self) -> [u8; 32] {
        self.runtime
            .cipherclerk()
            .read()
            .unwrap_or_else(|e| e.into_inner())
            .public_key()
            .0
    }
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
    u64::try_from(
        runtime
            .ledger()
            .lock()
            .unwrap()
            .get(&cell)
            .expect("cell exists")
            .state
            .balance(),
    )
    .expect("ordinary cell balance is non-negative")
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

/// Assert an EXECUTOR-level cell-program rejection (NOT an SDK-side error).
fn assert_program_violation(result: Result<TurnReceipt, SdkError>, what: &str) {
    match result {
        Err(SdkError::Turn(TurnError::ProgramViolation { .. })) => {}
        Err(other) => panic!("{what}: expected ProgramViolation, got {other:?}"),
        Ok(_) => panic!("{what}: expected the EXECUTOR to reject, but the turn committed"),
    }
}

/// Bring a new sovereign inhabitant onto an existing shared ledger: its own
/// cipherclerk + signing key, with a funded agent cell so it can pay turn fees.
fn join(into: &AgentRuntime, name: &'static str, balance: i64) -> Inhabitant {
    let rt = AgentRuntime::with_ledger(
        Arc::new(RwLock::new(AgentCipherclerk::new())),
        name,
        into.ledger().clone(),
    );
    let cell = Cell::with_balance(agent_pubkey(&rt), *blake3::hash(name.as_bytes()).as_bytes(), balance);
    assert_eq!(cell.id(), rt.cell_id(), "joined agent cell id must match its key");
    into.ledger()
        .lock()
        .unwrap()
        .insert_cell(cell)
        .expect("fresh joined inhabitant cell");
    Inhabitant { runtime: rt }
}

/// Drive a cell the inhabitant does NOT own by exercising the granted c-list
/// capability — the action is signed with the holder's OWN key, so the SENDER
/// the program's `SenderIs` clause sees is this inhabitant.
fn exercise(
    shared: &AgentRuntime,
    holder: &Inhabitant,
    proposal: CellId,
    effects: Vec<Effect>,
) -> Result<TurnReceipt, SdkError> {
    let cap_slot = shared
        .ledger()
        .lock()
        .unwrap()
        .get(&holder.cell())
        .expect("holder agent cell")
        .capabilities
        .lookup_by_target(&proposal)
        .expect("granted capability installed in the holder's c-list")
        .slot;
    holder.runtime.execute(vec![Effect::ExerciseViaCapability {
        cap_slot,
        inner_effects: effects,
    }])
}

/// THE DEMONSTRATION: a 2-of-3 council of three distinct sovereign inhabitants
/// governs by running — quorum gates ACCEPTED, a non-member vote is refused, a
/// below-quorum certification is refused, and a non-member subject's exit/floor
/// is never foreclosed by the council.
#[test]
fn multi_inhabitant_council_governs_by_running() {
    // ── Three distinct inhabitants on ONE shared world (ledger). Each has its
    //    own cipherclerk / signing key / cap-root. ──────────────────────────
    // `new_simple` funds alice's own agent cell (1M computrons) — enough for
    // the bootstrap + her turns.
    let alice_rt = AgentRuntime::new_simple(AgentCipherclerk::new(), "polis-alice");
    let mut alice = Inhabitant { runtime: alice_rt };
    let bob = join(&alice.runtime, "polis-bob", 200_000);
    let carol = join(&alice.runtime, "polis-carol", 200_000);
    // A NON-MEMBER inhabitant: a sovereign subject of the polis who is NOT on
    // the council. Their cell is the floor-witness.
    let mallory = join(&alice.runtime, "polis-mallory", 50_000);

    const N: usize = 3;
    const M: u64 = 2; // 2-of-3 quorum

    // ── The actor-bound charter: the three members, their published signing
    //    keys, threshold M. The membership + keys are content-addressed into
    //    the proposal cell's program (the deployed `SenderAuthorized` analogue:
    //    `AnyOf[Immutable{slot_i}, SenderIs{member_key_i}]` per member). ──────
    let members = vec![alice.cell(), bob.cell(), carol.cell()];
    let member_keys = vec![alice.pubkey(), bob.pubkey(), carol.pubkey()];
    let charter = CouncilCharter::with_member_keys(members.clone(), M, member_keys);
    assert_eq!(charter.members.len(), N);

    let plan = create_council_proposal(
        &charter,
        agent_pubkey(&alice.runtime),
        [0xC0; 32],
        alice.cell(),
        alice.cell(),
        0, // no treasury for this governance-only proposal
    )
    .expect("valid actor-bound charter");

    // ── Bootstrap: deploy the council factory, birth the proposal cell, and
    //    grant each member a c-list capability on it (the membership witness:
    //    each member genuinely HOLDS a capability — yet the program still binds
    //    each approval slot to its member's KEY). ─────────────────────────────
    alice.runtime.deploy_factory(plan.descriptor.clone());
    alice
        .runtime
        .execute(plan.create_effects.clone())
        .expect("create turn (factory birth) must commit");
    alice
        .runtime
        .execute(plan.fund_effects.clone())
        .expect("fund turn must commit");
    alice
        .runtime
        .execute(vec![Effect::Transfer {
            from: alice.cell(),
            to: plan.cell_id,
            amount: 3 * ADOPT_TURN_FEE,
        }])
        .expect("top up the wider adopt turn's budget");
    let grant_to = |to: CellId| Effect::GrantCapability {
        from: plan.cell_id,
        to,
        cap: CapabilityRef {
            target: plan.cell_id,
            slot: 0,
            permissions: AuthRequired::Signature,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    };
    let mut adopt = plan.adopt_effects.clone();
    adopt.push(grant_to(bob.cell()));
    adopt.push(grant_to(carol.cell()));
    // Also grant mallory (the non-member) a REAL capability — the "stolen /
    // shared capability" shape: holding a capability is NOT membership.
    adopt.push(grant_to(mallory.cell()));
    alice
        .runtime
        .execute_as(plan.cell_id, adopt, 4 * ADOPT_TURN_FEE)
        .expect("adopt turn granting all members + the non-member");

    // =========================================================================
    // PROPOSE — alice proposes; a real verified DRAFT→PROPOSED turn.
    // =========================================================================
    let action_hash = *blake3::hash(b"adopt the harbor-cleanup ordinance").as_bytes();
    let propose_receipt = alice
        .runtime
        .execute_on(plan.cell_id, propose(plan.cell_id, &charter, action_hash))
        .expect("propose must commit (DRAFT -> PROPOSED)");
    assert_eq!(
        slot_of(&alice.runtime, plan.cell_id, STATE_SLOT),
        field_from_u64(STATE_PROPOSED)
    );

    // =========================================================================
    // NON-MEMBER VOTE — REFUSED BY THE EXECUTOR. Mallory holds a real
    // capability on the proposal cell but is not a charter member; the
    // program's `SenderIs{member_key_i}` clause refuses her flipping ANY
    // member's approval slot. (These are MALLORY's OWN turns — she pays her own
    // gas to attempt them; the refusal is the program's, not a council action.)
    // =========================================================================
    assert_program_violation(
        exercise(&alice.runtime, &mallory, plan.cell_id, approve(plan.cell_id, &charter, 0).unwrap()),
        "non-member mallory flipping member 0's approval slot",
    );
    assert_program_violation(
        exercise(&alice.runtime, &mallory, plan.cell_id, approve(plan.cell_id, &charter, 1).unwrap()),
        "non-member mallory flipping member 1's approval slot",
    );

    // ── Record the polis FLOOR witnesses: mallory's sovereign cell, snapshot
    //    AFTER her own (refused) attempts and BEFORE the member ceremony — so
    //    the floor assertion below measures EXACTLY what the COUNCIL's turns
    //    (propose already done; vote/certify/execute below) do to a non-member
    //    subject: nothing. ────────────────────────────────────────────────────
    let mallory_balance_before = balance_of(&alice.runtime, mallory.cell());
    let mallory_state_before = slot_of(&alice.runtime, mallory.cell(), STATE_SLOT);

    // =========================================================================
    // VOTE — each member votes as itself (its own signing key is the sender).
    // bob votes by exercising his granted capability; alice votes on her own
    // cell. After ONE vote (below quorum M=2) certification is REFUSED.
    // =========================================================================
    let alice_vote = alice
        .runtime
        .execute_on(plan.cell_id, approve(plan.cell_id, &charter, 0).unwrap())
        .expect("member 0 (alice) approves her own slot");

    // BELOW QUORUM: 1 < M=2. Certification is refused by the AffineLe gate.
    assert_program_violation(
        alice.runtime.execute_on(plan.cell_id, certify_approval(plan.cell_id)),
        "certify with 1 of 2 required votes (below quorum)",
    );
    // The proposal has NOT advanced.
    assert_eq!(
        slot_of(&alice.runtime, plan.cell_id, STATE_SLOT),
        field_from_u64(STATE_PROPOSED),
        "below-quorum proposal does NOT pass"
    );

    // bob casts the SECOND distinct member vote (his own key is the sender).
    let bob_vote = exercise(&alice.runtime, &bob, plan.cell_id, approve(plan.cell_id, &charter, 1).unwrap())
        .expect("member 1 (bob) approves his own slot");

    // An OPERATOR-relayed vote for carol is refused too: capability possession
    // (alice owns the cell) does not let her cast another member's vote.
    assert_program_violation(
        alice.runtime.execute_on(plan.cell_id, approve(plan.cell_id, &charter, 2).unwrap()),
        "alice relaying carol's vote (sender is alice, not carol)",
    );

    // =========================================================================
    // QUORUM — now Σ votes = 2 = M. Certification commits BY CONSTRUCTION; the
    // proposal advances to APPROVED (ACCEPTED).
    // =========================================================================
    let certify_receipt = alice
        .runtime
        .execute_on(plan.cell_id, certify_approval(plan.cell_id))
        .expect("certify AT quorum must commit");
    assert_eq!(
        slot_of(&alice.runtime, plan.cell_id, STATE_SLOT),
        field_from_u64(STATE_APPROVED),
        "the council ACCEPTED at quorum"
    );
    assert_eq!(slot_of(&alice.runtime, plan.cell_id, APPROVED_FLAG_SLOT), field_from_u64(1));

    // Legibility: read the accepted machine back out of the shared ledger.
    let fields = alice
        .runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&plan.cell_id)
        .unwrap()
        .state
        .fields;
    let status = inspect_council(&charter, &fields);
    assert_eq!(status.state, ProposalState::Approved);
    assert!(status.members_commit_matches, "the cell publishes its actor-bound charter");
    assert_eq!(status.approvals, vec![true, true, false]);
    assert_eq!((status.approval_count, status.threshold), (M, M));
    assert!(status.certified);

    // EXECUTE — the accepted action's effects ride the EXECUTED step turn.
    let execute_receipt = alice
        .runtime
        .execute_on(plan.cell_id, execute_proposal(plan.cell_id, vec![]))
        .expect("execute at APPROVED must commit");

    // =========================================================================
    // THE POLIS FLOOR — mallory's exit was NEVER foreclosed by the council.
    // =========================================================================
    // (1) Executor-enforced: nothing the council did touched mallory's cell.
    assert_eq!(
        balance_of(&alice.runtime, mallory.cell()),
        mallory_balance_before,
        "the council never touched the non-member subject's balance"
    );
    assert_eq!(
        slot_of(&alice.runtime, mallory.cell(), STATE_SLOT),
        mallory_state_before,
        "the council never touched the non-member subject's state"
    );
    // (2) Executor-enforced: mallory can STILL act / exit on her own cell after
    //     the council has ACCEPTED — her exit is open. She moves her own funds
    //     to a fresh sink cell and the move LANDS (proving the exit is live).
    let sink = join(&alice.runtime, "polis-mallory-sink", 0);
    let exit_amount = 10_000u64;
    mallory
        .runtime
        .execute(vec![Effect::Transfer {
            from: mallory.cell(),
            to: sink.cell(),
            amount: exit_amount,
        }])
        .expect("the non-member subject's exit is OPEN after the council accepted");
    assert_eq!(
        balance_of(&alice.runtime, sink.cell()),
        exit_amount,
        "the subject independently exercised its exit (funds landed); the council had no say"
    );

    // ── REPORT (printed under `cargo test -- --nocapture`) ──────────────────
    eprintln!("── MULTI-INHABITANT POLIS COUNCIL — governed by running ──");
    eprintln!("  inhabitants (distinct cap-roots): alice, bob, carol (members) + mallory (non-member subject)");
    eprintln!("  council: {N} members, quorum M = {M} (2-of-3, actor-bound)");
    eprintln!(
        "  PROPOSE receipt   : {} (DRAFT->PROPOSED)",
        hex8(propose_receipt.receipt_hash())
    );
    eprintln!("  VOTE alice receipt: {}", hex8(alice_vote.receipt_hash()));
    eprintln!("  VOTE bob   receipt: {}", hex8(bob_vote.receipt_hash()));
    eprintln!(
        "  CERTIFY receipt   : {} (-> APPROVED at quorum)",
        hex8(certify_receipt.receipt_hash())
    );
    eprintln!("  EXECUTE receipt   : {}", hex8(execute_receipt.receipt_hash()));
    eprintln!("  below-quorum certify: REFUSED (executor ProgramViolation, AffineLe gate)");
    eprintln!("  non-member vote     : REFUSED (executor ProgramViolation, SenderIs clause)");
    eprintln!(
        "  polis floor (mallory's exit): OPEN — executor-enforced (SelfCell-only descriptor); subject spent {exit_amount} after ACCEPT"
    );
}

fn hex8(h: [u8; 32]) -> String {
    h[..4].iter().map(|b| format!("{b:02x}")).collect()
}
