//! Polis council ceremony — the governance walkthrough in one binary.
//!
//! Drives a complete 2-of-3 council proposal lifecycle on the REAL executor
//! (the same `AgentRuntime` + `TurnExecutor` the e2e tests use — every rule
//! you see enforced below is enforced by the cell program the factory
//! installs, not by SDK-side checks):
//!
//!   1. charter a 2-of-3 council and birth its proposal cell from a factory
//!      (create → fund the treasury → adopt),
//!   2. PROPOSE: stage an action hash,
//!   3. APPROVE ×1, then try to certify — the EXECUTOR rejects it (1 < 2),
//!   4. APPROVE ×2, certify — now it commits,
//!   5. EXECUTE: the EXECUTED step and the proposed treasury payout ride the
//!      SAME turn, so the receipt binds the action to the proposal,
//!   6. inspect the machine at each stage (`inspect_council` decodes the same
//!      slots `dregg polis council --cell <id>` reads from a live node).
//!
//! Run:
//!   cargo run -p dregg-sdk --example polis_ceremony

use dregg_cell::Cell;
use dregg_sdk::factories::ADOPT_TURN_FEE;
use dregg_sdk::polis::{
    CouncilCharter, approve, certify_approval, create_council_proposal, execute_proposal,
    inspect_council, propose,
};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, Effect};

fn main() {
    // ── 1. An operator agent + three member cells ───────────────────────────
    // The operator owns the proposal cell and relays member approvals (the
    // program binds approvals to member SLOTS; see `starbridge_polis` docs
    // for what is program-enforced vs carried by capability possession).
    let runtime_domain = "polis-ceremony-example";
    let mut runtime = AgentRuntime::new_simple(AgentCipherclerk::new(), runtime_domain);
    let agent = runtime.cell_id();
    let member = |tag: u8| {
        let cell = Cell::with_balance(
            [tag; 32],
            *blake3::hash(runtime_domain.as_bytes()).as_bytes(),
            0,
        );
        let id = cell.id();
        runtime
            .ledger()
            .lock()
            .unwrap()
            .insert_cell(cell)
            .expect("fresh member cell");
        id
    };
    let members = vec![member(0xA1), member(0xA2), member(0xA3)];
    let charter = CouncilCharter::new(members.clone(), 2);
    println!("operator agent cell : {agent}");
    for (i, m) in members.iter().enumerate() {
        println!("council member {i}    : {m}");
    }
    println!("charter             : 2-of-3\n");

    // ── Birth the proposal cell from its content-addressed factory ─────────
    let owner_pubkey = runtime
        .cipherclerk()
        .read()
        .unwrap_or_else(|e| e.into_inner())
        .public_key()
        .0;
    let endowment = 100; // the proposal's treasury
    let plan = create_council_proposal(&charter, owner_pubkey, [0x01; 32], agent, agent, endowment)
        .expect("valid charter");
    runtime.deploy_factory(plan.descriptor.clone());
    runtime
        .execute(plan.create_effects.clone())
        .expect("create turn (factory birth)");
    runtime
        .execute(plan.fund_effects.clone())
        .expect("fund turn (treasury endowment + adopt fee)");
    runtime
        .execute_as(plan.cell_id, plan.adopt_effects.clone(), ADOPT_TURN_FEE)
        .expect("adopt turn (operator self-grant)");
    println!("proposal cell born  : {}", plan.cell_id);
    println!("treasury funded     : {endowment} computrons\n");

    let show = |runtime: &AgentRuntime, label: &str| {
        let fields = runtime
            .ledger()
            .lock()
            .unwrap()
            .get(&plan.cell_id)
            .expect("proposal cell exists")
            .state
            .fields;
        let s = inspect_council(&charter, &fields);
        println!(
            "[{label}] state={:?} approvals={}/{} certified={}",
            s.state, s.approval_count, s.threshold, s.certified
        );
    };
    show(&runtime, "born   ");

    // ── 2. PROPOSE: stage the action hash ──────────────────────────────────
    let action_hash = *blake3::hash(b"pay the grantee 100 computrons").as_bytes();
    runtime
        .execute_on(plan.cell_id, propose(plan.cell_id, &charter, action_hash))
        .expect("propose");
    show(&runtime, "propose");

    // ── 3. One approval is NOT the threshold ────────────────────────────────
    runtime
        .execute_on(plan.cell_id, approve(plan.cell_id, &charter, 0).unwrap())
        .expect("member 0 approval");
    show(&runtime, "approve");
    match runtime.execute_on(plan.cell_id, certify_approval(plan.cell_id)) {
        Err(e) => println!("certify at 1-of-2   : EXECUTOR REJECTED (as it must) — {e}"),
        Ok(_) => panic!("the executor admitted certification below threshold"),
    }

    // ── 4. Second approval, then certification commits ─────────────────────
    runtime
        .execute_on(plan.cell_id, approve(plan.cell_id, &charter, 1).unwrap())
        .expect("member 1 approval");
    runtime
        .execute_on(plan.cell_id, certify_approval(plan.cell_id))
        .expect("certify at threshold");
    show(&runtime, "certify");

    // ── 5. EXECUTE: the payout rides the same turn as the EXECUTED step ────
    let grantee = members[2];
    let receipt = runtime
        .execute_on(
            plan.cell_id,
            execute_proposal(
                plan.cell_id,
                vec![Effect::Transfer {
                    from: plan.cell_id,
                    to: grantee,
                    amount: endowment,
                }],
            ),
        )
        .expect("execute at APPROVED");
    show(&runtime, "execute");

    let grantee_balance = runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&grantee)
        .expect("grantee exists")
        .state
        .balance();
    println!("\ngrantee balance     : {grantee_balance} (treasury paid exactly once)");
    println!("execute turn hash   : {}", hex::encode(receipt.turn_hash));
    println!(
        "receipt hash        : {}",
        hex::encode(receipt.receipt_hash())
    );
    println!(
        "\nThe same machine on a live node decodes with:\n  dregg polis council --cell {}",
        hex::encode(plan.cell_id.0)
    );
}
