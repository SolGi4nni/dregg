//! End-to-end demo of the agent-provenance app on the REAL verified executor.
//!
//! Run with:
//!
//! ```sh
//! cargo run -p starbridge-agent-provenance --example provenance_demo
//! ```
//!
//! It births a provenance log cell from the deployed factory, has an AI agent
//! append a 3-entry hash chain of attested outputs, then demonstrates the two
//! guarantees the app exists for:
//!
//!   1. TAMPER-EVIDENCE — overwriting a committed entry is REJECTED by the
//!      `WriteOnce` slot caveat the factory baked in at birth.
//!   2. VERIFIABILITY   — any party recomputes the hash chain from the published
//!      claims and the committed digests and checks it link-for-link.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, CellId, CellMode, EmbeddedExecutor, Effect,
};
use dregg_cell::FactoryCreationParams;
use starbridge_agent_provenance::{
    GENESIS_PREV, PROVENANCE_FACTORY_VK, build_append_action, claim_digest, entry_digests,
    entry_slot, provenance_child_program_vk, provenance_factory_descriptor, verify_chain,
};

fn hex8(d: &[u8; 32]) -> String {
    d[..8].iter().map(|b| format!("{b:02x}")).collect()
}

fn main() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [9u8; 32]);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    exec.deploy_factory(provenance_factory_descriptor());

    // Fund the agent so it can pay turn fees.
    let agent = cclerk.cell_id();
    exec.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&agent) {
            cell.state.set_balance(100_000_000);
        }
    });

    // Birth a provenance log cell from the factory.
    let owner = cclerk.public_key().0;
    let token: [u8; 32] = *blake3::hash(b"agent-scratchpad-1").as_bytes();
    let params = FactoryCreationParams {
        mode: CellMode::Sovereign,
        program_vk: Some(provenance_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(PROVENANCE_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth).expect("log birth commits");
    let log = CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&agent) {
            agent_cell
                .capabilities
                .grant(log, dregg_app_framework::AuthRequired::Signature);
        }
    });
    println!("✓ provenance log cell born: {}…", hex8(log.as_bytes()));

    // The agent appends a 3-step provenance chain of its attested outputs.
    let claims: Vec<_> = [
        "reasoning: the user asked for X; plan = [search, summarize]",
        "tool-call: web.search(\"dregg verifiable memory\") -> 5 results",
        "final: here is the cited answer ...",
    ]
    .iter()
    .map(|c| claim_digest(c.as_bytes()))
    .collect();
    let honest = entry_digests(&claims);

    let mut prev = GENESIS_PREV;
    for (i, claim) in claims.iter().enumerate() {
        exec.submit_action(&cclerk, build_append_action(&cclerk, log, i, &prev, claim))
            .unwrap_or_else(|e| panic!("append {i} rejected: {e}"));
        println!("✓ appended entry {i}: digest {}… (links prev {}…)", hex8(&honest[i]), hex8(&prev));
        prev = honest[i];
    }

    // Read the committed digests back off the ledger.
    let committed: Vec<_> = exec.with_ledger_mut(|ledger| {
        let cell = ledger.get(&log).expect("log cell");
        (0..claims.len()).map(|i| cell.state.fields[entry_slot(i)]).collect()
    });

    // (1) TAMPER-EVIDENCE: an overwrite of a committed entry is rejected.
    let tamper = {
        let forged = claim_digest(b"a forged rewrite of entry 0");
        cclerk.make_action(
            log,
            "tamper",
            vec![Effect::SetField { cell: log, index: entry_slot(0), value: forged }],
        )
    };
    match exec.submit_action(&cclerk, tamper) {
        Ok(_) => panic!("TAMPER SUCCEEDED — append-only is broken!"),
        Err(e) => println!("✓ tamper REJECTED by the executor: {e}"),
    }
    let after: [u8; 32] = exec
        .with_ledger_mut(|ledger| ledger.get(&log).unwrap().state.fields[entry_slot(0)]);
    assert_eq!(after, honest[0]);
    println!("✓ committed entry 0 UNCHANGED after the rejected tamper");

    // (2) VERIFIABILITY: any party recomputes and verifies the chain.
    assert!(verify_chain(&claims, &committed));
    println!("✓ provenance chain VERIFIES against the published claims");

    // ...and a tampered copy is caught by the same verifier.
    let mut forged = committed.clone();
    forged[1] = claim_digest(b"forged middle");
    assert!(!verify_chain(&claims, &forged));
    println!("✓ a tampered chain is REJECTED by the verifier");

    println!("\nproof-carrying agent provenance: append-only, tamper-evident, verifiable. ( ⌐■_■ )");
}
