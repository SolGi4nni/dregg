//! Factory-BIRTH executor tests: the canonical way a name cell comes alive.
//!
//! The other executor tests (`integration_register_full_flow.rs`) install the
//! name program on the agent's own pre-existing cell via `install_program` —
//! they prove the caveats bite, but never that the BIRTH PATH is real. These
//! tests drive the full constructor-transparency lane:
//!
//!   1. `EmbeddedExecutor::deploy_factory(name_factory_descriptor())`,
//!   2. a signed `Effect::CreateCellFromFactory` turn built by
//!      `AppCipherclerk::create_from_factory` and committed via `submit_turn`,
//!   3. the born cell carries the descriptor's `state_constraints` as its
//!      `CellProgram` FOR LIFE,
//!   4. a legal register turn is ACCEPTED through `submit_action`, and
//!   5. hostile turns (name-hash overwrite, expiry rollback) are REFUSED by
//!      the caveats installed at birth — not by any test-side scaffolding.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, EmbeddedExecutor,
};
use dregg_cell::FactoryCreationParams;
use starbridge_nameservice::{
    NAME_FACTORY_VK, build_register_action, build_renew_action, name_child_program_vk,
    name_factory_descriptor, name_hash,
};

fn make_cipherclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0x61u8; 32])
}

/// Deploy the name factory and birth a fresh per-name cell from it through
/// the executor. Returns the born cell's id.
fn birth_name_cell(exec: &EmbeddedExecutor, cclerk: &AppCipherclerk, token_tag: &[u8]) -> CellId {
    exec.deploy_factory(name_factory_descriptor());

    // Fund the agent cell so it can pay turn fees for the whole flow.
    let agent = cclerk.cell_id();
    exec.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&agent) {
            cell.state.set_balance(100_000_000);
        }
    });

    let owner = cclerk.public_key().0;
    let token: [u8; 32] = *blake3::hash(token_tag).as_bytes();
    let params = FactoryCreationParams {
        mode: CellMode::Sovereign,
        program_vk: Some(name_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(NAME_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth).expect("name-cell birth commits");

    let born = CellId::derive_raw(&owner, &token);

    // Hand the registrant an owner capability over the born cell so it can
    // author the register/renew turns that reach it.
    exec.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&agent) {
            agent_cell.capabilities.grant(born, AuthRequired::Signature);
        }
    });

    born
}

/// Birth → the born cell carries the descriptor's slot caveats as its
/// program → a legal first registration is ACCEPTED → a second registration
/// (overwriting the committed `NAME_HASH_SLOT`) is REFUSED by the `WriteOnce`
/// caveat the factory installed at birth.
#[test]
fn factory_born_name_cell_accepts_register_and_refuses_rebind() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let name_cell = birth_name_cell(&exec, &cclerk, b"alice.dregg-cell");

    // The born cell must carry a real CellProgram (the descriptor caveats).
    let has_program = exec.with_ledger_mut(|ledger| {
        ledger
            .get(&name_cell)
            .map(|c| !c.program.is_none())
            .unwrap_or(false)
    });
    assert!(
        has_program,
        "factory-born name cell must carry a CellProgram"
    );

    // ACCEPT: the first registration writes NAME_HASH/OWNER/EXPIRY from zero.
    let owner = [0xAAu8; 32];
    let reg = build_register_action(&cclerk, name_cell, "alice.dregg", owner, 1_000);
    let receipt = exec
        .submit_action(&cclerk, reg)
        .expect("first registration on the factory-born cell must commit");
    assert!(
        !receipt.emitted_events.is_empty(),
        "registration must emit name-registered"
    );

    // The committed binding reads back from the ledger.
    let committed = exec.with_ledger_mut(|ledger| {
        ledger.get(&name_cell).unwrap().state.fields[starbridge_nameservice::NAME_HASH_SLOT]
    });
    assert_eq!(committed, name_hash("alice.dregg"));

    // REFUSE: rebinding the committed name hash violates WriteOnce.
    let rebind = build_register_action(&cclerk, name_cell, "mallory.dregg", owner, 2_000);
    let err = exec
        .submit_action(&cclerk, rebind)
        .expect_err("rebinding a committed name must be refused");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("writeonce") || msg.contains("write-once") || msg.contains("program"),
        "refusal must cite the slot-caveat violation, got: {msg}"
    );

    // ...and the committed binding survives the refused turn.
    let still = exec.with_ledger_mut(|ledger| {
        ledger.get(&name_cell).unwrap().state.fields[starbridge_nameservice::NAME_HASH_SLOT]
    });
    assert_eq!(still, name_hash("alice.dregg"));
}

/// Birth → register → renew forward (ACCEPTED, `Monotonic`) → rollback the
/// expiry below the committed value (REFUSED by the `Monotonic` caveat
/// installed at birth).
#[test]
fn factory_born_name_cell_refuses_expiry_rollback() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let name_cell = birth_name_cell(&exec, &cclerk, b"bob.dregg-cell");

    let owner = [0xBBu8; 32];
    let reg = build_register_action(&cclerk, name_cell, "bob.dregg", owner, 500);
    exec.submit_action(&cclerk, reg)
        .expect("registration must commit");

    // ACCEPT: forward renewal.
    let renew = build_renew_action(&cclerk, name_cell, "bob.dregg", 5_256_000);
    exec.submit_action(&cclerk, renew)
        .expect("forward renewal must commit");

    // REFUSE: rolling the expiry back.
    let rollback = build_renew_action(&cclerk, name_cell, "bob.dregg", 300);
    let err = exec
        .submit_action(&cclerk, rollback)
        .expect_err("expiry rollback must be refused by Monotonic");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program"),
        "refusal must cite the Monotonic violation, got: {msg}"
    );
}
