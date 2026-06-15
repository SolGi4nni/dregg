//! App integration checks: the starbridge-apps factory lane.
//!
//! The old `apps/gallery` and `apps/identity` checks were retired in the
//! `apps/ → starbridge-apps/` migration (STARBRIDGE-APPS-PLAN.md §4.1).
//! These checks replace them with the REAL starbridge-apps integration
//! surface (the factory-birth executor lane landed in `90b34bbfa`):
//!
//! - `factory_descriptors_deploy`: every factory descriptor published by the
//!   six factory-birth apps deploys onto an embedded executor and registers
//!   under its declared `factory_vk`.
//! - `subscription_factory_birth`: a subscription cell is BORN through the
//!   executor (`Effect::CreateCellFromFactory` via `submit_turn`), carries
//!   the descriptor's perpetual `state_constraints` as its `CellProgram`,
//!   and a mode-mismatched birth is REFUSED by the factory.
//! - `identity_factory_birth`: an identity-issuer cell is born the same way
//!   and carries all four descriptor constraints (WriteOnce schema +
//!   MonotonicSequence counter + Monotonic revocation root +
//!   SenderAuthorized issuer set).

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, CellId, CellMode, EmbeddedExecutor, StateConstraint,
};
use dregg_cell::{CellProgram, FactoryCreationParams, FactoryDescriptor};

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check(
            "factory_descriptors_deploy",
            check_factory_descriptors_deploy,
        ),
        run_check(
            "subscription_factory_birth",
            check_subscription_factory_birth,
        ),
        run_check("identity_factory_birth", check_identity_factory_birth),
    ]
}

fn make_cipherclerk(tag: u8) -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [tag; 32])
}

/// Fund the agent cell so birth turns can pay their fee.
fn fund_agent(exec: &EmbeddedExecutor, agent: CellId) {
    exec.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&agent) {
            cell.state.set_balance(100_000_000);
        }
    });
}

/// Every factory descriptor of the six factory-birth starbridge-apps deploys
/// and registers under its declared `factory_vk`.
fn check_factory_descriptors_deploy() -> Result<(), String> {
    let cclerk = make_cipherclerk(0x71);
    let exec = EmbeddedExecutor::new(&cclerk, "default");

    let apps: [(&str, Vec<FactoryDescriptor>); 6] = [
        ("nameservice", starbridge_nameservice::factory_descriptors()),
        ("identity", starbridge_identity::factory_descriptors()),
        (
            "subscription",
            starbridge_subscription::factory_descriptors(),
        ),
        (
            "governed-namespace",
            starbridge_governed_namespace::factory_descriptors(),
        ),
        (
            "compartment-workflow-mandate",
            starbridge_compartment_workflow_mandate::factory_descriptors(),
        ),
        (
            "tool-access-delegation",
            starbridge_tool_access_delegation::factory_descriptors(),
        ),
    ];

    for (app, descriptors) in apps {
        if descriptors.is_empty() {
            return Err(format!(
                "{app}: factory_descriptors() returned no descriptors"
            ));
        }
        for descriptor in descriptors {
            let declared_vk = descriptor.factory_vk;
            let deployed_vk = exec.deploy_factory(descriptor);
            if deployed_vk != declared_vk {
                return Err(format!(
                    "{app}: deploy_factory returned vk {:02x}{:02x}.. but descriptor declares {:02x}{:02x}..",
                    deployed_vk[0], deployed_vk[1], declared_vk[0], declared_vk[1]
                ));
            }
        }
    }

    Ok(())
}

/// Birth a subscription cell through the executor: the accept path commits,
/// the born cell carries the descriptor's perpetual slot caveats, and a
/// mode-mismatched birth is refused.
fn check_subscription_factory_birth() -> Result<(), String> {
    let cclerk = make_cipherclerk(0x72);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    exec.deploy_factory(starbridge_subscription::subscription_factory_descriptor());
    fund_agent(&exec, cclerk.cell_id());

    let owner = cclerk.public_key().0;
    let token: [u8; 32] = *blake3::hash(b"preflight-subscription-birth").as_bytes();
    let params = FactoryCreationParams {
        // The descriptor pins Hosted as the default mode.
        mode: CellMode::Hosted,
        program_vk: Some(starbridge_subscription::subscription_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(
        starbridge_subscription::SUBSCRIPTION_FACTORY_VK,
        owner,
        token,
        params,
    );
    exec.submit_turn(&birth)
        .map_err(|e| format!("subscription birth turn rejected: {e}"))?;

    // The born cell exists and carries the descriptor's state_constraints
    // as its CellProgram (the slot caveats bite for life).
    let born = CellId::derive_raw(&owner, &token);
    let descriptor_constraints =
        starbridge_subscription::subscription_factory_descriptor().state_constraints;
    let constraints = exec
        .with_ledger_mut(|ledger| {
            ledger.get(&born).map(|cell| match &cell.program {
                CellProgram::Predicate(cs) => Ok(cs.clone()),
                other => Err(format!(
                    "born subscription cell must carry a Predicate program, got {other:?}"
                )),
            })
        })
        .ok_or("born subscription cell not found in ledger")??;
    if constraints.len() != descriptor_constraints.len() {
        return Err(format!(
            "born cell carries {} constraints, descriptor declares {}",
            constraints.len(),
            descriptor_constraints.len()
        ));
    }

    // REFUSE: a birth whose mode contradicts the descriptor must be rejected
    // by the factory (FactoryError::ModeMismatch through the executor).
    let token_bad: [u8; 32] = *blake3::hash(b"preflight-subscription-birth-refuse").as_bytes();
    let params_bad = FactoryCreationParams {
        mode: CellMode::Sovereign,
        program_vk: Some(starbridge_subscription::subscription_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth_bad = cclerk.create_from_factory(
        starbridge_subscription::SUBSCRIPTION_FACTORY_VK,
        owner,
        token_bad,
        params_bad,
    );
    match exec.submit_turn(&birth_bad) {
        Err(_) => Ok(()),
        Ok(_) => Err("mode-mismatched subscription birth must be REFUSED by the factory".into()),
    }
}

/// Birth an identity-issuer cell through the executor and verify it carries
/// all four of the descriptor's perpetual constraints.
fn check_identity_factory_birth() -> Result<(), String> {
    let cclerk = make_cipherclerk(0x73);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    exec.deploy_factory(starbridge_identity::issuer_factory_descriptor());
    fund_agent(&exec, cclerk.cell_id());

    let owner = cclerk.public_key().0;
    let token: [u8; 32] = *blake3::hash(b"preflight-identity-birth").as_bytes();
    let params = FactoryCreationParams {
        mode: CellMode::Sovereign,
        program_vk: Some(starbridge_identity::issuer_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth =
        cclerk.create_from_factory(starbridge_identity::ISSUER_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth)
        .map_err(|e| format!("issuer birth turn rejected: {e}"))?;

    let born = CellId::derive_raw(&owner, &token);
    let constraints = exec
        .with_ledger_mut(|ledger| {
            ledger.get(&born).map(|cell| match &cell.program {
                CellProgram::Predicate(cs) => Ok(cs.clone()),
                other => Err(format!(
                    "born issuer cell must carry a Predicate program, got {other:?}"
                )),
            })
        })
        .ok_or("born issuer cell not found in ledger")??;

    let schema_slot = starbridge_identity::SCHEMA_COMMITMENT_SLOT as u8;
    let counter_slot = starbridge_identity::ISSUANCE_COUNTER_SLOT as u8;
    let revocation_slot = starbridge_identity::REVOCATION_ROOT_SLOT as u8;

    if !constraints
        .iter()
        .any(|c| matches!(c, StateConstraint::WriteOnce { index } if *index == schema_slot))
    {
        return Err("born issuer missing WriteOnce schema-commitment constraint".into());
    }
    if !constraints.iter().any(
        |c| matches!(c, StateConstraint::MonotonicSequence { seq_index } if *seq_index == counter_slot),
    ) {
        return Err("born issuer missing MonotonicSequence issuance-counter constraint".into());
    }
    if !constraints
        .iter()
        .any(|c| matches!(c, StateConstraint::Monotonic { index } if *index == revocation_slot))
    {
        return Err("born issuer missing Monotonic revocation-root constraint".into());
    }
    if !constraints
        .iter()
        .any(|c| matches!(c, StateConstraint::SenderAuthorized { .. }))
    {
        return Err("born issuer missing SenderAuthorized issuer-set gate".into());
    }
    if constraints.len() != 4 {
        return Err(format!(
            "born issuer must carry exactly the 4 descriptor constraints, got {}",
            constraints.len()
        ));
    }

    Ok(())
}
