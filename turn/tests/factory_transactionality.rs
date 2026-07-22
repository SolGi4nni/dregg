use dregg_cell::{
    AuthRequired, Cell, CellMode, FactoryCreationParams, FactoryDescriptor, Ledger, Permissions,
};
use dregg_turn::{ActionBuilder, ComputronCosts, TurnBuilder, TurnExecutor};

fn open_agent() -> Cell {
    let mut cell = Cell::with_balance([1; 32], [2; 32], 1_000);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    cell
}

#[test]
fn later_ledger_failure_does_not_spend_factory_quota() {
    let agent = open_agent();
    let agent_id = agent.id();
    let owner = [3; 32];
    let token = [4; 32];
    let child = Cell::new_hosted(owner, token);
    let child_id = child.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(child).unwrap();

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    let factory_vk = executor.deploy_factory(FactoryDescriptor {
        factory_vk: [0xF1; 32],
        child_program_vk: None,
        child_vk_strategy: None,
        allowed_cap_templates: vec![],
        field_constraints: vec![],
        state_constraints: vec![],
        default_mode: CellMode::Hosted,
        creation_budget: Some(1),
    });
    let params = FactoryCreationParams {
        mode: CellMode::Hosted,
        program_vk: None,
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };

    let action = ActionBuilder::new_unchecked_for_tests(agent_id, "factory_create", agent_id)
        .effect_create_cell_from_factory(factory_vk, owner, token, params.clone())
        .build();
    let mut first = TurnBuilder::new(agent_id, 0);
    first.add_action(action);
    assert!(
        executor
            .execute(&first.fee(0).build(), &mut ledger)
            .is_rejected(),
        "the duplicate child makes the ledger insertion fail after quota validation"
    );
    assert_eq!(
        executor
            .factory_registry_mut()
            .creation_counts
            .get(&(factory_vk, 0)),
        None,
        "a rejected turn must restore the exact pre-turn factory counter image"
    );

    ledger.remove(&child_id);
    let action = ActionBuilder::new_unchecked_for_tests(agent_id, "factory_create", agent_id)
        .effect_create_cell_from_factory(factory_vk, owner, token, params)
        .build();
    let mut second = TurnBuilder::new(agent_id, 1);
    second.add_action(action);
    assert!(
        executor
            .execute(&second.fee(0).build(), &mut ledger)
            .is_committed(),
        "the one legitimate birth remains available after the rejected attempt"
    );
    assert!(ledger.get(&child_id).is_some());
    assert_eq!(
        executor
            .factory_registry_mut()
            .creation_counts
            .get(&(factory_vk, 0)),
        Some(&1)
    );
}
