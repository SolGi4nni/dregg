//! Cross-app composition gate — identity + CWM + SGM mandate scaffolds.
//!
//! Composes three apps through a single shared `EmbeddedExecutor`:
//!
//!   - `starbridge-identity` — issue → present → verify KYC credential
//!   - `starbridge-compartment-workflow-mandate` — advance `step_cursor`
//!     0→1→2→3 (review → redact → sign) on slots matching Lean
//!     `CompartmentWorkflowMandate.Core` (`step_cursor`, `commitment_anchor`)
//!   - `starbridge-storage-gateway-mandate` — authorize PUT under prefix,
//!     debit `volume_spent`, emit blob-hash audit on slots matching Lean
//!     `StorageGatewayMandate.Core` (`object_key`, `last_op`, `volume_spent`,
//!     `commitment_anchor`)
//!
//! Properties asserted (mirroring `cross_app_composition_e2e.rs`):
//!
//!   1. All turns across identity + both mandate cells form ONE causal receipt
//!      chain (`previous_receipt_hash` links every boundary).
//!   2. Re-executing the same turns on two fresh same-seed executors reproduces
//!      identical state transitions (`turn_hash`, `pre_state_hash`,
//!      `post_state_hash`, `effects_hash`) — replay determinism.

use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, CellId, EmbeddedExecutor};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::program::CellProgram;
use dregg_cell::state::{CellState, FieldElement};
use dregg_cell::{Cell, StateConstraint, field_from_u64};
use dregg_turn::{Action, TurnReceipt};

use starbridge_compartment_workflow_mandate::{
    CHARTER_TERMINAL_SLOT, COMMITMENT_ANCHOR_SLOT as CWM_ANCHOR_SLOT, DEFAULT_CHARTER_STEPS,
    DEFAULT_COMMITMENT_ANCHOR, DEFAULT_STEP_SPEND_POLICY, STEP_CURSOR_SLOT, WorkflowPhase,
    build_advance_step_action, clearance_label, cwm_cell_program,
};
use starbridge_identity::{
    AttrValue, CredentialAttributes, IssuerKeys, Predicate, PredicateRequest, PresentationOptions,
    REVOCATION_ROOT_SLOT, VerificationOptions, build_issue_credential_action,
    build_present_credential_action, build_verify_presentation_action, issue, kyc_schema, present,
};
use starbridge_storage_gateway_mandate::{
    COMMITMENT_ANCHOR_SLOT as SGM_ANCHOR_SLOT, DEFAULT_KEY_PREFIX, DEFAULT_READ_COMPARTMENT,
    DEFAULT_VOLUME_CEILING, KEY_PREFIX_HASH_SLOT, LAST_OP_SLOT, OBJECT_KEY_SLOT,
    READ_COMPARTMENT_SLOT, StorageOp, VOLUME_CEILING_SLOT, VOLUME_SPENT_SLOT,
    build_storage_put_action, key_prefix_field, object_key_field, sgm_cell_program,
};

const DEMO_OBJECT_KEY: &str = "uploads/doc.txt";
const DEMO_BLOB_HASH: u64 = 3_735_928_559;

fn agent(seed: u8) -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::from_seed([seed; 64]), [42u8; 32])
}

fn issuer_keys() -> IssuerKeys {
    IssuerKeys::new(
        [100u8; 32],
        [
            3, 154, 242, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0,
        ],
        b"mandate-composition-test",
        "starbridge-identity",
    )
}

fn attributes() -> CredentialAttributes {
    CredentialAttributes::new()
        .with("given_name", AttrValue::Text("Alice".into()))
        .with("verification_level", AttrValue::Integer(2))
}

fn seed_fields(state: &mut CellState, slots: &[(usize, FieldElement)]) {
    for &(index, value) in slots {
        state.fields[index] = value;
    }
}

struct Env {
    executor: EmbeddedExecutor,
    cipherclerk: AppCipherclerk,
    identity_cell: CellId,
    cwm_cell: CellId,
    sgm_cell: CellId,
}

fn fresh_env(seed: u8) -> Env {
    let cipherclerk = agent(seed);
    let executor = EmbeddedExecutor::new(&cipherclerk, "default");
    let owner_pk = cipherclerk.public_key().0;

    let identity_cell = executor.cell_id();
    executor.install_program(
        identity_cell,
        CellProgram::Predicate(vec![StateConstraint::Monotonic {
            index: REVOCATION_ROOT_SLOT as u8,
        }]),
    );

    let mk_cell = |domain: &[u8]| {
        Cell::with_balance(owner_pk, *blake3::hash(domain).as_bytes(), 1_000_000)
    };

    let cwm_obj = mk_cell(b"compartment-workflow-mandate");
    let cwm_cell = cwm_obj.id();
    executor.ensure_cell(cwm_obj).expect("cwm cell inserts");
    executor.install_program(cwm_cell, cwm_cell_program());
    executor.with_ledger_mut(|ledger| {
        let cell = ledger.get_mut(&cwm_cell).expect("cwm cell exists");
        seed_fields(
            &mut cell.state,
            &[
                (STEP_CURSOR_SLOT as usize, field_from_u64(0)),
                (CWM_ANCHOR_SLOT as usize, field_from_u64(DEFAULT_COMMITMENT_ANCHOR)),
                (CHARTER_TERMINAL_SLOT as usize, field_from_u64(DEFAULT_CHARTER_STEPS)),
                (
                    starbridge_compartment_workflow_mandate::CLEARANCE_GRAPH_ROOT_SLOT as usize,
                    clearance_label("officer"),
                ),
                (
                    starbridge_compartment_workflow_mandate::SPEND_POLICY_SLOT as usize,
                    field_from_u64(DEFAULT_STEP_SPEND_POLICY),
                ),
            ],
        );
    });

    let sgm_obj = mk_cell(b"storage-gateway-mandate");
    let sgm_cell = sgm_obj.id();
    executor.ensure_cell(sgm_obj).expect("sgm cell inserts");
    executor.install_program(sgm_cell, sgm_cell_program());
    executor.with_ledger_mut(|ledger| {
        let cell = ledger.get_mut(&sgm_cell).expect("sgm cell exists");
        seed_fields(
            &mut cell.state,
            &[
                (OBJECT_KEY_SLOT as usize, field_from_u64(0)),
                (LAST_OP_SLOT as usize, field_from_u64(0)),
                (VOLUME_SPENT_SLOT as usize, field_from_u64(0)),
                (SGM_ANCHOR_SLOT as usize, field_from_u64(DEFAULT_COMMITMENT_ANCHOR)),
                (VOLUME_CEILING_SLOT as usize, field_from_u64(DEFAULT_VOLUME_CEILING)),
                (KEY_PREFIX_HASH_SLOT as usize, key_prefix_field(DEFAULT_KEY_PREFIX)),
                (
                    READ_COMPARTMENT_SLOT as usize,
                    clearance_label(DEFAULT_READ_COMPARTMENT),
                ),
            ],
        );
    });

    executor.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&identity_cell) {
            agent_cell.capabilities.grant(cwm_cell, AuthRequired::None);
            agent_cell.capabilities.grant(sgm_cell, AuthRequired::None);
        }
    });

    Env {
        executor,
        cipherclerk,
        identity_cell,
        cwm_cell,
        sgm_cell,
    }
}

fn build_actions(env: &Env) -> Vec<Action> {
    let cc = &env.cipherclerk;

    let schema = kyc_schema();
    let credential = issue(
        &issuer_keys(),
        &schema,
        [9u8; 32],
        attributes(),
        1_700_000_000,
        None,
    )
    .expect("issuance succeeds");
    let issue_action =
        build_issue_credential_action(cc, env.identity_cell, &credential, 1, [0u8; 32]);

    let opts = PresentationOptions::new()
        .disclose("verification_level")
        .predicate(PredicateRequest::new(
            "verification_level",
            Predicate::Gte(1),
        ));
    let presentation = present(
        &credential,
        &dregg_token::AuthRequest {
            action: Some("read".into()),
            app_id: Some("mandate-composition-test".into()),
            user_id: Some(
                "0909090909090909090909090909090909090909090909090909090909090909".into(),
            ),
            now: Some(1_700_000_000),
            ..Default::default()
        },
        &opts,
    )
    .expect("presentation builds");
    let present_action = build_present_credential_action(cc, env.identity_cell, &presentation);

    let verify_opts = VerificationOptions {
        expected_schema: Some(schema),
        expected_disclosure: vec!["verification_level".into()],
        expected_predicates: vec![PredicateRequest::new(
            "verification_level",
            Predicate::Gte(1),
        )],
        ..Default::default()
    };
    let verify_action =
        build_verify_presentation_action(cc, env.identity_cell, &presentation, &verify_opts);

    vec![
        issue_action,
        present_action,
        verify_action,
        build_advance_step_action(cc, env.cwm_cell, 0, WorkflowPhase::Review),
        build_advance_step_action(cc, env.cwm_cell, 1, WorkflowPhase::Redact),
        build_advance_step_action(cc, env.cwm_cell, 2, WorkflowPhase::Sign),
        build_storage_put_action(
            cc,
            env.sgm_cell,
            DEMO_OBJECT_KEY,
            StorageOp::Put.demo_cost(),
            field_from_u64(DEMO_BLOB_HASH),
        ),
    ]
}

fn submit_all(env: &Env, actions: &[Action]) -> Vec<TurnReceipt> {
    actions
        .iter()
        .map(|a| {
            env.executor
                .submit_action(&env.cipherclerk, a.clone())
                .expect("mandate composition action commits")
        })
        .collect()
}

fn field_at(ex: &EmbeddedExecutor, cell: CellId, slot: usize) -> FieldElement {
    ex.with_ledger_mut(|ledger| ledger.get(&cell).expect("cell exists").state.fields[slot])
}

fn field_u64(ex: &EmbeddedExecutor, cell: CellId, slot: usize) -> u64 {
    let bytes = field_at(ex, cell, slot);
    u64::from_be_bytes(bytes[24..32].try_into().expect("u64 field"))
}

#[test]
fn cross_app_mandate_storage_chains_one_receipt_chain_and_emits_events() {
    let env = fresh_env(19);
    let actions = build_actions(&env);
    let receipts = submit_all(&env, &actions);

    assert_eq!(
        receipts.len(),
        7,
        "issue, present, verify, cwm×3, sgm put"
    );

    for (i, r) in receipts.iter().enumerate() {
        assert!(!r.emitted_events.is_empty(), "turn {i} must emit an event");
        assert_eq!(r.action_count, 1, "each composition turn carries one action");
    }

    assert_eq!(
        receipts[2].emitted_events[0].data[1][31], 1,
        "presentation must verify as accepted"
    );

    assert_eq!(
        field_u64(&env.executor, env.cwm_cell, STEP_CURSOR_SLOT as usize),
        DEFAULT_CHARTER_STEPS,
        "CWM step_cursor must complete review → redact → sign"
    );
    assert_eq!(
        field_u64(&env.executor, env.cwm_cell, CWM_ANCHOR_SLOT as usize),
        DEFAULT_COMMITMENT_ANCHOR,
        "CWM commitment_anchor must stay immutable"
    );

    assert_eq!(
        field_at(&env.executor, env.sgm_cell, OBJECT_KEY_SLOT as usize),
        object_key_field(DEMO_OBJECT_KEY),
        "SGM object_key must reflect the PUT target"
    );
    assert_eq!(
        field_u64(&env.executor, env.sgm_cell, LAST_OP_SLOT as usize),
        StorageOp::Put.to_field_value(),
        "SGM last_op must record PUT"
    );
    assert_eq!(
        field_u64(&env.executor, env.sgm_cell, VOLUME_SPENT_SLOT as usize),
        StorageOp::Put.demo_cost(),
        "SGM volume_spent must debit PUT cost"
    );
    assert_eq!(
        field_u64(&env.executor, env.sgm_cell, SGM_ANCHOR_SLOT as usize),
        DEFAULT_COMMITMENT_ANCHOR,
        "SGM commitment_anchor must stay immutable"
    );

    let sgm_receipt = &receipts[6];
    assert_eq!(
        sgm_receipt.emitted_events[0].data[2],
        field_from_u64(DEMO_BLOB_HASH),
        "storage-op emit must carry blob hash"
    );

    assert_eq!(receipts[0].previous_receipt_hash, None, "first turn is genesis");
    for i in 1..receipts.len() {
        assert_eq!(
            receipts[i].previous_receipt_hash,
            Some(receipts[i - 1].receipt_hash()),
            "turn {i} must link to turn {}'s receipt across the app boundary",
            i - 1
        );
    }
}

#[test]
fn cross_app_mandate_storage_state_transitions_are_deterministic_on_replay() {
    let actions = build_actions(&fresh_env(19));

    let first = submit_all(&fresh_env(19), &actions);
    let second = submit_all(&fresh_env(19), &actions);

    assert_eq!(first.len(), second.len());
    for (i, (a, b)) in first.iter().zip(second.iter()).enumerate() {
        assert_eq!(a.turn_hash, b.turn_hash, "turn_hash deterministic (turn {i})");
        assert_eq!(
            a.pre_state_hash, b.pre_state_hash,
            "pre_state deterministic (turn {i})"
        );
        assert_eq!(
            a.post_state_hash, b.post_state_hash,
            "post_state deterministic (turn {i})"
        );
        assert_eq!(
            a.effects_hash, b.effects_hash,
            "effects_hash deterministic (turn {i})"
        );
    }
}