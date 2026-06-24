//! ADVERSARIAL: does the live executor's `CapTpDelivered` authorization gate admit an
//! AMPLIFYING / UNTRUSTED handoff that the verified Lean kernel (and the captp
//! `validate_handoff` swiss gate) reject?
//!
//! The Lean spec (`Dregg2.Exec.AuthModes`, lines 16-25) documents the suspicion verbatim:
//! "dregg1 currently FAILS to enforce `granted ≤ held` here (it verifies the two
//! signatures and the cert/target binding, but never re-checks that the cert's conferred
//! permissions attenuate what the introducer held)."
//!
//! The structural reality: the executor has NO swiss table — the introducer's authoritative
//! `held` record (the swiss entry) lives ONLY in the captp/wire layer, consulted ONLY by
//! `validate_handoff`. So the executor's image of "held" is the TARGET CELL's own declared
//! permission lattice: a CapTpDelivered cert short-circuits that lattice entirely. Two gaps:
//!
//!   (A) INTRODUCER-TRUST: `verify_captp_delivered` takes `introducer_pk` from the
//!       recipient-supplied turn and verifies the cert is signed by THAT key — but never
//!       checks the introducer is a TRUSTED federation. An adversary self-signs a cert.
//!   (B) NON-AMPLIFICATION: the cert short-circuits the target cell's permission lattice
//!       (`verify_authorization` returns Ok early), so the cert confers authority to perform
//!       ANY action on the target regardless of the cell's declared `AuthRequired` — without
//!       any `granted ≤ held` (here: granted ≤ the cell's required tier) check.
//!
//! This test fixes a Signature-LOCKED target cell, then has an UNTRUSTED adversary (its own
//! fresh keypair = the "introducer") self-sign a handoff cert naming itself recipient and
//! submit a CapTpDelivered turn that mutates the locked cell. If the executor COMMITS, the
//! hole is CONFIRMED. After the fix it must REJECT (the locked cell's lattice is honored /
//! the untrusted introducer is refused), while a LEGITIMATE attenuating handoff still passes.

use dregg_captp::HandoffCertificate;
use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};
use dregg_types::{SigningKey, sign};

const LOCAL_FED: [u8; 32] = [0u8; 32];

fn locked_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::Signature,
        receive: AuthRequired::Signature,
        set_state: AuthRequired::Signature,
        set_permissions: AuthRequired::Signature,
        set_verification_key: AuthRequired::Signature,
        increment_nonce: AuthRequired::Signature,
        delegate: AuthRequired::Signature,
        access: AuthRequired::Signature,
    }
}

fn make_cell(seed: u8, balance: i64, perms: Permissions) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = perms;
    cell
}

fn executor() -> TurnExecutor {
    let mut e = TurnExecutor::new(ComputronCosts::zero());
    e.set_local_federation_id(LOCAL_FED);
    e
}

/// Build a CapTpDelivered turn whose `recipient_key` self-signs the canonical delivery
/// message — exactly as the wire builder does, so the executor's signature checks PASS.
/// `target` is the cell being mutated; `granted` is the cert's claimed permission tier.
#[allow(clippy::too_many_arguments)]
fn captp_turn(
    agent: CellId,
    target: CellId,
    effect: Effect,
    nonce: u64,
    introducer_sk: &SigningKey,
    introducer_fed: dregg_captp::FederationId,
    introducer_pk: [u8; 32],
    recipient_sk: &SigningKey,
    recipient_pk: [u8; 32],
    granted: AuthRequired,
) -> Turn {
    let cert = HandoffCertificate::create(
        introducer_sk,
        introducer_fed,
        dregg_captp::FederationId(LOCAL_FED),
        target,
        recipient_pk,
        granted,
        None, // no allowed_effects restriction
        None, // no expiry
        None, // unlimited uses
        [0u8; 32],
    );
    let effects = vec![effect];
    let signing_msg = Authorization::captp_delivered_signing_message_for_federation(
        &LOCAL_FED,
        &cert.nonce,
        &target,
        &target,
        nonce,
        &effects,
    );
    let sender_signature = sign(recipient_sk, &signing_msg).0;

    let action = Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::CapTpDelivered {
            handoff_cert: cert,
            introducer_pk,
            sender_pk: recipient_pk,
            sender_signature,
        },
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: dregg_turn::action::CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let mut forest = CallForest::new();
    forest.add_root(action);
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: Some(1_000),
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// THE CONFIRM/REFUTE TEST. An UNTRUSTED adversary self-signs a cert granting itself
/// `None` (the loosest tier = MORE authority than the held `Signature`-locked cell), and
/// mutates the locked cell via SetField. Pre-fix: the executor COMMITS (hole). Post-fix:
/// the executor REJECTS (untrusted introducer / amplification).
#[test]
fn adversary_amplifying_captp_handoff_is_rejected() {
    // The locked target cell: every action requires Signature.
    let target = make_cell(1, 100, locked_permissions());
    let target_id = target.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(target).unwrap();

    // The ADVERSARY: a fresh keypair that is NOT a trusted federation. It plays BOTH
    // introducer and recipient (self-handoff). It HOLDS a coarse access cap over `target`
    // (so the cap-graph gate at effect time passes) but CANNOT satisfy the cell's
    // Signature-tier permission lattice — which `verify_authorization` enforces for every
    // mode EXCEPT the short-circuiting CapTpDelivered. The exploit is the lattice BYPASS:
    // the self-signed cert lets the adversary perform a Signature-gated SetField it could
    // not authorize via any honest mode.
    let adversary_sk = SigningKey::from_bytes(&[7u8; 32]);
    let adversary_pk = adversary_sk.public_key().0;
    let adversary_fed = dregg_captp::FederationId(adversary_pk);

    // The adversary's OWN cell (the turn agent / recipient) must exist in the ledger so the
    // turn reaches the authorization gate. It holds a bare access cap over the locked target.
    let mut agent_cell = Cell::with_balance(adversary_pk, [0u8; 32], 1_000);
    agent_cell.permissions = {
        let mut p = locked_permissions();
        p.access = AuthRequired::None;
        p
    };
    // Grant the agent a coarse access cap over the locked target (passes the cap-graph gate).
    agent_cell
        .capabilities
        .grant(target_id, AuthRequired::None)
        .unwrap();
    let agent_id = agent_cell.id();
    ledger.insert_cell(agent_cell).unwrap();

    let turn = captp_turn(
        agent_id,
        target_id,
        Effect::SetField {
            cell: target_id,
            index: 4, // a developer slot (not reserved)
            value: [0x42; 32],
        },
        0,
        &adversary_sk,
        adversary_fed,
        adversary_pk,
        &adversary_sk,
        adversary_pk,
        AuthRequired::None, // GRANTS the loosest tier — amplification over the locked cell
    );

    let committed = executor().execute(&turn, &mut ledger.clone()).is_committed();
    assert!(
        !committed,
        "SOUNDNESS HOLE: the executor COMMITTED an amplifying CapTpDelivered turn from an \
         UNTRUSTED self-signed introducer against a Signature-LOCKED cell — Rust admits what \
         the verified Lean kernel (captp_granted_le_held / handoff_non_amplifying) refuses."
    );
}

/// POSITIVE CONTROL — a LEGITIMATE handoff (granted tier matches the cell's required tier;
/// no amplification) on an OPEN cell still commits. Guards against the fix over-rejecting.
#[test]
fn legitimate_captp_handoff_still_accepted() {
    // OPEN target cell: every action requires None (so a granted-None cert does NOT amplify).
    let mut open = Permissions::default();
    open.send = AuthRequired::None;
    open.receive = AuthRequired::None;
    open.set_state = AuthRequired::None;
    open.set_permissions = AuthRequired::None;
    open.set_verification_key = AuthRequired::None;
    open.increment_nonce = AuthRequired::None;
    open.delegate = AuthRequired::None;
    open.access = AuthRequired::None;

    let target = make_cell(2, 100, open.clone());
    let target_id = target.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(target).unwrap();

    // A handoff where the introducer == the local federation (trusted self-handoff) granting
    // the SAME tier the open cell requires (None ≤ None: attenuating, not amplifying).
    let intro_sk = SigningKey::from_bytes(&[0u8; 32]); // local_federation_id == [0;32]
    let intro_pk = intro_sk.public_key().0;
    let recip_sk = SigningKey::from_bytes(&[9u8; 32]);
    let recip_pk = recip_sk.public_key().0;

    // The recipient's OWN cell (the turn agent) must exist in the ledger and hold an access
    // cap over the OPEN target (passes the cap-graph gate). The target's lattice is None, so
    // the granted-None cert does NOT amplify — an honest, non-amplifying handoff.
    let mut agent_cell = Cell::with_balance(recip_pk, [0u8; 32], 1_000);
    agent_cell.permissions = open;
    agent_cell
        .capabilities
        .grant(target_id, AuthRequired::None)
        .unwrap();
    let agent_id = agent_cell.id();
    ledger.insert_cell(agent_cell).unwrap();

    let turn = captp_turn(
        agent_id,
        target_id,
        Effect::EmitEvent {
            cell: target_id,
            event: dregg_turn::Event::new([0u8; 32], vec![]),
        },
        0,
        &intro_sk,
        dregg_captp::FederationId(LOCAL_FED),
        intro_pk,
        &recip_sk,
        recip_pk,
        AuthRequired::None, // matches the open cell's required tier — no amplification
    );

    let committed = executor().execute(&turn, &mut ledger.clone()).is_committed();
    assert!(
        committed,
        "REGRESSION: a LEGITIMATE non-amplifying CapTpDelivered handoff on an OPEN cell was \
         REJECTED — the non-amplification fix is over-rejecting honest handoffs."
    );
}
