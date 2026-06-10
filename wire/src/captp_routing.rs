//! CapTP delivered-turn construction.
//!
//! VERB-LOCKSTEP: the per-message Effect lowering (ExportSturdyRef / EnlivenRef /
//! DropRef / ValidateHandoff) dissolved with those kernel verbs — CapTP state
//! lives in the federation mirror (swiss table / export GC), and stored authority
//! is the caps-in-slots factory story. What remains here is the SURVIVOR builder:
//! a turn whose `Authorization::CapTpDelivered` carries the introducer-signed
//! handoff cert + the recipient's delivery signature, for effects the recipient
//! submits itself.

use dregg_captp::HandoffCertificate;
use dregg_cell::{CellId, Preconditions};
use dregg_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect, symbol};
use dregg_turn::forest::{CallForest, CallTree};
use dregg_turn::turn::Turn;
use dregg_types::SigningKey;
use tracing::info;

/// Build a CapTP-routed Turn whose authorization is the verified handoff
/// delivery (Seam 3 keystone). Closes the receipt-mirror loop: every CapTP
/// PresentHandoff that the wire layer accepts produces a Turn whose
/// authorization carries the introducer-signed cert + a recipient signature
/// binding this exact Turn (cert nonce ↔ agent ↔ target ↔ turn_nonce ↔ effects).
///
/// `recipient_key` is the signing key paired with `handoff_cert.recipient_pk`.
/// In the wire-layer integration path this comes from the recipient's
/// presentation. (For an in-server test driver, the test code holds the
/// signing key and passes it here.)
pub fn build_captp_turn_delivered(
    agent: CellId,
    target: CellId,
    effect: Effect,
    nonce: u64,
    handoff_cert: HandoffCertificate,
    introducer_pk: [u8; 32],
    recipient_key: &SigningKey,
) -> Turn {
    let effects = vec![effect];
    // The agent for the signing message is the same as the action target
    // (gateway-mirrors-cell). This matches what the executor recomputes.
    let federation_id = [0u8; 32];
    let signing_msg = Authorization::captp_delivered_signing_message_for_federation(
        &federation_id,
        &handoff_cert.nonce,
        &target,
        &target,
        nonce,
        &effects,
    );
    let signature = dregg_types::sign(recipient_key, &signing_msg);
    let sender_pk = handoff_cert.recipient_pk;

    let action = Action {
        target,
        method: symbol("captp.route"),
        args: vec![],
        authorization: Authorization::CapTpDelivered {
            handoff_cert,
            introducer_pk,
            sender_pk,
            sender_signature: signature.0,
        },
        preconditions: Preconditions::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let call_forest = CallForest {
        roots: vec![CallTree::new(action)],
        forest_hash: [0u8; 32],
    };
    Turn {
        agent,
        nonce,
        call_forest,
        fee: 0,
        memo: Some("captp.route".to_string()),
        valid_until: None,
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

/// Build a CapTP-routed Turn from a pre-computed sender signature.
///
/// Used by the wire-layer PresentHandoff handler when the recipient sent
/// the canonical delivery signature in the wire message. The handler does
/// not have the recipient's signing key (only the recipient does).
#[allow(clippy::too_many_arguments)]
pub fn build_captp_turn_delivered_from_parts(
    agent: CellId,
    target: CellId,
    effect: Effect,
    nonce: u64,
    handoff_cert: HandoffCertificate,
    introducer_pk: [u8; 32],
    sender_pk: [u8; 32],
    sender_signature: [u8; 64],
) -> Turn {
    // Studio trace: captp_delivered turn constructed from wire-layer parts.
    // Emitted before executor verification; the executor emits a matching authorization event on success.
    info!(kind = "authorization", auth_kind = "captp_delivered", agent = %agent, target = %target, nonce);
    let action = Action {
        target,
        method: symbol("captp.route"),
        args: vec![],
        authorization: Authorization::CapTpDelivered {
            handoff_cert,
            introducer_pk,
            sender_pk,
            sender_signature,
        },
        preconditions: Preconditions::default(),
        effects: vec![effect],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let call_forest = CallForest {
        roots: vec![CallTree::new(action)],
        forest_hash: [0u8; 32],
    };
    Turn {
        agent,
        nonce,
        call_forest,
        fee: 0,
        memo: Some("captp.route".to_string()),
        valid_until: None,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_captp_turn_delivered_from_parts_carries_captp_delivered_auth() {
        let agent = CellId::from_bytes([1u8; 32]);
        let target = CellId::from_bytes([2u8; 32]);
        let (sk, pk) = dregg_types::generate_keypair();
        let cert = HandoffCertificate::create(
            &sk,
            dregg_captp::FederationId(pk.0),
            dregg_captp::FederationId(pk.0),
            target,
            pk.0,
            dregg_cell::permissions::AuthRequired::None,
            None,
            None,
            None,
            [9u8; 32],
        );
        let effect = Effect::EmitEvent {
            cell: target,
            event: dregg_turn::action::Event { topic: symbol("captp.test"), data: vec![] },
        };
        let turn =
            build_captp_turn_delivered_from_parts(agent, target, effect, 0, cert, pk.0, pk.0, [0u8; 64]);
        assert_eq!(turn.agent, agent);
        assert_eq!(turn.call_forest.roots.len(), 1);
        assert!(matches!(
            turn.call_forest.roots[0].action.authorization,
            Authorization::CapTpDelivered { .. }
        ));
    }
}
