//! Submit-seam closure for the cell-program slash intake — the intake turn
//! rides the node's OWN turn-submit pipeline.
//!
//! [`crate::relay_slash_intake::intake_dispute`] ends at a named seam: on a
//! conviction it returns a SIGNED, nonce-0 [`Turn`] invoking the
//! relay-operator cell's `slash` method, and its module docs say the
//! caller's turn pipeline sets the real nonce and ships it. This module is
//! that caller for a NODE deployment: [`prepare_slash_submit`] finalizes the
//! intake turn against the node's LIVE state (nonce off the acting cell,
//! expiry stamp, fee sized by the SAME estimator the submit executor
//! charges, receipt-chain binding) and signs it into the canonical
//! [`SignedTurn`] envelope — byte-for-byte the body `POST /turns/submit`
//! consumes (`postcard::to_stdvec(&SignedTurn)`; see
//! `api.rs::post_submit_signed_turn`).
//!
//! # What is REAL vs the remaining hop (honest scope)
//!
//! REAL — the tests below drive the ACTUAL route: they boot a solo
//! [`crate::state::NodeState`], install the relay-operator template
//! `CellProgram` on a relay cell in the node's authoritative ledger, run the
//! real referee via `intake_dispute`, finalize + sign here, and POST the
//! envelope through the axum router to `/turns/submit` — the same handler a
//! remote client hits, with every ingress gate live (ed25519 + fail-closed
//! PQ half over the turn hash, the signer↔agent binding,
//! actor/destination provisioning, the ONE producer gate
//! `executor_setup::execute_via_producer`, solo commit + receipt-chain
//! append). The relay cell's bond/dispute slots advance and the conserving
//! payout lands, enforced by the installed cell program in the node's
//! executor — nothing is re-implemented or mirrored here.
//!
//! THE REMAINING HOP — transport only. A deployment whose intake process is
//! not the node process still has to carry [`PreparedSlashSubmit::envelope`]
//! to the node's HTTP ingress (an ordinary `POST /turns/submit` with
//! `Content-Type: application/octet-stream`); an in-process embedder hands
//! it to the router exactly as the tests do. Nothing in that hop re-signs or
//! re-decides — the envelope is complete and the node's gates are the
//! authority.
//!
//! Nothing here weakens authorization: this module only finalizes fields the
//! executor checks anyway (nonce, expiry, fee, chain head) and signs with
//! the intake cipherclerk. Which authorization the DEPLOYED relay cell
//! demands for `slash` remains executor-enforced deployment configuration;
//! an unauthorized intake turn is rejected by the pipeline like any other.
//! The loop stays bilateral and owner-anchored: the conviction is the
//! intake's own referee run against authenticated inbox state, and the node
//! that executes it is the (deployment-chosen) node hosting the
//! relay-operator cell — no global-consensus vote, no global-owned entity.

use dregg_app_framework::AppCipherclerk;
use dregg_sdk::SignedTurn;
use dregg_turn::Turn;

use crate::executor_setup::{federation_id_for_executor, local_agent_cell, new_submit_executor};
use crate::state::NodeStateInner;

/// How long a prepared slash turn stays valid when the intake turn carries
/// no expiry of its own (the executor's expiry gate + the verified Lean
/// producer's wire marshal both want `valid_until` stamped).
pub const SLASH_TURN_VALIDITY_SECS: i64 = 3600;

/// A slash turn finalized against the live node state and signed into the
/// canonical `/turns/submit` wire envelope.
#[derive(Clone, Debug)]
pub struct PreparedSlashSubmit {
    /// The signed envelope — same shape the remote SDK ships.
    pub signed: SignedTurn,
    /// `postcard::to_stdvec(&signed)`: byte-for-byte the `POST /turns/submit`
    /// request body (`application/octet-stream`).
    pub envelope: Vec<u8>,
    /// The canonical turn hash the ingress verifies the signature over and
    /// reports back as `turn_hash` (hex) in `SubmitSignedTurnResponse`.
    pub turn_hash: [u8; 32],
}

/// Finalize an [`intake_dispute`](crate::relay_slash_intake::intake_dispute)
/// conviction turn for THIS node's `/turns/submit` pipeline and sign it.
///
/// Mirrors the bindings the remote SDK discovers before signing, and the
/// exact checks `post_submit_signed_turn` applies at ingress — fail-closed
/// HERE so a misbound turn never reaches the wire:
///
/// * **Federation binding.** The action signatures inside the turn bind the
///   intake cipherclerk's `federation_id`; the node executor verifies them
///   against [`federation_id_for_executor`]. A mismatch is refused outright
///   (re-signing under a different federation is not this module's job).
/// * **Agent binding.** The ingress requires
///   `turn.agent == CellId::derive_raw(signer, blake3("default"))`; the same
///   check runs here (it also catches a non-default-domain cipherclerk).
/// * **Nonce.** Read off the acting cell's LIVE state on the node ledger
///   (0 for a never-seen client — ingress `claim_signer_actor_cell`
///   materializes exactly that cell).
/// * **Expiry.** `valid_until` is stamped when absent.
/// * **Receipt-chain binding.** `AgentCipherclerk::append_receipt`'s strict prev
///   check is AGENT-SCOPED (`agent_receipt_head_hash`), not node-wide: the
///   immutable log interleaves every agent the node ever committed for. A solo
///   node, and any node acting as its own operator cell, therefore re-binds the
///   turn to THAT AGENT's causal head. Otherwise (a foreign client on a
///   multi-party node) the turn's OWN claimed prev is kept: the finalized
///   pass on every node is authoritative for it.
/// * **Fee.** A zero fee is sized by `new_submit_executor(s).estimate_cost`
///   — the same `ComputronCosts::default()` estimator the applying executor
///   charges, so the budget gate passes without over-funding.
///
/// The returned envelope commits or rejects entirely inside the node's
/// pipeline; this function performs no ledger mutation of any kind.
pub fn prepare_slash_submit(
    s: &NodeStateInner,
    cclerk: &AppCipherclerk,
    turn: &Turn,
) -> Result<PreparedSlashSubmit, String> {
    // Fail-closed federation binding: the executor verifies the action
    // signatures against ITS federation id; a foreign-bound cipherclerk
    // could only produce a turn the pipeline rejects, so refuse it here.
    let node_federation_id = federation_id_for_executor(s);
    if *cclerk.federation_id() != node_federation_id {
        return Err(
            "intake cipherclerk is bound to a different federation than this node; \
             construct it with executor_setup::federation_id_for_executor's value \
             BEFORE running intake_dispute"
                .to_string(),
        );
    }

    // The ingress's exact signer↔agent binding (post_submit_signed_turn):
    // turn.agent must be the signer's default cell.
    let default_token_id = *blake3::hash(b"default").as_bytes();
    let expected_agent = dregg_cell::CellId::derive_raw(&cclerk.public_key().0, &default_token_id);
    if turn.agent != expected_agent {
        return Err(
            "turn agent does not match the intake cipherclerk's default cell; \
             the ingress would refuse this envelope"
                .to_string(),
        );
    }

    let mut turn = turn.clone();

    // The real nonce (the intake seam left it 0): the acting cell's LIVE
    // nonce on the node ledger; 0 for a never-provisioned client, matching
    // the cell `claim_signer_actor_cell` materializes at ingress.
    turn.nonce = s
        .ledger
        .get(&turn.agent)
        .map(|c| c.state.nonce())
        .unwrap_or(0);

    // Expiry stamp (executor expiry gate + Lean-producer wire marshal).
    if turn.valid_until.is_none() {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);
        turn.valid_until = Some(now + SLASH_TURN_VALIDITY_SECS);
    }

    // Receipt-chain binding (see the doc comment): re-bind to THIS AGENT's own causal
    // head when the node is the authority for it, and keep the client's claimed prev
    // otherwise. The condition is unchanged; the value is. It used to be the node-WIDE
    // log head, on the premise (still written in the doc comment above until now) that
    // `append_receipt` gates on a single node chain. It does not — `append_receipt` calls
    // `agent_receipt_head_hash(&receipt.agent)` — so on a solo node with a foreign intake
    // cipherclerk this stamped some other agent's receipt and the envelope was refused,
    // and even for the operator it broke the moment the faucet committed.
    let is_solo = s.solo_consensus.as_ref().is_some_and(|sc| sc.is_solo);
    if is_solo || turn.agent == local_agent_cell(s) {
        turn.previous_receipt_hash = s.cclerk.agent_receipt_head_hash(&turn.agent);
    }

    // Size the fee (= the executor's computron budget cap) to the estimated
    // cost so the budget gate passes — exactly as commit_effects_as and the
    // faucet do. Estimator and applying executor share ComputronCosts::default().
    if turn.fee == 0 {
        turn.fee = new_submit_executor(s).estimate_cost(&turn);
    }

    let signed = cclerk.sign_turn(&turn);
    let turn_hash = signed.turn.hash();
    let envelope =
        postcard::to_stdvec(&signed).map_err(|e| format!("slash submit envelope encode: {e}"))?;
    Ok(PreparedSlashSubmit {
        signed,
        envelope,
        turn_hash,
    })
}

// =============================================================================
// Tests — the intake turn applies through the node's ACTUAL /turns/submit
// pipeline and the relay cell's bond/dispute slots advance.
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::extract::ConnectInfo;
    use axum::http::{Request, StatusCode};
    use http_body_util::BodyExt;
    use tower::ServiceExt;

    use dregg_captp::FederationId;
    use dregg_captp::custody::{CustodyReceipt, EvidenceOfDrop, InboxState};
    use dregg_cell::{AuthRequired, Cell, CellId, Permissions};
    use dregg_sdk::AgentCipherclerk;
    use dregg_storage_templates::relay_operator::{
        BOND_AMOUNT_SLOT, BOND_MIN_SLOT, DISPUTE_COUNT_SLOT, OPERATOR_PK_HASH_SLOT,
        QUOTA_BYTES_PER_EPOCH_SLOT, ROUTE_TABLE_ROOT_SLOT, relay_operator_program,
    };

    use crate::api::router;
    use crate::relay_dispute::{default_slash_treasury, u64_to_field};
    use crate::relay_slash_intake::{DisputeIntake, RelaySlots, SlashPolicy, intake_dispute};
    use crate::state::NodeState;

    // ── Mirrors of the intake module's evidence fixtures ────────────────────

    fn demo_receipt() -> CustodyReceipt {
        let (sk, pk) = dregg_types::generate_keypair();
        let relay = FederationId(pk.0);
        CustodyReceipt::sign(
            relay,
            &sk,
            [0xAB; 32],               // content_hash
            FederationId([0x03; 32]), // inbox_owner (the wronged party)
            [0x64; 32],               // old_root
            [0x8E; 32],               // new_root (promised)
            500,                      // accept_by
        )
    }

    fn dropped_inbox(evidence: &EvidenceOfDrop) -> InboxState {
        InboxState::from_dequeue(&evidence.receipt, &[], [0x64; 32], false)
    }

    const POLICY: SlashPolicy = SlashPolicy {
        requested_penalty: 500,
        proven_fee: 120,
        restitution_bounty: 30,
    };

    fn open_permissions() -> Permissions {
        Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        }
    }

    /// THE WELD, end to end through the node's own pipeline: a proven dispute
    /// is intaken (`intake_dispute`), finalized + signed here, POSTed to the
    /// node's ACTUAL `/turns/submit` route (in-process axum router — the same
    /// handler a remote client hits, every ingress gate live), and the slash
    /// LANDS on the cell-program relay cell in the node's authoritative
    /// ledger: bond decremented, dispute counter advanced, conserving payout
    /// delivered — all enforced by the installed relay_operator CellProgram
    /// in the node's executor.
    #[tokio::test]
    async fn proven_dispute_lands_slash_through_the_node_turns_submit_pipeline() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        state.write().await.unlocked = true;
        // Committee of one (solo): the submit path keeps its in-place commit
        // authoritatively — the regime a single relay-operator node runs in.
        {
            let mut s = state.write().await;
            let sk = s.cclerk.gossip_signing_key().to_bytes();
            s.solo_consensus = Some(dregg_federation::solo::SoloConsensusState::new(sk));
        }
        let recorder = metrics_exporter_prometheus::PrometheusBuilder::new().build_recorder();
        let app = router(state.clone(), false, recorder.handle());
        // Loopback caller (require_auth's pre-passphrase window admits only
        // loopback); the FOREIGNNESS under test is the intake identity.
        let addr: std::net::SocketAddr = "127.0.0.1:4447".parse().unwrap();

        // The intake cipherclerk, bound to THIS node's federation id (the
        // binding prepare_slash_submit fails closed on).
        let node_federation_id = {
            let s = state.read().await;
            crate::executor_setup::federation_id_for_executor(&s)
        };
        let intake_clerk = AgentCipherclerk::new();
        // The ML-DSA half of the intake identity. `AgentCipherclerk::sign_turn` always carries it,
        // and the ingress admission predicate anchors the carried key in the ACTING CELL's own PQ
        // identity commitment — so the cell seeded below must COMMIT it (`with_hybrid_balance`) or
        // the envelope is refused `pq-identity-not-enrolled` before the pipeline under test runs.
        let intake_ml_dsa_public_key = intake_clerk.ml_dsa_public_bytes();
        let cclerk = AppCipherclerk::new(intake_clerk, node_federation_id);
        let intake_agent = cclerk.cell_id();

        // Deployment seeding on the node's AUTHORITATIVE ledger: the funded
        // intake agent cell (canonical pk-bound, PQ-committed account, so the
        // ingress provisioning leaves it untouched) and a REAL relay-operator cell —
        // template CellProgram installed, the slot layout seeded (bond 10_000
        // / floor 1_000 / dispute_count 0), a 100_000 balance. The relay cell
        // is open-permissioned to isolate the PROGRAM's enforcement, exactly
        // like the intake module's embedded-executor weld test.
        let default_token_id = *blake3::hash(b"default").as_bytes();
        let relay_id = {
            let mut s = state.write().await;
            let agent_cell = Cell::with_hybrid_balance(
                cclerk.public_key().0,
                &intake_ml_dsa_public_key,
                default_token_id,
                1_000_000,
            )
            .expect("canonical ML-DSA-65 intake identity");
            assert_eq!(
                agent_cell.id(),
                intake_agent,
                "canonical pk-bound intake agent cell"
            );
            s.ledger.insert_cell(agent_cell).expect("intake agent cell");

            let mut relay = Cell::with_balance([0x51u8; 32], default_token_id, 100_000);
            relay.permissions = open_permissions();
            relay.program = relay_operator_program();
            let relay_id = relay.id();
            s.ledger.insert_cell(relay).expect("relay cell");
            {
                let cell = s.ledger.get_mut(&relay_id).expect("relay cell exists");
                cell.state
                    .set_field(BOND_AMOUNT_SLOT as usize, u64_to_field(10_000));
                cell.state
                    .set_field(BOND_MIN_SLOT as usize, u64_to_field(1_000));
                cell.state
                    .set_field(QUOTA_BYTES_PER_EPOCH_SLOT as usize, u64_to_field(1_000_000));
                cell.state.set_field(
                    OPERATOR_PK_HASH_SLOT as usize,
                    *blake3::hash(b"operator-pk").as_bytes(),
                );
                cell.state.set_field(
                    ROUTE_TABLE_ROOT_SLOT as usize,
                    *blake3::hash(b"route-table").as_bytes(),
                );
            }
            let agent = s
                .ledger
                .get_mut(&intake_agent)
                .expect("intake agent exists");
            agent
                .capabilities
                .grant(relay_id, AuthRequired::None)
                .expect("grant relay access");
            relay_id
        };

        // Live slot readings off the NODE ledger — not the legacy mirror.
        let slots = {
            let s = state.read().await;
            RelaySlots::from_cell_state(&s.ledger.get(&relay_id).expect("relay cell").state)
        };
        assert_eq!(
            slots,
            RelaySlots {
                bond_amount: 10_000,
                bond_min: 1_000,
                dispute_count: 0
            },
            "live-cell readback matches the seeded layout"
        );

        // The real referee: a genuine drop convicts and yields the slash turn.
        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        let inbox = dropped_inbox(&evidence);
        let DisputeIntake::Convicted { plan, turn } =
            intake_dispute(&cclerk, &evidence, &inbox, relay_id, slots, POLICY)
        else {
            panic!("a genuine drop must convict");
        };
        assert_eq!(plan.seized_amount, 500);

        // Finalize + sign against the LIVE node state (nonce, expiry, fee,
        // solo chain binding).
        let prepared = {
            let s = state.read().await;
            prepare_slash_submit(&s, &cclerk, &turn).expect("prepare must succeed")
        };
        assert!(
            prepared.signed.turn.fee > 0,
            "fee sized by the submit executor's estimator"
        );

        // THE PIPELINE: POST the canonical envelope to the node's own
        // /turns/submit route — the identical handler a remote client hits.
        let response = app
            .clone()
            .oneshot(
                Request::builder()
                    .method("POST")
                    .uri("/turns/submit")
                    .header("content-type", "application/octet-stream")
                    .extension(ConnectInfo(addr))
                    .body(Body::from(prepared.envelope.clone()))
                    .expect("submit request"),
            )
            .await
            .expect("submit response");
        assert_eq!(response.status(), StatusCode::OK);
        let bytes = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&bytes).expect("submit json");
        assert_eq!(
            json["accepted"], true,
            "the intake turn must commit through the pipeline: {json}"
        );
        assert_eq!(
            json["turn_hash"],
            serde_json::json!(dregg_types::hex_encode(&prepared.turn_hash)),
            "the route executed exactly the prepared turn"
        );

        // THE LANDING: the relay cell's bond/dispute slots advanced on the
        // node's authoritative ledger — the executor-enforced cell-program
        // transition, reached through the submit pipeline.
        let s = state.read().await;
        let relay_state = &s.ledger.get(&relay_id).expect("relay cell").state;
        assert_eq!(
            relay_state.fields[BOND_AMOUNT_SLOT as usize],
            u64_to_field(9_500),
            "bond decremented by the seizure"
        );
        assert_eq!(
            relay_state.fields[DISPUTE_COUNT_SLOT as usize],
            u64_to_field(1),
            "dispute counter advanced by exactly one"
        );

        // Conserving payout landed; the wronged party and the treasury were
        // provisioned by the route itself (provision_transfer_destinations).
        let wronged = CellId::from_bytes([0x03u8; 32]); // demo receipt inbox_owner
        let balance = |id: &CellId| s.ledger.get(id).map(|c| c.state.balance()).unwrap_or(0);
        assert_eq!(balance(&relay_id), 100_000 - 500);
        assert_eq!(balance(&wronged), 150);
        assert_eq!(balance(&default_slash_treasury()), 350);
        assert_eq!(
            plan.payout.restitution + plan.payout.remainder,
            plan.seized_amount,
            "the whole seizure left the operator, conserving (Sigma delta 0)"
        );
    }

    /// Fail-closed bindings: a cipherclerk bound to a FOREIGN federation, and
    /// a turn whose agent is not the signer's default cell, are both refused
    /// BEFORE the wire — the same outcomes the ingress would produce, caught
    /// where the operator can still fix the binding.
    #[tokio::test]
    async fn prepare_refuses_foreign_federation_and_mismatched_agent() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        let relay_id = CellId::from_bytes([0x11u8; 32]);
        let slots = RelaySlots {
            bond_amount: 10_000,
            bond_min: 1_000,
            dispute_count: 0,
        };

        // Foreign federation binding: the node's federation id is
        // blake3(node pubkey) here — [0xEE; 32] cannot match it.
        let foreign = AppCipherclerk::new(AgentCipherclerk::new(), [0xEE; 32]);
        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        let inbox = dropped_inbox(&evidence);
        let DisputeIntake::Convicted { turn, .. } =
            intake_dispute(&foreign, &evidence, &inbox, relay_id, slots, POLICY)
        else {
            panic!("a genuine drop must convict");
        };
        {
            let s = state.read().await;
            let err = prepare_slash_submit(&s, &foreign, &turn)
                .expect_err("foreign-federation cipherclerk must be refused");
            assert!(err.contains("federation"), "got: {err}");
        }

        // Mismatched agent binding: a correctly-bound cipherclerk, but the
        // turn claims to act as someone ELSE's cell.
        let node_federation_id = {
            let s = state.read().await;
            crate::executor_setup::federation_id_for_executor(&s)
        };
        let bound = AppCipherclerk::new(AgentCipherclerk::new(), node_federation_id);
        let DisputeIntake::Convicted { turn, .. } =
            intake_dispute(&bound, &evidence, &inbox, relay_id, slots, POLICY)
        else {
            panic!("a genuine drop must convict");
        };
        let mut hijacked = (*turn).clone();
        hijacked.agent = CellId::from_bytes([0x77u8; 32]);
        {
            let s = state.read().await;
            let err = prepare_slash_submit(&s, &bound, &hijacked)
                .expect_err("a turn acting as someone else's cell must be refused");
            assert!(err.contains("agent"), "got: {err}");
        }
    }

    /// The receipt-chain binding is the INTAKE AGENT's own head, not the node's.
    ///
    /// On a solo node this function re-binds the prepared turn's
    /// `previous_receipt_hash`. It used to bind the node-WIDE log head, on the premise
    /// (which the doc comment stated until 2026-07-26) that `append_receipt` gates a
    /// single node chain. It does not: it calls
    /// `agent_receipt_head_hash(&receipt.agent)`. So with a foreign intake cipherclerk
    /// — the module's whole point — the prepared envelope carried a STRANGER's receipt
    /// as its predecessor and the ingress refused it.
    ///
    /// The intake agent here has no chain of its own, so the correct answer is `None`;
    /// the wide head is `Some(stranger)`. Those disagreeing is the whole defect, and
    /// this asserts the prepared turn takes the first.
    #[tokio::test]
    async fn prepared_turn_binds_the_intake_agents_own_head_not_the_node_wide_head() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        {
            let mut s = state.write().await;
            s.unlocked = true;
            let sk = s.cclerk.gossip_signing_key().to_bytes();
            s.solo_consensus = Some(dregg_federation::solo::SoloConsensusState::new(sk));
        }

        let node_federation_id = {
            let s = state.read().await;
            crate::executor_setup::federation_id_for_executor(&s)
        };
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), node_federation_id);
        let intake_agent = cclerk.cell_id();

        // A stranger commits first — the faucet's role on any real node.
        let stranger_head = {
            let mut s = state.write().await;
            crate::faucet_grant_e2e::append_stranger_receipt(&mut s, CellId::from_bytes([0xEE; 32]))
        };

        let evidence = EvidenceOfDrop::from_receipt(demo_receipt());
        let inbox = dropped_inbox(&evidence);
        let DisputeIntake::Convicted { turn, .. } = intake_dispute(
            &cclerk,
            &evidence,
            &inbox,
            CellId::from_bytes([0x11u8; 32]),
            RelaySlots {
                bond_amount: 10_000,
                bond_min: 1_000,
                dispute_count: 0,
            },
            POLICY,
        ) else {
            panic!("a genuine drop must convict");
        };

        let s = state.read().await;
        assert_eq!(
            s.cclerk.receipt_log().last().map(|r| r.receipt_hash()),
            Some(stranger_head),
            "precondition: the node-wide log head is the stranger's"
        );
        assert_eq!(
            s.cclerk.agent_receipt_head_hash(&intake_agent),
            None,
            "precondition: the intake agent has no chain of its own"
        );

        let prepared = prepare_slash_submit(&s, &cclerk, &turn).expect("prepare must succeed");
        assert_eq!(
            prepared.signed.turn.previous_receipt_hash, None,
            "the prepared turn must claim the INTAKE AGENT's head (genesis), not the \
             node-wide log head {stranger_head:?} — the ingress compares the former"
        );
    }
}
