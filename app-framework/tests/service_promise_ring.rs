//! End-to-end prototype: two cells exchange a SERVICE for PAYMENT via the ring.
//!
//! A provider promises a service for payment; a consumer pays for it. The ring
//! matches them, the payment is ESCROWED against the promise, and then either the
//! provider FULFILLS (proves its service turn ran → payment released) or the
//! promise LAPSES (→ payment refunded). This test proves the four contracts:
//!
//!   1. HAPPY PATH   — service performed (a signed receipt fills the hole) → paid.
//!   2. REFUND PATH  — unfulfilled past the window → refunded to the consumer.
//!   3. ATOMICITY    — a forged/absent fulfillment never half-pays; release and
//!                     refund are mutually-exclusive one-shots.
//!   4. CONSERVATION — the payment asset's total is preserved across every path.

//! Assurance-perimeter #3: fulfillment is a VERIFIED EffectVM STARK (a
//! `ProvenReceipt`), NOT a trusted signature. The provider commits to the exact
//! state-commitment transition (`expected_pre/post_commitment`) at promise time; a
//! genuine proof of THAT transition fills the hole, a forged/wrong-transition proof
//! does not.

use dregg_app_framework::service_promise::{
    EscrowStatus, ServiceId, ServicePromise, ServicePromiseError, ServicePromiseExchange,
    ServiceRequest, fulfillment_proof,
};
use dregg_intent::CommitmentId;
use dregg_intent::exchange::AssetId;
use dregg_turn::conditional::{ConditionProof, ProvenReceipt};
use dregg_types::CellId;

mod support;
use support::install_verified_settlement_gate;

fn cid(b: u8) -> CommitmentId {
    CommitmentId([b; 32])
}
fn asset(b: u8) -> AssetId {
    let mut a = [0u8; 32];
    a[0] = b;
    a
}

/// The provider cell, the consumer cell, the escrow cell — distinct commitments
/// (the verified ledger keys them by their FULL 32-byte id, so they never alias).
const CONSUMER: u8 = 1;
const PROVIDER: u8 = 2;
const ESCROW: u8 = 9;
const PRICE: u64 = 100;
const SERVICE_TURN_HASH: [u8; 32] = [0xAB; 32];

/// A cheap exchange + promise/request whose committed transition endpoints are
/// arbitrary placeholders — for the refund path, which never verifies a proof.
fn setup() -> (ServicePromiseExchange, ServicePromise, ServiceRequest) {
    install_verified_settlement_gate();
    let exchange = ServicePromiseExchange::new(4, 0, cid(ESCROW), vec![]);
    let service = ServiceId::of(CellId::from_bytes([0x5e; 32]), "render-report");
    let promise = ServicePromise {
        provider: cid(PROVIDER),
        service,
        service_turn_hash: SERVICE_TURN_HASH,
        expected_pre_commitment: [0x11; 32],
        expected_post_commitment: [0x22; 32],
        payment_asset: asset(7),
        price: PRICE,
        timeout_height: 50,
    };
    let request = ServiceRequest {
        consumer: cid(CONSUMER),
        service,
        payment_asset: asset(7),
        offer: PRICE,
    };
    (exchange, promise, request)
}

/// An exchange + promise/request bound to a GENUINE minted proof: the promise's
/// committed endpoints ARE the proof's wide anchors, so `proven`'s
/// [`fulfillment_proof`] resolves the escrow. Heavy: mints one real wide rotated
/// EffectVM STARK.
fn setup_proven() -> (
    ServicePromiseExchange,
    ServicePromise,
    ServiceRequest,
    ProvenReceipt,
) {
    install_verified_settlement_gate();
    let proven = dregg_turn_prover::mint_transfer_proven_receipt(SERVICE_TURN_HASH, 7);
    let exchange = ServicePromiseExchange::new(4, 0, cid(ESCROW), vec![]);
    let service = ServiceId::of(CellId::from_bytes([0x5e; 32]), "render-report");
    let promise = ServicePromise {
        provider: cid(PROVIDER),
        service,
        service_turn_hash: SERVICE_TURN_HASH,
        expected_pre_commitment: proven.pre_commitment,
        expected_post_commitment: proven.post_commitment,
        payment_asset: asset(7),
        price: PRICE,
        timeout_height: 50,
    };
    let request = ServiceRequest {
        consumer: cid(CONSUMER),
        service,
        payment_asset: asset(7),
        offer: PRICE,
    };
    (exchange, promise, request, proven)
}

/// (1) HAPPY PATH + (4) CONSERVATION.
/// match → escrow → fulfill (signed receipt) → payment released to provider; the
/// payment asset is conserved at every step.
#[test]
fn happy_path_service_performed_then_paid() {
    let (exchange, promise, request, proven) = setup_proven();
    let pay = asset(7);

    let m = exchange
        .match_one(&promise, &request)
        .expect("ring matches the pair");
    assert_eq!(m.price, PRICE);

    let k0 = exchange.seed_ledger(&m, PRICE);
    assert_eq!(k0.total_asset(&pay), PRICE as i128);

    // Escrow the payment.
    let (mut escrow, k1) = exchange.fund(&m, &k0).expect("payment escrows");
    assert_eq!(k1.get(cid(CONSUMER).0, &pay), 0);
    assert_eq!(k1.get(cid(ESCROW).0, &pay), PRICE as i128);
    assert_eq!(
        k1.total_asset(&pay),
        PRICE as i128,
        "conserved after escrow"
    );

    // The provider performs the service turn and presents the VERIFIED proof.
    let proof = fulfillment_proof(&proven);
    let k2 = exchange
        .fulfill(&mut escrow, &k1, &proof, 10)
        .expect("a genuine proof releases the payment");

    assert_eq!(escrow.status, EscrowStatus::Released);
    assert_eq!(
        k2.get(cid(PROVIDER).0, &pay),
        PRICE as i128,
        "provider is paid"
    );
    assert_eq!(k2.get(cid(ESCROW).0, &pay), 0, "escrow drained");
    assert_eq!(k2.get(cid(CONSUMER).0, &pay), 0);
    assert_eq!(k2.total_asset(&pay), PRICE as i128, "conserved end-to-end");
}

/// (2) REFUND PATH + (4) CONSERVATION.
/// match → escrow → window lapses with no fulfillment → payment refunded whole to
/// the consumer; conserved throughout.
#[test]
fn refund_path_unfulfilled_then_refunded() {
    let (exchange, promise, request) = setup();
    let pay = asset(7);

    let m = exchange.match_one(&promise, &request).unwrap();
    let k0 = exchange.seed_ledger(&m, PRICE);
    let (mut escrow, k1) = exchange.fund(&m, &k0).expect("payment escrows");

    // Refund before the window closes is refused.
    assert_eq!(
        exchange.refund(&mut escrow, &k1, 10),
        Err(ServicePromiseError::NotYetRefundable {
            current_height: 10,
            timeout_height: 50
        })
    );
    assert_eq!(escrow.status, EscrowStatus::Funded, "still held");

    // After the window lapses, the unfulfilled payment refunds to the consumer.
    let k2 = exchange
        .refund(&mut escrow, &k1, 51)
        .expect("lapsed promise refunds");
    assert_eq!(escrow.status, EscrowStatus::Refunded);
    assert_eq!(
        k2.get(cid(CONSUMER).0, &pay),
        PRICE as i128,
        "consumer made whole"
    );
    assert_eq!(k2.get(cid(ESCROW).0, &pay), 0, "escrow drained");
    assert_eq!(k2.get(cid(PROVIDER).0, &pay), 0, "provider got nothing");
    assert_eq!(k2.total_asset(&pay), PRICE as i128, "conserved end-to-end");
}

/// (3) ATOMICITY — no half-settle.
/// A forged fulfillment (no verified proof, or a proof of a DIFFERENT turn) does not
/// release the payment: the escrow stays fully funded, nothing splits, and the
/// consumer can still refund the WHOLE amount once the window lapses.
#[test]
fn forged_fulfillment_never_half_pays() {
    let (exchange, promise, request, proven) = setup_proven();
    let pay = asset(7);

    let m = exchange.match_one(&promise, &request).unwrap();
    let k0 = exchange.seed_ledger(&m, PRICE);
    let (mut escrow, k1) = exchange.fund(&m, &k0).unwrap();

    // A proofless EffectVmProof (a receipt without a proof is not a trust root).
    let proofless = ConditionProof::EffectVmProof {
        receipt: Box::new(proven.receipt.clone()),
        proof_bytes: vec![],
        public_inputs: proven.effect_vm_public_inputs.clone(),
    };
    let err = exchange
        .fulfill(&mut escrow, &k1, &proofless, 10)
        .expect_err("a proofless fulfillment must not release payment");
    assert!(matches!(err, ServicePromiseError::Unfulfilled(_)));

    // No half-settle: every felt is still held in escrow, status unchanged.
    assert_eq!(escrow.status, EscrowStatus::Funded);
    assert_eq!(k1.get(cid(ESCROW).0, &pay), PRICE as i128);
    assert_eq!(k1.get(cid(PROVIDER).0, &pay), 0);
    assert_eq!(k1.total_asset(&pay), PRICE as i128);

    // A GENUINE proof of a DIFFERENT turn (its PI[TURN_HASH] / endpoints do not match
    // the promised transition) also fails to fill the hole.
    let other = dregg_turn_prover::mint_transfer_proven_receipt([0x00; 32], 7);
    let wrong_turn = fulfillment_proof(&other);
    assert!(matches!(
        exchange.fulfill(&mut escrow, &k1, &wrong_turn, 10),
        Err(ServicePromiseError::Unfulfilled(_))
    ));

    // The consumer can still refund the whole payment after the window.
    let k2 = exchange
        .refund(&mut escrow, &k1, 51)
        .expect("still refundable");
    assert_eq!(k2.get(cid(CONSUMER).0, &pay), PRICE as i128);
    assert_eq!(k2.total_asset(&pay), PRICE as i128);
}

/// (3) ATOMICITY — release and refund are mutually-exclusive one-shots.
/// Once released, refund is refused; once a (separate) escrow is refunded, fulfill
/// is refused. The held payment is taken by exactly one exit, exactly once.
#[test]
fn release_and_refund_are_one_shot_exclusive() {
    let (exchange, promise, request, proven) = setup_proven();
    let proof = fulfillment_proof(&proven);

    // Released escrow cannot also refund.
    let m = exchange.match_one(&promise, &request).unwrap();
    let k0 = exchange.seed_ledger(&m, PRICE);
    let (mut escrow, k1) = exchange.fund(&m, &k0).unwrap();
    let k2 = exchange.fulfill(&mut escrow, &k1, &proof, 10).unwrap();
    assert_eq!(escrow.status, EscrowStatus::Released);
    assert_eq!(
        exchange.refund(&mut escrow, &k2, 51),
        Err(ServicePromiseError::AlreadySettled),
        "a released escrow cannot refund"
    );
    // And it cannot release twice.
    assert_eq!(
        exchange.fulfill(&mut escrow, &k2, &proof, 11),
        Err(ServicePromiseError::AlreadySettled),
        "a released escrow cannot release again"
    );

    // Refunded escrow cannot also fulfill.
    let m2 = exchange.match_one(&promise, &request).unwrap();
    let k0b = exchange.seed_ledger(&m2, PRICE);
    let (mut escrow2, k1b) = exchange.fund(&m2, &k0b).unwrap();
    let _ = exchange.refund(&mut escrow2, &k1b, 51).unwrap();
    assert_eq!(escrow2.status, EscrowStatus::Refunded);
    assert_eq!(
        exchange.fulfill(&mut escrow2, &k1b, &proof, 10),
        Err(ServicePromiseError::AlreadySettled),
        "a refunded escrow cannot release"
    );
}
