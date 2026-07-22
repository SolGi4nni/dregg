//! Hostile state-machine gate for distributed private-book proof inputs.
//!
//! The source module is path-included so this hostile gate can use its
//! deliberately test-only reduced-degree fixtures.  Production exposes input
//! preparation behind `amm-input-binding`. Each owner now proves the first
//! nonlinear subrelation locally: its hidden kind and quantity are in range,
//! its one-hot selector and nine semantic message slots are exact, and all are
//! linked to the vector commitment held additively by the workers. Every BFV
//! u/e1/e2 coefficient is also proved in `[-32,31]` on that same vector. The
//! remaining Poseidon/BFV-polynomial-equation/clearing circuit is not yet a
//! distributed R1CS proof.

#[path = "../src/private_book_distributed_inputs.rs"]
mod distributed;

use distributed::{
    owner_proof_verification_count_for_test, reset_owner_proof_verification_count_for_test,
    DistributedInputCertificate, DistributedInputCoordinator, DistributedInputError,
    DistributedWitnessSession, LocalOrderWitness, PrivateSide, WitnessPartyMachine, BFV_DEGREE,
    BFV_SHORT_ABS_BOUND, LOCAL_WITNESS_WIDTH, MESSAGE_SLOT_WIDTH, OPTION_COUNT, ORDER_COUNT,
};
use ed25519_dalek::SigningKey;
use rand::rngs::StdRng;
use rand::SeedableRng;

fn keys<const N: usize>(base: u8) -> [SigningKey; N] {
    core::array::from_fn(|index| SigningKey::from_bytes(&[base + index as u8; 32]))
}

fn session(
    owner_keys: &[SigningKey; ORDER_COUNT],
    worker_keys: &[SigningKey; 3],
) -> DistributedWitnessSession {
    session_with_nonce(owner_keys, worker_keys, [0x42; 32])
}

fn session_with_nonce(
    owner_keys: &[SigningKey; ORDER_COUNT],
    worker_keys: &[SigningKey; 3],
    ceremony_nonce: [u8; 32],
) -> DistributedWitnessSession {
    DistributedWitnessSession::new_for_test(
        [0x41; 32],
        ceremony_nonce,
        owner_keys
            .each_ref()
            .map(|key| key.verifying_key().to_bytes()),
        worker_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        16,
    )
    .expect("test session")
}

#[test]
fn reused_rng_stream_is_session_separated_before_any_worker_sees_a_share() {
    let owner_keys = keys::<ORDER_COUNT>(0x10);
    let worker_keys = keys::<3>(0x30);
    let first_session = session_with_nonce(&owner_keys, &worker_keys, [0x42; 32]);
    let second_session = session_with_nonce(&owner_keys, &worker_keys, [0x43; 32]);

    let first_witness = LocalOrderWitness::from_seed(
        &first_session,
        0,
        PrivateSide::Bid,
        0,
        1,
        [0x50; 32],
        Some([700; 8]),
    )
    .unwrap();
    let second_witness = LocalOrderWitness::from_seed(
        &second_session,
        0,
        PrivateSide::Ask,
        3,
        15,
        [0x50; 32],
        Some([700; 8]),
    )
    .unwrap();
    let witness_delta = second_witness.value_for_test(0) - first_witness.value_for_test(0);

    // Model a process restart that repeats the dealer's exact RNG stream in a
    // later ceremony.  Without contextual derivation, workers zero and one
    // receive identical masks, while worker two can subtract its packets and
    // recover `witness_delta` exactly.
    let mut first_rng = StdRng::from_seed([0x60; 32]);
    let first = first_witness
        .deal(&first_session, &owner_keys[0], &mut first_rng)
        .unwrap();
    let mut second_rng = StdRng::from_seed([0x60; 32]);
    let second = second_witness
        .deal(&second_session, &owner_keys[0], &mut second_rng)
        .unwrap();

    for worker in 0..3 {
        assert_ne!(
            first.private_packets[worker].value_for_test(0),
            second.private_packets[worker].value_for_test(0),
            "worker {worker} received a linkable cross-ceremony order-kind share"
        );
        assert_ne!(
            first.private_packets[worker].blinding_for_test(),
            second.private_packets[worker].blinding_for_test(),
            "worker {worker} received a repeated cross-ceremony commitment blinding"
        );
    }
    let last_worker_delta =
        second.private_packets[2].value_for_test(0) - first.private_packets[2].value_for_test(0);
    assert_ne!(
        last_worker_delta, witness_delta,
        "one worker recovered the exact hidden order-kind delta"
    );
}

#[test]
fn every_semantic_option_row_is_exact_and_constraint_omissions_fail_closed() {
    use curve25519_dalek::scalar::Scalar;

    let owner_keys = keys::<ORDER_COUNT>(0x0a);
    let worker_keys = keys::<3>(0x2a);
    let session = session(&owner_keys, &worker_keys);

    // Exhaust the complete 8 × 16 semantic table rather than relying only on
    // representative bid/ask rows.
    for kind in 0..8usize {
        for quantity in 0..16usize {
            let witness = LocalOrderWitness::from_seed(
                &session,
                0,
                if kind < 4 {
                    PrivateSide::Bid
                } else {
                    PrivateSide::Ask
                },
                (kind % 4) as u8,
                quantity as u8,
                [kind as u8 * 16 + quantity as u8; 32],
                Some([700; 8]),
            )
            .unwrap();
            let selected = kind * 16 + quantity;
            for option in 0..OPTION_COUNT {
                assert_eq!(
                    witness.value_for_test(2 + option),
                    Scalar::from(u64::from(option == selected))
                );
            }
            for slot in 0..8 {
                let expected = if kind < 4 {
                    u64::from(slot <= kind) * quantity as u64
                } else {
                    u64::from(slot >= kind) * quantity as u64
                };
                assert_eq!(
                    witness.value_for_test(2 + OPTION_COUNT + slot),
                    Scalar::from(expected)
                );
            }
            assert_eq!(
                witness.value_for_test(2 + OPTION_COUNT + 8),
                Scalar::from((kind + 8 * quantity) as u64)
            );
        }
    }

    // Each mutation preserves a well-shaped private vector but violates one
    // load-bearing semantic/shortness constraint. Proof-byte corruption tests
    // alone would not catch an accidentally omitted constraint.
    let mutations = [
        (2, Scalar::ONE),                            // second selected option
        (2 + 20, Scalar::ZERO),                      // erase true option
        (2 + OPTION_COUNT, Scalar::from(5u64)),      // wrong unary slot
        (2 + OPTION_COUNT + 8, Scalar::ONE),         // wrong metadata/root code
        (2 + OPTION_COUNT + 9, Scalar::from(32u64)), // out-of-range BFV short
    ];
    for (case, (coordinate, value)) in mutations.into_iter().enumerate() {
        let mut witness = LocalOrderWitness::from_seed(
            &session,
            0,
            PrivateSide::Bid,
            1,
            4,
            [0xd0 + case as u8; 32],
            Some([800; 8]),
        )
        .unwrap();
        witness.set_value_for_test(coordinate, value);
        let mut rng = StdRng::from_seed([0xe0 + case as u8; 32]);
        assert!(matches!(
            witness.deal(&session, &owner_keys[0], &mut rng),
            Err(DistributedInputError::OrderRangeProofRejected)
        ));
    }

    // Preserve booleanity and sum=1 while moving the selected bit from
    // (kind=1, qty=4) to (kind=1, qty=5). The explicit kind/quantity/index
    // equations, rather than only the one-hot gadget, must reject it.
    let mut witness = LocalOrderWitness::from_seed(
        &session,
        0,
        PrivateSide::Bid,
        1,
        4,
        [0xd8; 32],
        Some([800; 8]),
    )
    .unwrap();
    witness.set_value_for_test(2 + 20, Scalar::ZERO);
    witness.set_value_for_test(2 + 21, Scalar::ONE);
    let mut rng = StdRng::from_seed([0xe8; 32]);
    assert!(matches!(
        witness.deal(&session, &owner_keys[0], &mut rng),
        Err(DistributedInputError::OrderRangeProofRejected)
    ));
}

#[test]
fn all_local_openings_bind_one_public_certificate_without_reconstruction() {
    let owner_keys = keys::<ORDER_COUNT>(0x11);
    let worker_keys = keys::<3>(0x31);
    let session = session(&owner_keys, &worker_keys);
    let mut workers = worker_keys
        .iter()
        .enumerate()
        .map(|(worker, key)| {
            WitnessPartyMachine::new(session.clone(), worker, key.clone()).expect("worker")
        })
        .collect::<Vec<_>>();
    let mut coordinator = DistributedInputCoordinator::new(session.clone());
    let mut expected = Vec::with_capacity(ORDER_COUNT);
    let mut prepared_packets = (0..workers.len())
        .map(|_| Vec::with_capacity(ORDER_COUNT))
        .collect::<Vec<_>>();

    for owner in 0..ORDER_COUNT {
        let witness = LocalOrderWitness::from_seed(
            &session,
            owner,
            if owner < 2 {
                PrivateSide::Bid
            } else {
                PrivateSide::Ask
            },
            owner as u8,
            (owner + 1) as u8,
            [0x51 + owner as u8; 32],
            (owner == 0).then_some(core::array::from_fn(|lane| 700 + lane as u32)),
        )
        .expect("local exact witness");
        assert_eq!(witness.owner(), owner);
        let kind = if owner < 2 { owner } else { 4 + owner };
        let quantity = owner + 1;
        let selected = kind * 16 + quantity;
        for option in 0..OPTION_COUNT {
            assert_eq!(
                witness.value_for_test(2 + option),
                curve25519_dalek::scalar::Scalar::from(u64::from(option == selected))
            );
        }
        assert_eq!(MESSAGE_SLOT_WIDTH, 9);
        for slot in 0..8 {
            let expected_slot = if kind < 4 {
                u64::from(slot <= kind) * quantity as u64
            } else {
                u64::from(slot >= kind) * quantity as u64
            };
            assert_eq!(
                witness.value_for_test(2 + OPTION_COUNT + slot),
                curve25519_dalek::scalar::Scalar::from(expected_slot),
                "owner {owner} semantic message slot {slot}"
            );
        }
        assert_eq!(
            witness.value_for_test(2 + OPTION_COUNT + 8),
            curve25519_dalek::scalar::Scalar::from((kind + 8 * quantity) as u64)
        );
        expected.push(
            (0..witness.width())
                .map(|coordinate| witness.value_for_test(coordinate))
                .collect::<Vec<_>>(),
        );
        let mut rng = StdRng::from_seed([0x71 + owner as u8; 32]);
        let output = witness
            .deal(&session, &owner_keys[owner], &mut rng)
            .expect("owner dealing");
        let contribution = output.contribution.clone();
        assert_eq!(contribution.owner(), owner);
        assert_ne!(contribution.digest(), [0; 32]);
        assert_ne!(contribution.owner_commitment(), [0; 32]);
        assert_eq!(contribution.order_range_proof_len_for_test(), 8_293);
        coordinator
            .accept_dealer(output.contribution)
            .expect("public dealing");
        for (worker, packet) in output.private_packets.into_iter().enumerate() {
            assert_eq!(packet.recipient(), worker);
            let acknowledgement = workers[worker]
                .accept(&contribution, packet)
                .expect("private commitment opening");
            coordinator
                .accept_acknowledgement(acknowledgement)
                .expect("public acknowledgement");
            prepared_packets[worker].push(owner);
        }
    }
    assert!(prepared_packets
        .iter()
        .all(|owners| owners.as_slice() == [0, 1, 2, 3]));

    let prepared = workers
        .into_iter()
        .map(|worker| worker.finish().expect("complete local share"))
        .collect::<Vec<_>>();
    let certificate = coordinator.finish().expect("complete public certificate");
    certificate.verify(&session).expect("public verification");
    assert_ne!(certificate.transcript_digest(), [0; 32]);
    assert_ne!(certificate.joint_input_commitment().unwrap(), [0; 32]);

    let wire = certificate.to_bytes();
    let decoded = DistributedInputCertificate::from_bytes(&wire, &session).expect("canonical wire");
    assert_eq!(decoded, certificate);
    let mut corrupt_wire = wire;
    *corrupt_wire.last_mut().unwrap() ^= 1;
    assert_eq!(
        DistributedInputCertificate::from_bytes(&corrupt_wire, &session),
        Err(DistributedInputError::MalformedCertificate)
    );

    // Test-only reconstruction demonstrates exact additive sharing.  No
    // production coordinator API accepts `PreparedWitnessShare` objects.
    for (worker, share) in prepared.iter().enumerate() {
        assert_eq!(share.session_digest(), session.digest());
        assert_eq!(share.worker(), worker);
    }
    for owner in 0..ORDER_COUNT {
        for coordinate in 0..session.local_witness_width() {
            let reconstructed = prepared
                .iter()
                .fold(curve25519_dalek::scalar::Scalar::ZERO, |sum, worker| {
                    sum + worker.owner_share(owner).unwrap().0[coordinate]
                });
            assert_eq!(reconstructed, expected[owner][coordinate]);
        }
        assert!(prepared
            .iter()
            .any(|worker| worker.owner_share(owner).unwrap().0[0] != expected[owner][0]));
    }
}

#[test]
fn private_packet_equivocation_and_public_signature_forgery_fail_closed() {
    let owner_keys = keys::<ORDER_COUNT>(0x12);
    let worker_keys = keys::<3>(0x32);
    let session = session(&owner_keys, &worker_keys);
    let witness = LocalOrderWitness::from_seed(
        &session,
        0,
        PrivateSide::Bid,
        2,
        7,
        [0x61; 32],
        Some([900; 8]),
    )
    .unwrap();
    let mut rng = StdRng::from_seed([0x62; 32]);
    let mut output = witness.deal(&session, &owner_keys[0], &mut rng).unwrap();
    output.private_packets[0].corrupt_value_for_test(0);
    let mut worker = WitnessPartyMachine::new(session.clone(), 0, worker_keys[0].clone()).unwrap();
    assert_eq!(
        worker.accept(&output.contribution, output.private_packets.remove(0)),
        Err(DistributedInputError::CommitmentMismatch)
    );

    let witness = LocalOrderWitness::from_seed(
        &session,
        0,
        PrivateSide::Bid,
        2,
        7,
        [0x61; 32],
        Some([900; 8]),
    )
    .unwrap();
    let mut rng = StdRng::from_seed([0x63; 32]);
    let mut output = witness.deal(&session, &owner_keys[0], &mut rng).unwrap();
    output.contribution.corrupt_share_commitment_for_test(0);
    let mut coordinator = DistributedInputCoordinator::new(session.clone());
    assert!(matches!(
        coordinator.accept_dealer(output.contribution),
        Err(DistributedInputError::InvalidCommitment)
            | Err(DistributedInputError::CommitmentMismatch)
            | Err(DistributedInputError::CertificateDigestMismatch)
    ));

    // An unauthenticated contribution must be rejected before any range,
    // selector-R1CS, or 16k-vector link proof verification. This is a CPU-DoS
    // boundary, not merely a final validity check.
    let witness = LocalOrderWitness::from_seed(
        &session,
        0,
        PrivateSide::Bid,
        3,
        8,
        [0x5d; 32],
        Some([899; 8]),
    )
    .unwrap();
    let mut rng = StdRng::from_seed([0x5e; 32]);
    let mut output = witness.deal(&session, &owner_keys[0], &mut rng).unwrap();
    reset_owner_proof_verification_count_for_test();
    output.contribution.corrupt_owner_signature_for_test();
    let mut coordinator = DistributedInputCoordinator::new(session.clone());
    assert_eq!(
        coordinator.accept_dealer(output.contribution),
        Err(DistributedInputError::InvalidSignature)
    );
    assert_eq!(owner_proof_verification_count_for_test(), 0);

    // Re-sign a checksum-valid artifact after changing a canonical response
    // scalar inside its range proof. Neither the owner signature nor framing
    // checksum can substitute for the nonlinear proof equation.
    let witness = LocalOrderWitness::from_seed(
        &session,
        0,
        PrivateSide::Bid,
        2,
        7,
        [0x64; 32],
        Some([901; 8]),
    )
    .unwrap();
    let mut rng = StdRng::from_seed([0x65; 32]);
    let mut output = witness.deal(&session, &owner_keys[0], &mut rng).unwrap();
    output
        .contribution
        .corrupt_range_proof_and_resign_for_test(&owner_keys[0]);
    let mut coordinator = DistributedInputCoordinator::new(session.clone());
    assert_eq!(
        coordinator.accept_dealer(output.contribution),
        Err(DistributedInputError::OrderRangeProofRejected)
    );

    let witness = LocalOrderWitness::from_seed(
        &session,
        0,
        PrivateSide::Ask,
        1,
        9,
        [0x66; 32],
        Some([902; 8]),
    )
    .unwrap();
    let mut rng = StdRng::from_seed([0x67; 32]);
    let mut output = witness.deal(&session, &owner_keys[0], &mut rng).unwrap();
    output
        .contribution
        .corrupt_selector_proof_and_resign_for_test(&owner_keys[0]);
    let mut coordinator = DistributedInputCoordinator::new(session.clone());
    assert_eq!(
        coordinator.accept_dealer(output.contribution),
        Err(DistributedInputError::OrderRangeProofRejected)
    );

    // The batch link is the load-bearing bridge from the valid scalar R1CS
    // commitments to the exact share-held vector. A checksum-valid,
    // legitimately re-signed mutation of its response must still reject.
    let witness = LocalOrderWitness::from_seed(
        &session,
        0,
        PrivateSide::Ask,
        0,
        10,
        [0x6e; 32],
        Some([904; 8]),
    )
    .unwrap();
    let mut rng = StdRng::from_seed([0x6f; 32]);
    let mut output = witness.deal(&session, &owner_keys[0], &mut rng).unwrap();
    output
        .contribution
        .corrupt_derived_link_and_resign_for_test(&owner_keys[0]);
    let mut coordinator = DistributedInputCoordinator::new(session.clone());
    assert_eq!(
        coordinator.accept_dealer(output.contribution),
        Err(DistributedInputError::OrderRangeProofRejected)
    );

    // A valid proof from another owner cannot be transplanted even after the
    // receiving owner recomputes both framing checksum and signature.
    let target = LocalOrderWitness::from_seed(
        &session,
        0,
        PrivateSide::Bid,
        1,
        4,
        [0x68; 32],
        Some([903; 8]),
    )
    .unwrap();
    let source =
        LocalOrderWitness::from_seed(&session, 1, PrivateSide::Ask, 2, 12, [0x69; 32], None)
            .unwrap();
    let mut target_rng = StdRng::from_seed([0x6a; 32]);
    let mut source_rng = StdRng::from_seed([0x6b; 32]);
    let mut target = target
        .deal(&session, &owner_keys[0], &mut target_rng)
        .unwrap();
    let source = source
        .deal(&session, &owner_keys[1], &mut source_rng)
        .unwrap();
    target
        .contribution
        .substitute_selector_proof_and_resign_for_test(&source.contribution, &owner_keys[0]);
    let mut coordinator = DistributedInputCoordinator::new(session.clone());
    assert_eq!(
        coordinator.accept_dealer(target.contribution),
        Err(DistributedInputError::OrderRangeProofRejected)
    );

    // The same transplant is non-replayable across a fresh ceremony request.
    let other_session = session_with_nonce(&owner_keys, &worker_keys, [0x44; 32]);
    let source = LocalOrderWitness::from_seed(
        &other_session,
        0,
        PrivateSide::Bid,
        1,
        4,
        [0x68; 32],
        Some([903; 8]),
    )
    .unwrap();
    let mut source_rng = StdRng::from_seed([0x6c; 32]);
    let source = source
        .deal(&other_session, &owner_keys[0], &mut source_rng)
        .unwrap();
    let target = LocalOrderWitness::from_seed(
        &session,
        0,
        PrivateSide::Bid,
        1,
        4,
        [0x68; 32],
        Some([903; 8]),
    )
    .unwrap();
    let mut target_rng = StdRng::from_seed([0x6d; 32]);
    let mut target = target
        .deal(&session, &owner_keys[0], &mut target_rng)
        .unwrap();
    target
        .contribution
        .substitute_selector_proof_and_resign_for_test(&source.contribution, &owner_keys[0]);
    let mut coordinator = DistributedInputCoordinator::new(session.clone());
    assert_eq!(
        coordinator.accept_dealer(target.contribution),
        Err(DistributedInputError::OrderRangeProofRejected)
    );

    // Build a complete certificate, then mutate a worker signature while
    // recomputing the public transcript digest. Signature verification, not the
    // checksum alone, remains load-bearing.
    let mut workers = worker_keys
        .iter()
        .enumerate()
        .map(|(worker, key)| {
            WitnessPartyMachine::new(session.clone(), worker, key.clone()).unwrap()
        })
        .collect::<Vec<_>>();
    let mut coordinator = DistributedInputCoordinator::new(session.clone());
    for owner in 0..ORDER_COUNT {
        let witness = LocalOrderWitness::from_seed(
            &session,
            owner,
            PrivateSide::Bid,
            owner as u8,
            1,
            [0x70 + owner as u8; 32],
            (owner == 0).then_some([1234; 8]),
        )
        .unwrap();
        let mut rng = StdRng::from_seed([0x80 + owner as u8; 32]);
        let output = witness
            .deal(&session, &owner_keys[owner], &mut rng)
            .unwrap();
        let contribution = output.contribution.clone();
        coordinator.accept_dealer(output.contribution).unwrap();
        for (worker, packet) in output.private_packets.into_iter().enumerate() {
            let ack = workers[worker].accept(&contribution, packet).unwrap();
            coordinator.accept_acknowledgement(ack).unwrap();
        }
    }
    let mut certificate = coordinator.finish().unwrap();
    certificate.corrupt_ack_signature_for_test(0);
    assert_eq!(
        certificate.verify(&session),
        Err(DistributedInputError::InvalidSignature)
    );
}

#[test]
fn exact_production_layout_and_session_separation_are_pinned() {
    assert_eq!(LOCAL_WITNESS_WIDTH, 2 + 128 + 9 + 3 * BFV_DEGREE + 8);
    assert_eq!(LOCAL_WITNESS_WIDTH, 12_435);
    assert_eq!(BFV_SHORT_ABS_BOUND, 20);

    let owner_keys = keys::<ORDER_COUNT>(0x13);
    let worker_keys = keys::<3>(0x33);
    let production = DistributedWitnessSession::new(
        [0x91; 32],
        [0x92; 32],
        owner_keys
            .each_ref()
            .map(|key| key.verifying_key().to_bytes()),
        worker_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
    )
    .unwrap();
    assert_eq!(production.degree(), BFV_DEGREE);
    assert_eq!(production.local_witness_width(), LOCAL_WITNESS_WIDTH);
    assert_eq!(production.relation_digest(), [0x91; 32]);
    assert_eq!(production.ceremony_nonce(), [0x92; 32]);
    let production_witness = LocalOrderWitness::from_seed(
        &production,
        0,
        PrivateSide::Ask,
        3,
        15,
        [0x94; 32],
        Some(core::array::from_fn(|lane| 50_000 + lane as u32)),
    )
    .unwrap();
    assert_eq!(production_witness.width(), LOCAL_WITNESS_WIDTH);
    assert!(production_witness.has_short_coefficient_outside_for_test(10));
    let mut production_rng = StdRng::from_seed([0x95; 32]);
    let production_deal = production_witness
        .deal(&production, &owner_keys[0], &mut production_rng)
        .expect("production-width owner range/link proof");
    assert_eq!(
        production_deal
            .contribution
            .order_range_proof_len_for_test(),
        400_869
    );

    assert_eq!(
        DistributedWitnessSession::new(
            [0x91; 32],
            [0; 32],
            owner_keys
                .each_ref()
                .map(|key| key.verifying_key().to_bytes()),
            worker_keys
                .iter()
                .map(|key| key.verifying_key().to_bytes())
                .collect(),
        ),
        Err(DistributedInputError::InvalidSession(
            "ceremony nonce must be fresh and nonzero"
        ))
    );

    let other = DistributedWitnessSession::new(
        [0x93; 32],
        [0x92; 32],
        owner_keys
            .each_ref()
            .map(|key| key.verifying_key().to_bytes()),
        worker_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
    )
    .unwrap();
    assert_ne!(production.digest(), other.digest());
}
