//! Exact and hostile gates for the deterministic share-opening backend.

#[path = "../src/private_book_canonical_backend.rs"]
mod private_book_canonical_backend;
#[path = "../src/private_book_distributed_inputs.rs"]
mod private_book_distributed_inputs;
#[path = "../src/private_book_distributed_prover.rs"]
mod private_book_distributed_prover;

use private_book_canonical_backend::{
    canonical_share_opening_protocol_id, CanonicalShareOpeningBackend,
    CanonicalShareOpeningVerifier,
};
use private_book_distributed_inputs::{
    DistributedInputCertificate, DistributedInputCoordinator, DistributedWitnessSession,
    LocalOrderWitness, PreparedWitnessShare, PrivateSide, WitnessPartyMachine, ORDER_COUNT,
};
use private_book_distributed_prover::{
    DistributedProverCoordinator, DistributedProverError, ShareBoundProverRequest,
    WorkerLocalProofBackend, WorkerProofContext, WorkerProofContribution, WorkerProofProcess,
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
    DistributedWitnessSession::new_for_test(
        [0x41; 32],
        [0x42; 32],
        owner_keys
            .each_ref()
            .map(|key| key.verifying_key().to_bytes()),
        worker_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        8,
    )
    .unwrap()
}

fn prepare_inputs(
    session: &DistributedWitnessSession,
    owner_keys: &[SigningKey; ORDER_COUNT],
    worker_keys: &[SigningKey; 3],
    dealing_seed_base: u8,
) -> (DistributedInputCertificate, Vec<PreparedWitnessShare>) {
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
            session,
            owner,
            if owner < 2 {
                PrivateSide::Bid
            } else {
                PrivateSide::Ask
            },
            owner as u8,
            (owner + 2) as u8,
            [0x50 + owner as u8; 32],
            (owner == 0).then_some([900; 8]),
        )
        .unwrap();
        let mut rng = StdRng::from_seed([dealing_seed_base + owner as u8; 32]);
        let output = witness.deal(session, &owner_keys[owner], &mut rng).unwrap();
        let contribution = output.contribution.clone();
        coordinator.accept_dealer(output.contribution).unwrap();
        for (worker, packet) in output.private_packets.into_iter().enumerate() {
            let acknowledgement = workers[worker].accept(&contribution, packet).unwrap();
            coordinator.accept_acknowledgement(acknowledgement).unwrap();
        }
    }
    let shares = workers
        .into_iter()
        .map(|worker| worker.finish().unwrap())
        .collect();
    (coordinator.finish().unwrap(), shares)
}

fn canonical_contributions(
    session: &DistributedWitnessSession,
    certificate: &DistributedInputCertificate,
    worker_keys: &[SigningKey; 3],
    shares: Vec<PreparedWitnessShare>,
) -> Vec<WorkerProofContribution> {
    let request =
        ShareBoundProverRequest::new(session, certificate, canonical_share_opening_protocol_id())
            .unwrap();
    shares
        .into_iter()
        .enumerate()
        .map(|(worker, share)| {
            WorkerProofProcess::new(
                session.clone(),
                worker,
                worker_keys[worker].clone(),
                CanonicalShareOpeningBackend::new(worker),
            )
            .unwrap()
            .run(&request, certificate, share)
            .unwrap()
        })
        .collect()
}

struct ArbitraryDigestBackend;

impl WorkerLocalProofBackend for ArbitraryDigestBackend {
    type Error = ();

    fn protocol_id(&self) -> [u8; 32] {
        canonical_share_opening_protocol_id()
    }

    fn prove_local(
        &mut self,
        _context: &WorkerProofContext,
        _input_certificate: &DistributedInputCertificate,
        _witness: PreparedWitnessShare,
    ) -> Result<[u8; 32], Self::Error> {
        Ok([0x99; 32])
    }
}

#[test]
fn exact_local_openings_produce_the_only_publicly_accepted_contributions() {
    let owner_keys = keys::<ORDER_COUNT>(0x10);
    let worker_keys = keys::<3>(0x30);
    let session = session(&owner_keys, &worker_keys);
    let (certificate, shares) = prepare_inputs(&session, &owner_keys, &worker_keys, 0x60);
    let contributions = canonical_contributions(&session, &certificate, &worker_keys, shares);
    let protocol_id = canonical_share_opening_protocol_id();
    let request = ShareBoundProverRequest::new(&session, &certificate, protocol_id).unwrap();
    let mut coordinator =
        DistributedProverCoordinator::new(session.clone(), &request, &certificate).unwrap();
    for contribution in contributions {
        coordinator.accept(contribution).unwrap();
    }
    let envelope = coordinator.finish().unwrap();
    let verifier = CanonicalShareOpeningVerifier::new(&certificate).unwrap();
    envelope
        .verify_backend(&session, &request, &certificate, &verifier)
        .unwrap();
    let digests = envelope
        .worker_transcript_digests()
        .map(|(_, digest)| digest)
        .collect::<Vec<_>>();
    assert_eq!(digests.len(), session.n_workers());
    assert!(digests.iter().all(|digest| *digest != [0; 32]));
}

#[test]
fn arbitrary_digest_and_cross_certificate_verifier_fail_closed() {
    let owner_keys = keys::<ORDER_COUNT>(0x11);
    let worker_keys = keys::<3>(0x31);
    let session = session(&owner_keys, &worker_keys);
    let (certificate, shares) = prepare_inputs(&session, &owner_keys, &worker_keys, 0x70);
    let protocol_id = canonical_share_opening_protocol_id();
    let request = ShareBoundProverRequest::new(&session, &certificate, protocol_id).unwrap();
    let arbitrary = shares
        .into_iter()
        .enumerate()
        .map(|(worker, share)| {
            WorkerProofProcess::new(
                session.clone(),
                worker,
                worker_keys[worker].clone(),
                ArbitraryDigestBackend,
            )
            .unwrap()
            .run(&request, &certificate, share)
            .unwrap()
        })
        .collect::<Vec<_>>();
    let mut coordinator =
        DistributedProverCoordinator::new(session.clone(), &request, &certificate).unwrap();
    for contribution in arbitrary {
        coordinator.accept(contribution).unwrap();
    }
    let envelope = coordinator.finish().unwrap();
    let verifier = CanonicalShareOpeningVerifier::new(&certificate).unwrap();
    assert_eq!(
        envelope.verify_backend(&session, &request, &certificate, &verifier),
        Err(DistributedProverError::BackendRejected)
    );

    let (other_certificate, other_shares) =
        prepare_inputs(&session, &owner_keys, &worker_keys, 0x80);
    let other_contributions =
        canonical_contributions(&session, &other_certificate, &worker_keys, other_shares);
    let other_request =
        ShareBoundProverRequest::new(&session, &other_certificate, protocol_id).unwrap();
    let mut other_coordinator =
        DistributedProverCoordinator::new(session.clone(), &other_request, &other_certificate)
            .unwrap();
    for contribution in other_contributions {
        other_coordinator.accept(contribution).unwrap();
    }
    let other_envelope = other_coordinator.finish().unwrap();
    assert_eq!(
        other_envelope.verify_backend(&session, &other_request, &other_certificate, &verifier),
        Err(DistributedProverError::BackendRejected)
    );
}
