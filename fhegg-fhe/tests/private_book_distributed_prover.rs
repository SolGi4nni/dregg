//! Hostile custody gates for the worker-local distributed-prover boundary.

#[path = "../src/private_book_distributed_inputs.rs"]
mod private_book_distributed_inputs;
#[path = "../src/private_book_distributed_prover.rs"]
mod private_book_distributed_prover;

use private_book_distributed_inputs::{
    DistributedInputCertificate, DistributedInputCoordinator, DistributedInputError,
    DistributedWitnessSession, LocalOrderWitness, PreparedWitnessShare, PrivateSide,
    WitnessPartyMachine, ORDER_COUNT,
};
use private_book_distributed_prover::{
    DistributedProverCoordinator, DistributedProverError, PublicDistributedProofVerifier,
    ShareBoundProverRequest, WorkerLocalProofBackend, WorkerProofContext, WorkerProofContribution,
    WorkerProofProcess,
};

use ed25519_dalek::SigningKey;
use rand::rngs::StdRng;
use rand::SeedableRng;

const PROTOCOL_ID: [u8; 32] = [0xa5; 32];

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
            (owner + 1) as u8,
            [0x50 + owner as u8; 32],
            (owner == 0).then_some([700; 8]),
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

struct LocalOnlyBackend {
    worker: usize,
}

impl WorkerLocalProofBackend for LocalOnlyBackend {
    type Error = &'static str;

    fn protocol_id(&self) -> [u8; 32] {
        PROTOCOL_ID
    }

    fn prove_local(
        &mut self,
        context: &WorkerProofContext,
        input_certificate: &DistributedInputCertificate,
        witness: PreparedWitnessShare,
    ) -> Result<[u8; 32], Self::Error> {
        if witness.worker() != self.worker
            || witness.session_digest() != context.session_digest()
            || input_certificate.transcript_digest() != context.input_certificate_digest()
        {
            return Err("misbound local proof request");
        }
        for owner in 0..ORDER_COUNT {
            let (values, _) = witness.owner_share(owner).ok_or("missing owner share")?;
            if values.is_empty() {
                return Err("empty owner share");
            }
        }

        // The fixture digest depends only on public context and worker id.
        // A real MPC backend replaces this with a publicly verifiable proof
        // transcript digest; it must not serialize `values` or their blindings.
        let mut hasher =
            blake3::Hasher::new_derive_key("fhegg/private-book-distributed-prover/test-backend/v1");
        hasher.update(&context.digest());
        hasher.update(&(self.worker as u64).to_be_bytes());
        Ok(*hasher.finalize().as_bytes())
    }
}

struct FixtureVerifier;

impl PublicDistributedProofVerifier for FixtureVerifier {
    type Error = &'static str;

    fn protocol_id(&self) -> [u8; 32] {
        PROTOCOL_ID
    }

    fn verify_transcript_digests(
        &self,
        context: &WorkerProofContext,
        transcript_digests: &[[u8; 32]],
    ) -> Result<(), Self::Error> {
        if transcript_digests.len() != context.n_workers()
            || transcript_digests.iter().any(|digest| *digest == [0; 32])
        {
            return Err("incomplete fixture transcript");
        }
        Ok(())
    }
}

fn run_workers(
    session: &DistributedWitnessSession,
    certificate: &DistributedInputCertificate,
    worker_keys: &[SigningKey; 3],
    shares: Vec<PreparedWitnessShare>,
) -> Vec<WorkerProofContribution> {
    let request = ShareBoundProverRequest::new(session, certificate, PROTOCOL_ID).unwrap();
    shares
        .into_iter()
        .enumerate()
        .map(|(worker, share)| {
            WorkerProofProcess::new(
                session.clone(),
                worker,
                worker_keys[worker].clone(),
                LocalOnlyBackend { worker },
            )
            .unwrap()
            .run(&request, certificate, share)
            .unwrap()
        })
        .collect()
}

#[test]
fn each_process_consumes_one_share_and_coordinator_sees_only_public_digests() {
    let owner_keys = keys::<ORDER_COUNT>(0x10);
    let worker_keys = keys::<3>(0x30);
    let session = session(&owner_keys, &worker_keys);
    let (certificate, shares) = prepare_inputs(&session, &owner_keys, &worker_keys, 0x60);
    let request = ShareBoundProverRequest::new(&session, &certificate, PROTOCOL_ID).unwrap();
    let contributions = run_workers(&session, &certificate, &worker_keys, shares);

    let wire = contributions[0].to_bytes();
    assert_eq!(
        WorkerProofContribution::from_bytes(&wire, &session, &certificate, &request).unwrap(),
        contributions[0]
    );
    let mut corrupt_wire = wire;
    *corrupt_wire.last_mut().unwrap() ^= 1;
    assert_eq!(
        WorkerProofContribution::from_bytes(&corrupt_wire, &session, &certificate, &request),
        Err(DistributedProverError::MalformedContribution)
    );

    let mut coordinator =
        DistributedProverCoordinator::new(session.clone(), &request, &certificate).unwrap();
    for contribution in contributions.into_iter().rev() {
        coordinator.accept(contribution).unwrap();
    }
    let bundle = coordinator.finish().unwrap();
    bundle
        .verify_envelope(&session, &request, &certificate)
        .unwrap();
    bundle
        .verify_backend(&session, &request, &certificate, &FixtureVerifier)
        .unwrap();
    assert_eq!(
        bundle
            .worker_transcript_digests()
            .map(|(worker, digest)| (worker, digest != [0; 32]))
            .collect::<Vec<_>>(),
        vec![(0, true), (1, true), (2, true)]
    );
    assert_ne!(bundle.transcript_digest(), [0; 32]);
    assert_eq!(bundle.request_digest(), request.digest());
}

#[test]
fn request_wire_refuses_source_viewer_mode_appended_plaintext_and_context_substitution() {
    let owner_keys = keys::<ORDER_COUNT>(0x12);
    let worker_keys = keys::<3>(0x32);
    let session = session(&owner_keys, &worker_keys);
    let (certificate, _) = prepare_inputs(&session, &owner_keys, &worker_keys, 0x68);
    let request = ShareBoundProverRequest::new(&session, &certificate, PROTOCOL_ID).unwrap();
    let wire = request.to_bytes();
    assert_eq!(
        ShareBoundProverRequest::from_bytes(&wire, &session, &certificate, PROTOCOL_ID).unwrap(),
        request
    );

    // The custody byte follows the 8-byte magic and u16 version.  Mode 2 is
    // reserved as an explicit negative test for monolithic/source-viewer use.
    let mut source_viewer = wire.clone();
    source_viewer[10] = 2;
    assert_eq!(
        ShareBoundProverRequest::from_bytes(&source_viewer, &session, &certificate, PROTOCOL_ID),
        Err(DistributedProverError::SourceViewerForbidden)
    );

    let mut appended_plaintext = wire.clone();
    appended_plaintext.extend_from_slice(b"plaintext-order-and-bfv-opening");
    assert_eq!(
        ShareBoundProverRequest::from_bytes(
            &appended_plaintext,
            &session,
            &certificate,
            PROTOCOL_ID
        ),
        Err(DistributedProverError::MalformedRequest)
    );

    assert_eq!(
        ShareBoundProverRequest::from_bytes(&wire, &session, &certificate, [0xa6; 32]),
        Err(DistributedProverError::RequestMismatch)
    );
    let (other_certificate, _) = prepare_inputs(&session, &owner_keys, &worker_keys, 0x69);
    assert_eq!(
        ShareBoundProverRequest::from_bytes(&wire, &session, &other_certificate, PROTOCOL_ID),
        Err(DistributedProverError::RequestMismatch)
    );
}

#[test]
fn duplicate_missing_misbound_and_forged_worker_material_fail_closed() {
    let owner_keys = keys::<ORDER_COUNT>(0x11);
    let worker_keys = keys::<3>(0x31);
    let session = session(&owner_keys, &worker_keys);
    let (first_certificate, first_shares) =
        prepare_inputs(&session, &owner_keys, &worker_keys, 0x70);
    let (second_certificate, second_shares) =
        prepare_inputs(&session, &owner_keys, &worker_keys, 0x80);
    let second_request =
        ShareBoundProverRequest::new(&session, &second_certificate, PROTOCOL_ID).unwrap();

    assert!(matches!(
        WorkerProofProcess::new(
            session.clone(),
            0,
            worker_keys[1].clone(),
            LocalOnlyBackend { worker: 0 }
        ),
        Err(DistributedProverError::SigningKeyMismatch)
    ));

    // Both certificates are valid for the same public session, but their
    // owner dealings and private shares differ.  Session equality alone must
    // not let a share cross this boundary.
    let first_worker_share = first_shares.into_iter().next().unwrap();
    let misbound = WorkerProofProcess::new(
        session.clone(),
        0,
        worker_keys[0].clone(),
        LocalOnlyBackend { worker: 0 },
    )
    .unwrap()
    .run(&second_request, &second_certificate, first_worker_share);
    assert_eq!(
        misbound,
        Err(DistributedProverError::Input(
            DistributedInputError::DealerMismatch
        ))
    );

    let contributions = run_workers(&session, &second_certificate, &worker_keys, second_shares);
    let mut coordinator =
        DistributedProverCoordinator::new(session.clone(), &second_request, &second_certificate)
            .unwrap();
    coordinator.accept(contributions[0].clone()).unwrap();
    assert_eq!(
        coordinator.accept(contributions[0].clone()),
        Err(DistributedProverError::DuplicateContribution)
    );

    let wrong_protocol_request =
        ShareBoundProverRequest::new(&session, &second_certificate, [0xa6; 32]).unwrap();
    let mut wrong_protocol = DistributedProverCoordinator::new(
        session.clone(),
        &wrong_protocol_request,
        &second_certificate,
    )
    .unwrap();
    assert_eq!(
        wrong_protocol.accept(contributions[0].clone()),
        Err(DistributedProverError::ProtocolMismatch)
    );

    let mut forged = contributions[1].clone();
    forged.corrupt_signature_for_test();
    assert_eq!(
        coordinator.accept(forged),
        Err(DistributedProverError::InvalidSignature)
    );

    let mut incomplete =
        DistributedProverCoordinator::new(session.clone(), &second_request, &second_certificate)
            .unwrap();
    incomplete.accept(contributions[0].clone()).unwrap();
    assert_eq!(
        incomplete.finish(),
        Err(DistributedProverError::MissingContributions)
    );

    let (_, fresh_first_shares) = prepare_inputs(&session, &owner_keys, &worker_keys, 0x70);
    let first_contributions = run_workers(
        &session,
        &first_certificate,
        &worker_keys,
        fresh_first_shares,
    );
    let mut wrong_certificate =
        DistributedProverCoordinator::new(session.clone(), &second_request, &second_certificate)
            .unwrap();
    assert_eq!(
        wrong_certificate.accept(first_contributions[0].clone()),
        Err(DistributedProverError::InputCertificateMismatch)
    );
}
