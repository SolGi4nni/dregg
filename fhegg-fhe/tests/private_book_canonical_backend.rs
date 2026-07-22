//! Exact and hostile gates for the logarithmic share-opening proof backend.

#[path = "../src/private_book_canonical_backend.rs"]
mod private_book_canonical_backend;
#[path = "../src/private_book_distributed_inputs.rs"]
mod private_book_distributed_inputs;
#[path = "../src/private_book_distributed_prover.rs"]
mod private_book_distributed_prover;

use private_book_canonical_backend::{
    canonical_share_opening_protocol_id, warm_production_generators_for_test,
    CanonicalShareOpeningBackend, CanonicalShareOpeningVerifier,
};
use private_book_distributed_inputs::{
    DistributedInputCertificate, DistributedInputCoordinator, DistributedWitnessSession,
    LocalOrderWitness, PreparedWitnessShare, PrivateSide, WitnessPartyMachine, BFV_DEGREE,
    ORDER_COUNT,
};
use private_book_distributed_prover::{
    DistributedProverCoordinator, DistributedProverError, ShareBoundProverRequest,
    WorkerLocalProofBackend, WorkerProofArtifact, WorkerProofContext, WorkerProofContribution,
    WorkerProofProcess,
};

use curve25519_dalek::scalar::Scalar;
use ed25519_dalek::SigningKey;
use rand::rngs::StdRng;
use rand::SeedableRng;
use std::time::Instant;

fn keys<const N: usize>(base: u8) -> [SigningKey; N] {
    core::array::from_fn(|index| SigningKey::from_bytes(&[base + index as u8; 32]))
}

fn session(
    owner_keys: &[SigningKey; ORDER_COUNT],
    worker_keys: &[SigningKey; 3],
) -> DistributedWitnessSession {
    session_with_degree(owner_keys, worker_keys, 8)
}

fn session_with_degree(
    owner_keys: &[SigningKey; ORDER_COUNT],
    worker_keys: &[SigningKey; 3],
    degree: usize,
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
        degree,
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
    canonical_contributions_with_generator_mode(session, certificate, worker_keys, shares, false)
}

fn canonical_contributions_with_generator_mode(
    session: &DistributedWitnessSession,
    certificate: &DistributedInputCertificate,
    worker_keys: &[SigningKey; 3],
    shares: Vec<PreparedWitnessShare>,
    force_fresh_generators: bool,
) -> Vec<WorkerProofContribution> {
    let request =
        ShareBoundProverRequest::new(session, certificate, canonical_share_opening_protocol_id())
            .unwrap();
    shares
        .into_iter()
        .enumerate()
        .map(|(worker, share)| {
            let backend = if force_fresh_generators {
                CanonicalShareOpeningBackend::new_with_fresh_generators_for_test(worker)
            } else {
                CanonicalShareOpeningBackend::new(worker)
            };
            WorkerProofProcess::new(
                session.clone(),
                worker,
                worker_keys[worker].clone(),
                backend,
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
    ) -> Result<WorkerProofArtifact, Self::Error> {
        WorkerProofArtifact::new(vec![0x99; 32]).map_err(|_| ())
    }
}

struct CorruptProofBackend {
    inner: CanonicalShareOpeningBackend,
    mutation: Option<ArtifactMutation>,
}

#[derive(Clone, Copy)]
enum ArtifactMutation {
    ResponseScalar,
    SwapOwnerProofs,
}

impl WorkerLocalProofBackend for CorruptProofBackend {
    type Error = ();

    fn protocol_id(&self) -> [u8; 32] {
        canonical_share_opening_protocol_id()
    }

    fn prove_local(
        &mut self,
        context: &WorkerProofContext,
        input_certificate: &DistributedInputCertificate,
        witness: PreparedWitnessShare,
    ) -> Result<WorkerProofArtifact, Self::Error> {
        let honest = self
            .inner
            .prove_local(context, input_certificate, witness)
            .map_err(|_| ())?;
        let Some(mutation) = self.mutation else {
            return Ok(honest);
        };
        let mut bytes = honest.as_bytes().to_vec();
        let proof_len = u32::from_be_bytes(bytes[86..90].try_into().unwrap()) as usize;
        match mutation {
            ArtifactMutation::ResponseScalar => {
                // Substitute one canonical response scalar while leaving both
                // codecs valid. Add one to avoid even negligible equality with
                // the honestly sampled response.
                let response_start = 90 + proof_len - 32;
                let original = Option::<Scalar>::from(Scalar::from_canonical_bytes(
                    bytes[response_start..response_start + 32]
                        .try_into()
                        .unwrap(),
                ))
                .unwrap();
                bytes[response_start..response_start + 32]
                    .copy_from_slice(&(original + Scalar::ONE).to_bytes());
            }
            ArtifactMutation::SwapOwnerProofs => {
                // Proof lengths are fixed for a given padded vector width. Swap
                // owner 0 and owner 1 proof bodies while retaining canonical
                // framing; owner/order transcript binding must reject it.
                let second_len_start = 90 + proof_len;
                assert_eq!(
                    u32::from_be_bytes(
                        bytes[second_len_start..second_len_start + 4]
                            .try_into()
                            .unwrap()
                    ) as usize,
                    proof_len
                );
                let first = bytes[90..90 + proof_len].to_vec();
                let second_start = second_len_start + 4;
                let second = bytes[second_start..second_start + proof_len].to_vec();
                bytes[90..90 + proof_len].copy_from_slice(&second);
                bytes[second_start..second_start + proof_len].copy_from_slice(&first);
            }
        }
        refresh_artifact_checksum(&mut bytes);
        WorkerProofArtifact::new(bytes).map_err(|_| ())
    }
}

struct ReplayArtifactBackend {
    artifact: WorkerProofArtifact,
}

impl WorkerLocalProofBackend for ReplayArtifactBackend {
    type Error = ();

    fn protocol_id(&self) -> [u8; 32] {
        canonical_share_opening_protocol_id()
    }

    fn prove_local(
        &mut self,
        _context: &WorkerProofContext,
        _input_certificate: &DistributedInputCertificate,
        _witness: PreparedWitnessShare,
    ) -> Result<WorkerProofArtifact, Self::Error> {
        Ok(self.artifact.clone())
    }
}

fn refresh_artifact_checksum(bytes: &mut [u8]) {
    let checksum_start = bytes.len() - 32;
    let mut hasher =
        blake3::Hasher::new_derive_key("fhegg/private-book-share-opening-pok/artifact/v2");
    hasher.update(&(checksum_start as u64).to_be_bytes());
    hasher.update(&bytes[..checksum_start]);
    let checksum = *hasher.finalize().as_bytes();
    bytes[checksum_start..].copy_from_slice(&checksum);
}

fn envelope_from_contributions(
    session: &DistributedWitnessSession,
    certificate: &DistributedInputCertificate,
    contributions: Vec<WorkerProofContribution>,
) -> private_book_distributed_prover::DistributedProverEnvelope {
    let request =
        ShareBoundProverRequest::new(session, certificate, canonical_share_opening_protocol_id())
            .unwrap();
    let mut coordinator =
        DistributedProverCoordinator::new(session.clone(), &request, certificate).unwrap();
    for contribution in contributions {
        coordinator.accept(contribution).unwrap();
    }
    coordinator.finish().unwrap()
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
    assert!(envelope
        .worker_public_artifacts()
        .all(|(_, artifact)| artifact.len() < 8 * 1024));
}

#[test]
fn authenticated_encrypted_orders_gate_real_game_asset_settlement_canonical_generator_cache_profile(
) {
    let owner_keys = keys::<ORDER_COUNT>(0x18);
    let worker_keys = keys::<3>(0x38);
    let session = session_with_degree(&owner_keys, &worker_keys, BFV_DEGREE);

    let fresh_inputs_started = Instant::now();
    let (fresh_certificate, fresh_shares) =
        prepare_inputs(&session, &owner_keys, &worker_keys, 0x68);
    eprintln!(
        "fhegg canonical-generator profile: fresh-input-preparation={:?}",
        fresh_inputs_started.elapsed()
    );
    let fresh_prove_started = Instant::now();
    let fresh_contributions = canonical_contributions_with_generator_mode(
        &session,
        &fresh_certificate,
        &worker_keys,
        fresh_shares,
        true,
    );
    eprintln!(
        "fhegg canonical-generator profile: fresh-prove-three={:?}",
        fresh_prove_started.elapsed()
    );
    let fresh_envelope =
        envelope_from_contributions(&session, &fresh_certificate, fresh_contributions);
    let fresh_request = ShareBoundProverRequest::new(
        &session,
        &fresh_certificate,
        canonical_share_opening_protocol_id(),
    )
    .unwrap();
    let fresh_verifier =
        CanonicalShareOpeningVerifier::new_with_fresh_generators_for_test(&fresh_certificate)
            .unwrap();
    let fresh_verify_started = Instant::now();
    fresh_envelope
        .verify_backend(
            &session,
            &fresh_request,
            &fresh_certificate,
            &fresh_verifier,
        )
        .unwrap();
    eprintln!(
        "fhegg canonical-generator profile: fresh-public-verify={:?}",
        fresh_verify_started.elapsed()
    );

    let cached_inputs_started = Instant::now();
    let (cached_certificate, cached_shares) =
        prepare_inputs(&session, &owner_keys, &worker_keys, 0x68);
    // The certificates contain randomized zero-knowledge proofs, so their
    // bytes are intentionally not a stable comparison oracle.  What must be
    // identical across the fresh/cache generator lifecycles is the public
    // statement: the owner commitments and every worker-share commitment.
    fresh_certificate.verify(&session).unwrap();
    cached_certificate.verify(&session).unwrap();
    assert_eq!(
        cached_certificate.joint_input_commitment().unwrap(),
        fresh_certificate.joint_input_commitment().unwrap()
    );
    for owner in 0..ORDER_COUNT {
        assert_eq!(
            cached_certificate.owner_commitment(owner),
            fresh_certificate.owner_commitment(owner)
        );
        for worker in 0..session.n_workers() {
            assert_eq!(
                cached_certificate.share_commitment(owner, worker),
                fresh_certificate.share_commitment(owner, worker)
            );
        }
    }
    eprintln!(
        "fhegg canonical-generator profile: cached-input-preparation={:?}",
        cached_inputs_started.elapsed()
    );
    let cold_init_started = Instant::now();
    warm_production_generators_for_test();
    eprintln!(
        "fhegg canonical-generator profile: cold-cache-init={:?}",
        cold_init_started.elapsed()
    );
    let cached_prove_started = Instant::now();
    let cached_contributions =
        canonical_contributions(&session, &cached_certificate, &worker_keys, cached_shares);
    eprintln!(
        "fhegg canonical-generator profile: warm-prove-three={:?}",
        cached_prove_started.elapsed()
    );
    let cached_envelope =
        envelope_from_contributions(&session, &cached_certificate, cached_contributions);
    let cached_request = ShareBoundProverRequest::new(
        &session,
        &cached_certificate,
        canonical_share_opening_protocol_id(),
    )
    .unwrap();
    let cached_verifier = CanonicalShareOpeningVerifier::new(&cached_certificate).unwrap();
    let cached_verify_started = Instant::now();
    cached_envelope
        .verify_backend(
            &session,
            &cached_request,
            &cached_certificate,
            &cached_verifier,
        )
        .unwrap();
    eprintln!(
        "fhegg canonical-generator profile: warm-public-verify={:?}",
        cached_verify_started.elapsed()
    );
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

#[test]
fn roster_signed_corrupt_share_proof_is_rejected_by_cryptographic_verifier() {
    let owner_keys = keys::<ORDER_COUNT>(0x12);
    let worker_keys = keys::<3>(0x32);
    let session = session(&owner_keys, &worker_keys);
    let (certificate, shares) = prepare_inputs(&session, &owner_keys, &worker_keys, 0x90);
    let protocol_id = canonical_share_opening_protocol_id();
    let request = ShareBoundProverRequest::new(&session, &certificate, protocol_id).unwrap();
    let contributions = shares
        .into_iter()
        .enumerate()
        .map(|(worker, share)| {
            let backend = CorruptProofBackend {
                inner: CanonicalShareOpeningBackend::new(worker),
                mutation: (worker == 0).then_some(ArtifactMutation::ResponseScalar),
            };
            let contribution = WorkerProofProcess::new(
                session.clone(),
                worker,
                worker_keys[worker].clone(),
                backend,
            )
            .unwrap()
            .run(&request, &certificate, share)
            .unwrap();
            (worker, contribution)
        })
        .collect::<Vec<_>>();

    let mut coordinator =
        DistributedProverCoordinator::new(session.clone(), &request, &certificate).unwrap();
    for (_, contribution) in contributions {
        coordinator.accept(contribution).unwrap();
    }
    let envelope = coordinator.finish().unwrap();
    // The roster signatures and generic artifact hashes are genuine.  The
    // proof verifier, not the worker attestation, rejects the forged opening.
    envelope
        .verify_envelope(&session, &request, &certificate)
        .unwrap();
    let verifier = CanonicalShareOpeningVerifier::new(&certificate).unwrap();
    assert_eq!(
        envelope.verify_backend(&session, &request, &certificate, &verifier),
        Err(DistributedProverError::BackendRejected)
    );
}

#[test]
fn proof_artifacts_are_not_replayable_across_worker_request_or_owner_order() {
    let owner_keys = keys::<ORDER_COUNT>(0x13);
    let worker_keys = keys::<3>(0x33);
    let session = session(&owner_keys, &worker_keys);
    let (certificate, shares) = prepare_inputs(&session, &owner_keys, &worker_keys, 0xa0);
    let honest_contributions =
        canonical_contributions(&session, &certificate, &worker_keys, shares);
    let honest_envelope = envelope_from_contributions(&session, &certificate, honest_contributions);
    let artifacts = honest_envelope
        .worker_public_artifacts()
        .map(|(_, bytes)| WorkerProofArtifact::new(bytes.to_vec()).unwrap())
        .collect::<Vec<_>>();

    // Re-sign worker 1's proof artifact as worker 0. Generic contribution
    // authentication succeeds, but the worker-bound proof transcript fails.
    let (same_certificate, replay_shares) =
        prepare_inputs(&session, &owner_keys, &worker_keys, 0xa0);
    // The dealer/share commitments are reproduced by the fixture RNG, while
    // the owner-local R1CS proof correctly uses fresh prover entropy. Requiring
    // byte-identical certificates here would accidentally require deterministic
    // zero-knowledge proofs; the regenerated private shares still name the
    // exact original dealing digests checked below by WorkerProofProcess.
    assert_ne!(certificate.to_bytes(), same_certificate.to_bytes());
    let request = ShareBoundProverRequest::new(
        &session,
        &certificate,
        canonical_share_opening_protocol_id(),
    )
    .unwrap();
    let cross_worker = replay_shares
        .into_iter()
        .enumerate()
        .map(|(worker, share)| {
            let artifact = if worker == 0 {
                artifacts[1].clone()
            } else {
                artifacts[worker].clone()
            };
            WorkerProofProcess::new(
                session.clone(),
                worker,
                worker_keys[worker].clone(),
                ReplayArtifactBackend { artifact },
            )
            .unwrap()
            .run(&request, &certificate, share)
            .unwrap()
        })
        .collect::<Vec<_>>();
    let envelope = envelope_from_contributions(&session, &certificate, cross_worker);
    envelope
        .verify_envelope(&session, &request, &certificate)
        .unwrap();
    let verifier = CanonicalShareOpeningVerifier::new(&certificate).unwrap();
    assert_eq!(
        envelope.verify_backend(&session, &request, &certificate, &verifier),
        Err(DistributedProverError::BackendRejected)
    );

    // Re-sign artifacts from certificate/request A under a fresh request B.
    // The exact internal request/certificate/commitment binding rejects them.
    let (other_certificate, other_shares) =
        prepare_inputs(&session, &owner_keys, &worker_keys, 0xb0);
    let other_request = ShareBoundProverRequest::new(
        &session,
        &other_certificate,
        canonical_share_opening_protocol_id(),
    )
    .unwrap();
    let cross_request = other_shares
        .into_iter()
        .enumerate()
        .map(|(worker, share)| {
            WorkerProofProcess::new(
                session.clone(),
                worker,
                worker_keys[worker].clone(),
                ReplayArtifactBackend {
                    artifact: artifacts[worker].clone(),
                },
            )
            .unwrap()
            .run(&other_request, &other_certificate, share)
            .unwrap()
        })
        .collect::<Vec<_>>();
    let envelope = envelope_from_contributions(&session, &other_certificate, cross_request);
    envelope
        .verify_envelope(&session, &other_request, &other_certificate)
        .unwrap();
    let verifier = CanonicalShareOpeningVerifier::new(&other_certificate).unwrap();
    assert_eq!(
        envelope.verify_backend(&session, &other_request, &other_certificate, &verifier),
        Err(DistributedProverError::BackendRejected)
    );

    // Finally retain the right worker/request/artifact framing but swap two
    // owner proofs. The public verifier must enforce canonical owner order.
    let (_, owner_swap_shares) = prepare_inputs(&session, &owner_keys, &worker_keys, 0xa0);
    let owner_swapped = owner_swap_shares
        .into_iter()
        .enumerate()
        .map(|(worker, share)| {
            WorkerProofProcess::new(
                session.clone(),
                worker,
                worker_keys[worker].clone(),
                CorruptProofBackend {
                    inner: CanonicalShareOpeningBackend::new(worker),
                    mutation: (worker == 0).then_some(ArtifactMutation::SwapOwnerProofs),
                },
            )
            .unwrap()
            .run(&request, &certificate, share)
            .unwrap()
        })
        .collect::<Vec<_>>();
    let envelope = envelope_from_contributions(&session, &certificate, owner_swapped);
    envelope
        .verify_envelope(&session, &request, &certificate)
        .unwrap();
    let certificate_verifier = CanonicalShareOpeningVerifier::new(&certificate).unwrap();
    assert_eq!(
        envelope.verify_backend(&session, &request, &certificate, &certificate_verifier),
        Err(DistributedProverError::BackendRejected)
    );
}
