//! Production-degree exact-BFV continuation gate.
//!
//! This target derives every owner quotient from the deployed `fhe.rs`
//! ciphertext/key/message-table relation, then runs the bounded private custody
//! ceremony. The 3,072 public negacyclic correlations and production owner
//! proofs make it heavy-only; reduced protocol state-machine teeth live in the
//! library test module.

use dregg_circuit_prove::dark_bazaar_private::{statement, PrivateBookWitness, PrivateOrder, Side};
use ed25519_dalek::SigningKey;
use fhegg_fhe::private_book_distributed_bfv::{
    BfvQuotientCoordinator, BfvQuotientWorkerMachine, BfvRelationCoordinator,
    BfvWorkerRelationProof, DistributedBfvError, DistributedBfvProofEnvelope,
    DistributedBfvPublicRelation, DistributedBfvRelationRound, DistributedBfvRound,
    OwnerBfvQuotients,
};
use fhegg_fhe::private_book_distributed_inputs::{
    DealerOutput, DistributedInputCoordinator, DistributedWitnessSession, LocalOrderWitness,
    OwnerWitnessContinuation, PrivateSide, WitnessPartyMachine, ORDER_COUNT,
};
use fhegg_fhe::private_book_distributed_root::{
    prove_owner_root_link, RootLinkCoordinator, RootLinkDraft,
};
use fhegg_fhe::private_book_relation::{
    encrypt_private_book, PrivateBookCiphertexts, PrivateBookEncryptionOpening,
};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
};
use rand::rngs::StdRng;
use rand::SeedableRng;

fn keys<const N: usize>(base: u8) -> [SigningKey; N] {
    core::array::from_fn(|index| SigningKey::from_bytes(&[base + index as u8; 32]))
}

fn rewrite_checksum(bytes: &mut [u8], domain: &str) {
    let checksum_start = bytes.len() - 32;
    let mut hasher = blake3::Hasher::new_derive_key(domain);
    hasher.update(&(checksum_start as u64).to_be_bytes());
    hasher.update(&bytes[..checksum_start]);
    bytes[checksum_start..].copy_from_slice(hasher.finalize().as_bytes());
}

fn collective_keygen(
    session: &KeygenSession,
    params: &BfvParams,
) -> (Vec<ThresholdParty>, CollectivePublicKey) {
    let mut coordinator = KeygenCoordinator::new(session.clone(), params.clone());
    let mut parties = Vec::with_capacity(session.n_parties());
    for party in 0..session.n_parties() {
        let (state, contribution) =
            ThresholdParty::join(session, party, params).expect("party keygen");
        coordinator.accept(contribution).expect("ordered keygen");
        parties.push(state);
    }
    (parties, coordinator.finish().expect("collective key"))
}

#[test]
fn exact_fhe_rs_rows_derive_bounded_private_quotients_for_every_owner() {
    let params = BfvParams::fold_set();
    let key_session = KeygenSession::from_seed(2, [0x21; 32]).expect("key session");
    let (_key_parties, public_key) = collective_keygen(&key_session, &params);
    let witness = PrivateBookWitness::try_from_orders_with_blinding(
        &[
            PrivateOrder::bid(10, 2),
            PrivateOrder::bid(6, 1),
            PrivateOrder::ask(5, 0),
            PrivateOrder::ask(8, 1),
        ],
        core::array::from_fn(|lane| 17_000 + lane as u32),
    )
    .expect("private book");
    let seeds = [[0x31; 32], [0x32; 32], [0x33; 32], [0x34; 32]];
    let opening = PrivateBookEncryptionOpening::from_seeds(seeds);
    let public = statement(0xDBA2, &witness).expect("private statement");
    let ciphertexts =
        encrypt_private_book(&witness, &opening, &params, &public_key).expect("BFV book");

    let owner_keys = keys::<ORDER_COUNT>(0x40);
    let worker_keys = keys::<3>(0x60);
    let session = DistributedWitnessSession::new(
        public,
        &ciphertexts,
        &params,
        &public_key,
        [0x80; 32],
        owner_keys
            .each_ref()
            .map(|key| key.verifying_key().to_bytes()),
        worker_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
    )
    .expect("production session");
    let mut input_workers = worker_keys
        .iter()
        .enumerate()
        .map(|(worker, key)| {
            WitnessPartyMachine::new(session.clone(), worker, key.clone()).expect("input worker")
        })
        .collect::<Vec<_>>();
    let mut input_coordinator = DistributedInputCoordinator::new(session.clone());
    let mut continuations = Vec::<OwnerWitnessContinuation>::with_capacity(ORDER_COUNT);
    for owner in 0..ORDER_COUNT {
        let order = witness.orders[owner];
        let local = LocalOrderWitness::from_seed(
            &session,
            owner,
            match order.side {
                Side::Bid => PrivateSide::Bid,
                Side::Ask => PrivateSide::Ask,
            },
            order.limit,
            order.qty,
            seeds[owner],
            (owner == 0).then_some(witness.blinding),
        )
        .expect("exact local witness");
        let mut rng = StdRng::from_seed([0x90 + owner as u8; 32]);
        let DealerOutput {
            contribution,
            private_packets,
            continuation,
        } = local
            .deal(&session, &owner_keys[owner], &mut rng)
            .expect("base deal");
        let public_contribution = contribution.clone();
        input_coordinator
            .accept_dealer(contribution)
            .expect("base public deal");
        for (worker, packet) in private_packets.into_iter().enumerate() {
            let acknowledgement = input_workers[worker]
                .accept(&public_contribution, packet)
                .expect("base opening");
            input_coordinator
                .accept_acknowledgement(acknowledgement)
                .expect("base ack");
        }
        continuations.push(continuation);
    }
    let prepared_inputs = input_workers
        .into_iter()
        .map(|worker| worker.finish().expect("prepared base share"))
        .collect::<Vec<_>>();
    let input_certificate = input_coordinator.finish().expect("base certificate");

    let exact_public =
        DistributedBfvPublicRelation::derive(public, &ciphertexts, &params, &public_key)
            .expect("canonical exact public coefficients");
    assert_eq!(session.relation_digest(), exact_public.relation_digest());

    // The source-viewer proof binds the exact HidingFRI root opening, while
    // every owner independently links only its own selected coordinates to the
    // already certified distributed vector. No coordinator receives an order,
    // BFV seed, vector opening, root blind, or scalar-commitment blinding.
    let mut root_rng = StdRng::from_seed([0x9f; 32]);
    let root_output = RootLinkDraft::create(
        &session,
        &input_certificate,
        &exact_public,
        &witness,
        &mut root_rng,
    )
    .expect("commitment-bound Poseidon root draft");
    let mut root_coordinator = RootLinkCoordinator::new(
        session.clone(),
        input_certificate.clone(),
        root_output.draft.clone(),
        &exact_public,
    )
    .expect("root-link coordinator");
    for (owner, (continuation, private_opening)) in continuations
        .iter()
        .zip(root_output.private_packets)
        .enumerate()
    {
        let mut rng = StdRng::from_seed([0x9a + owner as u8; 32]);
        let proof = prove_owner_root_link(
            continuation,
            &session,
            &input_certificate,
            &root_output.draft,
            private_opening,
            &owner_keys[owner],
            &mut rng,
        )
        .expect("owner-local root link");
        root_coordinator.accept(proof).expect("root owner proof");
    }
    let root_certificate = root_coordinator.finish().expect("complete root link");
    root_certificate
        .verify(&session, &input_certificate, &exact_public)
        .expect("public commitment-bound Poseidon root verification");
    assert_ne!(root_certificate.transcript_digest(), [0; 32]);
    let root_wire = root_certificate.to_bytes();
    assert_eq!(
        root_wire.len(),
        fhegg_fhe::private_book_distributed_root::RootLinkCertificate::expected_wire_len(&session)
            .expect("fixed root wire length")
    );
    let decoded_root = fhegg_fhe::private_book_distributed_root::RootLinkCertificate::from_bytes(
        &root_wire,
        &session,
        &input_certificate,
        &exact_public,
    )
    .expect("strict root-link transport");
    assert_eq!(decoded_root.to_bytes(), root_wire);
    assert!(
        fhegg_fhe::private_book_distributed_root::RootLinkCertificate::from_bytes(
            &root_wire[..root_wire.len() - 1],
            &session,
            &input_certificate,
            &exact_public,
        )
        .is_err()
    );
    let mut trailing_root = root_wire.clone();
    trailing_root.push(0);
    assert!(
        fhegg_fhe::private_book_distributed_root::RootLinkCertificate::from_bytes(
            &trailing_root,
            &session,
            &input_certificate,
            &exact_public,
        )
        .is_err()
    );
    // Repair the nested checksum after each hostile framing mutation so the
    // parser teeth, rather than the checksum, are what reject it.
    const ROOT_CHECKSUM_DOMAIN: &str =
        "fhegg/private-book-distributed-root/certificate-checksum/v1";
    const ROOT_DRAFT_BYTES: usize = 2_143;
    let owner_count_offset = 78 + ROOT_DRAFT_BYTES;
    let first_owner_offset = owner_count_offset + 2;
    let first_link_len_offset = first_owner_offset + 2 + 32;
    for (offset, replacement) in [
        (0usize, vec![b'X']),
        (8, 2u16.to_be_bytes().to_vec()),
        (74, 0u32.to_be_bytes().to_vec()),
        (owner_count_offset, 3u16.to_be_bytes().to_vec()),
        (first_owner_offset, 1u16.to_be_bytes().to_vec()),
        (first_link_len_offset, 0u32.to_be_bytes().to_vec()),
    ] {
        let mut malformed = root_wire.clone();
        malformed[offset..offset + replacement.len()].copy_from_slice(&replacement);
        rewrite_checksum(&mut malformed, ROOT_CHECKSUM_DOMAIN);
        assert!(
            fhegg_fhe::private_book_distributed_root::RootLinkCertificate::from_bytes(
                &malformed,
                &session,
                &input_certificate,
                &exact_public,
            )
            .is_err()
        );
    }

    let round = DistributedBfvRound::new(&session, &input_certificate, &exact_public)
        .expect("exact BFV round");
    let mut quotient_workers = worker_keys
        .iter()
        .enumerate()
        .map(|(worker, key)| {
            BfvQuotientWorkerMachine::new(round.clone(), worker, key.clone())
                .expect("quotient worker")
        })
        .collect::<Vec<_>>();
    let mut quotient_coordinator = BfvQuotientCoordinator::new(round.clone());
    for (owner, continuation) in continuations.into_iter().enumerate() {
        let quotients = OwnerBfvQuotients::derive_exact(&round, continuation, &exact_public)
            .expect("all exact owner equations divide their RNS modulus");
        let mut rng = StdRng::from_seed([0xa0 + owner as u8; 32]);
        let output = quotients
            .deal(&round, &owner_keys[owner], &mut rng)
            .expect("bounded quotient deal");
        let contribution = output.contribution.clone();
        quotient_coordinator
            .accept_dealer(output.contribution)
            .expect("public quotient deal");
        for (worker, packet) in output.private_packets.into_iter().enumerate() {
            let acknowledgement = quotient_workers[worker]
                .accept(&contribution, packet)
                .expect("private quotient opening");
            quotient_coordinator
                .accept_acknowledgement(acknowledgement)
                .expect("quotient ack");
        }
    }
    let prepared_quotients = quotient_workers
        .into_iter()
        .map(|worker| worker.finish().expect("prepared quotient share"))
        .collect::<Vec<_>>();
    let quotient_certificate = quotient_coordinator
        .finish()
        .expect("bounded quotient certificate");

    let relation_round = DistributedBfvRelationRound::new(
        &round,
        &input_certificate,
        &quotient_certificate,
        &exact_public,
    )
    .expect("post-custody exact relation round");
    assert_ne!(relation_round.second_challenge(), [0; 32]);
    let mut relation_coordinator = BfvRelationCoordinator::new(relation_round.clone());
    for (worker, (input_share, quotient_share)) in prepared_inputs
        .into_iter()
        .zip(prepared_quotients)
        .enumerate()
    {
        let mut rng = StdRng::from_seed([0xb0 + worker as u8; 32]);
        let proof = BfvWorkerRelationProof::create(
            &relation_round,
            input_share,
            quotient_share,
            &input_certificate,
            &quotient_certificate,
            &worker_keys[worker],
            &mut rng,
        )
        .expect("worker exact relation proof");
        relation_coordinator.accept(proof).expect("worker proof");
    }
    let relation_certificate = relation_coordinator
        .finish()
        .expect("exact BFV relation certificate");
    assert_ne!(relation_certificate.transcript_digest(), [0; 32]);

    let envelope = DistributedBfvProofEnvelope::new(
        &session,
        &exact_public,
        input_certificate.clone(),
        quotient_certificate.clone(),
        relation_certificate,
        root_certificate,
    )
    .expect("transportable complete public proof");
    let envelope_wire = envelope.to_bytes();
    let decoded = DistributedBfvProofEnvelope::from_bytes(&envelope_wire, &session, &exact_public)
        .expect("strict complete public proof decode");
    assert_eq!(decoded.to_bytes(), envelope_wire);
    assert_ne!(decoded.transcript_digest(), [0; 32]);
    let input_len = envelope.input_certificate().to_bytes().len();
    let quotient_len = envelope.quotient_certificate().to_bytes().len();
    let relation_len = envelope.relation_certificate().to_bytes().len();
    let root_len = envelope.root_certificate().to_bytes().len();
    assert_eq!(
        envelope_wire.len(),
        154 + input_len + quotient_len + relation_len + root_len
    );
    let mut truncated = envelope_wire.clone();
    truncated.pop();
    assert!(matches!(
        DistributedBfvProofEnvelope::from_bytes(&truncated, &session, &exact_public),
        Err(DistributedBfvError::MalformedWire)
    ));
    let quotient_length_offset = 78 + input_len;
    let relation_length_offset = quotient_length_offset + 4 + quotient_len;
    let root_length_offset = relation_length_offset + 4 + relation_len;
    for offset in [
        74usize,
        quotient_length_offset,
        relation_length_offset,
        root_length_offset,
    ] {
        for encoded in [0u32, u32::MAX] {
            let mut malformed = envelope_wire.clone();
            malformed[offset..offset + 4].copy_from_slice(&encoded.to_be_bytes());
            rewrite_checksum(
                &mut malformed,
                "fhegg/private-book-distributed-bfv/public-envelope-checksum/v2-root-bound",
            );
            assert!(matches!(
                DistributedBfvProofEnvelope::from_bytes(&malformed, &session, &exact_public),
                Err(DistributedBfvError::MalformedWire)
            ));
        }
    }
    let mut downgraded = envelope_wire.clone();
    downgraded[..8].copy_from_slice(b"FHDBE001");
    downgraded[8..10].copy_from_slice(&1u16.to_be_bytes());
    rewrite_checksum(
        &mut downgraded,
        "fhegg/private-book-distributed-bfv/public-envelope-checksum/v2-root-bound",
    );
    assert!(matches!(
        DistributedBfvProofEnvelope::from_bytes(&downgraded, &session, &exact_public),
        Err(DistributedBfvError::MalformedWire)
    ));

    let mut wrong_rows = ciphertexts.rows().clone();
    wrong_rows[0].polys[0].rows[0][0] ^= 1;
    let wrong_public = DistributedBfvPublicRelation::derive(
        public,
        &PrivateBookCiphertexts::from_rows(wrong_rows),
        &params,
        &public_key,
    )
    .expect("well-shaped but substituted public rows");
    assert!(matches!(
        DistributedBfvRound::new(&session, &input_certificate, &wrong_public),
        Err(DistributedBfvError::ExactPublicRelation)
    ));
    assert!(matches!(
        DistributedBfvProofEnvelope::from_bytes(&envelope_wire, &session, &wrong_public),
        Err(DistributedBfvError::MalformedWire)
    ));
}
