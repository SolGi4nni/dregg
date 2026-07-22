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
    BfvQuotientCoordinator, BfvQuotientWorkerMachine, DistributedBfvError,
    DistributedBfvPublicRelation, DistributedBfvRound, OwnerBfvQuotients,
};
use fhegg_fhe::private_book_distributed_inputs::{
    DealerOutput, DistributedInputCoordinator, DistributedWitnessSession, LocalOrderWitness,
    OwnerWitnessContinuation, PrivateSide, WitnessPartyMachine, ORDER_COUNT,
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
    let _prepared_inputs = input_workers
        .into_iter()
        .map(|worker| worker.finish().expect("prepared base share"))
        .collect::<Vec<_>>();
    let input_certificate = input_coordinator.finish().expect("base certificate");

    let exact_public =
        DistributedBfvPublicRelation::derive(public, &ciphertexts, &params, &public_key)
            .expect("canonical exact public coefficients");
    assert_eq!(session.relation_digest(), exact_public.relation_digest());
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
    for worker in quotient_workers {
        let _ = worker.finish().expect("prepared quotient share");
    }
    quotient_coordinator
        .finish()
        .expect("bounded quotient certificate");

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
}
