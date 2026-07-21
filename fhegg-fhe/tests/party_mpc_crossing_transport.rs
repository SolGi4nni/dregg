//! Live authenticated PartyMPC crossing for the canonical packed private book.
//!
//! This replaces a producer-invented `simulate_public_transcript` carrier with
//! actual party machines, encrypted peer ingress, signed gate/output frames,
//! and exact public reconstruction. The test starts at the four exact private
//! BFV proof rows, homomorphically folds those same ciphertexts, crosses the
//! masked threshold decrypt-to-shares boundary, and gives each process only its
//! local nine-slot mod-`t` share. No side-specific source encoding is available
//! on this path.

#![cfg(feature = "amm-input-binding")]

use std::thread;
use std::time::{Duration, Instant};

use dregg_circuit_prove::dark_bazaar_private::{statement, PrivateBookWitness, PrivateOrder};
use ed25519_dalek::SigningKey;
use fhegg_fhe::boundary::{MaskedBoundaryParty, MaskedDecryptCoordinator, MaskedDecryptSession};
use fhegg_fhe::mpc::Crossing;
use fhegg_fhe::mpc_party::transport::{
    fresh_crossing_preprocessing_seed, prepare_private_book_crossing_input,
    verify_public_crossing_transcript, CrossingCoordinatorMachine, CrossingPartyMachine,
    CrossingTransportError, CrossingTransportRoster,
};
use fhegg_fhe::mpc_party::{trusted_dealer_triples, DistributedRun, PartyMpcSession};
use fhegg_fhe::private_book_relation::{
    encrypt_private_book, fold_private_book_ciphertexts, private_book_relation_digest,
    verify_private_book_opening, PrivateBookEncryptionOpening, PRIVATE_BOOK_LIVE_SLOTS,
};
use fhegg_fhe::threshold::{
    BfvParams, KeygenCoordinator, KeygenSession, ThresholdParty, MIN_SMUDGE_BITS,
};
use rand::rngs::StdRng;
use rand::SeedableRng;

fn exact_private_book_boundary() -> (BfvParams, [u8; 32], [[u64; 9]; 2]) {
    let params = BfvParams::fold_set();
    let keygen_session =
        KeygenSession::from_seed(2, [0x20; 32]).expect("collective keygen session");
    let mut keygen = KeygenCoordinator::new(keygen_session.clone(), params.clone());
    let mut threshold_parties = Vec::new();
    for party in 0..2 {
        let (state, contribution) = ThresholdParty::join(&keygen_session, party, &params)
            .expect("party-owned threshold key share");
        keygen
            .accept(contribution)
            .expect("ordered key contribution");
        threshold_parties.push(state);
    }
    let public_key = keygen.finish().expect("collective public key");

    // These exact private orders produce D=[3,3,2,0], S=[0,2,2,3]. Buckets
    // 1 and 2 tie at volume two, so the crossing must keep the lower index.
    let witness = PrivateBookWitness::try_from_orders_with_blinding(
        &[
            PrivateOrder::bid(2, 2),
            PrivateOrder::bid(1, 1),
            PrivateOrder::ask(2, 1),
            PrivateOrder::ask(1, 3),
        ],
        core::array::from_fn(|lane| 0x100 + lane as u32),
    )
    .expect("canonical private N4K4 witness");
    let opening =
        PrivateBookEncryptionOpening::from_seeds([[0x21; 32], [0x22; 32], [0x23; 32], [0x24; 32]]);
    let public_statement = statement(0x5BA2_C205, &witness).expect("private clearing statement");
    assert_eq!((public_statement.p_star, public_statement.v_star), (1, 2));
    let ciphertexts = encrypt_private_book(&witness, &opening, &params, &public_key)
        .expect("exact side-hiding BFV proof rows");
    verify_private_book_opening(
        public_statement,
        &witness,
        &ciphertexts,
        &opening,
        &params,
        &public_key,
    )
    .expect("same private opening drives HidingFRI root and BFV rows");
    let relation_digest =
        private_book_relation_digest(public_statement, &ciphertexts, &params, &public_key);
    let folded = fold_private_book_ciphertexts(&ciphertexts, &params)
        .expect("homomorphic fold consumes those exact proof rows");

    // Mask and threshold-decrypt the one exact nine-slot fold. The coordinator
    // learns only the one-time-padded opening; each mask owner derives its own
    // local mod-t share without exposing the mask or an unmasked curve.
    let boundary_session = MaskedDecryptSession::from_public(
        relation_digest,
        2,
        PRIVATE_BOOK_LIVE_SLOTS,
        folded.ciphertext().clone(),
        &params,
    )
    .expect("source-bound masked boundary");
    let mut mask_coordinator =
        MaskedDecryptCoordinator::new(boundary_session.clone(), params.clone());
    let mut mask_parties = Vec::new();
    for party in 0..2 {
        let (state, contribution) =
            MaskedBoundaryParty::prepare(&boundary_session, party, &params, &public_key)
                .expect("party retains one-time pad");
        mask_coordinator
            .accept(contribution)
            .expect("exact-session encrypted mask");
        mask_parties.push(state);
    }
    let masked = mask_coordinator
        .finish()
        .expect("exact fold plus full encrypted-mask roster");
    let decrypt_wires = threshold_parties
        .iter()
        .map(|party| {
            party
                .partial_decrypt(masked.ciphertext(), MIN_SMUDGE_BITS)
                .expect("smudged share of exact masked fold")
                .to_wire_bytes()
        })
        .collect::<Vec<_>>();
    let masked_opening = masked
        .open_framed(&decrypt_wires, &params)
        .expect("full threshold roster opens only padded fold");
    let packed_shares: [[u64; PRIVATE_BOOK_LIVE_SLOTS]; 2] = mask_parties
        .iter()
        .map(|party| {
            party
                .derive_mod_t_share(&masked_opening)
                .expect("party-local exact-fold share")
                .try_into()
                .expect("fixed nine-slot private-book carrier")
        })
        .collect::<Vec<[u64; PRIVATE_BOOK_LIVE_SLOTS]>>()
        .try_into()
        .expect("two PartyMPC ingress rows");

    // Test-only parity oracle. Neither the transport nor its public transcript
    // receives this reconstruction.
    let expected = [3, 3, 2, 0, 0, 2, 2, 3, 63];
    for slot in 0..PRIVATE_BOOK_LIVE_SLOTS {
        assert_eq!(
            packed_shares
                .iter()
                .fold(0, |sum, row| (sum + row[slot]) % params.plaintext_modulus()),
            expected[slot],
            "masked boundary parity at packed slot {slot}"
        );
    }
    (params, relation_digest, packed_shares)
}

fn public_frame_route(frame: &[u8]) -> (usize, usize, u64) {
    let sender = u32::from_be_bytes(frame[40..44].try_into().expect("sender field")) as usize;
    let recipient = u32::from_be_bytes(frame[44..48].try_into().expect("recipient field")) as usize;
    let sequence = u64::from_be_bytes(frame[48..56].try_into().expect("sequence field"));
    (sender, recipient, sequence)
}

fn drive_crossing(
    session: &PartyMpcSession,
    roster: &CrossingTransportRoster,
    party_keys: &[SigningKey; 2],
    coordinator_key: &SigningKey,
    packed_shares: [[u64; 9]; 2],
) -> (DistributedRun, Vec<Vec<u8>>) {
    let mut dealer_rng = StdRng::seed_from_u64(0xDBA2_C206);
    let triples = trusted_dealer_triples(session, &mut dealer_rng).expect("shape-only triples");
    let mut inputs = packed_shares
        .iter()
        .enumerate()
        .map(|(party, packed)| {
            prepare_private_book_crossing_input(
                session,
                party,
                packed,
                &mut StdRng::seed_from_u64(0xDBA2_C300 + party as u64),
            )
            .expect("party-local packed input")
        })
        .collect::<Vec<_>>();
    let mut triples = triples.into_iter();
    let mut parties = (0..session.n_parties())
        .map(|party| {
            CrossingPartyMachine::new(
                session.clone(),
                roster.clone(),
                party,
                party_keys[party].clone(),
                inputs.remove(0),
                triples.next().expect("one Beaver row per party"),
            )
            .expect("crossing party machine")
        })
        .collect::<Vec<_>>();
    let mut coordinator =
        CrossingCoordinatorMachine::new(session.clone(), roster.clone(), coordinator_key.clone())
            .expect("reveal-only coordinator");

    let mut authenticated_public_frames = Vec::new();
    let mut party_done = vec![false; session.n_parties()];
    let mut result = None;
    let deadline = Instant::now() + Duration::from_secs(30);
    while result.is_none() || party_done.iter().any(|done| !done) {
        assert!(Instant::now() < deadline, "crossing transport stalled");
        let mut progressed = false;

        for sender in 0..parties.len() {
            loop {
                let frame = parties[sender]
                    .try_next_frame()
                    .expect("party emits authenticated frame");
                let Some(frame) = frame else { break };
                progressed = true;
                let recipient = frame.recipient();
                let bytes = frame.into_bytes();
                if recipient == roster.coordinator() {
                    authenticated_public_frames.push(bytes.clone());
                    coordinator
                        .accept_frame(&bytes)
                        .expect("coordinator authenticates party frame");
                } else {
                    parties[recipient]
                        .accept_frame(&bytes)
                        .expect("peer authenticates and decrypts ingress");
                }
            }
        }

        loop {
            let frame = coordinator
                .try_next_frame()
                .expect("coordinator emits authenticated opening");
            let Some(frame) = frame else { break };
            progressed = true;
            let recipient = frame.recipient();
            let bytes = frame.into_bytes();
            authenticated_public_frames.push(bytes.clone());
            parties[recipient]
                .accept_frame(&bytes)
                .expect("party authenticates coordinator opening");
        }

        for (party, machine) in parties.iter_mut().enumerate() {
            if !party_done[party] {
                if machine
                    .try_result()
                    .expect("party completion report")
                    .is_some()
                {
                    party_done[party] = true;
                    progressed = true;
                }
            }
        }
        if result.is_none() {
            if let Some(run) = coordinator
                .try_result()
                .expect("coordinator crossing result")
            {
                result = Some(run);
                progressed = true;
            }
        }
        if !progressed {
            thread::yield_now();
        }
    }
    (
        result.expect("full roster reconstructs crossing"),
        authenticated_public_frames,
    )
}

#[test]
fn exact_packed_rows_drive_authenticated_crossing_and_bind_every_public_bit() {
    let party_keys = [
        SigningKey::from_bytes(&[0x31; 32]),
        SigningKey::from_bytes(&[0x32; 32]),
    ];
    let coordinator_key = SigningKey::from_bytes(&[0x33; 32]);
    let roster = CrossingTransportRoster::new(
        party_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        coordinator_key.verifying_key().to_bytes(),
    )
    .expect("strict transport roster");
    let (params, source_digest, packed_shares) = exact_private_book_boundary();
    let session = PartyMpcSession::new(
        source_digest,
        2,
        4,
        8,
        params.plaintext_modulus(),
        Duration::from_secs(5),
    )
    .expect("source-bound N4K4 crossing session");
    let (run, frames) = drive_crossing(
        &session,
        &roster,
        &party_keys,
        &coordinator_key,
        packed_shares,
    );
    assert_eq!(
        run.crossing,
        Crossing {
            p_star: Some(1),
            v_star: 2,
        }
    );
    assert!(run.transcript.is_reveal_only(&session));
    verify_public_crossing_transcript(&session, &roster, &frames, &run.crossing, &run.transcript)
        .expect("authenticated frames reconstruct the exact live transcript");

    let mut invented_crossing = run.crossing.clone();
    invented_crossing.p_star = Some(2);
    assert!(verify_public_crossing_transcript(
        &session,
        &roster,
        &frames,
        &invented_crossing,
        &run.transcript,
    )
    .is_err());
    let mut invented_transcript = run.transcript.clone();
    invented_transcript.masked[0].d ^= 1;
    assert!(verify_public_crossing_transcript(
        &session,
        &roster,
        &frames,
        &run.crossing,
        &invented_transcript,
    )
    .is_err());
    let mut corrupted_signature = frames.clone();
    let signature_byte = corrupted_signature[0].len() - 33;
    corrupted_signature[0][signature_byte] ^= 1;
    assert!(
        verify_public_crossing_transcript(
            &session,
            &roster,
            &corrupted_signature,
            &run.crossing,
            &run.transcript,
        )
        .is_err(),
        "a modified party signature/checksum cannot authenticate the public transcript"
    );
    let mut reordered_one_sender = frames.clone();
    let first = reordered_one_sender
        .iter()
        .position(|frame| public_frame_route(frame) == (0, roster.coordinator(), 0))
        .expect("party zero gate zero frame");
    let second = reordered_one_sender
        .iter()
        .position(|frame| public_frame_route(frame) == (0, roster.coordinator(), 1))
        .expect("party zero gate one frame");
    reordered_one_sender.swap(first, second);
    assert!(
        verify_public_crossing_transcript(
            &session,
            &roster,
            &reordered_one_sender,
            &run.crossing,
            &run.transcript,
        )
        .is_err(),
        "one sender's signed gate sequence cannot be reordered"
    );
    assert!(
        verify_public_crossing_transcript(
            &session,
            &roster,
            &frames[..frames.len() - 1],
            &run.crossing,
            &run.transcript,
        )
        .is_err(),
        "one missing signed share must fail closed"
    );

    let wrong_session = PartyMpcSession::new(
        [0x42; 32],
        2,
        4,
        8,
        params.plaintext_modulus(),
        Duration::from_secs(5),
    )
    .unwrap();
    assert!(matches!(
        verify_public_crossing_transcript(
            &wrong_session,
            &roster,
            &frames,
            &run.crossing,
            &run.transcript,
        ),
        Err(CrossingTransportError::SessionMismatch)
    ));
}

#[test]
fn packed_private_input_refuses_wrong_shape_or_noncanonical_share() {
    let session =
        PartyMpcSession::new([0x51; 32], 2, 4, 8, 65_537, Duration::from_secs(1)).unwrap();
    let mut rng = StdRng::seed_from_u64(7);
    assert!(prepare_private_book_crossing_input(&session, 0, &[0; 8], &mut rng).is_err());
    let mut noncanonical = [0u64; 9];
    noncanonical[8] = session.plaintext_modulus();
    assert!(prepare_private_book_crossing_input(&session, 0, &noncanonical, &mut rng).is_err());
    let equality =
        PartyMpcSession::equality([0x51; 32], 2, 8, 65_537, Duration::from_secs(1)).unwrap();
    assert!(prepare_private_book_crossing_input(&equality, 0, &[0; 9], &mut rng).is_err());

    let context = [0x61; 32];
    let trusted_root = [0x62; 32];
    let first = fresh_crossing_preprocessing_seed(
        &session,
        context,
        &trusted_root,
        &mut StdRng::seed_from_u64(8),
    )
    .expect("crossing preprocessing is invocation-separated");
    let second = fresh_crossing_preprocessing_seed(
        &session,
        context,
        &trusted_root,
        &mut StdRng::seed_from_u64(9),
    )
    .expect("fresh invocation");
    assert_ne!(first, second);
    assert!(
        fresh_crossing_preprocessing_seed(
            &equality,
            context,
            &trusted_root,
            &mut StdRng::seed_from_u64(8),
        )
        .is_err(),
        "crossing preprocessing cannot be replayed under equality"
    );
}
