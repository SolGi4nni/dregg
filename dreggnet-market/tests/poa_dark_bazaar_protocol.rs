//! PoA receipt-bound Dark Bazaar protocol exercise.
//!
//! Four issuer-authenticated Path of Angels expedition receipts name the exact
//! Ed25519 keys which sign four canonical private-book BFV rows.  A candidate
//! Bazaar session transcript binds the PoA federation/content epoch and the
//! ordered signed-receipt digests before any order is accepted.  Those exact
//! rows then drive the fixed N=4,K=4 HidingFRI proof, the transferable
//! same-opening Bulletproof, a masked threshold opening into local shares, and
//! an actual authenticated PartyMPC crossing.  A 2-of-2 committee signs the
//! resulting complete clearing claim and replay protection consumes it once.
//!
//! Honest boundary: the receipt envelope is authenticated but not yet a Lean
//! `JudgedRun` capability.  The source verifier sees every order and encryption
//! seed while checking exact reencryption, order side remains public on the
//! ingress wire, the local PartyMPC uses trusted-dealer preprocessing, and its
//! transport/full-claim quorum are classical compatibility mode.  The overall
//! privacy grade is therefore operator-visible HidingFRI, not house-blind or
//! independent-operator threshold.  Most importantly, successful clearing
//! still cannot mint/list/settle PoA salvage: `PoaSalvageMinter` must finish by
//! refusing `MissingTransitionVerifier` and leave the asset vault empty.
//!
//! This is a minutes-class release-only test because it produces the fixed
//! n=4096 Bulletproof.  Route the whole binary through nextest's heavy profile.

#![cfg(feature = "private-attested-clearing")]

use std::thread;
use std::time::{Duration, Instant};

use dregg_circuit_prove::dark_bazaar_private::{self, PrivateBookWitness, PrivateOrder};
use dreggnet_market::poa_expedition::{
    PoaContributionBounds, PoaContributionClaim, PoaExpeditionClaim, PoaExpeditionError,
    PoaExpeditionPolicy, PoaExpeditionReceipt, PoaSalvageMinter,
};
use dreggnet_market::private_attested_clearing::{
    PrivateAttestedClearingPolicy, private_order_root_commitment,
};
use dreggnet_market::private_bfv_attested_clearing::{
    PrivateBfvAttestedClearingVerifier, PrivateBfvAuthorityError, PrivateBfvQuorumSecurity,
};
use dungeon_on_dregg::loot::LootVault;
use ed25519_dalek::SigningKey;
use fhegg_fhe::attestation::{
    AttestationError, AttestedClearingReceipt, AuthenticatedQuorumVerifier, BfvPublicIdentity,
    ComputationIntegrityEvidence, ComputationIntegrityResidual, ExpectedClearingContext,
    InMemoryReplayGuard, InputDigest, QuorumVerifierError,
};
use fhegg_fhe::boundary::{
    BoundaryError, MaskedBoundaryParty, MaskedDecryptCoordinator, MaskedDecryptSession,
};
use fhegg_fhe::mpc::Crossing;
use fhegg_fhe::mpc_party::transport::{
    CrossingCoordinatorMachine, CrossingPartyMachine, CrossingTransportError,
    CrossingTransportRoster, prepare_private_book_crossing_input,
    verify_public_crossing_transcript,
};
use fhegg_fhe::mpc_party::{DistributedRun, PartyMpcSession, trusted_dealer_triples};
use fhegg_fhe::order_ingress::{
    AuthenticatedOrderBook, OrderIngressError, OrderIngressSession, SignedOrderSubmission,
};
use fhegg_fhe::private_book_bfv_zk::prove_private_book_bfv_zk;
use fhegg_fhe::private_book_relation::{
    FoldedPrivateBookCiphertext, PRIVATE_BOOK_LIVE_SLOTS, PRIVATE_BOOK_PUBLIC_BOUND,
    PrivateBookEncryptionOpening, encrypt_private_book, fold_private_book_ciphertexts,
};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, MIN_SMUDGE_BITS,
    ThresholdParty,
};
use rand::{SeedableRng, rngs::StdRng};

const BAZAAR_DOMAIN: &[u8] = b"pathofangels.network/bazaar-ingress/v1\0";
const WRONG_DOMAIN: &[u8] = b"pathofangels.network/bazaar-ingress/v2\0";
const VALUE_BITS: usize = 8;

fn collective_key(params: &BfvParams) -> (KeygenSession, Vec<ThresholdParty>, CollectivePublicKey) {
    let keygen = KeygenSession::from_seed(2, [0x21; 32]).expect("PoA Bazaar key session");
    let mut coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
    let mut parties = Vec::with_capacity(keygen.n_parties());
    for party in 0..keygen.n_parties() {
        let (state, contribution) =
            ThresholdParty::join(&keygen, party, params).expect("party-local key share");
        coordinator
            .accept(contribution)
            .expect("ordered threshold contribution");
        parties.push(state);
    }
    (
        keygen,
        parties,
        coordinator.finish().expect("collective public key"),
    )
}

fn poa_receipt(trader: usize, player_key: [u8; 32], issuer: &SigningKey) -> PoaExpeditionReceipt {
    let mut judge_input_digest = [0x50; 32];
    judge_input_digest[0] = 0x50 + trader as u8;
    let mut judge_output_digest = [0x58; 32];
    judge_output_digest[0] = 0x58 + trader as u8;
    let mut post_state = [0x60; 32];
    post_state[0] = 0x60 + trader as u8;
    PoaExpeditionReceipt::issue(
        PoaExpeditionClaim::new(
            [0x11; 32],
            [0x12; 32],
            [0x13; 32],
            [0x14; 32],
            judge_input_digest,
            judge_output_digest,
            [0x15; 32],
            post_state,
            format!("poa-expedition:trader-{trader}"),
            player_key,
            trader as u64 + 1,
            447 + trader as u16,
            trader as u8,
            PoaContributionClaim {
                intel: trader as u32 + 1,
                supplies: 1,
                cohesion: 2,
                influence: 0,
                score: 17 + trader as u32,
                relics: vec![447_001 + trader as u32],
            },
            [0x70 + trader as u8; 32],
        ),
        issuer,
    )
}

/// Candidate transcript for the future Lean-emitted Bazaar ingress adapter.
/// Keeping this helper test-local prevents a Rust test from becoming protocol
/// authority before the typed Lean/export boundary is selected.
fn receipt_bound_bazaar_nonce(domain: &[u8], receipts: &[PoaExpeditionReceipt; 4]) -> [u8; 32] {
    let first = &receipts[0].claim;
    let mut hasher = blake3::Hasher::new();
    hasher.update(domain);
    hasher.update(&first.federation);
    hasher.update(&first.session);
    hasher.update(&first.mission);
    hasher.update(&first.artifact_digest);
    hasher.update(&(receipts.len() as u64).to_be_bytes());
    for receipt in receipts {
        hasher.update(&receipt.claim.player_key);
        hasher.update(&receipt.claim.counter.to_be_bytes());
        hasher.update(&receipt.digest());
    }
    *hasher.finalize().as_bytes()
}

fn proof_session(nonce: [u8; 32]) -> u32 {
    const BABY_BEAR_ORDER: u32 = 0x7800_0001;
    let reduced =
        u32::from_be_bytes(nonce[..4].try_into().expect("four-byte prefix")) % BABY_BEAR_ORDER;
    if reduced == 0 { 1 } else { reduced }
}

fn derive_packed_private_book_shares(
    nonce: [u8; 32],
    folded: &FoldedPrivateBookCiphertext,
    params: &BfvParams,
    public_key: &CollectivePublicKey,
    threshold_parties: &[ThresholdParty],
) -> [[u64; PRIVATE_BOOK_LIVE_SLOTS]; 2] {
    let session = MaskedDecryptSession::from_public(
        nonce,
        threshold_parties.len(),
        PRIVATE_BOOK_LIVE_SLOTS,
        folded.ciphertext().clone(),
        params,
    )
    .expect("receipt-bound packed fold names the masked boundary");
    let mut coordinator = MaskedDecryptCoordinator::new(session.clone(), params.clone());
    let mut mask_parties = Vec::with_capacity(threshold_parties.len());
    for party in 0..threshold_parties.len() {
        let (state, contribution) =
            MaskedBoundaryParty::prepare(&session, party, params, public_key)
                .expect("party retains its exact-fold one-time pad");
        coordinator
            .accept(contribution)
            .expect("unique exact-session encrypted mask");
        mask_parties.push(state);
    }
    let masked = coordinator
        .finish()
        .expect("exact fold plus full encrypted-mask roster");
    let decrypt_wires = threshold_parties
        .iter()
        .map(|party| {
            party
                .partial_decrypt(masked.ciphertext(), MIN_SMUDGE_BITS)
                .expect("smudged share of the exact masked fold")
                .to_wire_bytes()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        masked.open_framed(&decrypt_wires[..1], params),
        Err(BoundaryError::QuorumTooSmall { have: 1, need: 2 }),
        "one BFV share cannot reveal even the padded packed book",
    );
    let mut wrong_target = folded.ciphertext().clone();
    wrong_target.polys[0].rows[0][0] =
        (wrong_target.polys[0].rows[0][0] + 1) % wrong_target.moduli[0];
    let wrong_share = threshold_parties[0]
        .partial_decrypt(&wrong_target, MIN_SMUDGE_BITS)
        .expect("well-formed share for a different ciphertext")
        .to_wire_bytes();
    assert_eq!(
        masked.open_framed(&[wrong_share, decrypt_wires[1].clone()], params),
        Err(BoundaryError::SessionMismatch),
        "a valid share for another ciphertext cannot join this opening",
    );
    let opening = masked
        .open_framed(&decrypt_wires, params)
        .expect("the complete roster opens only the padded fold");
    mask_parties
        .iter()
        .map(|party| {
            party
                .derive_mod_t_share(&opening)
                .expect("party-local exact-fold mod-t share")
                .try_into()
                .expect("fixed nine-slot packed book")
        })
        .collect::<Vec<[u64; PRIVATE_BOOK_LIVE_SLOTS]>>()
        .try_into()
        .expect("fixed two-party crossing roster")
}

fn drive_crossing(
    session: &PartyMpcSession,
    roster: &CrossingTransportRoster,
    party_keys: &[SigningKey; 2],
    coordinator_key: &SigningKey,
    packed_shares: [[u64; PRIVATE_BOOK_LIVE_SLOTS]; 2],
) -> (DistributedRun, Vec<Vec<u8>>) {
    let triples = trusted_dealer_triples(session, &mut StdRng::seed_from_u64(0xDBA2_C206))
        .expect("test-only trusted-dealer preprocessing");
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
            .expect("authenticated crossing party")
        })
        .collect::<Vec<_>>();
    let mut coordinator =
        CrossingCoordinatorMachine::new(session.clone(), roster.clone(), coordinator_key.clone())
            .expect("reveal-only authenticated coordinator");

    let mut public_frames = Vec::new();
    let mut party_done = vec![false; session.n_parties()];
    let mut result = None;
    let deadline = Instant::now() + Duration::from_secs(30);
    while result.is_none() || party_done.iter().any(|done| !done) {
        assert!(Instant::now() < deadline, "PoA Bazaar crossing stalled");
        let mut progressed = false;
        for sender in 0..parties.len() {
            loop {
                let Some(frame) = parties[sender]
                    .try_next_frame()
                    .expect("party emits authenticated frame")
                else {
                    break;
                };
                progressed = true;
                let recipient = frame.recipient();
                let bytes = frame.into_bytes();
                if recipient == roster.coordinator() {
                    public_frames.push(bytes.clone());
                    coordinator
                        .accept_frame(&bytes)
                        .expect("coordinator authenticates party frame");
                } else {
                    parties[recipient]
                        .accept_frame(&bytes)
                        .expect("peer authenticates encrypted ingress");
                }
            }
        }
        loop {
            let Some(frame) = coordinator
                .try_next_frame()
                .expect("coordinator emits authenticated opening")
            else {
                break;
            };
            progressed = true;
            let recipient = frame.recipient();
            let bytes = frame.into_bytes();
            public_frames.push(bytes.clone());
            parties[recipient]
                .accept_frame(&bytes)
                .expect("party authenticates coordinator opening");
        }
        for (party, machine) in parties.iter_mut().enumerate() {
            if !party_done[party]
                && machine
                    .try_result()
                    .expect("party completion report")
                    .is_some()
            {
                party_done[party] = true;
                progressed = true;
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
        result.expect("full roster reconstructs the crossing"),
        public_frames,
    )
}

#[test]
fn poa_receipt_keys_seal_one_private_book_then_stop_before_salvage_settlement() {
    let issuer = SigningKey::from_bytes(&[0x10; 32]);
    let trader_keys = [
        SigningKey::from_bytes(&[0x31; 32]),
        SigningKey::from_bytes(&[0x32; 32]),
        SigningKey::from_bytes(&[0x33; 32]),
        SigningKey::from_bytes(&[0x34; 32]),
    ];
    let receipts: [PoaExpeditionReceipt; 4] = trader_keys
        .iter()
        .enumerate()
        .map(|(trader, key)| poa_receipt(trader, key.verifying_key().to_bytes(), &issuer))
        .collect::<Vec<_>>()
        .try_into()
        .expect("fixed four-receipt roster");
    let policy = PoaExpeditionPolicy::new(
        [0x11; 32],
        [0x12; 32],
        [0x13; 32],
        [0x14; 32],
        PoaContributionBounds {
            intel: 8,
            supplies: 8,
            cohesion: 8,
            influence: 8,
            score: 100,
        },
        issuer.verifying_key(),
    );
    for (trader, receipt) in receipts.iter().enumerate() {
        policy.verify(receipt).expect("authenticated PoA envelope");
        assert_eq!(
            receipt.claim.player_key,
            trader_keys[trader].verifying_key().to_bytes(),
            "receipt roster slot is the order-signing identity",
        );
    }

    let bazaar_nonce = receipt_bound_bazaar_nonce(BAZAAR_DOMAIN, &receipts);
    assert_ne!(
        bazaar_nonce,
        receipt_bound_bazaar_nonce(WRONG_DOMAIN, &receipts),
        "the explicit Bazaar protocol domain changes the session",
    );
    let mut substituted_receipts = receipts.clone();
    let mut substituted_claim = substituted_receipts[0].claim.clone();
    substituted_claim.counter += 4;
    substituted_claim.judge_output_digest[0] ^= 1;
    substituted_receipts[0] = PoaExpeditionReceipt::issue(substituted_claim, &issuer);
    policy
        .verify(&substituted_receipts[0])
        .expect("substitution is independently valid under the same PoA policy");
    let substituted_nonce = receipt_bound_bazaar_nonce(BAZAAR_DOMAIN, &substituted_receipts);
    assert_ne!(
        bazaar_nonce, substituted_nonce,
        "another valid receipt/counter must name another Bazaar session",
    );
    let mut permuted_receipts = receipts.clone();
    permuted_receipts.swap(0, 1);
    assert_ne!(
        bazaar_nonce,
        receipt_bound_bazaar_nonce(BAZAAR_DOMAIN, &permuted_receipts),
        "trader roster order is part of the session identity",
    );

    // These exact private orders produce D=[3,3,2,0], S=[0,2,2,3].
    // Buckets 1 and 2 tie at volume two, so the Lean-authored rule chooses 1.
    let private_orders = [
        PrivateOrder::bid(2, 2),
        PrivateOrder::bid(1, 1),
        PrivateOrder::ask(2, 1),
        PrivateOrder::ask(1, 3),
    ];
    let witness = PrivateBookWitness::try_from_orders_with_blinding(
        &private_orders,
        core::array::from_fn(|lane| 19_000 + lane as u32),
    )
    .expect("fixed private book");
    let private_seeds = [[0x51; 32], [0x52; 32], [0x53; 32], [0x54; 32]];
    let opening = PrivateBookEncryptionOpening::from_seeds(private_seeds);
    let params = BfvParams::fold_set();
    let (keygen, threshold_parties, public_key) = collective_key(&params);
    let bfv = BfvPublicIdentity::from_public(&params, &keygen, &public_key);
    let ciphertexts = encrypt_private_book(&witness, &opening, &params, &public_key)
        .expect("canonical private-book BFV rows");

    let ingress = OrderIngressSession::new(
        bazaar_nonce,
        dark_bazaar_private::PRICE_COUNT,
        &params,
        &public_key,
    )
    .expect("receipt-bound order ingress");
    let wrong_domain_ingress = OrderIngressSession::new(
        receipt_bound_bazaar_nonce(WRONG_DOMAIN, &receipts),
        dark_bazaar_private::PRICE_COUNT,
        &params,
        &public_key,
    )
    .expect("shape-valid wrong-domain ingress");
    let substituted_ingress = OrderIngressSession::new(
        substituted_nonce,
        dark_bazaar_private::PRICE_COUNT,
        &params,
        &public_key,
    )
    .expect("shape-valid substituted-receipt ingress");
    let mut source_book = AuthenticatedOrderBook::new(
        ingress.clone(),
        receipts
            .iter()
            .map(|receipt| receipt.claim.player_key)
            .collect(),
    )
    .expect("receipt-key trader roster");

    let mut public_wires = Vec::new();
    for trader in 0..private_orders.len() {
        let submission = SignedOrderSubmission::encrypt_and_sign_private_book_row(
            &ingress,
            trader,
            0,
            private_orders[trader],
            private_seeds[trader],
            &params,
            &public_key,
            &trader_keys[trader],
        )
        .expect("receipt-key holder signs its exact canonical row");
        assert_eq!(
            InputDigest::ciphertext(submission.ciphertext()),
            InputDigest::ciphertext(&ciphertexts.rows()[trader]),
            "signed source row byte-identifies its proof row",
        );
        let wire = submission.to_wire_bytes();
        for seed in private_seeds {
            assert!(
                !wire.windows(seed.len()).any(|window| window == seed),
                "private encryption seed leaked into the public order wire",
            );
        }
        assert_eq!(
            u64::from_be_bytes(wire[57..65].try_into().expect("public-bound field")),
            PRIVATE_BOOK_PUBLIC_BOUND,
            "private-book ingress publishes one fixed aggregate bound",
        );
        assert_eq!(
            SignedOrderSubmission::from_wire_bytes(&wire, &wrong_domain_ingress, &params)
                .unwrap_err(),
            OrderIngressError::SessionMismatch,
            "the same signed row is not portable to another protocol domain",
        );
        assert_eq!(
            SignedOrderSubmission::from_wire_bytes(&wire, &substituted_ingress, &params)
                .unwrap_err(),
            OrderIngressError::SessionMismatch,
            "one substituted valid PoA receipt invalidates every old order wire",
        );

        let mut tampered_wire = wire.clone();
        *tampered_wire.last_mut().expect("signature byte") ^= 1;
        let tampered = SignedOrderSubmission::from_wire_bytes(&tampered_wire, &ingress, &params)
            .expect("signature corruption preserves wire shape");
        assert_eq!(
            source_book
                .accept_private_book_opened(
                    tampered,
                    private_orders[trader],
                    private_seeds[trader],
                    &params,
                    &public_key,
                )
                .unwrap_err(),
            OrderIngressError::InvalidSignature { trader },
        );

        let mut wrong_seed = private_seeds[trader];
        wrong_seed[0] ^= 1;
        assert_eq!(
            source_book
                .accept_private_book_opened(
                    submission.clone(),
                    private_orders[trader],
                    wrong_seed,
                    &params,
                    &public_key,
                )
                .unwrap_err(),
            OrderIngressError::EncryptionOpeningMismatch { trader },
        );
        source_book
            .accept_private_book_opened(
                submission.clone(),
                private_orders[trader],
                private_seeds[trader],
                &params,
                &public_key,
            )
            .expect("operator-visible exact canonical-row reencryption check");
        assert_eq!(
            source_book
                .accept_private_book_opened(
                    submission,
                    private_orders[trader],
                    private_seeds[trader],
                    &params,
                    &public_key,
                )
                .unwrap_err(),
            OrderIngressError::DuplicateSource {
                trader,
                sequence: 0,
            },
            "one receipt-key source sequence is consumable once",
        );
        public_wires.push(wire);
    }
    let source_inputs = source_book
        .finish_private_book_source_inputs()
        .expect("canonical ordered message/ciphertext digest pairs");
    assert_eq!(source_inputs.len(), private_orders.len() * 2);

    let (clearing_proof, statement) =
        dark_bazaar_private::prove_zk(proof_session(bazaar_nonce), &witness)
            .expect("HidingFRI private clearing proof");
    assert_eq!((statement.p_star, statement.v_star), (1, 2));
    let bfv_proof = prove_private_book_bfv_zk(
        statement,
        &witness,
        &ciphertexts,
        &opening,
        &params,
        &public_key,
    )
    .expect("transferable same-opening Bulletproof");
    let folded = fold_private_book_ciphertexts(&ciphertexts, &params)
        .expect("homomorphic fold of the exact four proof rows");
    let packed_shares = derive_packed_private_book_shares(
        bazaar_nonce,
        &folded,
        &params,
        &public_key,
        &threshold_parties,
    );

    let committee_keys = [
        SigningKey::from_bytes(&[0x81; 32]),
        SigningKey::from_bytes(&[0x82; 32]),
    ];
    let coordinator_key = SigningKey::from_bytes(&[0x83; 32]);
    let transport_roster = CrossingTransportRoster::new(
        committee_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        coordinator_key.verifying_key().to_bytes(),
    )
    .expect("classical compatibility transport roster");
    let mpc_session = PartyMpcSession::new(
        bazaar_nonce,
        2,
        dark_bazaar_private::PRICE_COUNT,
        VALUE_BITS,
        params.plaintext_modulus(),
        Duration::from_secs(5),
    )
    .expect("receipt-bound N4K4 PartyMPC session");
    let (distributed, public_frames) = drive_crossing(
        &mpc_session,
        &transport_roster,
        &committee_keys,
        &coordinator_key,
        packed_shares,
    );
    assert_eq!(
        distributed.crossing,
        Crossing {
            p_star: Some(statement.p_star as usize),
            v_star: statement.v_star as u64,
        },
        "actual PartyMPC output equals the HidingFRI-proved output",
    );
    assert!(distributed.transcript.is_reveal_only(&mpc_session));
    verify_public_crossing_transcript(
        &mpc_session,
        &transport_roster,
        &public_frames,
        &distributed.crossing,
        &distributed.transcript,
    )
    .expect("authenticated public frames reconstruct the exact crossing");
    let wrong_mpc_session = PartyMpcSession::new(
        substituted_nonce,
        2,
        dark_bazaar_private::PRICE_COUNT,
        VALUE_BITS,
        params.plaintext_modulus(),
        Duration::from_secs(5),
    )
    .expect("shape-valid substituted-receipt MPC session");
    assert!(matches!(
        verify_public_crossing_transcript(
            &wrong_mpc_session,
            &transport_roster,
            &public_frames,
            &distributed.crossing,
            &distributed.transcript,
        ),
        Err(CrossingTransportError::SessionMismatch)
    ));
    let mut tampered_frames = public_frames.clone();
    let tampered_byte = tampered_frames[0].len() - 33;
    tampered_frames[0][tampered_byte] ^= 1;
    assert!(
        verify_public_crossing_transcript(
            &mpc_session,
            &transport_roster,
            &tampered_frames,
            &distributed.crossing,
            &distributed.transcript,
        )
        .is_err(),
        "a modified authenticated frame cannot authorize a clearing",
    );

    let quorum = AuthenticatedQuorumVerifier::new(
        committee_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .expect("strict 2-of-2 clearing committee");
    let mut ordered_inputs = ciphertexts
        .rows()
        .iter()
        .map(InputDigest::ciphertext)
        .collect::<Vec<_>>();
    ordered_inputs.push(InputDigest::commitment(private_order_root_commitment(
        statement.order_root,
    )));
    ordered_inputs.extend(source_inputs.clone());
    ordered_inputs.push(InputDigest::ciphertext(folded.ciphertext()));
    let expected = ExpectedClearingContext {
        session: &mpc_session,
        ordered_roster: quorum.ordered_roster(),
        bfv: &bfv,
        ordered_inputs: &ordered_inputs,
        transcript: &distributed.transcript,
        crossing: &distributed.crossing,
    };
    let mut clearing_receipt = AttestedClearingReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("canonical full clearing claim");
    let verifier = PrivateBfvAttestedClearingVerifier::new_source_bound(
        quorum.clone(),
        PrivateAttestedClearingPolicy::new(VALUE_BITS as u32, bfv.clone())
            .expect("fixed private-clearing policy"),
        bazaar_nonce,
        statement,
        params.clone(),
        public_key.clone(),
        ciphertexts.clone(),
        source_inputs,
    )
    .expect("receipt-specific source-bound verifier");
    let signatures = committee_keys
        .iter()
        .enumerate()
        .map(|(party, key)| {
            quorum
                .sign_claim(&clearing_receipt.claim_digest(), party, key)
                .expect("committee signs the complete claim digest")
        })
        .collect::<Vec<_>>();
    assert!(matches!(
        quorum.assemble_evidence(&clearing_receipt.claim_digest(), &signatures[..1]),
        Err(QuorumVerifierError::InsufficientSignatures { have: 1, need: 2 })
    ));
    clearing_receipt.computation_integrity = verifier
        .assemble_evidence(
            &clearing_receipt.claim,
            &signatures,
            &clearing_proof,
            &bfv_proof,
        )
        .expect("quorum + HidingFRI + same-opening evidence compose");
    let authority = verifier
        .verify_authority(&clearing_receipt, &expected)
        .expect("complete private clearing authority");
    assert_eq!(
        authority.quorum_security(),
        PrivateBfvQuorumSecurity::ClassicalCompatibility
    );
    assert_eq!((authority.price(), authority.volume()), (1, 2));
    assert_eq!(authority.claim_session_nonce(), bazaar_nonce);

    let wrong_expected = ExpectedClearingContext {
        session: &wrong_mpc_session,
        ordered_roster: expected.ordered_roster,
        bfv: expected.bfv,
        ordered_inputs: expected.ordered_inputs,
        transcript: expected.transcript,
        crossing: expected.crossing,
    };
    assert!(matches!(
        verifier.verify_authority(&clearing_receipt, &wrong_expected),
        Err(PrivateBfvAuthorityError::Binding(_))
    ));
    let mut corrupted_receipt = clearing_receipt.clone();
    let ComputationIntegrityEvidence::External { evidence, .. } =
        &mut corrupted_receipt.computation_integrity
    else {
        unreachable!("composite evidence is external")
    };
    *evidence.last_mut().expect("composite checksum byte") ^= 1;
    assert_eq!(
        verifier.verify_authority(&corrupted_receipt, &expected),
        Err(PrivateBfvAuthorityError::InvalidCompositeEvidence)
    );

    let clearing_wire = clearing_receipt.canonical_envelope_bytes();
    for seed in private_seeds {
        assert!(
            !clearing_wire
                .windows(seed.len())
                .any(|window| window == seed),
            "private opening leaked into the public clearing receipt",
        );
    }
    let mut replay_guard = InMemoryReplayGuard::default();
    clearing_receipt
        .verify_full(&expected, &verifier, &mut replay_guard)
        .expect("complete receipt is consumable once");
    assert_eq!(
        clearing_receipt.verify_full(&expected, &verifier, &mut replay_guard),
        Err(AttestationError::ReplayDetected),
        "the exact receipt-bound clearing cannot be replayed",
    );

    // Clearing is real; PoA salvage authority is not.  Do not manufacture a
    // generic asset, listing, or settlement to make the test look complete.
    let mut vault = LootVault::new();
    let mut minter = PoaSalvageMinter::new(policy);
    assert_eq!(
        minter.mint(&mut vault, &receipts[0]).unwrap_err(),
        PoaExpeditionError::MissingTransitionVerifier,
        "private clearing cannot launder an issuer-only receipt into salvage",
    );
    assert_eq!(
        vault.item_count(),
        0,
        "without the Lean judged-transition adapter there is nothing to list or settle",
    );
}
