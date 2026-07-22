//! Descent -> authenticated no-single-viewer fhEgg -> real Dark Bazaar settle.
//!
//! The three economic rows are encrypted and signed at trader ingress, folded
//! under a four-custodian collective BFV key, opened by any three custodians only
//! behind one-time masks and VSS-transcript-bound signed share envelopes, and
//! crossed by the three live MPC parties. Digest-only custody audit commitments
//! join the exact source/transcript/result in a unanimous live-party receipt
//! that gates the existing executor settlement, after which the original
//! provenance-carrying Descent asset crosses atomically for $DREGG.
//!
//! Honest boundary: the test instantiates today's bivariate-VSS 3-of-4 setup and
//! trusted Beaver triples. Custodian 3 is absent after DKG. Every committed VSS
//! row opening and pairwise cross-evaluation is checked before party state
//! exists; public `-a*s+e` coefficient images force those hidden constants to
//! the actual fhe.rs RLWE public-key contributions, and that exact transcript is
//! carried through the signed openings. The remaining lattice seam is explicit:
//! no ZK proof yet establishes the hidden ternary/CBD ranges, nor links each
//! public decrypt share to `c1*s_i +` in-range smudge. The computation signatures
//! authenticate the outer claim, not malicious-MPC execution. The live sealed
//! board no longer merely co-endorses ciphertexts: a configured ingress
//! verifier reproduces each exact BFV encryption from the operator-visible
//! order/randomness opening, signs a replayable certificate, and the real
//! WriteOnce seal commits that certificate's source digest. Every selected
//! custodian now proves its exact committed `c1*s_i + smudge` relation and the
//! in-range smudge/quotient witnesses in zero knowledge. The remaining lattice
//! seam is setup shortness: the hidden DKG ternary/CBD coefficients are bound
//! algebraically but do not yet carry their own range/sampler-image proof.

#![cfg(feature = "fhegg-settlement")]

use std::thread;
use std::time::Duration;

use dreggnet_market::fhegg_settlement::FheggSettlementError;
use dreggnet_market::{DarkBazaarOffering, DarkBazaarSession, TURN_LIST};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};
use dreggnet_trade::{AssetId, LegSpec, TradeWorld};
use dungeon_on_dregg::loot::{LootVault, roll_drop};
use ed25519_dalek::SigningKey;
use fhegg_fhe::additive::CollectiveOrderFoldEngine;
use fhegg_fhe::attestation::{
    AttestationError, AttestedClearingReceipt, AuthenticatedQuorumVerifier, BfvPublicIdentity,
    ComputationIntegrityEvidence, ComputationIntegrityResidual, ExpectedClearingContext,
    InMemoryReplayGuard, InputDigest,
};
use fhegg_fhe::boundary::{
    BoundaryError, MaskedBoundaryParty, MaskedDecryptCoordinator, MaskedDecryptSession,
    MaskedOpening,
};
use fhegg_fhe::mpc::Crossing;
use fhegg_fhe::mpc_party::{
    PartyArithmeticInput, PartyMpcSession, local_channels, run_party, trusted_dealer_triples,
};
use fhegg_fhe::order_ingress::{
    AuthenticatedOrderBook, OrderIngressSession, SignedOrderSubmission,
};
use fhegg_fhe::threshold::quorum::{
    AuthenticatedOpeningAudit, AuthenticatedQuorumCombiner, AuthenticatedQuorumRoster,
    DealerVssCommitment, QuorumError, QuorumKeygenSession, QuorumOpeningSession, QuorumParty,
    VerifiedDkgTranscript, deal, finish_verified_keygen, partial_decrypt_quorum_parallel,
};
use fhegg_fhe::threshold::{BfvParams, CollectivePublicKey, MIN_SMUDGE_BITS};
use fhegg_fhe::{Order, Side};
use procgen_dregg::CommittedSeed;
use rand::{SeedableRng, rngs::StdRng};
use starbridge_sealed_auction::Phase;

const KEY_N: usize = 4;
const OPEN_T: usize = 3;
const LIVE_N: usize = 3;
const K: usize = 4;
const VALUE_BITS: usize = 16;
const MARKET_SEED: u64 = 0xF4_E6_6D;
const SELLER: &str = "descent-player:alice";
const LOW_BIDDER: &str = "bazaar-bidder:bob";
const WINNER: &str = "bazaar-bidder:carol";

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

fn land(
    offering: &DarkBazaarOffering,
    session: &mut DarkBazaarSession,
    turn: &str,
    arg: i64,
    who: &str,
) {
    let outcome = offering.advance(session, Action::new(turn, turn, arg, true), actor(who));
    assert!(
        matches!(outcome, Outcome::Landed { .. }),
        "{turn} refused: {outcome:?}"
    );
}

fn listed_market(offering: &DarkBazaarOffering) -> DarkBazaarSession {
    let mut session = offering
        .open(SessionConfig::with_seed(MARKET_SEED))
        .expect("Dark Bazaar opens");
    land(offering, &mut session, TURN_LIST, 3, SELLER);
    session
}

fn assert_unmutated(session: &DarkBazaarSession, receipts_before: usize) {
    assert_eq!(session.market().receipts_len(), receipts_before);
    assert_eq!(session.market().phase(), Some(Phase::Commit));
    assert_eq!(session.market().onledger_phase(), Some(0));
    assert!(!session.is_settled());
    assert!(session.clearing().is_none());
}

fn collective_keygen(
    params: &BfvParams,
) -> (
    QuorumKeygenSession,
    VerifiedDkgTranscript,
    Vec<QuorumParty>,
    CollectivePublicKey,
) {
    let keygen = QuorumKeygenSession::from_seed(KEY_N, OPEN_T, [0x31; 32])
        .expect("fixed 3-of-4 public DKG session");
    let verified_dealers = (0..KEY_N)
        .map(|dealer| {
            let bundle = deal(&keygen, dealer, params).expect("bivariate-VSS DKG dealer");
            let public_wire = bundle.vss_commitment().to_wire_bytes();
            let parsed = DealerVssCommitment::from_wire_bytes(&public_wire, params)
                .expect("strict public VSS commitment transport");
            assert_eq!(&parsed, bundle.vss_commitment());
            bundle
                .verify(params)
                .expect("all committed row openings and cross-evaluations agree")
        })
        .collect();
    let (collective, transcript, assemblies) =
        finish_verified_keygen(&keygen, verified_dealers, params)
            .expect("complete verified public DKG")
            .into_parts();
    let parties = assemblies
        .into_iter()
        .enumerate()
        .map(|(party, assembly)| {
            QuorumParty::assemble_verified(&keygen, party, assembly, &transcript, params)
                .expect("recipient assembles only transcript-admitted dealer evaluations")
        })
        .collect();
    (keygen, transcript, parties, collective)
}

fn quorum_masked_curve(
    nonce: [u8; 32],
    target: fhegg_fhe::bfv_lean::LeanCiphertext,
    params: &BfvParams,
    keygen: &QuorumKeygenSession,
    dkg_transcript: &VerifiedDkgTranscript,
    collective: &CollectivePublicKey,
    key_parties: &mut [QuorumParty],
    custody_keys: &[SigningKey],
    combiner: &mut AuthenticatedQuorumCombiner,
    exercise_refusals: bool,
) -> (
    Vec<MaskedBoundaryParty>,
    MaskedOpening,
    AuthenticatedOpeningAudit,
) {
    let session = MaskedDecryptSession::from_public(nonce, LIVE_N, K, target, params)
        .expect("three-live-party masked-decrypt session");
    let mut coordinator = MaskedDecryptCoordinator::new(session.clone(), params.clone());
    let mut masks = Vec::with_capacity(LIVE_N);
    for party in 0..LIVE_N {
        let (state, encrypted_mask) =
            MaskedBoundaryParty::prepare(&session, party, params, collective)
                .expect("party retains mask and exports Enc(mask)");
        coordinator
            .accept(encrypted_mask)
            .expect("full unique mask contribution");
        masks.push(state);
    }
    let masked = coordinator.finish().expect("homomorphically masked curve");
    let opening =
        QuorumOpeningSession::new_verified(keygen.clone(), dkg_transcript, nonce, vec![0, 1, 2])
            .expect("canonical live custody roster");
    let raw_shares = partial_decrypt_quorum_parallel(
        key_parties,
        &opening,
        masked.ciphertext(),
        MIN_SMUDGE_BITS,
        params,
    )
    .expect("live custodians emit canonical smudged shares concurrently");
    if exercise_refusals {
        assert_eq!(
            combiner
                .roster()
                .sign_share(raw_shares[0].clone(), &custody_keys[1]),
            Err(QuorumError::SignerKeyMismatch { party: 0 })
        );
    }
    let framed = raw_shares
        .into_iter()
        .map(|share| {
            let party = share.party();
            combiner
                .roster()
                .sign_share(share, &custody_keys[party])
                .expect("custodian authenticates its exact DKG-bound share")
                .to_wire_bytes()
        })
        .collect::<Vec<_>>();

    if exercise_refusals {
        assert_eq!(
            masked.open_authenticated_quorum_framed(combiner, &opening, &framed[..2], params,),
            Err(BoundaryError::Quorum(QuorumError::QuorumTooSmall {
                have: 2,
                need: 3,
            }))
        );
        let mut forged = framed.clone();
        *forged[0].last_mut().expect("signature byte") ^= 1;
        assert_eq!(
            masked.open_authenticated_quorum_framed(combiner, &opening, &forged, params),
            Err(BoundaryError::Quorum(QuorumError::InvalidSignature {
                party: 0,
            }))
        );
        assert_eq!(
            masked.open_authenticated_quorum_framed(
                combiner,
                &opening,
                &[framed[1].clone(), framed[0].clone(), framed[2].clone()],
                params,
            ),
            Err(BoundaryError::Quorum(QuorumError::NonCanonicalShareOrder))
        );
        let wrong_nonce = QuorumOpeningSession::new_verified(
            keygen.clone(),
            dkg_transcript,
            [0xff; 32],
            vec![0, 1, 2],
        )
        .expect("canonical but wrong masked-boundary nonce");
        assert_eq!(
            masked.open_authenticated_quorum_framed(combiner, &wrong_nonce, &framed, params,),
            Err(BoundaryError::SessionMismatch)
        );
    }

    let (padded, audit) = masked
        .open_authenticated_quorum_framed_with_audit(combiner, &opening, &framed, params)
        .expect("three authenticated custodians open only the padded curve");
    if exercise_refusals {
        assert_eq!(
            masked.open_authenticated_quorum_framed(combiner, &opening, &framed, params),
            Err(BoundaryError::Quorum(QuorumError::Replay))
        );
    }
    (masks, padded, audit)
}

#[test]
fn authenticated_encrypted_orders_gate_real_game_asset_settlement() {
    let run_seed = CommittedSeed::from_bytes([0xD4; 32]);
    let draw = roll_drop(&run_seed, "boss:the Lantern Eater", 0);
    let mut vault = LootVault::new();
    let loot = vault.claim(SELLER, &draw).expect("fair Descent drop");
    let mut world = TradeWorld::with_assets(vault.into_assets());
    world.fund_dregg(SELLER, 0);
    world.fund_dregg(WINNER, 3);

    let source_verifier = SigningKey::from_bytes(&[0x29; 32]);
    let offering = DarkBazaarOffering::new()
        .with_fhegg_source_verifier(source_verifier.verifying_key().to_bytes())
        .expect("deployment-selected exact-opening verifier");
    let mut market = listed_market(&offering);

    // The real one-unit first-price auction is represented as two qty-1 bids
    // plus the seller's qty-1 ask at the winning price. Uniform clearing is 3×1.
    let private_orders = [
        Order {
            side: Side::Bid,
            limit: 2,
            qty: 1,
        },
        Order {
            side: Side::Bid,
            limit: 3,
            qty: 1,
        },
        Order {
            side: Side::Ask,
            limit: 3,
            qty: 1,
        },
    ];

    let params = BfvParams::fold_set();
    let (keygen, dkg_transcript, mut key_parties, collective) = collective_keygen(&params);
    let custody_keys = (0..KEY_N)
        .map(|party| SigningKey::from_bytes(&[0x41 + party as u8; 32]))
        .collect::<Vec<_>>();
    let custody_roster = AuthenticatedQuorumRoster::new_verified(
        keygen.clone(),
        &dkg_transcript,
        custody_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
    )
    .expect("DKG-bound four-custodian identity roster");
    let custody_roster_digest = custody_roster.digest();
    let mut custody_combiner = AuthenticatedQuorumCombiner::new(custody_roster);
    // Custodian 3 disappears after DKG: neither its BFV party state nor its
    // authentication secret is retained by the live opening path.
    let offline_party = key_parties.pop().expect("fourth BFV custodian");
    assert_eq!(offline_party.party(), 3);
    drop(offline_party);
    let live_custody_keys = custody_keys.into_iter().take(LIVE_N).collect::<Vec<_>>();
    let trader_keys = private_orders
        .iter()
        .enumerate()
        .map(|(trader, _)| SigningKey::from_bytes(&[0x51 + trader as u8; 32]))
        .collect::<Vec<_>>();
    let ingress = OrderIngressSession::new(
        market
            .fhegg_order_ingress_nonce()
            .expect("listing-bound ingress nonce"),
        K,
        &params,
        &collective,
    )
    .expect("listing-bound encrypted ingress");
    let mut encrypted_book = AuthenticatedOrderBook::new(
        ingress.clone(),
        trader_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
    )
    .expect("authenticated trader roster");
    let mut listing_action = None;
    let mut bid_actions = Vec::new();
    for (trader, (order, key)) in private_orders.iter().zip(&trader_keys).enumerate() {
        let (submission, opening, _) = SignedOrderSubmission::encrypt_and_sign_openable(
            &ingress,
            trader,
            0,
            order,
            &params,
            &collective,
            key,
        )
        .expect("trader-local encrypted signed order");
        let binding = encrypted_book
            .accept_opened(submission, order, opening, &params, &collective)
            .expect("signature plus exact BFV opening and unary row");
        if trader < 2 {
            let bidder = if trader == 0 { LOW_BIDDER } else { WINNER };
            let certificate = binding.certify_for_market(bidder.as_bytes(), &source_verifier);
            let action =
                DarkBazaarOffering::fhegg_source_bound_bid_action(order.limit as i64, &certificate);
            bid_actions.push((action, actor(bidder)));
        } else {
            let certificate = binding.certify_listing_for_market(
                SELLER.as_bytes(),
                loot.asset_id.0,
                &source_verifier,
            );
            listing_action = Some((
                DarkBazaarOffering::fhegg_listing_source_action(&certificate),
                actor(SELLER),
            ));
        }
    }
    let mut replayable_actions = Vec::new();
    let (action, seller) = listing_action.expect("seller exact ask/asset certificate");
    let outcome = offering.advance(&mut market, action.clone(), seller.clone());
    assert!(
        matches!(outcome, Outcome::Landed { .. }),
        "source-bound listing refused: {outcome:?}"
    );
    replayable_actions.push((action, seller));
    for (action, bidder) in bid_actions {
        let outcome = offering.advance(&mut market, action.clone(), bidder.clone());
        assert!(
            matches!(outcome, Outcome::Landed { .. }),
            "source-bound bid refused: {outcome:?}"
        );
        replayable_actions.push((action, bidder));
    }
    let (encrypted_rows, mut ordered_inputs) = encrypted_book.finish().into_parts();
    market
        .verify_fhegg_bound_order_inputs(&ordered_inputs)
        .expect("every exact signed ciphertext pair is frozen into the board");
    let receipts_before = market.market().receipts_len();
    let source_commitment = market
        .fhegg_source_commitment()
        .expect("exact source-bound on-ledger board commitment");
    let session_nonce = market
        .fhegg_settlement_session_nonce()
        .expect("source-bound board-derived fhEgg session nonce");

    let folded = CollectiveOrderFoldEngine::cpu_only()
        .fold_rows(encrypted_rows, K, params.plaintext_modulus())
        .expect("carry-free collective BFV fold");
    // Custodian 3 is absent from here onward. The remaining three custodians
    // complete both masked openings, the MPC, and the attested settlement.
    let (demand_masks, demand_opening, demand_custody_audit) = quorum_masked_curve(
        [0x71; 32],
        folded.d_ct,
        &params,
        &keygen,
        &dkg_transcript,
        &collective,
        &mut key_parties,
        &live_custody_keys,
        &mut custody_combiner,
        true,
    );
    let (supply_masks, supply_opening, supply_custody_audit) = quorum_masked_curve(
        [0x72; 32],
        folded.s_ct,
        &params,
        &keygen,
        &dkg_transcript,
        &collective,
        &mut key_parties,
        &live_custody_keys,
        &mut custody_combiner,
        false,
    );
    assert_eq!(key_parties.len(), LIVE_N);
    assert_eq!(demand_custody_audit.share_count(), OPEN_T);
    assert_eq!(supply_custody_audit.share_count(), OPEN_T);
    assert_eq!(demand_custody_audit.roster_digest(), custody_roster_digest);
    assert_eq!(supply_custody_audit.roster_digest(), custody_roster_digest);
    assert_eq!(
        demand_custody_audit.vss_setup_digest(),
        Some(dkg_transcript.digest())
    );
    assert_eq!(
        supply_custody_audit.vss_setup_digest(),
        Some(dkg_transcript.digest())
    );
    assert_ne!(
        demand_custody_audit.digest(),
        supply_custody_audit.digest(),
        "the two exact opening sessions/targets have distinct audit commitments"
    );
    let dkg_transcript_input = ordered_inputs.len();
    ordered_inputs.push(InputDigest::commitment(dkg_transcript.digest()));
    let custody_audit_start = ordered_inputs.len();
    ordered_inputs.push(InputDigest::commitment(demand_custody_audit.digest()));
    ordered_inputs.push(InputDigest::commitment(supply_custody_audit.digest()));
    ordered_inputs.push(
        market
            .fhegg_source_input()
            .expect("canonical market source input"),
    );

    let mpc_session = PartyMpcSession::new(
        session_nonce,
        LIVE_N,
        K,
        VALUE_BITS,
        params.plaintext_modulus(),
        Duration::from_secs(5),
    )
    .expect("board-bound output-boundary session");
    let arithmetic_inputs = demand_masks
        .into_iter()
        .zip(supply_masks)
        .enumerate()
        .map(|(party, (demand_state, supply_state))| {
            let demand = demand_state
                .derive_mod_t_share(&demand_opening)
                .expect("party-local demand share");
            let supply = supply_state
                .derive_mod_t_share(&supply_opening)
                .expect("party-local supply share");
            let mut sharing_rng = StdRng::seed_from_u64(0x7400 + party as u64);
            PartyArithmeticInput::new(&mpc_session, party, &demand, &supply, &mut sharing_rng)
                .expect("opaque arithmetic ingress")
        })
        .collect::<Vec<_>>();
    let mut triple_rng = StdRng::seed_from_u64(0x7500);
    let triples = trusted_dealer_triples(&mpc_session, &mut triple_rng)
        .expect("shape-correct trusted preprocessing");
    let (coordinator, endpoints) = local_channels(&mpc_session);
    let workers = arithmetic_inputs
        .into_iter()
        .zip(triples)
        .zip(endpoints)
        .map(|((input, triples), endpoint)| {
            thread::spawn(move || run_party(input, triples, endpoint))
        })
        .collect::<Vec<_>>();
    let distributed = coordinator
        .coordinate(&mpc_session)
        .expect("distributed crossing quorum");
    for worker in workers {
        worker
            .join()
            .expect("party thread exits")
            .expect("party completes");
    }
    assert_eq!(
        distributed.crossing,
        Crossing {
            p_star: Some(3),
            v_star: 1
        }
    );

    let committee_keys = [
        SigningKey::from_bytes(&[0x76; 32]),
        SigningKey::from_bytes(&[0x77; 32]),
        SigningKey::from_bytes(&[0x78; 32]),
    ];
    let verifier = AuthenticatedQuorumVerifier::new(
        committee_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        LIVE_N,
    )
    .expect("unanimous computation-integrity policy");
    let bfv = BfvPublicIdentity::from_quorum_public(&params, &keygen, &collective);
    assert_eq!((bfv.n_parties, bfv.opening_threshold), (4, 3));
    let expected = ExpectedClearingContext {
        session: &mpc_session,
        ordered_roster: verifier.ordered_roster(),
        bfv: &bfv,
        ordered_inputs: &ordered_inputs,
        transcript: &distributed.transcript,
        crossing: &distributed.crossing,
    };
    let mut attestation = AttestedClearingReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("canonical encrypted-source/result claim");
    let claim_digest = attestation.claim_digest();
    let signatures = committee_keys
        .iter()
        .enumerate()
        .map(|(party, key)| {
            verifier
                .sign_claim(&claim_digest, party, key)
                .expect("committee endorses exact claim")
        })
        .collect::<Vec<_>>();
    attestation.computation_integrity = verifier
        .assemble_evidence(&claim_digest, &signatures)
        .expect("unanimous authenticated evidence");

    let mut replay_guard = InMemoryReplayGuard::default();

    // Cross-session replay is rejected before evidence verification/replay burn.
    let wrong_session = PartyMpcSession::new(
        [0x99; 32],
        LIVE_N,
        K,
        VALUE_BITS,
        params.plaintext_modulus(),
        Duration::from_secs(5),
    )
    .expect("well-shaped but unrelated session");
    let wrong_session_expected = ExpectedClearingContext {
        session: &wrong_session,
        ..expected
    };
    assert!(matches!(
        offering.settle_fhegg_verified(
            &mut market,
            &attestation,
            &wrong_session_expected,
            &verifier,
            &mut replay_guard,
        ),
        Err(FheggSettlementError::SessionMismatch)
    ));
    assert_unmutated(&market, receipts_before);

    // Substituting the live sealed-board commitment is refused independently.
    let mut wrong_inputs = ordered_inputs.clone();
    *wrong_inputs.last_mut().expect("source commitment") = InputDigest::commitment([0x99; 32]);
    let wrong_source_expected = ExpectedClearingContext {
        ordered_inputs: &wrong_inputs,
        ..expected
    };
    assert!(matches!(
        offering.settle_fhegg_verified(
            &mut market,
            &attestation,
            &wrong_source_expected,
            &verifier,
            &mut replay_guard,
        ),
        Err(FheggSettlementError::SourceCommitmentCount { found: 0 })
    ));
    assert_unmutated(&market, receipts_before);

    // Replacing one exact BFV ciphertext and having the ENTIRE computation
    // quorum freshly sign that changed claim still cannot detach it from the
    // WriteOnce source-bound bid seal. Co-endorsement is not source proof.
    let mut substituted_ciphertext_inputs = ordered_inputs.clone();
    substituted_ciphertext_inputs[1] =
        InputDigest::ciphertext_bytes(b"canonical but unrelated BFV row");
    let substituted_ciphertext_expected = ExpectedClearingContext {
        ordered_inputs: &substituted_ciphertext_inputs,
        ..expected
    };
    let mut resigned_substitution = AttestedClearingReceipt::issue(
        &substituted_ciphertext_expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("changed claim is structurally canonical");
    let changed_digest = resigned_substitution.claim_digest();
    let changed_signatures = committee_keys
        .iter()
        .enumerate()
        .map(|(party, key)| verifier.sign_claim(&changed_digest, party, key).unwrap())
        .collect::<Vec<_>>();
    resigned_substitution.computation_integrity = verifier
        .assemble_evidence(&changed_digest, &changed_signatures)
        .unwrap();
    assert!(matches!(
        offering.settle_fhegg_verified(
            &mut market,
            &resigned_substitution,
            &substituted_ciphertext_expected,
            &verifier,
            &mut replay_guard,
        ),
        Err(FheggSettlementError::SourceInputPairCount { bid: 0, found: 0 })
    ));
    assert_unmutated(&market, receipts_before);

    // The all-dealer VSS transcript is a first-class receipt input, not merely
    // implied by process-local party state or custody signatures.
    let mut wrong_dkg_inputs = ordered_inputs.clone();
    wrong_dkg_inputs[dkg_transcript_input] = InputDigest::commitment([0xb6; 32]);
    let wrong_dkg_expected = ExpectedClearingContext {
        ordered_inputs: &wrong_dkg_inputs,
        ..expected
    };
    assert!(matches!(
        offering.settle_fhegg_verified(
            &mut market,
            &attestation,
            &wrong_dkg_expected,
            &verifier,
            &mut replay_guard,
        ),
        Err(FheggSettlementError::Attestation(
            AttestationError::BindingMismatch
        ))
    ));
    assert_unmutated(&market, receipts_before);

    // Substituting either digest-only custody transcript keeps the live-board
    // join intact, but breaks the signed claim before evidence/replay or state
    // mutation. No raw decryption share is retained by the claim.
    let mut wrong_audit_inputs = ordered_inputs.clone();
    wrong_audit_inputs[custody_audit_start] = InputDigest::commitment([0xa5; 32]);
    let wrong_audit_expected = ExpectedClearingContext {
        ordered_inputs: &wrong_audit_inputs,
        ..expected
    };
    assert!(matches!(
        offering.settle_fhegg_verified(
            &mut market,
            &attestation,
            &wrong_audit_expected,
            &verifier,
            &mut replay_guard,
        ),
        Err(FheggSettlementError::Attestation(
            AttestationError::BindingMismatch
        ))
    ));
    assert_unmutated(&market, receipts_before);

    // A different result cannot reach receipt verification or mutate the board.
    let wrong_crossing = Crossing {
        p_star: Some(2),
        v_star: 1,
    };
    let wrong_result_expected = ExpectedClearingContext {
        crossing: &wrong_crossing,
        ..expected
    };
    assert!(matches!(
        offering.settle_fhegg_verified(
            &mut market,
            &attestation,
            &wrong_result_expected,
            &verifier,
            &mut replay_guard,
        ),
        Err(FheggSettlementError::ResultMismatch {
            expected_price: 3,
            claimed_price: Some(2),
            claimed_volume: 1,
        })
    ));
    assert_unmutated(&market, receipts_before);

    // Canonical binding alone is deliberately not a settlement authorization:
    // the relying party's computation-integrity policy must verify in full.
    let mut binding_only = attestation.clone();
    binding_only.computation_integrity = ComputationIntegrityEvidence::BindingOnly(
        ComputationIntegrityResidual::OutputOnlySelfAssertion,
    );
    assert!(matches!(
        offering.settle_fhegg_verified(
            &mut market,
            &binding_only,
            &expected,
            &verifier,
            &mut replay_guard,
        ),
        Err(FheggSettlementError::Attestation(
            AttestationError::ComputationIntegrityResidual(
                ComputationIntegrityResidual::OutputOnlySelfAssertion
            )
        ))
    ));
    assert_unmutated(&market, receipts_before);

    // Even a valid private clear cannot substitute a different Descent asset.
    // This refusal occurs before replay consumption and leaves both the market
    // executor and complete trade-world image untouched.
    let world_before = world.state_audit_digest();
    assert!(matches!(
        offering.settle_fhegg_asset_atomic(
            &mut market,
            &mut world,
            AssetId([0xA6; 32]),
            &attestation,
            &expected,
            &verifier,
            &mut replay_guard,
        ),
        Err(dreggnet_market::fhegg_atomic_asset::AtomicFheggAssetSettlementError::Asset(
            dreggnet_market::asset_backed::AssetBackedError::SourceAssetMismatch {
                expected,
                provided,
            }
        )) if expected == loot.asset_id && provided == AssetId([0xA6; 32])
    ));
    assert_unmutated(&market, receipts_before);
    assert_eq!(world.state_audit_digest(), world_before);

    // The exact fully authenticated receipt lands the auction lifecycle and
    // the original provenance-carrying Descent asset/$DREGG cross as one
    // process-local atomic transaction.
    let authorized = offering
        .settle_fhegg_asset_atomic(
            &mut market,
            &mut world,
            loot.asset_id,
            &attestation,
            &expected,
            &verifier,
            &mut replay_guard,
        )
        .expect("authenticated private clearing atomically crosses the Descent loot");
    assert_eq!(authorized.fhegg.claim_digest, claim_digest);
    assert_eq!(authorized.fhegg.source_commitment, source_commitment);
    assert_eq!((authorized.fhegg.price, authorized.fhegg.volume), (3, 1));
    assert_eq!(authorized.fhegg.winner, actor(WINNER));
    assert_eq!(authorized.world_before, world_before);
    assert_eq!(authorized.world_after, world.state_audit_digest());
    assert_ne!(authorized.audit_digest, [0; 32]);
    assert!(authorized.audit_digest_verifies());
    assert!(market.is_settled());
    assert!(market.clearing().expect("real clear").conserved());

    // A distinct replay-equivalent live session reaches the external replay
    // guard and is refused without touching its executor state.
    let mut replay_market = listed_market(&offering);
    for (action, bidder) in replayable_actions {
        let outcome = offering.advance(&mut replay_market, action, bidder);
        assert!(matches!(outcome, Outcome::Landed { .. }));
    }
    let replay_receipts = replay_market.market().receipts_len();
    assert_eq!(
        replay_market
            .fhegg_source_commitment()
            .expect("same deterministic board"),
        source_commitment
    );
    assert!(matches!(
        offering.settle_fhegg_verified(
            &mut replay_market,
            &attestation,
            &expected,
            &verifier,
            &mut replay_guard,
        ),
        Err(FheggSettlementError::Attestation(
            AttestationError::ReplayDetected
        ))
    ));
    assert_unmutated(&replay_market, replay_receipts);

    let crossed = authorized.asset;
    assert_eq!(crossed.asset, loot.asset_id);
    assert_eq!(crossed.seller, actor(SELLER));
    assert_eq!(crossed.winner, actor(WINNER));
    assert_eq!(crossed.price, 3);
    assert_eq!(crossed.settlement.a_gave, LegSpec::Asset(loot.asset_id));
    assert_eq!(crossed.settlement.b_gave, LegSpec::Dregg(3));
    assert!(crossed.provenance.verified);
    assert_eq!(world.current_holder_label(loot.asset_id), Some(WINNER));
    assert_eq!(world.lineage_len(loot.asset_id), 3);
    assert_eq!(world.dregg_balance(WINNER), 0);
    assert_eq!(world.dregg_balance(SELLER), 3);
}
