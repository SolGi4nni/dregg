//! Authenticated Dark Bazaar clearing with crash-tolerant BFV custody.
//!
//! Four parties perform the semi-honest Shamir DKG, then custodian 3 disappears.
//! The remaining three parties open only the one-time-padded demand/supply
//! curves, three mask owners derive private mod-t shares, distributed MPC
//! reveals only `(p*, V*)`, and an Ed25519 quorum receipt binds the exact signed
//! ciphertext inputs and transcript.  No joint BFV secret key is constructed.
//!
//! This is not malicious-secure: setup needs every dealer, dealer/decrypt-share
//! transports are not authenticated or VSS-proven, preprocessing is trusted,
//! and the MPC transport is process-shaped.

use std::thread;
use std::time::Duration;

use ed25519_dalek::SigningKey;
use fhe::bfv::PublicKey;
use fhe_traits::{DeserializeParametrized, Serialize as FheSerialize};
use fhegg_fhe::additive::CollectiveOrderFoldEngine;
use fhegg_fhe::attestation::{
    AttestationError, AttestedClearingReceipt, AuthenticatedQuorumVerifier, BfvPublicIdentity,
    ComputationIntegrityEvidence, ComputationIntegrityResidual, ExpectedClearingContext,
    InMemoryReplayGuard,
};
use fhegg_fhe::boundary::{
    BoundaryError, MaskedBoundaryParty, MaskedDecryptCoordinator, MaskedDecryptSession,
    MaskedOpening,
};
use fhegg_fhe::mpc_party::{
    local_channels, run_party, trusted_dealer_triples, PartyArithmeticInput, PartyMpcSession,
};
use fhegg_fhe::order_ingress::{
    AuthenticatedOrderBook, OrderIngressSession, SignedOrderSubmission,
};
use fhegg_fhe::threshold::quorum::{
    deal, finish_public_key, PrivateDealerShare, QuorumError, QuorumKeygenSession,
    QuorumOpeningSession, QuorumParty,
};
use fhegg_fhe::threshold::{BfvParams, CollectivePublicKey, MIN_SMUDGE_BITS};
use fhegg_fhe::{reference_clear, Order, Side};
use rand::rngs::StdRng;
use rand::SeedableRng;

const KEY_N: usize = 4;
const OPEN_T: usize = 3;
const LIVE: usize = 3;
const K: usize = 4;
const VALUE_BITS: usize = 16;

fn quorum_keygen(
    params: &BfvParams,
) -> (QuorumKeygenSession, Vec<QuorumParty>, CollectivePublicKey) {
    let session = QuorumKeygenSession::from_seed(KEY_N, OPEN_T, [0x31; 32])
        .expect("fixed 3-of-4 public DKG session");
    let mut public = Vec::with_capacity(KEY_N);
    let mut inboxes: Vec<Vec<PrivateDealerShare>> = (0..KEY_N).map(|_| Vec::new()).collect();
    for dealer in 0..KEY_N {
        // This quorum runs no ct*ct multiply, so it needs no relin key and keeps
        // no dealer secret: `_relin_secret` drops here.
        let (contribution, private, _relin_secret) = deal(&session, dealer, params)
            .expect("semi-honest DKG dealer")
            .into_parts();
        public.push(contribution);
        for share in private {
            let recipient = share.recipient();
            inboxes[recipient].push(share);
        }
    }
    let collective = finish_public_key(&session, &public, params).expect("complete public DKG");
    let parties = inboxes
        .into_iter()
        .enumerate()
        .map(|(party, inbox)| {
            QuorumParty::assemble(&session, party, inbox, params)
                .expect("recipient assembles every dealer evaluation")
        })
        .collect();
    (session, parties, collective)
}

/// Mask one encrypted curve and open it through custodians 0,1,2.  The mask
/// owners and opening custodians happen to share indices here, but the boundary
/// binds the roles independently: masks bind to `MaskedDecryptSession`, while
/// decryption shares bind to the Shamir key session, exact roster, and ct.
fn quorum_masked_curve(
    nonce: [u8; 32],
    target: fhegg_fhe::bfv_lean::LeanCiphertext,
    params: &BfvParams,
    keygen: &QuorumKeygenSession,
    collective: &CollectivePublicKey,
    key_parties: &mut [QuorumParty],
    exercise_refusals: bool,
) -> (Vec<MaskedBoundaryParty>, MaskedOpening) {
    let mask_session = MaskedDecryptSession::from_public(nonce, LIVE, K, target, params)
        .expect("three live mask owners");
    let mut coordinator = MaskedDecryptCoordinator::new(mask_session.clone(), params.clone());
    let mut mask_states = Vec::with_capacity(LIVE);
    for party in 0..LIVE {
        let (state, contribution) =
            MaskedBoundaryParty::prepare(&mask_session, party, params, collective)
                .expect("live party retains mask");
        coordinator
            .accept(contribution)
            .expect("unique encrypted mask");
        mask_states.push(state);
    }
    let masked = coordinator.finish().expect("masked curve");
    let opening = QuorumOpeningSession::new(keygen.clone(), nonce, vec![0, 1, 2])
        .expect("canonical live opening roster");
    let framed = [0usize, 1, 2]
        .into_iter()
        .map(|party| {
            key_parties[party]
                .partial_decrypt(&opening, masked.ciphertext(), MIN_SMUDGE_BITS, params)
                .expect("live custodian emits one exact-target share")
                .to_wire_bytes()
        })
        .collect::<Vec<_>>();

    if exercise_refusals {
        assert_eq!(
            masked.open_quorum_framed(&opening, &framed[..2], params),
            Err(BoundaryError::QuorumTooSmall { have: 2, need: 3 }),
            "an undersized opening must not produce a padded curve"
        );
        assert!(matches!(
            key_parties[0].partial_decrypt(&opening, masked.ciphertext(), MIN_SMUDGE_BITS, params,),
            Err(QuorumError::Replay)
        ));
        let wrong_nonce = QuorumOpeningSession::new(keygen.clone(), [0xff; 32], vec![0, 1, 2])
            .expect("canonical but wrong boundary nonce");
        assert_eq!(
            masked.open_quorum_framed(&wrong_nonce, &framed, params),
            Err(BoundaryError::SessionMismatch)
        );
    }

    let opened = masked
        .open_quorum_framed(&opening, &framed, params)
        .expect("three live custodians open only the padded curve");
    (mask_states, opened)
}

#[test]
fn authenticated_dark_bazaar_clears_with_one_of_four_custodians_offline() {
    let params = BfvParams::fold_set();
    let (keygen, mut key_parties, collective) = quorum_keygen(&params);

    // Fail before any ciphertext/output exists: the interpolation roster is an
    // independently validated policy object, not metadata supplied by a share.
    assert_eq!(
        QuorumOpeningSession::new(keygen.clone(), [0x70; 32], vec![0, 1]),
        Err(QuorumError::QuorumTooSmall { have: 2, need: 3 })
    );
    assert_eq!(
        QuorumOpeningSession::new(keygen.clone(), [0x70; 32], vec![1, 0, 2]),
        Err(QuorumError::NonCanonicalRoster)
    );

    let orders = [
        Order {
            side: Side::Bid,
            limit: 2,
            qty: 7,
        },
        Order {
            side: Side::Ask,
            limit: 1,
            qty: 4,
        },
        Order {
            side: Side::Bid,
            limit: 1,
            qty: 5,
        },
        Order {
            side: Side::Ask,
            limit: 2,
            qty: 6,
        },
    ];
    let expected = reference_clear(&orders, K);
    assert_eq!(expected.p_star, Some(2));
    assert_eq!(expected.v_star, 7);

    // Plain orders exist only inside trader closures.  The clearing side sees
    // strict signed ciphertext envelopes.
    let trader_keys = (0..orders.len())
        .map(|trader| SigningKey::from_bytes(&[0x51 + trader as u8; 32]))
        .collect::<Vec<_>>();
    let trader_public_keys = trader_keys
        .iter()
        .map(|key| key.verifying_key().to_bytes())
        .collect::<Vec<_>>();
    let ingress =
        OrderIngressSession::new([0x61; 32], K, &params, &collective).expect("ingress session");
    let public_key_bytes = collective.pk.to_bytes();
    let wires = orders
        .into_iter()
        .zip(trader_keys.iter().cloned())
        .enumerate()
        .map(|(trader, (order, signing_key))| {
            let params = params.clone();
            let ingress = ingress.clone();
            let public_key_bytes = public_key_bytes.clone();
            thread::spawn(move || {
                let pk = PublicKey::from_bytes(&public_key_bytes, params.arc())
                    .expect("collective public key parses at trader");
                SignedOrderSubmission::encrypt_and_sign(
                    &ingress,
                    trader,
                    0,
                    &order,
                    &params,
                    &CollectivePublicKey { pk },
                    &signing_key,
                )
                .expect("trader-local signed encryption")
                .0
                .to_wire_bytes()
            })
        })
        .collect::<Vec<_>>()
        .into_iter()
        .map(|party| party.join().expect("trader exits"))
        .collect::<Vec<_>>();
    let mut book = AuthenticatedOrderBook::new(ingress.clone(), trader_public_keys)
        .expect("strict trader roster");
    for wire in wires.iter().rev() {
        let submission = SignedOrderSubmission::from_wire_bytes(wire, &ingress, &params)
            .expect("strict authenticated wire");
        book.accept(submission).expect("fresh source");
    }
    let (encrypted_rows, ordered_inputs) = book.finish().into_parts();
    let folded = CollectiveOrderFoldEngine::cpu_only()
        .fold_rows(encrypted_rows, K, params.plaintext_modulus())
        .expect("authenticated encrypted book folds");

    // Custodian 3 is now offline and is never referenced again.  Both encrypted
    // curves still cross the true 3-of-4 opening boundary.
    let (demand_masks, demand_opening) = quorum_masked_curve(
        [0x71; 32],
        folded.d_ct,
        &params,
        &keygen,
        &collective,
        &mut key_parties,
        true,
    );
    let (supply_masks, supply_opening) = quorum_masked_curve(
        [0x72; 32],
        folded.s_ct,
        &params,
        &keygen,
        &collective,
        &mut key_parties,
        false,
    );
    assert_eq!(key_parties[3].party(), 3);

    let mpc_session = PartyMpcSession::new(
        [0x73; 32],
        LIVE,
        K,
        VALUE_BITS,
        params.plaintext_modulus(),
        Duration::from_secs(5),
    )
    .expect("three-live-party MPC session");
    let inputs = demand_masks
        .into_iter()
        .zip(supply_masks)
        .enumerate()
        .map(|(party, (demand, supply))| {
            let mpc_session = mpc_session.clone();
            let demand_opening = demand_opening.clone();
            let supply_opening = supply_opening.clone();
            thread::spawn(move || {
                let demand = demand
                    .derive_mod_t_share(&demand_opening)
                    .expect("private demand share");
                let supply = supply
                    .derive_mod_t_share(&supply_opening)
                    .expect("private supply share");
                let mut rng = StdRng::seed_from_u64(0x7400 + party as u64);
                PartyArithmeticInput::new(&mpc_session, party, &demand, &supply, &mut rng)
                    .expect("opaque MPC ingress")
            })
        })
        .collect::<Vec<_>>()
        .into_iter()
        .map(|party| party.join().expect("mask party exits"))
        .collect::<Vec<_>>();

    let mut triple_rng = StdRng::seed_from_u64(0x7500);
    let triples = trusted_dealer_triples(&mpc_session, &mut triple_rng)
        .expect("shape-only trusted preprocessing");
    let (coordinator, endpoints) = local_channels(&mpc_session);
    let mpc_threads = inputs
        .into_iter()
        .zip(triples)
        .zip(endpoints)
        .map(|((input, triples), endpoint)| {
            thread::spawn(move || run_party(input, triples, endpoint))
        })
        .collect::<Vec<_>>();
    let distributed = coordinator
        .coordinate(&mpc_session)
        .expect("live MPC quorum clears");
    for party in mpc_threads {
        party
            .join()
            .expect("MPC thread exits")
            .expect("MPC party completes");
    }
    assert_eq!(distributed.crossing.p_star, expected.p_star);
    assert_eq!(distributed.crossing.v_star, u64::from(expected.v_star));
    assert!(distributed.transcript.is_reveal_only(&mpc_session));

    // The receipt records a four-custodian BFV domain with threshold three,
    // while its computation roster is the exact three live MPC parties.
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
        LIVE,
    )
    .expect("unanimous live computation committee");
    let bfv = BfvPublicIdentity::from_quorum_public(&params, &keygen, &collective);
    assert_eq!(bfv.n_parties, 4);
    assert_eq!(bfv.opening_threshold, 3);
    let context = ExpectedClearingContext {
        session: &mpc_session,
        ordered_roster: verifier.ordered_roster(),
        bfv: &bfv,
        ordered_inputs: &ordered_inputs,
        transcript: &distributed.transcript,
        crossing: &distributed.crossing,
    };
    let mut receipt = AttestedClearingReceipt::issue(
        &context,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .expect("canonical source/result claim");
    let claim = receipt.claim_digest();
    let signatures = committee_keys
        .iter()
        .enumerate()
        .map(|(party, key)| {
            verifier
                .sign_claim(&claim, party, key)
                .expect("live party signs exact claim")
        })
        .collect::<Vec<_>>();
    receipt.computation_integrity = verifier
        .assemble_evidence(&claim, &signatures)
        .expect("authenticated live quorum evidence");

    let mut replay = InMemoryReplayGuard::default();
    receipt
        .verify_full(&context, &verifier, &mut replay)
        .expect("exact private clearing accepts once");
    assert_eq!(
        receipt.verify_full(&context, &verifier, &mut replay),
        Err(AttestationError::ReplayDetected)
    );
}
