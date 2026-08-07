//! Focused crash-tolerant threshold-opening teeth.
//!
//! These tests use a real fhe.rs collective public key and ciphertext.  They
//! demonstrate that an arbitrary live `t`-of-`n` subset decrypts while an
//! offline party contributes nothing, and that roster/share/replay confusion
//! fails before a public result is returned.  This is a semi-honest DKG/API
//! test, not verifiable secret sharing or malicious-share validation.

use ed25519_dalek::SigningKey;
use fhe::bfv::{Encoding, Plaintext};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize as FheSerialize};
use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::threshold::quorum::{
    combine_quorum, deal, finish_public_key, partial_decrypt_quorum_parallel,
    AuthenticatedQuorumCombiner, AuthenticatedQuorumDecryptShare, AuthenticatedQuorumRoster,
    PrivateDealerShare, QuorumDecryptShare, QuorumError, QuorumKeygenSession, QuorumOpeningSession,
    QuorumParty,
};
use fhegg_fhe::threshold::{BfvParams, CollectivePublicKey, MIN_SMUDGE_BITS};

const N: usize = 4;
const T: usize = 3;

fn setup() -> (
    BfvParams,
    QuorumKeygenSession,
    CollectivePublicKey,
    Vec<QuorumParty>,
) {
    let params = BfvParams::fold_set();
    let session = QuorumKeygenSession::from_seed(N, T, [0x71; 32]).expect("valid t-of-n session");
    let mut public = Vec::with_capacity(N);
    let mut inboxes: Vec<Vec<PrivateDealerShare>> = (0..N).map(|_| Vec::new()).collect();

    for dealer in 0..N {
        let (contribution, private, _relin_secret) = deal(&session, dealer, &params)
            .expect("semi-honest dealer")
            .into_parts();
        public.push(contribution);
        for share in private {
            let recipient = share.recipient();
            inboxes[recipient].push(share);
        }
    }

    let collective =
        finish_public_key(&session, &public, &params).expect("all public setup dealers present");
    let parties = inboxes
        .into_iter()
        .enumerate()
        .map(|(party, inbox)| {
            QuorumParty::assemble(&session, party, inbox, &params)
                .expect("all private dealer evaluations present")
        })
        .collect();
    (params, session, collective, parties)
}

fn encrypt(collective: &CollectivePublicKey, params: &BfvParams, prefix: &[u64]) -> LeanCiphertext {
    let mut slots = vec![0u64; params.degree()];
    slots[..prefix.len()].copy_from_slice(prefix);
    let plaintext =
        Plaintext::try_encode(&slots, Encoding::simd(), params.arc()).expect("SIMD encode");
    let mut rng = rand_09::rng();
    let ciphertext = collective
        .pk
        .try_encrypt(&plaintext, &mut rng)
        .expect("collective encrypt");
    LeanCiphertext::from_fhe_bytes(
        &ciphertext.to_bytes(),
        params.moduli(),
        params.degree(),
        prefix.iter().copied().max().unwrap_or(0),
    )
    .expect("strict ciphertext parse")
}

fn custody_keys() -> Vec<SigningKey> {
    (0..N)
        .map(|party| SigningKey::from_bytes(&[0xb1 + party as u8; 32]))
        .collect()
}

fn authenticated_roster(
    session: &QuorumKeygenSession,
    keys: &[SigningKey],
) -> AuthenticatedQuorumRoster {
    AuthenticatedQuorumRoster::new(
        session.clone(),
        keys.iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
    )
    .expect("canonical DKG-bound custody identity roster")
}

#[test]
fn parallel_quorum_share_generation_preserves_canonical_roster_and_refusals() {
    let (params, session, collective, mut parties) = setup();
    let ciphertext = encrypt(&collective, &params, &[7, 19, 31, 43]);
    let opening = QuorumOpeningSession::new(session.clone(), [0x3a; 32], vec![0, 2, 3])
        .expect("canonical 3-of-4 opening");

    let shares = partial_decrypt_quorum_parallel(
        &mut parties,
        &opening,
        &ciphertext,
        MIN_SMUDGE_BITS,
        &params,
    )
    .expect("independent custody workers run concurrently");
    assert_eq!(
        shares
            .iter()
            .map(QuorumDecryptShare::party)
            .collect::<Vec<_>>(),
        opening.parties()
    );
    assert_eq!(
        &combine_quorum(&shares, &opening, &params).expect("parallel shares combine")[..4],
        &[7, 19, 31, 43]
    );

    assert_eq!(
        partial_decrypt_quorum_parallel(
            &mut parties,
            &opening,
            &ciphertext,
            MIN_SMUDGE_BITS,
            &params,
        ),
        Err(QuorumError::Replay)
    );

    parties.remove(2);
    let other_ciphertext = encrypt(&collective, &params, &[1, 2, 3, 4]);
    let other_opening = QuorumOpeningSession::new(session, [0x3b; 32], vec![0, 2, 3])
        .expect("same canonical roster");
    assert_eq!(
        partial_decrypt_quorum_parallel(
            &mut parties,
            &other_opening,
            &other_ciphertext,
            MIN_SMUDGE_BITS,
            &params,
        ),
        Err(QuorumError::MissingCustodyParty { party: 2 })
    );
}

#[test]
fn any_named_threshold_subset_opens_while_an_unselected_party_is_offline() {
    let (params, session, collective, mut parties) = setup();
    let rosters = [[0usize, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]];

    // Exercise every 3-of-4 interpolation set.  In each round the fourth
    // party is entirely absent from that opening.
    for (round, roster) in rosters.into_iter().enumerate() {
        let expected = [7 + round as u64, 19, 23, 41, 65_535];
        let ciphertext = encrypt(&collective, &params, &expected);
        let opening =
            QuorumOpeningSession::new(session.clone(), [0x81 + round as u8; 32], roster.to_vec())
                .expect("canonical live threshold roster");
        let mut framed = Vec::new();
        for party in roster {
            let share = parties[party]
                .partial_decrypt(&opening, &ciphertext, MIN_SMUDGE_BITS, &params)
                .expect("selected live party decrypts");
            let wire = share.to_wire_bytes();
            let roundtrip =
                QuorumDecryptShare::from_wire_bytes(&wire, &params).expect("strict share framing");
            assert_eq!(roundtrip, share);
            framed.push(roundtrip);
        }

        let opened = combine_quorum(&framed, &opening, &params).expect("three of four open");
        assert_eq!(&opened[..expected.len()], &expected);
    }
}

#[test]
fn quorum_roster_share_wire_and_replay_refusals_have_teeth() {
    let (params, session, collective, mut parties) = setup();
    assert_eq!(
        QuorumOpeningSession::new(session.clone(), [1; 32], vec![0, 1]),
        Err(QuorumError::QuorumTooSmall { have: 2, need: 3 })
    );
    assert_eq!(
        QuorumOpeningSession::new(session.clone(), [1; 32], vec![0, 0, 2]),
        Err(QuorumError::NonCanonicalRoster)
    );
    assert_eq!(
        QuorumOpeningSession::new(session.clone(), [1; 32], vec![2, 1, 3]),
        Err(QuorumError::NonCanonicalRoster)
    );

    let ciphertext = encrypt(&collective, &params, &[3, 5, 8, 13]);
    let opening = QuorumOpeningSession::new(session.clone(), [0x91; 32], vec![0, 2, 3])
        .expect("canonical roster");
    assert!(matches!(
        parties[1].partial_decrypt(&opening, &ciphertext, MIN_SMUDGE_BITS, &params),
        Err(QuorumError::PartyNotSelected { party: 1 })
    ));

    let shares = [0usize, 2, 3]
        .into_iter()
        .map(|party| {
            parties[party]
                .partial_decrypt(&opening, &ciphertext, MIN_SMUDGE_BITS, &params)
                .expect("first exact-target share")
        })
        .collect::<Vec<_>>();

    assert_eq!(
        combine_quorum(&shares[..2], &opening, &params),
        Err(QuorumError::QuorumTooSmall { have: 2, need: 3 })
    );
    assert_eq!(
        combine_quorum(
            &[shares[0].clone(), shares[0].clone(), shares[2].clone()],
            &opening,
            &params,
        ),
        Err(QuorumError::DuplicateParty { party: 0 })
    );

    // A structurally valid opening-nonce mutation parses, but cannot be mixed
    // into the relying party's exact expected session.
    let mut wrong_opening_wire = shares[0].to_wire_bytes();
    let nonce_offset = 8 + 8 + 8 + 32;
    wrong_opening_wire[nonce_offset] ^= 1;
    let wrong_opening = QuorumDecryptShare::from_wire_bytes(&wrong_opening_wire, &params)
        .expect("mutated nonce remains canonical framing");
    assert_eq!(
        combine_quorum(
            &[wrong_opening, shares[1].clone(), shares[2].clone()],
            &opening,
            &params,
        ),
        Err(QuorumError::SessionMismatch)
    );

    // A non-canonical RNS residue is rejected by the wire parser.
    let mut malformed = shares[0].to_wire_bytes();
    let last = malformed.len() - 8;
    malformed[last..].copy_from_slice(&u64::MAX.to_le_bytes());
    assert_eq!(
        QuorumDecryptShare::from_wire_bytes(&malformed, &params),
        Err(QuorumError::MalformedWire)
    );

    // Same target, same or different nonce: an in-memory party never resamples
    // smudge for a coordinator that wants to average repeated openings.
    assert!(matches!(
        parties[0].partial_decrypt(&opening, &ciphertext, MIN_SMUDGE_BITS, &params),
        Err(QuorumError::Replay)
    ));
    let renamed = QuorumOpeningSession::new(session, [0x92; 32], vec![0, 2, 3])
        .expect("different public nonce");
    assert!(matches!(
        parties[0].partial_decrypt(&renamed, &ciphertext, MIN_SMUDGE_BITS, &params),
        Err(QuorumError::Replay)
    ));

    // Positive control: all refusal checks above leave the original exact
    // share set usable.
    let opened = combine_quorum(&shares, &opening, &params).expect("valid quorum survives");
    assert_eq!(&opened[..4], &[3, 5, 8, 13]);
}

#[test]
fn setup_refuses_missing_dealers_before_party_state_exists() {
    let params = BfvParams::fold_set();
    let session = QuorumKeygenSession::from_seed(3, 2, [0xa1; 32]).expect("valid setup session");
    let (_public, private, _relin_secret) =
        deal(&session, 0, &params).expect("one dealer").into_parts();
    let only_one = private
        .into_iter()
        .filter(|share| share.recipient() == 0)
        .collect();
    assert!(matches!(
        QuorumParty::assemble(&session, 0, only_one, &params),
        Err(QuorumError::MissingDealerShares { have: 1, need: 3 })
    ));
}

#[test]
fn authenticated_three_of_four_opening_binds_identity_session_target_and_order() {
    let (params, session, collective, mut parties) = setup();
    let keys = custody_keys();
    let roster = authenticated_roster(&session, &keys);
    let ciphertext = encrypt(&collective, &params, &[11, 29, 47, 65_535]);
    let opening = QuorumOpeningSession::new(session.clone(), [0xc1; 32], vec![0, 2, 3])
        .expect("custodian 1 may be offline");

    let raw = [0usize, 2, 3]
        .into_iter()
        .map(|party| {
            parties[party]
                .partial_decrypt(&opening, &ciphertext, MIN_SMUDGE_BITS, &params)
                .expect("selected custodian forms one share")
        })
        .collect::<Vec<_>>();

    assert_eq!(
        roster.sign_share(raw[0].clone(), &keys[1]),
        Err(QuorumError::SignerKeyMismatch { party: 0 })
    );

    let signed = raw
        .iter()
        .map(|share| {
            roster
                .sign_share(share.clone(), &keys[share.party()])
                .expect("party authenticates its exact share")
        })
        .collect::<Vec<_>>();
    let framed = signed
        .iter()
        .map(|share| {
            let wire = share.to_wire_bytes();
            assert_eq!(
                AuthenticatedQuorumDecryptShare::from_wire_bytes(&wire, &params)
                    .expect("strict authenticated envelope framing"),
                *share
            );
            wire
        })
        .collect::<Vec<_>>();

    let mut combiner = AuthenticatedQuorumCombiner::new(roster.clone());

    assert_eq!(
        combiner.combine_framed(&opening, &ciphertext, &framed[..2], &params),
        Err(QuorumError::QuorumTooSmall { have: 2, need: 3 })
    );
    assert_eq!(
        combiner.combine_framed(
            &opening,
            &ciphertext,
            &[framed[0].clone(), framed[0].clone(), framed[2].clone()],
            &params,
        ),
        Err(QuorumError::DuplicateParty { party: 0 })
    );
    assert_eq!(
        combiner.combine_framed(
            &opening,
            &ciphertext,
            &[framed[1].clone(), framed[0].clone(), framed[2].clone()],
            &params,
        ),
        Err(QuorumError::NonCanonicalShareOrder)
    );

    let mut wrong_roster = framed.clone();
    wrong_roster[0][8] ^= 1;
    assert_eq!(
        combiner.combine_framed(&opening, &ciphertext, &wrong_roster, &params),
        Err(QuorumError::AuthenticationRosterMismatch)
    );

    let mut forged = framed.clone();
    *forged[0].last_mut().expect("signature byte") ^= 1;
    assert_eq!(
        combiner.combine_framed(&opening, &ciphertext, &forged, &params),
        Err(QuorumError::InvalidSignature { party: 0 })
    );

    let other_ciphertext = encrypt(&collective, &params, &[12, 30, 48, 65_534]);
    assert_eq!(
        combiner.combine_framed(&opening, &other_ciphertext, &framed, &params),
        Err(QuorumError::SessionMismatch)
    );
    // Party state also prevents reusing the same opening nonce/roster for a
    // different target, while its earlier valid share remains usable.
    assert_eq!(
        parties[0].partial_decrypt(&opening, &other_ciphertext, MIN_SMUDGE_BITS, &params),
        Err(QuorumError::Replay)
    );

    let (opened, audit) = combiner
        .combine_framed_with_audit(&opening, &ciphertext, &framed, &params)
        .expect("authenticated 3-of-4 opening");
    assert_eq!(&opened[..4], &[11, 29, 47, 65_535]);
    assert_eq!(audit.share_count(), T);
    assert_eq!(audit.roster_digest(), roster.digest());
    assert_ne!(audit.opening_digest(), audit.ciphertext_digest());
    assert_ne!(audit.transcript_digest(), [0; 32]);
    assert_ne!(audit.digest(), [0; 32]);
    let audit_debug = format!("{audit:?}");
    assert!(!audit_debug.contains("smudge_bits"));
    assert!(!audit_debug.contains("signature"));
    assert!(!audit_debug.contains("polys"));
    assert_eq!(
        combiner.combine_framed(&opening, &ciphertext, &framed, &params),
        Err(QuorumError::Replay)
    );

    let duplicate_keys = vec![
        keys[0].verifying_key().to_bytes(),
        keys[0].verifying_key().to_bytes(),
        keys[2].verifying_key().to_bytes(),
        keys[3].verifying_key().to_bytes(),
    ];
    assert!(matches!(
        AuthenticatedQuorumRoster::new(session, duplicate_keys),
        Err(QuorumError::DuplicatePublicKey { party: 1 })
    ));
}
