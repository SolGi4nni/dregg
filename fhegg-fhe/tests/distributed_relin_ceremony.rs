//! Teeth for the DISTRIBUTED relinearization ceremony.
//!
//! The ceremony runs on the additive-of-dealers structure `s = sum_d s_d`, not
//! on the Lagrange custody rows — see `threshold::distributed_relin` for why the
//! Lagrange composition cannot be sound. These tests drive it at the MESSAGE
//! level (the exact bytes the party processes seal and send), against a real
//! `t < n` quorum DKG, and check the two poles:
//!
//! * a key assembled from an honest full-roster ceremony actually relinearizes —
//!   verified by decrypting a `ct x ct` product through the `t`-of-`n` quorum and
//!   comparing against the plaintext product;
//! * a key is REFUSED when the ceremony is not an honest full roster: a tampered
//!   share, a share replayed from the wrong round, a short roster, a duplicated
//!   party, a share from a different ceremony, and a round-2 share computed
//!   against a round-1 aggregate the coordinator never published.
//!
//! Every mutation below is asserted to have actually changed the bytes before
//! the refusal is read, so a mutation that silently became a no-op fails the
//! test instead of passing it.

use fhe::bfv::{Encoding, Plaintext};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize as FheSerialize};
use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::bfv_mul::{BoundedCiphertext, MulEngine};
use fhegg_fhe::threshold::distributed_relin::{
    aggregate_round_1, assemble_relin_key, RelinDealerParty,
};
use fhegg_fhe::threshold::quorum::{
    combine_quorum, deal, finish_public_key, DealerRelinSecret, PrivateDealerShare,
    QuorumKeygenSession, QuorumOpeningSession, QuorumParty,
};
use fhegg_fhe::threshold::relin::{RelinError, RelinKeySession};
use fhegg_fhe::threshold::{BfvParams, CollectivePublicKey, MIN_SMUDGE_BITS};
use std::time::Duration;

const N: usize = 4;
const T: usize = 3;

struct Committee {
    params: BfvParams,
    session: QuorumKeygenSession,
    collective: CollectivePublicKey,
    parties: Vec<QuorumParty>,
    dealer_secrets: Vec<DealerRelinSecret>,
}

/// A real `t < n` quorum DKG, keeping each dealer's short secret exactly as a
/// party process would after `Dealing::own`.
fn committee(crp_seed: u8) -> Committee {
    let params = BfvParams::fold_set();
    let session =
        QuorumKeygenSession::from_seed(N, T, [crp_seed; 32]).expect("valid t-of-n session");
    let mut public = Vec::with_capacity(N);
    let mut inboxes: Vec<Vec<PrivateDealerShare>> = (0..N).map(|_| Vec::new()).collect();
    let mut dealer_secrets = Vec::with_capacity(N);

    for dealer in 0..N {
        let (contribution, private, relin_secret) = deal(&session, dealer, &params)
            .expect("dealer")
            .into_parts();
        public.push(contribution);
        dealer_secrets.push(relin_secret);
        for share in private {
            inboxes[share.recipient()].push(share);
        }
    }

    let collective = finish_public_key(&session, &public, &params).expect("collective key");
    let parties = inboxes
        .into_iter()
        .enumerate()
        .map(|(party, inbox)| {
            QuorumParty::assemble(&session, party, inbox, &params).expect("custody assembles")
        })
        .collect();

    Committee {
        params,
        session,
        collective,
        parties,
        dealer_secrets,
    }
}

fn relin_session(committee: &Committee, entropy: u8) -> RelinKeySession {
    RelinKeySession::from_public_entropy(
        committee.session.public_key_session(),
        &committee.collective,
        [entropy; 32],
        Duration::from_secs(600),
    )
    .expect("relin ceremony identity")
}

/// Every dealer's relin party, in canonical order.
fn relin_parties(committee: &Committee, session: &RelinKeySession) -> Vec<RelinDealerParty> {
    committee
        .dealer_secrets
        .iter()
        .map(|secret| {
            RelinDealerParty::new(session, &committee.params, secret).expect("relin party binds")
        })
        .collect()
}

/// Drive the full two-round ceremony and return `(round-1 aggregate, round-2
/// messages)` — exactly the bytes the coordinator holds.
fn run_ceremony(
    committee: &Committee,
    session: &RelinKeySession,
    parties: &[RelinDealerParty],
) -> (Vec<u8>, Vec<Vec<u8>>) {
    let round_1: Vec<Vec<u8>> = parties
        .iter()
        .map(|party| party.round_1().expect("round 1"))
        .collect();
    let aggregate =
        aggregate_round_1(session, &committee.params, &round_1).expect("round 1 aggregates");
    let round_2: Vec<Vec<u8>> = parties
        .iter()
        .map(|party| party.round_2(&aggregate).expect("round 2"))
        .collect();
    (aggregate, round_2)
}

fn encrypt(committee: &Committee, value: u64) -> fhe::bfv::Ciphertext {
    let mut slots = vec![0u64; committee.params.degree()];
    slots[0] = value;
    let plaintext = Plaintext::try_encode(&slots, Encoding::simd(), committee.params.arc())
        .expect("SIMD encode");
    committee
        .collective
        .pk
        .try_encrypt(&plaintext, &mut rand_09::rng())
        .expect("collective encrypt")
}

/// Open a ciphertext through a real `t`-of-`n` quorum opening.
fn open(
    committee: &mut Committee,
    ciphertext: &fhe::bfv::Ciphertext,
    plain_bound: u64,
    nonce: u8,
) -> u64 {
    let lean = LeanCiphertext::from_fhe_bytes(
        &ciphertext.to_bytes(),
        committee.params.moduli(),
        committee.params.degree(),
        plain_bound,
    )
    .expect("strict ciphertext parse");
    let roster: Vec<usize> = (0..T).collect();
    let opening = QuorumOpeningSession::new(committee.session.clone(), [nonce; 32], roster.clone())
        .expect("canonical opening");
    let shares: Vec<_> = roster
        .iter()
        .map(|&party| {
            committee.parties[party]
                .partial_decrypt(&opening, &lean, MIN_SMUDGE_BITS, &committee.params)
                .expect("custody share")
        })
        .collect();
    combine_quorum(&shares, &opening, &committee.params).expect("shares combine")[0]
}

// ── POLE 1: a valid distributed relin key actually relinearizes ──────────────

#[test]
fn a_distributed_relin_key_relinearizes_a_real_product() {
    let mut committee = committee(0x71);
    let session = relin_session(&committee, 0x11);
    let parties = relin_parties(&committee, &session);
    let (aggregate, round_2) = run_ceremony(&committee, &session, &parties);

    let key = assemble_relin_key(&session, &committee.params, &aggregate, &round_2)
        .expect("an honest full-roster ceremony assembles a key");

    // The whole point of a relin key: a ct x ct product stays decryptable.
    let (left, right) = (11u64, 13u64);
    let engine =
        MulEngine::new(&key, committee.params.arc()).expect("the relin key drives a multiplicator");
    let product = engine
        .multiply(
            &BoundedCiphertext::new(encrypt(&committee, left), 64),
            &BoundedCiphertext::new(encrypt(&committee, right), 64),
        )
        .expect("ct x ct multiply under the distributed relin key");

    let opened = open(&mut committee, &product.ct, product.plain_bound, 0x21);
    assert_eq!(
        opened,
        left * right,
        "the distributed relin key did not relinearize: a ct x ct product opened to {opened} \
         instead of {}",
        left * right
    );
}

// ── POLE 2: everything that is not an honest full-roster ceremony is REFUSED ──

/// A byte-flip deep in a round-2 share's algebraic payload.
///
/// This is the one corruption STRUCTURAL assembly cannot catch, and saying so
/// precisely is the point of this test. Aggregation checks no well-formedness
/// proof, so a flipped coefficient that still parses is a valid-looking share
/// carrying a wrong value: `assemble_relin_key` returns a key, and the fault is
/// invisible until multiply time. The acceptance gate is what refuses it, and
/// the assertions below pin BOTH halves of that — the key really is corrupt
/// (it does not relinearize), and the gate really does refuse it.
#[test]
fn a_tampered_round_two_share_is_caught_by_the_acceptance_gate() {
    let mut committee = committee(0x72);
    let session = relin_session(&committee, 0x12);
    let parties = relin_parties(&committee, &session);
    let (aggregate, mut round_2) = run_ceremony(&committee, &session, &parties);

    // Flip a byte deep inside the algebraic payload, past the header.
    let before = round_2[1].clone();
    let at = before.len() / 2;
    round_2[1][at] ^= 0xff;
    assert_ne!(
        before, round_2[1],
        "the mutation did not change the share; every verdict below would be vacuous"
    );

    let key = match assemble_relin_key(&session, &committee.params, &aggregate, &round_2) {
        // If the flip landed on a coefficient the strict poly parser rejects,
        // the structural layer catches it and there is nothing left to gate.
        Err(_) => return,
        Ok(key) => key,
    };

    // The key assembled. Show it is genuinely corrupt before claiming the gate
    // earned anything: a correct key would open this product to 11 * 13.
    let engine =
        MulEngine::new(&key, committee.params.arc()).expect("a corrupt key still builds an engine");
    let product = engine
        .multiply(
            &BoundedCiphertext::new(encrypt(&committee, 11), 64),
            &BoundedCiphertext::new(encrypt(&committee, 13), 64),
        )
        .expect("ct x ct multiply");
    let opened = open(&mut committee, &product.ct, product.plain_bound, 0x22);
    assert_ne!(
        opened,
        11 * 13,
        "the tampered share produced a key that relinearizes correctly; the mutation was a no-op \
         and the gate below would be proving nothing"
    );

    // THE REFUSAL. Fresh random trials, opened through the real t-of-n quorum.
    let mut nonce = 0x30u8;
    let params = committee.params.clone();
    let collective = committee.collective.clone();
    let refused = fhegg_fhe::threshold::distributed_relin::relin_acceptance_gate(
        &key,
        &params,
        &collective,
        8,
        |bounded| {
            nonce = nonce.wrapping_add(1);
            Ok(open(
                &mut committee,
                &bounded.ct,
                bounded.plain_bound,
                nonce,
            ))
        },
    );
    assert!(
        matches!(refused, Err(RelinError::AcceptanceFailed { .. })),
        "the acceptance gate passed a relin key built from a tampered share: {refused:?}"
    );
}

/// The other pole of the gate: an HONEST key must pass it, or the gate is just a
/// refusal machine and proves nothing about the tampered case above.
#[test]
fn an_honest_distributed_relin_key_passes_the_acceptance_gate() {
    let mut committee = committee(0x77);
    let session = relin_session(&committee, 0x18);
    let parties = relin_parties(&committee, &session);
    let (aggregate, round_2) = run_ceremony(&committee, &session, &parties);
    let key = assemble_relin_key(&session, &committee.params, &aggregate, &round_2)
        .expect("honest ceremony");

    let mut nonce = 0x40u8;
    let params = committee.params.clone();
    let collective = committee.collective.clone();
    fhegg_fhe::threshold::distributed_relin::relin_acceptance_gate(
        &key,
        &params,
        &collective,
        8,
        |bounded| {
            nonce = nonce.wrapping_add(1);
            Ok(open(
                &mut committee,
                &bounded.ct,
                bounded.plain_bound,
                nonce,
            ))
        },
    )
    .expect("an honest distributed relin key must pass its own acceptance gate");
}

#[test]
fn a_round_one_share_replayed_as_round_two_is_refused() {
    let committee = committee(0x73);
    let session = relin_session(&committee, 0x13);
    let parties = relin_parties(&committee, &session);
    let (aggregate, mut round_2) = run_ceremony(&committee, &session, &parties);

    let replayed = parties[2].round_1().expect("a fresh round-1 share");
    assert_ne!(
        round_2[2], replayed,
        "the replay is byte-identical to the round-2 share it replaces"
    );
    round_2[2] = replayed;

    assert_eq!(
        assemble_relin_key(&session, &committee.params, &aggregate, &round_2).unwrap_err(),
        RelinError::PhaseMismatch,
        "a round-1 share was accepted where a round-2 share belongs"
    );
}

#[test]
fn a_short_roster_and_a_duplicated_party_are_both_refused() {
    let committee = committee(0x74);
    let session = relin_session(&committee, 0x14);
    let parties = relin_parties(&committee, &session);
    let (aggregate, round_2) = run_ceremony(&committee, &session, &parties);

    // Relin is n-of-n: a missing party is not a smaller quorum, it is a key that
    // decrypts to garbage. It must refuse, not degrade.
    let short = &round_2[..N - 1];
    assert!(
        matches!(
            assemble_relin_key(&session, &committee.params, &aggregate, short),
            Err(RelinError::QuorumTooSmall { have, need }) if have == N - 1 && need == N
        ),
        "an incomplete relin roster assembled a key"
    );

    let mut duplicated = round_2[..N - 1].to_vec();
    duplicated.push(round_2[0].clone());
    assert_eq!(
        assemble_relin_key(&session, &committee.params, &aggregate, &duplicated).unwrap_err(),
        RelinError::DuplicateParty { party: 0 },
        "one party counted twice stood in for the missing one"
    );
}

#[test]
fn a_share_from_a_different_ceremony_is_refused() {
    let committee = committee(0x75);
    let session = relin_session(&committee, 0x15);
    let parties = relin_parties(&committee, &session);
    let (aggregate, mut round_2) = run_ceremony(&committee, &session, &parties);

    // A SECOND ceremony over the same committee and the same secrets, differing
    // only in its public entropy. Its shares are well formed, correctly signed
    // by a real party, and belong to the wrong key.
    let other_session = relin_session(&committee, 0x16);
    assert_ne!(
        session.session_id(),
        other_session.session_id(),
        "the two ceremonies collapsed to one identity"
    );
    let other_parties = relin_parties(&committee, &other_session);
    let (_, other_round_2) = run_ceremony(&committee, &other_session, &other_parties);

    assert_ne!(round_2[3], other_round_2[3]);
    round_2[3] = other_round_2[3].clone();

    assert!(
        matches!(
            assemble_relin_key(&session, &committee.params, &aggregate, &round_2),
            Err(RelinError::SessionMismatch { .. })
        ),
        "a share from a different relin ceremony was folded into this key"
    );
}

#[test]
fn a_round_two_share_answering_an_unpublished_aggregate_is_refused() {
    let committee = committee(0x76);
    let session = relin_session(&committee, 0x17);
    let parties = relin_parties(&committee, &session);
    let (aggregate, mut round_2) = run_ceremony(&committee, &session, &parties);

    // A second, equally well-formed round-1 aggregate over the SAME ceremony:
    // fresh smoothing noise makes it differ from the published one. Upstream's
    // assembler reads the carried aggregate from the first share it sees and
    // never compares the rest, so without the explicit check this share is
    // folded in silently.
    let divergent_round_1: Vec<Vec<u8>> = parties
        .iter()
        .map(|party| party.round_1().expect("round 1"))
        .collect();
    let divergent =
        aggregate_round_1(&session, &committee.params, &divergent_round_1).expect("aggregates");
    assert_ne!(
        aggregate, divergent,
        "the two round-1 aggregates are identical; this test would be vacuous"
    );

    round_2[1] = parties[1].round_2(&divergent).expect("round 2");

    assert_eq!(
        assemble_relin_key(&session, &committee.params, &aggregate, &round_2).unwrap_err(),
        RelinError::RoundOneAggregateMismatch { party: 1 },
        "a party answering an aggregate the coordinator never published was folded in"
    );
}
