//! Executable rung toward malicious PartyMPC preprocessing.
//!
//! PartyMPC v3 authenticates and encrypts process traffic and can reconstruct
//! the public decision transcript from the exact signed frames.  That is not a
//! proof that the secret Beaver rows were formed correctly: the protected
//! `TripleMaterial` codec deliberately checks only session/shape/canonical bits.
//!
//! This test supplies the strongest check available without changing that
//! runtime boundary.  A trusted preprocessing auditor opens the complete
//! protected roster once, checks every global GF(2) Beaver relation
//! `xor(c_i) = xor(a_i) & xor(b_i)`, and emits only salted row commitments plus
//! a canonical certificate digest.  The salts and rows stay protected.  A
//! relying process can later re-open the same protected material and require
//! exact certificate equality before provisioning it.
//!
//! This is intentionally not called malicious-secure MPC.  The auditor sees
//! the preprocessing, a malicious dealer can still know otherwise-valid
//! triples, and no proof here binds operand shares or each online gate's hidden
//! wires to those triples.  Dealer-free preprocessing/sacrifice or ZK/MAC
//! proofs, input provenance, and worker/Dark-AMM wiring remain separate work.

use std::thread;
use std::time::{Duration, Instant};

use ed25519_dalek::SigningKey;
use fhegg_fhe::mpc_party::transport::{
    verify_public_decision_transcript, EqualityCoordinatorMachine, EqualityPartyMachine,
    EqualityTransportRoster,
};
use fhegg_fhe::mpc_party::{
    trusted_dealer_triples, DistributedDecisionRun, PartyEqualityInput, PartyMpcError,
    PartyMpcSession, TripleMaterial,
};
use rand::rngs::StdRng;
use rand::SeedableRng;
use sha2::{Digest, Sha256};

const N: usize = 3;
const VALUE_BITS: usize = 8;
const MODULUS: u64 = 257;
// magic + nonce + (parties,buckets,value-bits,modulus,timeout-secs) +
// timeout-nanos + circuit + (party,count)
const TRIPLE_WIRE_HEADER_BYTES: usize = 8 + 32 + 8 * 5 + 4 + 1 + 8 * 2;
const TRIPLE_ROW_COMMITMENT_DOMAIN: &[u8] = b"fhegg/party-mpc-triple-row-commitment/v1";
const TRIPLE_FORMATION_CERTIFICATE_DOMAIN: &[u8] =
    b"fhegg/party-mpc-triple-formation-certificate/v1";

#[derive(Clone, Debug, PartialEq, Eq)]
struct TripleFormationCertificate {
    session_nonce: [u8; 32],
    parties: usize,
    gates: usize,
    row_commitments: Vec<[u8; 32]>,
    digest: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TripleFormationError {
    RosterSize { have: usize, need: usize },
    SaltCount { have: usize, need: usize },
    CanonicalRow { party: usize, error: PartyMpcError },
    InvalidRelation { gate: usize, a: u8, b: u8, c: u8 },
    ArithmeticOverflow,
    CertificateMismatch,
}

/// Verify the complete protected preprocessing roster and commit to its exact
/// canonical rows without publishing either a row or its hiding salt.
fn audit_triple_formation(
    session: &PartyMpcSession,
    protected_rows: &[Vec<u8>],
    hiding_salts: &[[u8; 32]],
) -> Result<TripleFormationCertificate, TripleFormationError> {
    if protected_rows.len() != session.n_parties() {
        return Err(TripleFormationError::RosterSize {
            have: protected_rows.len(),
            need: session.n_parties(),
        });
    }
    if hiding_salts.len() != session.n_parties() {
        return Err(TripleFormationError::SaltCount {
            have: hiding_salts.len(),
            need: session.n_parties(),
        });
    }

    let gates = session.exact_and_gates();
    let triple_bytes = gates
        .checked_mul(3)
        .ok_or(TripleFormationError::ArithmeticOverflow)?;
    let expected_len = TRIPLE_WIRE_HEADER_BYTES
        .checked_add(triple_bytes)
        .ok_or(TripleFormationError::ArithmeticOverflow)?;
    let mut triples_by_party = Vec::with_capacity(session.n_parties());
    let mut row_commitments = Vec::with_capacity(session.n_parties());

    for (party, (wire, salt)) in protected_rows.iter().zip(hiding_salts).enumerate() {
        // Reuse the shipping codec as the first gate.  It checks the complete
        // session (including circuit kind and timeout), exact party slot/count,
        // canonical bits, bounded length, and exact EOF.
        TripleMaterial::from_wire_bytes(session, party, wire)
            .map(drop)
            .map_err(|error| TripleFormationError::CanonicalRow { party, error })?;
        if wire.len() != expected_len {
            return Err(TripleFormationError::CanonicalRow {
                party,
                error: PartyMpcError::MalformedTripleMaterialWire,
            });
        }
        triples_by_party.push(&wire[TRIPLE_WIRE_HEADER_BYTES..]);

        let mut commitment = Sha256::new();
        commitment.update((TRIPLE_ROW_COMMITMENT_DOMAIN.len() as u64).to_be_bytes());
        commitment.update(TRIPLE_ROW_COMMITMENT_DOMAIN);
        commitment.update(session.nonce());
        commitment.update((party as u64).to_be_bytes());
        commitment.update((gates as u64).to_be_bytes());
        commitment.update(salt);
        commitment.update((wire.len() as u64).to_be_bytes());
        commitment.update(wire);
        row_commitments.push(commitment.finalize().into());
    }

    for gate in 0..gates {
        let offset = gate * 3;
        let mut a = 0u8;
        let mut b = 0u8;
        let mut c = 0u8;
        for triples in &triples_by_party {
            a ^= triples[offset];
            b ^= triples[offset + 1];
            c ^= triples[offset + 2];
        }
        if c != (a & b) {
            return Err(TripleFormationError::InvalidRelation { gate, a, b, c });
        }
    }

    let mut certificate = Sha256::new();
    certificate.update((TRIPLE_FORMATION_CERTIFICATE_DOMAIN.len() as u64).to_be_bytes());
    certificate.update(TRIPLE_FORMATION_CERTIFICATE_DOMAIN);
    certificate.update(session.nonce());
    certificate.update((session.n_parties() as u64).to_be_bytes());
    certificate.update((session.buckets() as u64).to_be_bytes());
    certificate.update((session.value_bits() as u64).to_be_bytes());
    certificate.update(session.plaintext_modulus().to_be_bytes());
    certificate.update((gates as u64).to_be_bytes());
    certificate.update((row_commitments.len() as u64).to_be_bytes());
    for commitment in &row_commitments {
        certificate.update(commitment);
    }
    Ok(TripleFormationCertificate {
        session_nonce: session.nonce(),
        parties: session.n_parties(),
        gates,
        row_commitments,
        digest: certificate.finalize().into(),
    })
}

fn verify_triple_formation_certificate(
    expected: &TripleFormationCertificate,
    session: &PartyMpcSession,
    protected_rows: &[Vec<u8>],
    hiding_salts: &[[u8; 32]],
) -> Result<(), TripleFormationError> {
    let actual = audit_triple_formation(session, protected_rows, hiding_salts)?;
    if &actual == expected {
        Ok(())
    } else {
        Err(TripleFormationError::CertificateMismatch)
    }
}

fn session(tag: u8) -> PartyMpcSession {
    PartyMpcSession::equality([tag; 32], N, VALUE_BITS, MODULUS, Duration::from_secs(5)).unwrap()
}

fn triple_rows(session: &PartyMpcSession, seed: u64) -> Vec<Vec<u8>> {
    let mut dealer = StdRng::seed_from_u64(seed);
    trusted_dealer_triples(session, &mut dealer)
        .unwrap()
        .into_iter()
        .map(|material| material.to_wire_bytes().unwrap())
        .collect()
}

fn hiding_salts(tag: u8) -> [[u8; 32]; N] {
    [
        [tag; 32],
        [tag.wrapping_add(1); 32],
        [tag.wrapping_add(2); 32],
    ]
}

fn toggle_triple_share(rows: &mut [Vec<u8>], party: usize, gate: usize, component: usize) {
    assert!(party < rows.len());
    assert!(component < 3);
    rows[party][TRIPLE_WIRE_HEADER_BYTES + gate * 3 + component] ^= 1;
}

fn transport_fixture() -> (Vec<[u8; 32]>, [u8; 32], EqualityTransportRoster) {
    let party_seeds = vec![[0x31; 32], [0x32; 32], [0x33; 32]];
    let coordinator_seed = [0x41; 32];
    let party_public_keys = party_seeds
        .iter()
        .map(|seed| SigningKey::from_bytes(seed).verifying_key().to_bytes())
        .collect();
    let coordinator_public_key = SigningKey::from_bytes(&coordinator_seed)
        .verifying_key()
        .to_bytes();
    let roster = EqualityTransportRoster::new(party_public_keys, coordinator_public_key).unwrap();
    (party_seeds, coordinator_seed, roster)
}

fn drive_authenticated_equality(
    session: &PartyMpcSession,
    protected_rows: Vec<Vec<u8>>,
    left: [u64; N],
    right: [u64; N],
) -> (
    DistributedDecisionRun,
    Vec<Vec<u8>>,
    EqualityTransportRoster,
) {
    let (party_seeds, coordinator_seed, roster) = transport_fixture();
    let mut parties = protected_rows
        .into_iter()
        .enumerate()
        .map(|(party, wire)| {
            let material = TripleMaterial::from_wire_bytes(session, party, &wire).unwrap();
            let mut ingress_rng = StdRng::seed_from_u64(0x5100 ^ party as u64);
            let input = PartyEqualityInput::new(
                session,
                party,
                left[party],
                right[party],
                &mut ingress_rng,
            )
            .unwrap();
            EqualityPartyMachine::new(
                session.clone(),
                roster.clone(),
                party,
                SigningKey::from_bytes(&party_seeds[party]),
                input,
                material,
            )
            .unwrap()
        })
        .collect::<Vec<_>>();
    let mut coordinator = EqualityCoordinatorMachine::new(
        session.clone(),
        roster.clone(),
        SigningKey::from_bytes(&coordinator_seed),
    )
    .unwrap();

    let mut authenticated_public_frames = Vec::new();
    let mut party_done = vec![false; session.n_parties()];
    let mut decision = None;
    let deadline = Instant::now() + Duration::from_secs(10);
    while decision.is_none() || party_done.iter().any(|done| !done) {
        let mut outbound = Vec::new();
        for machine in &mut parties {
            while let Some(frame) = machine.try_next_frame().unwrap() {
                outbound.push(frame);
            }
        }
        for frame in outbound {
            if frame.recipient() == roster.coordinator() {
                authenticated_public_frames.push(frame.as_bytes().to_vec());
                coordinator.accept_frame(frame.as_bytes()).unwrap();
            } else {
                parties[frame.recipient()]
                    .accept_frame(frame.as_bytes())
                    .unwrap();
            }
        }

        while let Some(frame) = coordinator.try_next_frame().unwrap() {
            parties[frame.recipient()]
                .accept_frame(frame.as_bytes())
                .unwrap();
        }
        for (party, machine) in parties.iter_mut().enumerate() {
            if !party_done[party] {
                if let Some(report) = machine.try_result().unwrap() {
                    assert_eq!(report.party, party);
                    assert_eq!(report.and_gates, session.exact_and_gates());
                    party_done[party] = true;
                }
            }
        }
        if decision.is_none() {
            decision = coordinator.try_result().unwrap();
        }
        assert!(
            Instant::now() < deadline,
            "authenticated equality with audited preprocessing timed out"
        );
        thread::yield_now();
    }

    (decision.unwrap(), authenticated_public_frames, roster)
}

#[test]
fn triple_formation_certificate_binds_every_canonical_row_and_relation() {
    let mpc_session = session(0x71);
    let salts = hiding_salts(0x81);
    let rows = triple_rows(&mpc_session, 0x7172);
    let certificate = audit_triple_formation(&mpc_session, &rows, &salts).unwrap();
    assert_eq!(certificate.session_nonce, mpc_session.nonce());
    assert_eq!(certificate.parties, N);
    assert_eq!(certificate.gates, mpc_session.exact_and_gates());
    assert_eq!(certificate.row_commitments.len(), N);
    verify_triple_formation_certificate(&certificate, &mpc_session, &rows, &salts).unwrap();

    // A relation-preserving substitution is invisible to the bare Beaver
    // equation: changing the same a-share in two rows preserves xor(a), hence
    // preserves c=a&b.  The salted per-row commitments still make it refuse.
    let mut relation_preserving_substitution = rows.clone();
    toggle_triple_share(&mut relation_preserving_substitution, 0, 0, 0);
    toggle_triple_share(&mut relation_preserving_substitution, 1, 0, 0);
    audit_triple_formation(&mpc_session, &relation_preserving_substitution, &salts).unwrap();
    assert_eq!(
        verify_triple_formation_certificate(
            &certificate,
            &mpc_session,
            &relation_preserving_substitution,
            &salts,
        ),
        Err(TripleFormationError::CertificateMismatch)
    );

    let mut substituted_salts = salts;
    substituted_salts[2][0] ^= 1;
    assert_eq!(
        verify_triple_formation_certificate(&certificate, &mpc_session, &rows, &substituted_salts,),
        Err(TripleFormationError::CertificateMismatch)
    );

    let mut reordered = rows.clone();
    reordered.swap(0, 1);
    assert!(matches!(
        audit_triple_formation(&mpc_session, &reordered, &salts),
        Err(TripleFormationError::CanonicalRow { party: 0, .. })
    ));

    let other_session = session(0x72);
    assert!(matches!(
        audit_triple_formation(&other_session, &rows, &salts),
        Err(TripleFormationError::CanonicalRow { party: 0, .. })
    ));
}

#[test]
fn malformed_beaver_relation_passes_v3_framing_and_flips_equality_but_audit_refuses() {
    let session = session(0x91);
    let salts = hiding_salts(0xa1);
    let mut rows = triple_rows(&session, 0x9192);
    let final_gate = session.exact_and_gates() - 1;

    // The final gate is the last prefix-equality AND. Flipping one party's c
    // share preserves the current protected codec (all fields/bits remain
    // canonical) but makes the global Beaver relation false and flips the
    // reconstructed equality bit.
    toggle_triple_share(&mut rows, 0, final_gate, 2);
    TripleMaterial::from_wire_bytes(&session, 0, &rows[0]).unwrap();
    let Err(TripleFormationError::InvalidRelation { gate, a, b, c }) =
        audit_triple_formation(&session, &rows, &salts)
    else {
        panic!("the malformed final triple must fail the formation audit");
    };
    assert_eq!(gate, final_gate);
    assert_ne!(c, a & b);

    let left = [20, 30, 27];
    let right = [10, 11, 56];
    assert_eq!(
        left.iter().sum::<u64>() % MODULUS,
        right.iter().sum::<u64>() % MODULUS
    );
    let (decision, authenticated_frames, roster) =
        drive_authenticated_equality(&session, rows, left, right);

    // The v3 verifier correctly proves that the public transcript came from
    // the exact authenticated frames. It cannot prove the hidden triple was
    // well formed, so it accepts this internally consistent false decision.
    verify_public_decision_transcript(
        &session,
        &roster,
        &authenticated_frames,
        &decision.transcript,
    )
    .unwrap();
    assert!(
        !decision.is_equal(),
        "the malformed final triple must be a live falsifier"
    );
    assert_eq!(decision.transcript.revealed_equal, 0);
}
