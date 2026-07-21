//! Hostile gate for authority-certified PartyMPC preprocessing.
//!
//! The underlying authority remains a trusted Beaver dealer.  This gate proves
//! a narrower property with live protocol consequences: after that authority
//! checks every global GF(2) relation and signs the ordered row commitments, a
//! router or custody peer cannot mutate, relabel, replay across a context, or
//! equivocate one row into another certified session before the MPC output is
//! formed.

use std::thread;
use std::time::Duration;

use ed25519_dalek::SigningKey;
use fhegg_fhe::mpc_party::transport::{
    EqualityPartyMachine, EqualityTransportError, EqualityTransportRoster,
};
use fhegg_fhe::mpc_party::{
    certified_dealer_triples, local_channels, run_party_equality, PartyEqualityInput,
    PartyMpcError, PartyMpcSession, TripleMaterial,
};
use rand::rngs::StdRng;
use rand::SeedableRng;

const N: usize = 3;
const MODULUS: u64 = 257;

fn base_session(tag: u8) -> PartyMpcSession {
    PartyMpcSession::equality([tag; 32], N, 8, MODULUS, Duration::from_secs(2)).unwrap()
}

fn certified_batch(
    base: &PartyMpcSession,
    seed: u64,
) -> fhegg_fhe::mpc_party::CertifiedTripleBatch {
    let authority = SigningKey::from_bytes(&[0x41; 32]);
    certified_dealer_triples(base, &mut StdRng::seed_from_u64(seed), &authority).unwrap()
}

#[test]
fn certified_rows_complete_honest_equality_and_bind_the_exact_batch() {
    let base = base_session(0x71);
    let batch = certified_batch(&base, 0x7172);
    let (session, certificate, materials) = batch.into_parts();
    session.require_certified_preprocessing().unwrap();
    assert_eq!(certificate.n_parties(), N);
    assert_eq!(certificate.gates(), session.exact_and_gates());
    assert_eq!(certificate.row_commitments().len(), N);
    assert_eq!(
        session.preprocessing_binding().unwrap().1,
        certificate.digest()
    );

    // Exercise the protected-custody parser, not only in-memory dealer output.
    let wires = materials
        .iter()
        .map(|material| material.to_wire_bytes().unwrap())
        .collect::<Vec<_>>();
    let materials = wires
        .iter()
        .enumerate()
        .map(|(party, wire)| TripleMaterial::from_wire_bytes(&session, party, wire).unwrap())
        .collect::<Vec<_>>();

    // Equal modulo t: 20+30+27 = 10+11+56 = 77.
    let left = [20, 30, 27];
    let right = [10, 11, 56];
    let inputs = (0..N)
        .map(|party| {
            PartyEqualityInput::new(
                &session,
                party,
                left[party],
                right[party],
                &mut StdRng::seed_from_u64(0x7200 + party as u64),
            )
            .unwrap()
        })
        .collect::<Vec<_>>();
    let (coordinator, endpoints) = local_channels(&session);
    let parties = inputs
        .into_iter()
        .zip(materials)
        .zip(endpoints)
        .map(|((input, triples), endpoint)| {
            thread::spawn(move || run_party_equality(input, triples, endpoint))
        })
        .collect::<Vec<_>>();
    let decision = coordinator.coordinate_equality(&session).unwrap();
    assert!(decision.is_equal());
    for party in parties {
        let report = party.join().unwrap().unwrap();
        assert_eq!(report.and_gates, session.exact_and_gates());
    }
}

#[test]
fn malformed_relabelled_replayed_and_equivocated_rows_refuse_before_a_gate() {
    let base_a = base_session(0x81);
    let batch_a = certified_batch(&base_a, 0x8182);
    let (session_a, certificate_a, materials_a) = batch_a.into_parts();
    let wires_a = materials_a
        .iter()
        .map(|material| material.to_wire_bytes().unwrap())
        .collect::<Vec<_>>();

    // The last byte is the c-share of the final AND gate.  This is the exact
    // mutation that flips the equality decision on the legacy path while all
    // bits and framing remain canonical.  The signed row commitment rejects it
    // before the material can enter a party machine.
    let mut malformed_relation = wires_a[0].clone();
    *malformed_relation.last_mut().unwrap() ^= 1;
    assert!(matches!(
        TripleMaterial::from_wire_bytes(&session_a, 0, &malformed_relation),
        Err(PartyMpcError::InvalidTripleFormationCertificate)
    ));

    // The authority signature is checked independently of the row hash.
    let signature_offset = 8 + 32 + 32 + 8 + 8 + N * 32 + 32;
    let mut forged_certificate = wires_a[0].clone();
    forged_certificate[signature_offset] ^= 1;
    assert!(matches!(
        TripleMaterial::from_wire_bytes(&session_a, 0, &forged_certificate),
        Err(PartyMpcError::InvalidTripleFormationCertificate)
    ));

    assert!(matches!(
        TripleMaterial::from_wire_bytes(&session_a, 1, &wires_a[0]),
        Err(PartyMpcError::SessionMismatch)
    ));

    let base_b = base_session(0x82);
    let batch_b = certified_batch(&base_b, 0x8283);
    let (session_b, certificate_b, mut materials_b) = batch_b.into_parts();
    assert_ne!(certificate_a.digest(), certificate_b.digest());
    assert!(matches!(
        TripleMaterial::from_wire_bytes(&session_b, 0, &wires_a[0]),
        Err(PartyMpcError::SessionMismatch)
    ));

    // Even under the same public base session, a fresh batch has a distinct
    // session identity. Mixing its valid party-0 row into batch A fails before
    // input ingress or the first Beaver opening.
    let same_context_batch = certified_batch(&base_a, 0x8384);
    let (same_context_session, _, mut same_context_materials) = same_context_batch.into_parts();
    assert_ne!(
        session_a.preprocessing_binding(),
        same_context_session.preprocessing_binding()
    );
    let input_a =
        PartyEqualityInput::new(&session_a, 0, 20, 10, &mut StdRng::seed_from_u64(0x8485)).unwrap();
    let (_coordinator, mut endpoints) = local_channels(&session_a);
    let error = run_party_equality(
        input_a,
        same_context_materials.remove(0),
        endpoints.remove(0),
    )
    .unwrap_err();
    assert_eq!(error, PartyMpcError::SessionMismatch);

    // Positive control: the other context's own certified row still parses;
    // refusals above did not poison unrelated material.
    let wire_b = materials_b.remove(0).to_wire_bytes().unwrap();
    TripleMaterial::from_wire_bytes(&session_b, 0, &wire_b).unwrap();
}

#[test]
fn authenticated_peer_frames_cannot_cross_certified_batch_domains() {
    let base = base_session(0x91);
    let (session_a, _, mut materials_a) = certified_batch(&base, 0x9192).into_parts();
    let (session_b, _, mut materials_b) = certified_batch(&base, 0x9293).into_parts();
    assert_ne!(
        session_a.preprocessing_binding(),
        session_b.preprocessing_binding()
    );

    let keys = [
        SigningKey::from_bytes(&[0x51; 32]),
        SigningKey::from_bytes(&[0x52; 32]),
        SigningKey::from_bytes(&[0x53; 32]),
    ];
    let coordinator = SigningKey::from_bytes(&[0x54; 32]);
    let roster = EqualityTransportRoster::new(
        keys.iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        coordinator.verifying_key().to_bytes(),
    )
    .unwrap();
    let input_a =
        PartyEqualityInput::new(&session_a, 0, 20, 10, &mut StdRng::seed_from_u64(0x9394)).unwrap();
    let input_b =
        PartyEqualityInput::new(&session_b, 1, 30, 11, &mut StdRng::seed_from_u64(0x9495)).unwrap();
    let mut party_a = EqualityPartyMachine::new(
        session_a,
        roster.clone(),
        0,
        keys[0].clone(),
        input_a,
        materials_a.remove(0),
    )
    .unwrap();
    let mut party_b = EqualityPartyMachine::new(
        session_b,
        roster,
        1,
        keys[1].clone(),
        input_b,
        materials_b.remove(1),
    )
    .unwrap();

    let deadline = std::time::Instant::now() + Duration::from_secs(1);
    let frame_for_b = loop {
        assert!(
            std::time::Instant::now() < deadline,
            "party A did not emit its certified-session peer ingress"
        );
        if let Some(frame) = party_a.try_next_frame().unwrap() {
            if frame.recipient() == 1 {
                break frame;
            }
        }
        thread::yield_now();
    };
    assert_eq!(
        party_b.accept_frame(frame_for_b.as_bytes()),
        Err(EqualityTransportError::SessionMismatch)
    );
}
