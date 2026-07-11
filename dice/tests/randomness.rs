//! Non-vacuous verification tests for dregg-dice.
//!
//! These exercise the load-bearing properties: deterministic stream
//! reproduction, grinding detection (a changed `draw_count` diverges), skipped/
//! extra-index detection, an unbiased + reject-free bounded mapping, and the
//! CommitReveal round-trip incl. tamper rejection. The trust-level caveat
//! (selective abort is NOT prevented by CommitReveal) is asserted structurally
//! below.

use dregg_dice::{
    Beacon, BeaconKind, BeaconParams, BeaconSchedule, CommitReveal, Deterministic, DrawError,
    DrawStream, EventId, EvidenceKind, Finalization, FinalizeMode, HashChainBeacon, Hybrid,
    KeyChain, MockBeacon, RandomnessEvidence, RandomnessRequest, RandomnessSource, Seed, ServerVrf,
    VerifyError, VrfEvalError, verify_beacon_round, verify_epoch_membership,
};

fn sample_request(draw_count: u32) -> RandomnessRequest {
    RandomnessRequest {
        game_binding: b"game/epoch-7".to_vec(),
        seq: 42,
        pre_state_root: [0x11; 32],
        action_hash: [0x22; 32],
        event_kind: "combat/hit".to_string(),
        draw_count,
    }
}

// ── Draw stream: a verifier reproduces the full stream from (seed, index). ──

#[test]
fn draw_stream_is_deterministic_and_reproducible() {
    let seed = Seed::from_bytes([0x5a; 32]);
    let a = DrawStream::new(seed, 8);
    let b = DrawStream::new(seed, 8); // an independent "verifier" reconstruction

    for i in 0..8 {
        assert_eq!(
            a.draw(i).unwrap(),
            b.draw(i).unwrap(),
            "same (seed,index) must yield the same draw"
        );
    }
    // Different indices produce different draws (stream is not constant).
    assert_ne!(a.draw(0).unwrap(), a.draw(1).unwrap());
    // A different seed produces a different stream.
    let other = DrawStream::new(Seed::from_bytes([0x5b; 32]), 8);
    assert_ne!(a.draw(0).unwrap(), other.draw(0).unwrap());
}

// ── Grinding detection: a changed draw_count changes the EventId, so the
//    evidence produced for the original count fails verification. ──

#[test]
fn changed_draw_count_changes_event_id() {
    let base = sample_request(3);
    let mut grinded = base.clone();
    grinded.draw_count = 4;
    assert_ne!(
        base.event_id().as_bytes(),
        grinded.event_id().as_bytes(),
        "draw_count is bound into the EventId"
    );
    // The same holds for event_kind (subsystem domain separation).
    let mut other_kind = base.clone();
    other_kind.event_kind = "loot".to_string();
    assert_ne!(base.event_id().as_bytes(), other_kind.event_id().as_bytes());
}

#[test]
fn grinding_draw_count_fails_verification() {
    // Server produces honest evidence for a 3-draw event.
    let req = sample_request(3);
    let src = CommitReveal {
        server_reveal: [0xaa; 32],
        player_contribution: [0xbb; 32],
    };
    let ev = src.evidence(&req);

    // Honest verification succeeds.
    let seed = CommitReveal::seed(&req, &ev).expect("honest evidence verifies");

    // An attacker re-presents the SAME evidence against a request with a
    // different draw_count (hoping to consume a different, favorable stream).
    // The EventId moves → the re-derived seed moves → the transcript no longer
    // matches → detected.
    let mut grinded_req = req.clone();
    grinded_req.draw_count = 5;
    assert_eq!(
        CommitReveal::seed(&grinded_req, &ev),
        Err(VerifyError::TranscriptMismatch),
        "grinding draw_count must be detected"
    );

    // Sanity: the honest seed does reproduce the committed transcript.
    let stream = DrawStream::new(seed, req.draw_count);
    assert_eq!(
        stream.transcript_commitment(),
        ev.draw_transcript_commitment
    );
}

// ── Skipped/extra index is detectable. ──

#[test]
fn out_of_range_index_is_rejected() {
    let stream = DrawStream::new(Seed::from_bytes([1; 32]), 3);
    assert!(stream.draw(0).is_ok());
    assert!(stream.draw(2).is_ok());
    assert_eq!(
        stream.draw(3),
        Err(DrawError::IndexOutOfRange {
            index: 3,
            draw_count: 3
        }),
        "index == draw_count is out of range"
    );
}

#[test]
fn extra_or_skipped_draw_changes_transcript() {
    let seed = Seed::from_bytes([7; 32]);
    let three = DrawStream::new(seed, 3).transcript_commitment();
    let four = DrawStream::new(seed, 4).transcript_commitment(); // one extra draw
    let two = DrawStream::new(seed, 2).transcript_commitment(); // one skipped draw
    assert_ne!(three, four, "an extra draw changes the transcript");
    assert_ne!(three, two, "a skipped draw changes the transcript");
}

// ── Bounded mapping: unbiased + reject-free + deterministic. ──

#[test]
fn bounded_mapping_is_deterministic() {
    let seed = Seed::from_bytes([0x99; 32]);
    let s1 = DrawStream::new(seed, 100);
    let s2 = DrawStream::new(seed, 100);
    for i in 0..100 {
        assert_eq!(
            s1.draw_bounded(i, 20).unwrap(),
            s2.draw_bounded(i, 20).unwrap()
        );
        // Range respected.
        assert!(s1.draw_bounded(i, 20).unwrap() < 20);
        // Die convenience is 1-based.
        let d = s1.draw_die(i, 6).unwrap();
        assert!((1..=6).contains(&d));
    }
    assert_eq!(s1.draw_bounded(0, 0), Err(DrawError::ZeroBound));
}

#[test]
fn bounded_mapping_is_unbiased_and_reject_free() {
    // Roll a d6 sixty thousand times via distinct indices. The wide
    // multiply-and-shift mapping consumes EXACTLY ONE raw draw per index (no
    // rejection loop), so the number of draws is a public constant `n` — this is
    // what lets draw_count be bound up front. Verify the outputs are near-uniform.
    const N: u32 = 60_000;
    const SIDES: u64 = 6;
    let stream = DrawStream::new(Seed::from_bytes([0x42; 32]), N);

    let mut buckets = [0u64; SIDES as usize];
    for i in 0..N {
        // draw_die is 1..=6; index into 0..6.
        let face = stream.draw_die(i, SIDES).unwrap();
        assert!((1..=SIDES).contains(&face));
        buckets[(face - 1) as usize] += 1;
    }

    // Every face appears (reject-free coverage) and total is exactly N (one draw
    // consumed per index — no draw was discarded).
    let total: u64 = buckets.iter().sum();
    assert_eq!(
        total, N as u64,
        "exactly one outcome per draw — reject-free"
    );
    assert!(buckets.iter().all(|&c| c > 0), "every face must appear");

    // Chi-square goodness-of-fit against uniform. Expected = N/6 = 10000 per face.
    // df = 5; the 0.1% critical value is ~20.5, 0.01% is ~25.7. The stream is
    // deterministic (fixed seed), so this is a stable, non-flaky assertion; a
    // biased mapping (e.g. `x % 6`) would inflate this well past the threshold.
    let expected = N as f64 / SIDES as f64;
    let chi2: f64 = buckets
        .iter()
        .map(|&c| {
            let d = c as f64 - expected;
            d * d / expected
        })
        .sum();
    assert!(
        chi2 < 20.5,
        "d6 distribution not uniform enough: chi2 = {chi2:.3} (buckets = {buckets:?})"
    );

    // Each bucket within 5% of expected — a coarse eyeball backstop.
    for &c in &buckets {
        let dev = (c as f64 - expected).abs() / expected;
        assert!(dev < 0.05, "bucket deviates {:.3} from uniform", dev);
    }
}

// ── CommitReveal round-trip + tamper rejection. ──

#[test]
fn commit_reveal_round_trip() {
    let req = sample_request(4);
    let src = CommitReveal {
        server_reveal: [0xc0; 32],
        player_contribution: [0x0d; 32],
    };
    let ev = src.evidence(&req);

    // Evidence carries the published commitment (server committed before reveal).
    match &ev.source {
        EvidenceKind::CommitReveal {
            server_commitment,
            server_reveal,
            ..
        } => {
            assert_eq!(*server_commitment, CommitReveal::commit(server_reveal));
        }
        _ => panic!("wrong evidence kind"),
    }

    // produce → verify → seed round-trips, and the seed reproduces the draws.
    let seed = CommitReveal::seed(&req, &ev).expect("round-trip verifies");
    let stream = DrawStream::new(seed, req.draw_count);
    assert_eq!(
        stream.transcript_commitment(),
        ev.draw_transcript_commitment
    );
}

#[test]
fn tampered_reveal_fails_commitment() {
    let req = sample_request(2);
    let src = CommitReveal {
        server_reveal: [0x01; 32],
        player_contribution: [0x02; 32],
    };
    let mut ev = src.evidence(&req);

    // Attacker swaps in a different reveal (to bias the seed) but leaves the
    // published commitment. The reveal no longer opens the commitment → rejected
    // before the seed is even used.
    if let EvidenceKind::CommitReveal { server_reveal, .. } = &mut ev.source {
        *server_reveal = [0xff; 32];
    }
    assert_eq!(
        CommitReveal::seed(&req, &ev),
        Err(VerifyError::CommitmentMismatch),
        "a tampered reveal must fail commitment verification"
    );
}

#[test]
fn tampered_player_contribution_fails_transcript() {
    // The player's contribution is not behind a commitment, but it feeds the
    // seed, so changing it moves the transcript → detected there.
    let req = sample_request(2);
    let src = CommitReveal {
        server_reveal: [0x01; 32],
        player_contribution: [0x02; 32],
    };
    let mut ev = src.evidence(&req);
    if let EvidenceKind::CommitReveal {
        player_contribution,
        ..
    } = &mut ev.source
    {
        *player_contribution = [0x03; 32];
    }
    assert_eq!(
        CommitReveal::seed(&req, &ev),
        Err(VerifyError::TranscriptMismatch)
    );
}

/// TRUST-LEVEL NOTE (asserted structurally): CommitReveal prevents unilateral
/// *choice* but NOT selective *abort*. There is no protocol step here by which a
/// party is *forced* to reveal — `CommitReveal::seed` verifies evidence that
/// already contains the reveal. A dishonest last-revealer who dislikes the
/// outcome simply never produces the evidence, and the transition never lands.
/// This test documents that gap: we can compute the outcome from a would-be
/// reveal *before* committing to landing it, which is exactly the abort lever.
/// Closing it needs timeout finalization (a follow-up), NOT anything in this crate.
#[test]
fn commit_reveal_selective_abort_is_not_prevented() {
    let req = sample_request(1);
    let unfavorable_hunt = |reveal: [u8; 32]| -> u64 {
        let src = CommitReveal {
            server_reveal: reveal,
            player_contribution: [0x00; 32],
        };
        let ev = src.evidence(&req);
        let seed = CommitReveal::seed(&req, &ev).unwrap();
        DrawStream::new(seed, 1).draw_die(0, 20).unwrap()
    };
    // The server can evaluate the outcome for its (already chosen) reveal BEFORE
    // deciding to publish the evidence at all. Nothing in the verifier forces
    // publication — that is the selective-abort gap, by construction.
    let outcome = unfavorable_hunt([0x77; 32]);
    assert!((1..=20).contains(&outcome));
    // (No cryptographic control here prevents "see result, then decline to land".)
}

// ── Deterministic + MockBeacon round-trips, and the VRF/Hybrid stubs. ──

#[test]
fn deterministic_source_round_trip() {
    let req = sample_request(3);
    let src = Deterministic {
        context: [0x33; 32],
    };
    let ev = src.evidence(&req);
    let seed = Deterministic::seed(&req, &ev).expect("verifies");
    assert_eq!(
        DrawStream::new(seed, req.draw_count).transcript_commitment(),
        ev.draw_transcript_commitment
    );
    // Cross-source verifier rejects a foreign evidence kind.
    assert_eq!(
        CommitReveal::seed(&req, &ev),
        Err(VerifyError::SourceMismatch)
    );
}

#[test]
fn mock_beacon_round_trip() {
    let req = sample_request(2);
    let src = MockBeacon {
        beacon_id: b"drand/quicknet".to_vec(),
        round: 9_000_001,
        output: [0xbe; 32],
    };
    let ev = src.evidence(&req);
    let seed = MockBeacon::seed(&req, &ev).expect("verifies");
    assert_eq!(
        DrawStream::new(seed, req.draw_count).transcript_commitment(),
        ev.draw_transcript_commitment
    );
    // A different beacon output → different seed → different transcript.
    let mut tampered = ev.clone();
    if let EvidenceKind::Beacon { output, .. } = &mut tampered.source {
        *output = [0xbf; 32];
    }
    assert_eq!(
        MockBeacon::seed(&req, &tampered),
        Err(VerifyError::TranscriptMismatch)
    );
}

// ── Hybrid: genesis LB-VRF key-chain ∧ delayed schedule-bound beacon, with
//    timeout finalization. Small epoch/chain to keep the lattice keygen fast. ──

/// Small key-chain so `epoch = seq` keygen stays fast in tests.
const NUM_EPOCHS: usize = 8;

/// A hybrid request at a small `seq` (so the key-chain need only cover a few
/// epochs) with the beacon schedule's round comfortably inside the chain.
fn hybrid_base_request(draw_count: u32) -> RandomnessRequest {
    let mut req = sample_request(draw_count);
    req.seq = 5; // epoch = 5 < NUM_EPOCHS; round = base(5) + 5*stride(1) = 10
    req
}

/// A hash-chain beacon over `chain_root`, schedule `round = 5 + seq*1`.
fn make_beacon(chain_root: [u8; 32]) -> HashChainBeacon {
    HashChainBeacon::new(
        chain_root,
        200,
        b"hashchain/test".to_vec(),
        BeaconSchedule {
            base_round: 5,
            stride: 1,
        },
    )
}

/// A request whose `game_binding` pins the key-chain root + beacon params at genesis.
fn hybrid_request(kc_root: &[u8; 32], params: &BeaconParams, draw_count: u32) -> RandomnessRequest {
    let mut req = hybrid_base_request(draw_count);
    req.game_binding = Hybrid::genesis_binding(kc_root, params);
    req
}

#[test]
fn hybrid_round_trip_provided() {
    let kc = KeyChain::from_master_seed(&[0xA1; 32], NUM_EPOCHS);
    let beacon = make_beacon([0x02; 32]);
    let params = beacon.params();
    let req = hybrid_request(&kc.root(), &params, 3);

    let hybrid = Hybrid::new(kc, Box::new(beacon));
    let ev = hybrid.evidence(&req);

    match &ev.source {
        EvidenceKind::Hybrid {
            finalization,
            vrf_output,
            vrf_proof,
            epoch_proof,
            beacon,
            ..
        } => {
            assert_eq!(*finalization, Finalization::ServerProvided);
            assert!(!vrf_output.is_empty() && !vrf_proof.is_empty());
            assert_eq!(epoch_proof.len(), 3, "Merkle depth log2(8) = 3");
            // The round is schedule-bound: base(5) + seq(5)*stride(1) = 10.
            assert_eq!(beacon.round, 10);
        }
        other => panic!("expected Hybrid evidence, got {other:?}"),
    }

    let seed = Hybrid::seed(&req, &ev).expect("honest hybrid evidence verifies");
    assert_eq!(
        DrawStream::new(seed, req.draw_count).transcript_commitment(),
        ev.draw_transcript_commitment
    );
}

#[test]
fn hybrid_seed_depends_on_both_vrf_and_beacon() {
    // Baseline: key-chain A, beacon X.
    let kc_a = KeyChain::from_master_seed(&[0x10; 32], NUM_EPOCHS);
    let beacon_x = make_beacon([0x20; 32]);
    let req_ax = hybrid_request(&kc_a.root(), &beacon_x.params(), 1);
    let seed_ax = Hybrid::seed(
        &req_ax,
        &Hybrid::new(kc_a, Box::new(beacon_x)).evidence(&req_ax),
    )
    .expect("verifies");

    // Change ONLY the beacon (different chain root ⇒ different round output).
    let kc_a2 = KeyChain::from_master_seed(&[0x10; 32], NUM_EPOCHS);
    let beacon_y = make_beacon([0x21; 32]);
    let req_ay = hybrid_request(&kc_a2.root(), &beacon_y.params(), 1);
    let seed_ay = Hybrid::seed(
        &req_ay,
        &Hybrid::new(kc_a2, Box::new(beacon_y)).evidence(&req_ay),
    )
    .expect("verifies");
    assert_ne!(
        seed_ax.as_bytes(),
        seed_ay.as_bytes(),
        "changing the beacon must change the hybrid seed"
    );

    // Change ONLY the VRF key-chain (different master ⇒ different epoch key/output).
    let kc_b = KeyChain::from_master_seed(&[0x11; 32], NUM_EPOCHS);
    let beacon_x2 = make_beacon([0x20; 32]);
    let req_bx = hybrid_request(&kc_b.root(), &beacon_x2.params(), 1);
    let seed_bx = Hybrid::seed(
        &req_bx,
        &Hybrid::new(kc_b, Box::new(beacon_x2)).evidence(&req_bx),
    )
    .expect("verifies");
    assert_ne!(
        seed_ax.as_bytes(),
        seed_bx.as_bytes(),
        "changing the VRF key-chain must change the hybrid seed"
    );

    // And, holding the event fixed, the VRF half genuinely contributes to the mix:
    // a beacon-only (ServerMissed) finalization of the SAME request differs from the
    // ServerProvided seed (which additionally folds the VRF output).
    let kc_c = KeyChain::from_master_seed(&[0x10; 32], NUM_EPOCHS);
    let beacon_z = make_beacon([0x20; 32]);
    let req = hybrid_request(&kc_c.root(), &beacon_z.params(), 1);
    let provided =
        Hybrid::seed(&req, &Hybrid::new(kc_c, Box::new(beacon_z)).evidence(&req)).unwrap();
    let kc_c2 = KeyChain::from_master_seed(&[0x10; 32], NUM_EPOCHS);
    let beacon_z2 = make_beacon([0x20; 32]);
    let missed = Hybrid::seed(
        &req,
        &Hybrid::new(kc_c2, Box::new(beacon_z2))
            .with_mode(FinalizeMode::SimulateServerMissed)
            .evidence(&req),
    )
    .unwrap();
    assert_ne!(
        provided.as_bytes(),
        missed.as_bytes(),
        "same request, same beacon: provided (VRF-folded) ≠ beacon-only → the VRF half is load-bearing"
    );
}

#[test]
fn hybrid_wrong_beacon_round_is_rejected() {
    // Hatch #2 (schedule layer): the server cannot substitute a favourable,
    // already-published round — even one whose output chain-verifies.
    let kc = KeyChain::from_master_seed(&[0x30; 32], NUM_EPOCHS);
    let beacon = make_beacon([0x31; 32]);
    let params = beacon.params();
    let req = hybrid_request(&kc.root(), &params, 1);
    let mut ev = Hybrid::new(kc, Box::new(beacon)).evidence(&req);

    // Reschedule to round+1 and supply the CORRECT chain output for that other round
    // (so verify_beacon_round would pass) — the schedule binding still rejects it.
    let honest = make_beacon([0x31; 32]);
    if let EvidenceKind::Hybrid { beacon, .. } = &mut ev.source {
        let bad_round = beacon.round + 1;
        beacon.round = bad_round;
        beacon.output = honest.round_output(bad_round);
        // params/anchor unchanged ⇒ genesis binding still matches.
    }
    assert_eq!(
        Hybrid::seed(&req, &ev),
        Err(VerifyError::BeaconRoundMismatch),
        "a rescheduled beacon round must be rejected even if it chain-verifies"
    );
}

#[test]
fn hybrid_wrong_epoch_key_is_rejected() {
    // Hatch #1: the eval key is the genesis-committed key for THIS transition's
    // epoch (= seq). A server that evaluates a DIFFERENT epoch's key (hoping for a
    // favourable output) fails the Merkle membership check at leaf `seq`.
    let kc = KeyChain::from_master_seed(&[0x40; 32], NUM_EPOCHS);
    let beacon = make_beacon([0x41; 32]);
    let params = beacon.params();
    let req = hybrid_request(&kc.root(), &params, 1); // seq = 5

    // Read a DIFFERENT epoch's (epoch 2) committed key + proof from an identical
    // (deterministic) key-chain, then move the chain into the producer.
    let kc_read = KeyChain::from_master_seed(&[0x40; 32], NUM_EPOCHS);
    let wrong_pk = kc_read.public_key_bytes(2);
    let wrong_proof = kc_read.epoch_proof(2);

    let mut ev = Hybrid::new(kc, Box::new(beacon)).evidence(&req);
    // Substitute epoch-2's key + membership path while the request still binds seq=5.
    if let EvidenceKind::Hybrid {
        vrf_public_key,
        epoch_proof,
        ..
    } = &mut ev.source
    {
        *vrf_public_key = wrong_pk;
        *epoch_proof = wrong_proof;
    }
    assert_eq!(
        Hybrid::seed(&req, &ev),
        Err(VerifyError::EpochKeyMismatch),
        "a key from the wrong epoch must be rejected by the genesis key-chain membership"
    );
}

#[test]
fn hybrid_swapped_keychain_root_fails_genesis_binding() {
    // Hatch #1 (genesis layer): a server that commits a fresh, favourable key-chain
    // root at turn time fails, because the request's game_binding pins the original.
    let kc = KeyChain::from_master_seed(&[0x50; 32], NUM_EPOCHS);
    let beacon = make_beacon([0x51; 32]);
    let params = beacon.params();
    let req = hybrid_request(&kc.root(), &params, 1); // binds kc's root

    // The attacker builds a whole different key-chain and produces valid evidence
    // under it (its own root in the evidence) — but the genesis binding rejects it.
    let attacker_kc = KeyChain::from_master_seed(&[0x99; 32], NUM_EPOCHS);
    let attacker_beacon = make_beacon([0x51; 32]);
    let ev = Hybrid::new(attacker_kc, Box::new(attacker_beacon)).evidence(&req);
    assert_eq!(
        Hybrid::seed(&req, &ev),
        Err(VerifyError::GenesisBindingMismatch),
        "a per-turn key-chain-root swap must be rejected by the genesis binding"
    );
}

#[test]
fn hybrid_forged_vrf_proof_is_rejected() {
    let kc = KeyChain::from_master_seed(&[0x60; 32], NUM_EPOCHS);
    let beacon = make_beacon([0x61; 32]);
    let params = beacon.params();
    let req = hybrid_request(&kc.root(), &params, 1);
    let mut ev = Hybrid::new(kc, Box::new(beacon)).evidence(&req);
    assert!(
        Hybrid::seed(&req, &ev).is_ok(),
        "honest hybrid evidence verifies first"
    );

    if let EvidenceKind::Hybrid { vrf_proof, .. } = &mut ev.source {
        vrf_proof[100] ^= 0x01; // flip a byte in the LB-VRF response region
    }
    let r = Hybrid::seed(&req, &ev);
    assert!(
        matches!(
            r,
            Err(VerifyError::VrfProofInvalid) | Err(VerifyError::MalformedVrfEvidence(_))
        ),
        "a forged hybrid LB-VRF proof must be rejected, got {r:?}"
    );
}

#[test]
fn hybrid_timeout_finalizes_without_reroll() {
    // THE ANTI-ABORT PROPERTY (hatch #5). The server withholds its LB-VRF proof past
    // the deadline. Anyone finalizes from the beacon alone (ServerMissed). The
    // outcome is DETERMINED — not chooseable — and there is NO reroll.
    let kc = KeyChain::from_master_seed(&[0x70; 32], NUM_EPOCHS);
    let beacon = make_beacon([0x71; 32]);
    let params = beacon.params();
    let req = hybrid_request(&kc.root(), &params, 2);

    // A would-be finalizer produces the timeout evidence (no VRF proof).
    let missed_ev = Hybrid::new(kc, Box::new(beacon))
        .with_mode(FinalizeMode::SimulateServerMissed)
        .evidence(&req);
    match &missed_ev.source {
        EvidenceKind::Hybrid {
            finalization,
            vrf_output,
            vrf_proof,
            epoch_proof,
            ..
        } => {
            assert_eq!(
                *finalization,
                Finalization::ServerMissed,
                "fault is recorded"
            );
            assert!(vrf_output.is_empty(), "no VRF output on the timeout path");
            assert!(vrf_proof.is_empty(), "no VRF proof on the timeout path");
            assert!(epoch_proof.is_empty(), "no epoch proof on the timeout path");
        }
        other => panic!("expected Hybrid evidence, got {other:?}"),
    }

    // It STILL finalizes to a determined seed.
    let missed_seed = Hybrid::seed(&req, &missed_ev).expect("timeout path finalizes");

    // NO REROLL / NO ALTERNATIVE: the missed seed is a pure function of the beacon
    // round output + event id. A withholding server cannot bias it — stuffing
    // arbitrary junk into the (ignored) VRF fields yields the SAME finalized seed.
    let mut junk_ev = missed_ev.clone();
    if let EvidenceKind::Hybrid {
        vrf_public_key,
        vrf_output,
        vrf_proof,
        epoch_proof,
        ..
    } = &mut junk_ev.source
    {
        *vrf_public_key = vec![0xaa; 4096];
        *vrf_output = vec![0xbb; 128];
        *vrf_proof = vec![0xcc; 9472];
        *epoch_proof = vec![[0xdd; 32]; 3];
    }
    let junk_seed = Hybrid::seed(&req, &junk_ev).expect("timeout path still finalizes");
    assert_eq!(
        missed_seed.as_bytes(),
        junk_seed.as_bytes(),
        "the server-missed outcome is fixed — no reroll, no alternative"
    );

    // Independent finalizers agree (deterministic in public data).
    let kc2 = KeyChain::from_master_seed(&[0x70; 32], NUM_EPOCHS);
    let beacon2 = make_beacon([0x71; 32]);
    let req2 = hybrid_request(&kc2.root(), &beacon2.params(), 2);
    assert_eq!(req.game_binding, req2.game_binding);
    let missed_seed2 = Hybrid::seed(
        &req2,
        &Hybrid::new(kc2, Box::new(beacon2))
            .with_mode(FinalizeMode::SimulateServerMissed)
            .evidence(&req2),
    )
    .expect("timeout path finalizes");
    assert_eq!(
        missed_seed.as_bytes(),
        missed_seed2.as_bytes(),
        "any finalizer computes the same server-missed seed"
    );

    // The provided outcome (had the server acted) is a distinct determined seed:
    // the paths are marker-separated and the server, withholding before the beacon
    // matured, chose neither — both are functions of the unpredictable beacon.
    let kc3 = KeyChain::from_master_seed(&[0x70; 32], NUM_EPOCHS);
    let beacon3 = make_beacon([0x71; 32]);
    let req3 = hybrid_request(&kc3.root(), &beacon3.params(), 2);
    let provided_seed =
        Hybrid::seed(&req3, &Hybrid::new(kc3, Box::new(beacon3)).evidence(&req3)).unwrap();
    assert_ne!(
        missed_seed.as_bytes(),
        provided_seed.as_bytes(),
        "provided vs missed are distinct determined outcomes (marker-separated)"
    );
}

// ── HashChainBeacon + verify_beacon_round: forward-secure, pure verification. ──

#[test]
fn hash_chain_beacon_round_verifies_and_rejects_wrong_output() {
    let schedule = BeaconSchedule {
        base_round: 10,
        stride: 1,
    };
    let beacon = HashChainBeacon::new(
        [0x01; 32],
        100,
        b"hashchain/test".to_vec(),
        schedule.clone(),
    );
    let params = beacon.params();

    let round = schedule.expected_round(5); // 15
    let output = beacon.round_output(round);
    verify_beacon_round(&params, round, &output).expect("an honest round verifies");

    // A wrong output (does not chain to the anchor) is rejected.
    let mut bad = output;
    bad[0] ^= 0x01;
    assert_eq!(
        verify_beacon_round(&params, round, &bad),
        Err(VerifyError::BeaconVerifyFailed),
        "a wrong beacon output must be rejected"
    );
    // The right output at the WRONG round is rejected (H^round no longer hits anchor).
    assert_eq!(
        verify_beacon_round(&params, round + 1, &output),
        Err(VerifyError::BeaconVerifyFailed)
    );
    // Round 0 and past the chain length are rejected.
    assert_eq!(
        verify_beacon_round(&params, 0, &output),
        Err(VerifyError::BeaconVerifyFailed)
    );
    assert_eq!(
        verify_beacon_round(&params, 101, &output),
        Err(VerifyError::BeaconVerifyFailed)
    );
}

#[test]
fn drand_beacon_verification_is_the_remaining_gap() {
    // HONEST GAP: the shipped beacon is a hash chain (single operator). A real
    // threshold drand-BLS beacon's round verification (a BLS pairing check vs the
    // pinned group key) is not wired — the `Drand` variant fails closed. This
    // documents hatch #2's remaining production work.
    let params = BeaconParams {
        beacon_id: b"drand/quicknet".to_vec(),
        kind: BeaconKind::Drand {
            group_public_key: vec![0u8; 48],
            scheme: "bls-unchained-g1-rfc9380".to_string(),
        },
        schedule: BeaconSchedule {
            base_round: 1,
            stride: 1,
        },
    };
    assert!(
        matches!(
            verify_beacon_round(&params, 1, &[0u8; 32]),
            Err(VerifyError::BackendUnavailable(_))
        ),
        "real drand-BLS verification is the remaining gap for hatch #2"
    );
}

#[test]
fn keychain_membership_verifies_and_rejects_wrong_epoch() {
    // The genesis key-chain (hatch #1) at the membership layer: the committed leaf
    // for an epoch verifies, and presenting it at a different epoch index fails.
    let kc = KeyChain::from_master_seed(&[0x80; 32], NUM_EPOCHS);
    let root = kc.root();

    let pk3 = kc.public_key_bytes(3);
    let proof3 = kc.epoch_proof(3);
    assert!(
        verify_epoch_membership(&root, 3, &pk3, &proof3),
        "the committed epoch-3 key verifies at leaf 3"
    );
    // Epoch-3's key presented at leaf 4 (wrong epoch) is rejected.
    assert!(
        !verify_epoch_membership(&root, 4, &pk3, &proof3),
        "the epoch-3 key must not verify as epoch 4"
    );
    // A tampered public key is rejected at its own leaf.
    let mut pk3_bad = pk3.clone();
    pk3_bad[0] ^= 0x01;
    assert!(
        !verify_epoch_membership(&root, 3, &pk3_bad, &proof3),
        "a tampered epoch key is rejected"
    );
    // A different chain's root does not accept this key.
    let other = KeyChain::from_master_seed(&[0x81; 32], NUM_EPOCHS);
    assert!(
        !verify_epoch_membership(&other.root(), 3, &pk3, &proof3),
        "membership is against the genesis-committed root"
    );
}

// ── ServerVrf: the REAL post-quantum LB-VRF source (pqvrf, Set I). ──

#[test]
fn server_vrf_lb_round_trip() {
    // Produce → verify → seed with the real LB-VRF. The seed is DETERMINED by the
    // verified VRF output, and the transcript reconstructs from it.
    let req = sample_request(3);
    let source = ServerVrf::from_key_seed(&[0x11; 32]);
    let ev = source.try_evidence(&req).expect("honest LB-VRF eval");

    // The recorded evidence is the LB-VRF variant carrying pk + output + proof.
    match &ev.source {
        EvidenceKind::LbVrf {
            public_key,
            output,
            proof,
        } => {
            assert!(!public_key.is_empty() && !output.is_empty() && !proof.is_empty());
        }
        other => panic!("expected LbVrf evidence, got {other:?}"),
    }

    // The pure verifier re-runs pqvrf::verify and recovers the seed.
    let seed = ServerVrf::seed(&req, &ev).expect("LB-VRF evidence verifies");
    let stream = DrawStream::new(seed, req.draw_count);
    assert_eq!(
        stream.transcript_commitment(),
        ev.draw_transcript_commitment
    );

    // The seed is a function of the VERIFIED output: a different key/input yields a
    // different verified output, hence a different seed.
    let other = ServerVrf::from_key_seed(&[0x12; 32]);
    let ev2 = other.try_evidence(&req).expect("second key evals once");
    let seed2 = ServerVrf::seed(&req, &ev2).expect("verifies");
    assert_ne!(
        seed.as_bytes(),
        seed2.as_bytes(),
        "a different key epoch yields a different verified output → different seed"
    );
}

#[test]
fn server_vrf_forged_proof_is_rejected() {
    // NON-VACUOUS: flip a byte of the real LB-VRF proof. pqvrf::verify (the
    // one-output tooth, uniqueness reducing to Module-SIS) rejects it.
    let req = sample_request(2);
    let source = ServerVrf::from_key_seed(&[0x21; 32]);
    let mut ev = source.try_evidence(&req).expect("honest eval");
    assert!(
        ServerVrf::seed(&req, &ev).is_ok(),
        "honest proof verifies first"
    );

    if let EvidenceKind::LbVrf { proof, .. } = &mut ev.source {
        proof[0] ^= 0xFF;
    }
    assert_eq!(
        ServerVrf::seed(&req, &ev),
        Err(VerifyError::VrfProofInvalid),
        "a forged LB-VRF proof must be rejected by pqvrf::verify"
    );
}

#[test]
fn server_vrf_forged_output_is_rejected() {
    // A tampered OUTPUT is not the LB-VRF value bound by the proof's challenge, so
    // pqvrf::verify rejects it — the server cannot present a second output.
    let req = sample_request(2);
    let source = ServerVrf::from_key_seed(&[0x22; 32]);
    let mut ev = source.try_evidence(&req).expect("honest eval");

    if let EvidenceKind::LbVrf { output, .. } = &mut ev.source {
        output[0] ^= 0x01; // stays < p (low bit), still canonical-length → reaches verify
    }
    assert_eq!(
        ServerVrf::seed(&req, &ev),
        Err(VerifyError::VrfProofInvalid),
        "a forged LB-VRF output must be rejected — one output per input"
    );
}

#[test]
fn server_vrf_swapped_key_is_rejected() {
    // The server cannot swap in a fresh key on ALREADY-RECORDED evidence: the proof
    // was made under the original key, so it fails pqvrf::verify under the new pk.
    let req = sample_request(1);
    let honest = ServerVrf::from_key_seed(&[0x31; 32]);
    let mut ev = honest.try_evidence(&req).expect("honest eval");

    // A different key epoch's public key bytes.
    let attacker = ServerVrf::from_key_seed(&[0x32; 32]);
    if let EvidenceKind::LbVrf { public_key, .. } = &mut ev.source {
        *public_key = attacker.public_key_bytes();
    }
    assert_eq!(
        ServerVrf::seed(&req, &ev),
        Err(VerifyError::VrfProofInvalid),
        "a proof does not verify under a swapped public key"
    );
}

#[test]
fn server_vrf_key_commitment_binds_the_request() {
    // The request-binding model: a request commits the per-event key via
    // key_commitment(pk). A verifier that recomputes it from the evidence's pk and
    // compares detects a swapped key epoch BEFORE the draw.
    let honest = ServerVrf::from_key_seed(&[0x41; 32]);
    let honest_pk = honest.public_key_bytes();
    let committed = ServerVrf::key_commitment(&honest_pk);

    // The honest key's pk opens the commitment.
    assert_eq!(committed, ServerVrf::key_commitment(&honest_pk));
    // A different key epoch does not.
    let other = ServerVrf::from_key_seed(&[0x42; 32]);
    assert_ne!(
        committed,
        ServerVrf::key_commitment(&other.public_key_bytes()),
        "a swapped key epoch fails the request's key commitment"
    );
}

#[test]
fn server_vrf_key_is_one_time() {
    // Set I is one-time: the SAME ServerVrf refuses a second evaluation (its key is
    // burned on first use). Each event must mint its own key epoch.
    let req = sample_request(1);
    let source = ServerVrf::from_key_seed(&[0x51; 32]);
    assert!(!source.key_consumed());
    let _ev = source
        .try_evidence(&req)
        .expect("first eval consumes the key");
    assert!(source.key_consumed());
    assert_eq!(
        source.try_evidence(&req),
        Err(VrfEvalError::KeyConsumed),
        "a one-time key must refuse a second evaluation"
    );
}

#[test]
fn server_vrf_malformed_evidence_is_rejected() {
    // A wrong-length byte field is rejected as malformed before the proof check.
    let req = sample_request(1);
    let source = ServerVrf::from_key_seed(&[0x61; 32]);
    let mut ev = source.try_evidence(&req).expect("honest eval");
    if let EvidenceKind::LbVrf { proof, .. } = &mut ev.source {
        proof.truncate(proof.len() - 1); // no longer the canonical length
    }
    assert!(
        matches!(
            ServerVrf::seed(&req, &ev),
            Err(VerifyError::MalformedVrfEvidence(_))
        ),
        "a wrong-length proof is rejected as malformed"
    );
}

#[test]
fn server_vrf_wrong_evidence_kind_is_rejected() {
    // Cross-source: ServerVrf::seed on foreign (CommitReveal) evidence is a mismatch.
    let req = sample_request(1);
    let foreign = CommitReveal {
        server_reveal: [1; 32],
        player_contribution: [2; 32],
    }
    .evidence(&req);
    assert_eq!(
        ServerVrf::seed(&req, &foreign),
        Err(VerifyError::SourceMismatch)
    );
}

// ── EventId domain separation + serde. ──

#[test]
fn event_id_derive_matches_request() {
    let req = sample_request(3);
    let direct = EventId::derive(
        &req.game_binding,
        req.seq,
        &req.pre_state_root,
        &req.action_hash,
        &req.event_kind,
        req.draw_count,
    );
    assert_eq!(direct.as_bytes(), req.event_id().as_bytes());
}

#[test]
fn request_commitment_changes_with_any_bound_field() {
    let base = sample_request(3).commitment();
    let mut r = sample_request(3);
    r.seq = 43;
    assert_ne!(base, r.commitment());
    let mut r2 = sample_request(3);
    r2.action_hash = [0x23; 32];
    assert_ne!(base, r2.commitment());
}

#[test]
fn evidence_serde_round_trip() {
    let req = sample_request(2);
    let ev = CommitReveal {
        server_reveal: [9; 32],
        player_contribution: [8; 32],
    }
    .evidence(&req);
    let json = serde_json::to_string(&ev).unwrap();
    let back: RandomnessEvidence = serde_json::from_str(&json).unwrap();
    assert_eq!(ev, back);
    // The deserialized evidence still verifies.
    assert!(CommitReveal::seed(&req, &back).is_ok());
}
