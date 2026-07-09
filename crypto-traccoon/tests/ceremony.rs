//! End-to-end tests of the TRaccoon 3-round ceremony. Each maps to a property
//! the task names:
//!
//! * `honest_t_of_n_verifies`      — a full honest T-of-N signature VERIFIES.
//! * `sub_threshold_does_not_sign` — fewer than T signers does NOT verify.
//! * `reused_mask_is_detectable`   — replaying a one-time mask corrupts z.
//! * `commit_round_binds`          — a rushing party that changes its nonce
//!   after seeing others is caught in round 2.

use crypto_traccoon::hash;
use crypto_traccoon::linalg::PolyVec;
use crypto_traccoon::threshold::{
    self, aggregate_w, check_openings, combine, compute_challenge, keygen, round1, round2, round3,
    verify, Params, Round2Msg,
};

fn setup() -> (threshold::PublicKey, Vec<threshold::SignerKey>) {
    keygen(Params::reference(), 0xDEADBEEF)
}

// ---------------------------------------------------------------------------
// 1. Honest T-of-N verifies.
// ---------------------------------------------------------------------------
#[test]
fn honest_t_of_n_verifies() {
    let (pk, keys) = setup();
    let msg = b"transfer 10 to alice";
    let sig = threshold::run_session(&pk, &keys, &[1, 2, 3], msg, 0x1234);
    assert!(
        verify(&pk, msg, &sig),
        "honest 3-of-5 signature must verify"
    );
    // A different message must NOT verify under the same signature.
    assert!(
        !verify(&pk, b"transfer 999 to eve", &sig),
        "signature is message-bound"
    );
}

// ---------------------------------------------------------------------------
// 2. Sub-threshold cannot produce a valid signature.
// ---------------------------------------------------------------------------
#[test]
fn sub_threshold_does_not_sign() {
    let (pk, keys) = setup();
    let msg = b"quorum needed";
    // Only 2 signers try to sign a 3-of-5 key. They run the ceremony honestly
    // among themselves, but their Lagrange set has only 2 points, so
    // Σ λ_{i,S} s_i ≠ sk and the verification equation cannot close.
    let set = vec![1, 2];
    let sig = threshold::run_session(&pk, &keys, &set, msg, 0x99);
    assert!(!verify(&pk, msg, &sig), "2 of 3-threshold must NOT verify");
}

// ---------------------------------------------------------------------------
// 3. The masks are one-time: a replayed / stale mask is detectably wrong.
// ---------------------------------------------------------------------------
//
// We drive the rounds by hand. One party emits a round-3 response whose masking
// belongs to a DIFFERENT session (a replayed one-time mask). The row-masks m_i
// broadcast THIS session no longer cancel the stale column-mask, so the leftover
// mask term survives into z, blowing ‖z‖ past B (and breaking the equation).
#[test]
fn reused_mask_is_detectable() {
    let (pk, keys) = setup();
    let msg = b"session A";
    let set = vec![1, 2, 3];
    let d = pk.params.d();
    let by = |i: usize| keys.iter().find(|k| k.index == i).unwrap().clone();

    // Honest rounds 1 & 2.
    let mut states = Vec::new();
    let mut r1 = Vec::new();
    for &i in &set {
        let (st, m) = round1(&pk, &by(i), msg, &set, 0xAAA);
        states.push(st);
        r1.push(m);
    }
    let r2: Vec<Round2Msg> = states.iter().map(round2).collect();
    check_openings(&r1, &r2, msg, &set).expect("honest openings verify");
    let w = aggregate_w(&r2, pk.params.k);
    let c = compute_challenge(&pk, msg, &w);

    // Honest baseline signature verifies and is short.
    let honest_r3: Vec<_> = set
        .iter()
        .map(|&i| {
            let st = states.iter().find(|s| s.index == i).unwrap();
            round3(&pk, &by(i), st, &c)
        })
        .collect();
    let honest_sig = combine(&r1, &honest_r3, c, d);
    assert!(
        verify(&pk, msg, &honest_sig),
        "baseline honest sig verifies"
    );

    // Now corrupt signer 1's round-3 message with a STALE mask: add a mask cell
    // from a different session id. This models replaying a one-time mask.
    let stale = hash::mask_cell(b"pairwise", b"OTHER-session-id", 2, 1, d);
    let mut tampered = honest_r3.clone();
    tampered[0].z = tampered[0].z.add(&stale);

    let bad_sig = combine(&r1, &tampered, c, d);
    // The stale mask does not cancel: z is no longer short, and the equation
    // does not close.
    assert!(bad_sig.z.norm_inf() > 200, "leftover mask makes z large");
    assert!(
        !verify(&pk, msg, &bad_sig),
        "reused/stale mask must be detected"
    );

    // Sanity: the ONLY difference from the honest path is the stale mask; remove
    // it and we are back to the verifying signature (masks are the whole story).
    let removed = PolyVec(
        tampered[0]
            .z
            .0
            .iter()
            .zip(&stale.0)
            .map(|(a, b)| a.sub(b))
            .collect(),
    );
    tampered[0].z = removed;
    let repaired = combine(&r1, &tampered, c, d);
    assert!(
        verify(&pk, msg, &repaired),
        "removing the stale mask restores validity"
    );
}

// ---------------------------------------------------------------------------
// 4. The commit round binds: a rushing party that changes its nonce after
//    seeing the others' reveals is caught.
// ---------------------------------------------------------------------------
#[test]
fn commit_round_binds() {
    let (pk, keys) = setup();
    let msg = b"no rushing";
    let set = vec![1, 2, 3];
    let by = |i: usize| keys.iter().find(|k| k.index == i).unwrap().clone();

    // Round 1: everyone commits.
    let mut states = Vec::new();
    let mut r1 = Vec::new();
    for &i in &set {
        let (st, m) = round1(&pk, &by(i), msg, &set, 0xBBB);
        states.push(st);
        r1.push(m);
    }

    // Honest reveals pass the binding check.
    let honest_r2: Vec<Round2Msg> = states.iter().map(round2).collect();
    assert!(
        check_openings(&r1, &honest_r2, msg, &set).is_ok(),
        "honest reveals bind"
    );

    // Rushing: signer 3 tries to open a DIFFERENT w after seeing the others.
    // It re-derives a fresh nonce (as if adapting to the revealed w_1, w_2) and
    // reveals THAT instead of the w it committed to.
    let (rogue_state, _rogue_com) =
        round1(&pk, &by(3), msg, &set, 0xF00D /* different nonce */);
    let mut rushing_r2 = honest_r2.clone();
    rushing_r2.iter_mut().find(|m| m.index == 3).unwrap().w = round2(&rogue_state).w; // swap in the un-committed nonce

    match check_openings(&r1, &rushing_r2, msg, &set) {
        Err(culprit) => assert_eq!(culprit, 3, "the rushing party (signer 3) is caught"),
        Ok(()) => panic!("a changed nonce must fail the commit-binding check"),
    }
}
