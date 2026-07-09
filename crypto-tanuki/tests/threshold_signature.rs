//! End-to-end tests for the Tanuki two-round threshold signature reference:
//!
//! 1. an honest `t`-of-`n` signature VERIFIES;
//! 2. a SUB-THRESHOLD set does NOT produce a valid signature;
//! 3. the `b`-aggregation BINDS the session — a swapped `W_j` changes `ssid`,
//!    hence `b`, hence the whole signature (and the tampered one is rejected).

use crypto_tanuki::threshold::{
    finalize, keygen, run_ceremony, sign1, sign2, verify, Params, Round1Public, Round2Public,
};

fn key_pkg() -> crypto_tanuki::KeyPackage {
    keygen(&Params::reference(), b"tanuki-reference-master-seed-0001")
}

#[test]
fn honest_threshold_signature_verifies() {
    let keys = key_pkg();
    // A 3-of-5 signing set (signers at positions 0,2,4 → indices 1,3,5).
    let (sig, _r1) = run_ceremony(&keys, &[0, 2, 4], b"attack at dawn", b"nonce/honest");
    assert!(
        verify(&keys.params, &keys.vk, b"attack at dawn", &sig),
        "an honest t-of-n signature must verify"
    );
    // The response and hint are SHORT — verification has teeth (a random z would
    // have ‖z‖∞ ≈ q/2 ≈ 4.19M, dwarfing the bound).
    assert!(sig.z.norm_inf() <= keys.params.z_bound, "‖z‖ within bound");
    assert!(sig.h.norm_inf() <= keys.params.h_bound, "‖h‖ within bound");
    assert!(sig.z.norm_inf() < 4_000_000, "honest z is genuinely short");
}

#[test]
fn every_threshold_subset_verifies() {
    let keys = key_pkg();
    let positions = [0usize, 1, 2, 3, 4];
    let mut count = 0;
    for a in 0..5 {
        for b in (a + 1)..5 {
            for c in (b + 1)..5 {
                let (sig, _) = run_ceremony(
                    &keys,
                    &[positions[a], positions[b], positions[c]],
                    b"msg",
                    b"n",
                );
                assert!(
                    verify(&keys.params, &keys.vk, b"msg", &sig),
                    "3-subset {{{a},{b},{c}}} must verify"
                );
                count += 1;
            }
        }
    }
    assert_eq!(count, 10, "all C(5,3) subsets exercised");
}

#[test]
fn wrong_message_is_rejected() {
    let keys = key_pkg();
    let (sig, _) = run_ceremony(&keys, &[0, 1, 2], b"the real message", b"nonce/m");
    assert!(verify(&keys.params, &keys.vk, b"the real message", &sig));
    assert!(
        !verify(&keys.params, &keys.vk, b"a forged message", &sig),
        "the signature must not verify against a different message"
    );
}

#[test]
fn sub_threshold_set_cannot_produce_a_valid_signature() {
    // With t = 3, run the ceremony with only 2 signers. The Lagrange
    // reconstruction over a 2-set does NOT recover s: it yields a full-range
    // R_q element s' ≠ s. So the combined z = c·s' + R·b is NOT short, and the
    // norm bound (the threshold-enforcement leg) rejects it. (The combiner
    // always computes h to satisfy the challenge check, so it is precisely the
    // ‖z‖/‖h‖ bounds — not the hash equality — that enforce the threshold.)
    let keys = key_pkg(); // REAL reference bounds
    let (sig, _r1) = run_ceremony(&keys, &[0, 1], b"sub-threshold attempt", b"nonce/sub");
    assert!(
        !verify(&keys.params, &keys.vk, b"sub-threshold attempt", &sig),
        "a 2-of-3-threshold set must NOT yield a valid signature"
    );
    // Witness the mechanism: the wrong reconstruction blows the norm bound.
    assert!(
        sig.z.norm_inf() > keys.params.z_bound || sig.h.norm_inf() > keys.params.h_bound,
        "sub-threshold z/h must exceed the acceptance bounds"
    );
    assert!(
        sig.z.norm_inf() > 1_000_000,
        "wrong reconstruction ⇒ non-short z"
    );
}

#[test]
fn a_single_signer_cannot_forge() {
    // A single signer (< t) reconstructs s' from one share (λ = 1 over a 1-set),
    // again a full-range element ≠ s; z is not short and is rejected.
    let keys = key_pkg();
    let (sig, _) = run_ceremony(&keys, &[2], b"solo forgery", b"nonce/solo");
    assert!(
        !verify(&keys.params, &keys.vk, b"solo forgery", &sig),
        "a single signer (< t) must not forge"
    );
    assert!(
        sig.z.norm_inf() > keys.params.z_bound || sig.h.norm_inf() > keys.params.h_bound,
        "single-signer z/h must exceed the acceptance bounds"
    );
}

#[test]
fn b_aggregation_binds_the_session_swapped_w_changes_signature() {
    let keys = key_pkg();
    let params = &keys.params;
    let msg = b"bind me";
    let positions = [0usize, 2, 4];

    // Round 1 for the real set.
    let mut r1: Vec<Round1Public> = Vec::new();
    let mut r1_sec = Vec::new();
    for &pos in &positions {
        let key = &keys.signer_keys[pos];
        let (p, s) = sign1(
            params,
            &keys.vk,
            key.index,
            &[b"nonce/bind".as_ref(), &[key.index as u8]].concat(),
        );
        r1.push(p);
        r1_sec.push(s);
    }

    // An INDEPENDENT round-1 commitment for the same signer (different nonce) —
    // what a rushing adversary might try to substitute for W_j after seeing others.
    let victim = 0usize; // position in `positions`
    let key_v = &keys.signer_keys[positions[victim]];
    let (p_alt, _s_alt) = sign1(params, &keys.vk, key_v.index, b"nonce/DIFFERENT");
    assert_ne!(r1[victim].w_i, p_alt.w_i, "the alternate W_j must differ");

    // Honest run.
    let mut r2: Vec<Round2Public> = Vec::new();
    for (n, &pos) in positions.iter().enumerate() {
        let key = &keys.signer_keys[pos];
        r2.push(sign2(params, &keys.vk, key, &r1_sec[n], &r1, msg));
    }
    let sig_honest = finalize(params, &keys.vk, &r1, &r2, msg);
    assert!(verify(params, &keys.vk, msg, &sig_honest));

    // Swap W_j → the derived b, hence w, c, z_i all change. Re-run round 2 over
    // the SWAPPED round-1 set: a DIFFERENT signature results (binding).
    let mut r1_swapped = r1.clone();
    r1_swapped[victim].w_i = p_alt.w_i.clone();
    let mut r2_swapped: Vec<Round2Public> = Vec::new();
    for (n, &pos) in positions.iter().enumerate() {
        let key = &keys.signer_keys[pos];
        r2_swapped.push(sign2(params, &keys.vk, key, &r1_sec[n], &r1_swapped, msg));
    }
    let sig_swapped = finalize(params, &keys.vk, &r1_swapped, &r2_swapped, msg);

    // The two signatures differ (the challenge itself is bound to {W_j}).
    assert_ne!(
        sig_honest.c, sig_swapped.c,
        "swapping a W_j must change the session challenge c (b-aggregation binds ssid)"
    );

    // And a MIX-AND-MATCH attack fails: honest round-2 shares do NOT finalize
    // into a valid signature against the swapped round-1 transcript (the
    // aggregation vector b the honest signers used no longer matches).
    let sig_mixed = finalize(params, &keys.vk, &r1_swapped, &r2, msg);
    assert!(
        !verify(params, &keys.vk, msg, &sig_mixed),
        "round-2 shares bound to the original ssid must not validate under a swapped W_j"
    );
}

#[test]
fn tampered_response_is_rejected() {
    let keys = key_pkg();
    let (mut sig, _) = run_ceremony(&keys, &[0, 1, 2], b"integrity", b"nonce/tamper");
    assert!(verify(&keys.params, &keys.vk, b"integrity", &sig));
    // Nudge one coefficient of z: w' changes → challenge mismatch → reject.
    sig.z.0[0].coeffs[0] = (sig.z.0[0].coeffs[0] + 1) % crypto_tanuki::Q;
    assert!(
        !verify(&keys.params, &keys.vk, b"integrity", &sig),
        "a tampered z must be rejected"
    );
}
