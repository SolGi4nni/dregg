//! Verify the REAL AWS Nitro attestation document captured end-to-end from a live
//! enclave (us-east-1, c5.xlarge, debug-mode) whose app bound `user_data = [0xAB; 32]`.

use dregg_tee_verify::verify_nitro_core;

const REAL_DOC: &[u8] = include_bytes!("data/nitro_att.bin");

#[test]
fn verifies_real_live_nitro_doc_and_extracts_bound_report_data() {
    let (claims, ts_ms) = verify_nitro_core(REAL_DOC)
        .expect("the real Nitro doc must verify: COSE sig + chain to the pinned AWS root");

    // The enclave app bound exactly this commitment into user_data.
    assert_eq!(
        claims.report_data, [0xABu8; 32],
        "report_data must equal the commitment the enclave bound"
    );
    assert_eq!(
        claims.tcb,
        dregg_cell::tee_attest::TcbStatus::NoPolicyOnPlatform,
        "a real Nitro doc carries no microcode/firmware version, so no TCB policy can have \
         run — the claims must say so rather than report a pass"
    );
    assert!(ts_ms > 1_700_000_000_000, "doc timestamp looks real (ms)");
    println!(
        "OK real Nitro doc: measurement={} report_data={} ts_ms={}",
        hex::encode(claims.measurement),
        hex::encode(claims.report_data),
        ts_ms
    );
}

#[test]
fn tampering_the_signed_bytes_is_rejected() {
    // Non-vacuity baseline, LOCAL to this tamper test: the UNMUTATED doc must verify.
    // Without it, if `nitro_att.bin` ever drifts so the base doc stops parsing, the
    // mutation below would also fail and this test would pass FOR THE WRONG REASON —
    // tamper-rejection silently disabled. Assert the positive first, then the negative.
    assert!(
        verify_nitro_core(REAL_DOC).is_ok(),
        "baseline: the unmutated real Nitro doc must verify (else the tamper check is vacuous)"
    );
    // Flip a byte in the middle of the payload region -> COSE sig (or parse) must fail.
    let mut doc = REAL_DOC.to_vec();
    let mid = doc.len() / 2;
    doc[mid] ^= 0xFF;
    assert!(
        verify_nitro_core(&doc).is_err(),
        "a tampered doc must not verify"
    );
}

#[test]
fn a_truncated_doc_is_rejected() {
    // Non-vacuity baseline, LOCAL to this test: the FULL doc must verify, so the
    // rejection below is genuinely attributable to the truncation and not to a drifted
    // fixture that never verified in the first place.
    assert!(
        verify_nitro_core(REAL_DOC).is_ok(),
        "baseline: the full real Nitro doc must verify (else the truncation check is vacuous)"
    );
    assert!(verify_nitro_core(&REAL_DOC[..REAL_DOC.len() / 2]).is_err());
}
