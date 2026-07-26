//! **The archive re-check, against a REAL Chutes TDX quote.**
//!
//! A per-turn attestation record is only worth writing down if a later reader can tell whether it
//! has been altered. `recheck_archived_binding` is that reader's tool: it re-derives the Chutes
//! `report_data` binding from a stored quote and the stored `nonce_hex` / `e2e_pubkey_b64`, so an
//! edited row stops matching its own quote.
//!
//! ## The fixture, and what patching it does and does not fake
//!
//! `tee-verify/tests/data/chutes_tdx_quote.bin` is a real TDX v4 quote captured from Chutes
//! evidence (the same fixture `dregg-tee-verify`'s own TDX tests use; reused rather than
//! duplicated, since it is one repo). Its `report_data` commits to the nonce and instance key
//! that were live at capture — neither of which we have, and SHA-256 does not run backwards.
//!
//! So the tests here PATCH `report_data[0..32]` to the binding of a nonce/pubkey pair we choose,
//! at the documented TD10 offset. That is legitimate precisely because the function under test
//! makes NO cryptographic claim: it is a structural tamper check on a record at rest, explicitly
//! not an attestation, and a patched quote exercises it exactly as a genuine one would. Nothing
//! in this file demonstrates that any quote is authentic — the DCAP crypto lives in
//! `dregg-tee-verify`'s own tests, and the live verification happens once, at attestation time,
//! against fresh collateral.

use dregg_chutes_e2ee::{quote_sha256_hex, recheck_archived_binding};
use dregg_tee_verify::chutes_report_data_binding;

/// A real TDX v4 quote (raw bytes), shared with `dregg-tee-verify`'s TDX fixtures.
const REAL_QUOTE: &[u8] = include_bytes!("../../tee-verify/tests/data/chutes_tdx_quote.bin");

/// Absolute offset of the TD10 `report_data` field: 48-byte quote header, then the TD10 report,
/// whose `report_data` sits at body offset 520 (see `dregg-tee-verify`'s `tdx_chutes` fixtures,
/// which read the same field at the same place).
const REPORT_DATA_OFFSET: usize = 48 + 520;

const NONCE: &str = "9f2c4a1b7e8d05364f1a2b3c4d5e6f708192a3b4c5d6e7f8091a2b3c4d5e6f70";
const PUBKEY: &str = "dGhpcy1pcy1ub3QtYS1yZWFsLW1sLWtlbS1rZXktYnV0LWl0LWlzLWEtc3RyaW5n";

/// The real quote with `report_data[0..32]` set to the binding of `nonce`/`pubkey`.
fn quote_bound_to(nonce: &str, pubkey: &str) -> Vec<u8> {
    let mut quote = REAL_QUOTE.to_vec();
    let binding = chutes_report_data_binding(nonce, pubkey);
    quote[REPORT_DATA_OFFSET..REPORT_DATA_OFFSET + 32].copy_from_slice(&binding);
    quote
}

/// GREEN: a record whose stored nonce and instance key are the pair its quote commits to passes.
#[test]
fn an_unaltered_record_rechecks_clean() {
    let quote = quote_bound_to(NONCE, PUBKEY);
    assert!(
        recheck_archived_binding(&quote, NONCE, PUBKEY).is_ok(),
        "the pair the quote commits to must re-check clean"
    );
}

/// **RED — the gate's whole reason to exist.** Editing EITHER stored preimage breaks the check,
/// including edits designed to look innocuous (one hex digit; one base64 character). Without this
/// an archived record's nonce and instance key would be free text nobody could contradict.
#[test]
fn editing_either_stored_preimage_is_caught() {
    let quote = quote_bound_to(NONCE, PUBKEY);

    // One hex digit of the nonce.
    let mut nudged = NONCE.to_string();
    nudged.replace_range(0..1, "8");
    assert_ne!(nudged, NONCE);
    let err = recheck_archived_binding(&quote, &nudged, PUBKEY)
        .expect_err("a one-character nonce edit must be caught");
    assert!(err.contains("altered"), "the reason names the fault: {err}");

    // One character of the instance key.
    let mut other_key = PUBKEY.to_string();
    other_key.replace_range(0..1, "e");
    assert_ne!(other_key, PUBKEY);
    assert!(
        recheck_archived_binding(&quote, NONCE, &other_key).is_err(),
        "a one-character instance-key edit must be caught"
    );

    // Both swapped for a wholly different, internally consistent pair — an attacker who supplies
    // a matching pair still fails, because the QUOTE is what they must match, not each other.
    let elsewhere = "0011223344556677889900112233445566778899001122334455667788990011";
    assert!(
        recheck_archived_binding(&quote, elsewhere, "b3RoZXIta2V5").is_err(),
        "a self-consistent but unrelated pair must not satisfy this quote"
    );

    // And a record bound to a DIFFERENT session does not satisfy this one's stored pair.
    let other_session = quote_bound_to(elsewhere, "b3RoZXIta2V5");
    assert!(
        recheck_archived_binding(&other_session, NONCE, PUBKEY).is_err(),
        "a quote from another session must not pass this record's preimages"
    );
    assert!(recheck_archived_binding(&other_session, elsewhere, "b3RoZXIta2V5").is_ok());
}

/// A blob that is not a TDX quote at all is an `Err`, not a silent pass — so an archive row whose
/// quote column was replaced with rubbish cannot read as "checks out".
#[test]
fn a_non_quote_blob_is_refused_rather_than_passed() {
    for blob in [
        b"not a quote at all".to_vec(),
        Vec::new(),
        REAL_QUOTE[..64].to_vec(), // a real prefix, truncated mid-report
    ] {
        assert!(
            recheck_archived_binding(&blob, NONCE, PUBKEY).is_err(),
            "a non-quote blob must be refused"
        );
    }
}

/// The digest half of the record check: the stored digest is the handle onto the stored bytes, so
/// a single flipped byte anywhere in the quote must change it.
#[test]
fn the_quote_digest_is_sensitive_to_any_byte() {
    let quote = quote_bound_to(NONCE, PUBKEY);
    let digest = quote_sha256_hex(&quote);
    assert_eq!(digest.len(), 64);

    for index in [0usize, REPORT_DATA_OFFSET, quote.len() - 1] {
        let mut tampered = quote.clone();
        tampered[index] ^= 0x01;
        assert_ne!(
            quote_sha256_hex(&tampered),
            digest,
            "flipping byte {index} must change the digest"
        );
    }
}
