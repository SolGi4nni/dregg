//! **Every check in `attest_check` shown going RED, against a REAL Chutes TDX quote.**
//!
//! A check that cannot fail is not a check, and six lines of green tell a reader nothing about
//! which of them is load-bearing. So each check here is driven twice: once over an intact record
//! (it passes) and once over exactly the corruption it exists to catch (it fails, and the other
//! five stay green, which is what shows the failure was ATTRIBUTED rather than smeared).
//!
//! ## The fixture, and what patching it does and does not fake
//!
//! `tee-verify/tests/data/chutes_tdx_quote.bin` is a real TDX v4 quote captured from Chutes
//! evidence, and `tee-verify/tests/data/chutes_measurements.json` is a snapshot of the live
//! registry it matches. Both are reused from `dregg-tee-verify` rather than duplicated. The
//! quote's `report_data` commits to the nonce and instance key that were live at capture, neither
//! of which we have, and SHA-256 does not run backwards, so the tests below patch
//! `report_data[0..32]` to the binding of a pair we choose, at the documented TD10 offset. The
//! same latitude the sibling `dregg-chutes-e2ee/tests/archive_recheck.rs` takes, for the same
//! reason: checks 1 to 5 make no cryptographic claim, so a patched quote exercises them exactly
//! as a genuine one would.
//!
//! **Nothing in this file demonstrates that any quote is authentic.** That is check 6, it needs
//! Intel-signed collateral, and what is shown here is that it FAILS without valid collateral and
//! that it does not run without any. Its green lives in `dregg-tee-verify`'s network test.

use base64::Engine as _;

use dregg_attest_check::{
    verify_record, CheckState, NarrationAttestationRecord, RecordIdentity, Verdict, Verification,
    NOT_ESTABLISHED, WITHOUT_COLLATERAL,
};
use dregg_tee_verify::{
    chutes_report_data_binding, quote_sha256_hex, registers_structural_unverified,
};
use dungeon_on_dregg::narrator::{tee_provenance_commitment, TeeProvenance};

/// A real TDX v4 quote (raw bytes), shared with `dregg-tee-verify`'s TDX fixtures.
const REAL_QUOTE: &[u8] = include_bytes!("../../tee-verify/tests/data/chutes_tdx_quote.bin");

/// A snapshot of `https://api.chutes.ai/servers/tee/measurements`, the same fixture the TDX tests
/// prove this quote's MRTD+RTMR0..2 match exactly one entry of.
const REGISTRY: &str = include_str!("../../tee-verify/tests/data/chutes_measurements.json");

/// Absolute offset of the TD10 `report_data` field: 48-byte quote header, then the TD10 report,
/// whose `report_data` sits at body offset 520.
const REPORT_DATA_OFFSET: usize = 48 + 520;

const NONCE: &str = "9f2c4a1b7e8d05364f1a2b3c4d5e6f708192a3b4c5d6e7f8091a2b3c4d5e6f70";
const OTHER_NONCE: &str = "0011223344556677889900112233445566778899001122334455667788990011";

/// A well-formed 1184-byte ML-KEM-768 public key, base64 STANDARD, from a deterministic pattern.
/// The real length matters: check 2 gates on the key decoding to exactly an ML-KEM-768 key before
/// it compares anything, so a short stand-in would exercise the gate instead of the binding.
fn pubkey(seed: u8) -> String {
    let bytes: Vec<u8> = (0..1184usize)
        .map(|i| ((i as u32).wrapping_mul(37).wrapping_add(11 + seed as u32) % 256) as u8)
        .collect();
    base64::engine::general_purpose::STANDARD.encode(bytes)
}

/// The real quote with `report_data[0..32]` set to the binding of `nonce`/`pubkey`.
fn quote_bound_to(nonce: &str, pubkey_b64: &str) -> Vec<u8> {
    let mut quote = REAL_QUOTE.to_vec();
    let binding = chutes_report_data_binding(nonce, pubkey_b64);
    quote[REPORT_DATA_OFFSET..REPORT_DATA_OFFSET + 32].copy_from_slice(&binding);
    quote
}

/// The identity fields of an INTACT archive row for `quote`: the measurement folded from the
/// quote's own registers, the digest of the quote's own bytes, and a receipt commitment derived
/// the way the landing turn derived it (this stands in for the value read off the receipt, which
/// is what the bot stores).
fn intact_identity(quote: &[u8], nonce: &str, pubkey_b64: &str) -> RecordIdentity {
    let registers = registers_structural_unverified(quote).expect("the fixture is a TDX quote");
    let measurement = registers.folded_measurement();
    let digest = quote_sha256_hex(quote);
    let quote_sha256: [u8; 32] = hex::decode(&digest).unwrap().try_into().unwrap();
    let instance_id = "1d5fdd83-2e7c-4b6a-9f10-c0ffee000001".to_string();
    let tcb_status = "UpToDate".to_string();
    RecordIdentity {
        receipt_hex: "4f2a1b3c9d8e".repeat(5) + "abcd",
        provider: "chutes-tee".to_string(),
        model: "Qwen/Qwen3-32B-TEE".to_string(),
        instance_id: instance_id.clone(),
        measurement_hex: hex::encode(measurement),
        tcb_status: tcb_status.clone(),
        quote_sha256_hex: digest,
        quote_len: quote.len(),
        nonce_hex: nonce.to_string(),
        e2e_pubkey_b64: pubkey_b64.to_string(),
        // What the landed receipt bound. Computed here from the UNTAMPERED four preimages, once,
        // exactly as the turn computed it; every tamper below leaves this fixed and moves a
        // preimage, which is the whole shape of check 4.
        receipt_commit_hex: hex::encode(tee_provenance_commitment(&TeeProvenance::new(
            measurement,
            instance_id,
            tcb_status,
            quote_sha256,
        ))),
        measurement_registry: "https://api.chutes.ai/servers/tee/measurements".to_string(),
        archived_at_unix: 1_753_500_000,
    }
}

/// An intact record over an intact quote.
fn intact() -> (Vec<u8>, NarrationAttestationRecord) {
    let key = pubkey(0);
    let quote = quote_bound_to(NONCE, &key);
    let record = NarrationAttestationRecord::of(intact_identity(&quote, NONCE, &key));
    (quote, record)
}

/// The state of check `n` (1-based, as the panel numbers them).
fn state(v: &Verification, n: u8) -> CheckState {
    v.checks
        .iter()
        .find(|c| c.number == n)
        .unwrap_or_else(|| panic!("check {n} exists"))
        .state
}

/// The detail line of check `n`.
fn detail(v: &Verification, n: u8) -> String {
    v.checks
        .iter()
        .find(|c| c.number == n)
        .unwrap()
        .detail
        .clone()
}

/// Assert that exactly `failing` failed, and everything else that RAN passed.
fn only_failure_is(v: &Verification, failing: u8) {
    let failed: Vec<u8> = v
        .checks
        .iter()
        .filter(|c| c.state == CheckState::Fail)
        .map(|c| c.number)
        .collect();
    assert_eq!(
        failed,
        vec![failing],
        "expected only check {failing} to fail; report was:\n{}",
        v.render()
    );
}

// ── GREEN: the baseline the reds are measured against ────────────────────────────────────────

/// An intact record passes every check that can run without collateral, and check 6 does NOT run.
/// The verdict for that is NOT a pass, and the exit code is not zero: the record is unaltered and
/// its enclave is in the registry, but nothing here has decided the quote is genuine.
#[test]
fn an_intact_record_passes_the_five_offline_checks_and_does_not_claim_the_sixth() {
    let (quote, record) = intact();
    let v = verify_record(&quote, &record, Some(REGISTRY), None, &[]);

    for n in 1..=5 {
        assert_eq!(
            state(&v, n),
            CheckState::Pass,
            "check {n} should pass on an intact record; report was:\n{}",
            v.render()
        );
    }
    assert_eq!(state(&v, 6), CheckState::NotRun);
    assert_eq!(v.verdict(), Verdict::Unauthenticated);
    assert_eq!(v.exit_code(), 3, "a run that skipped check 6 is not a pass");
    assert!(v.verdict_line().contains("UNDECIDED"));

    // Check 3 named the registry entry it matched, so a reader can go look at it.
    assert!(
        detail(&v, 3).contains("match registry entry"),
        "{}",
        detail(&v, 3)
    );
}

/// The ceiling sentence prints on EVERY outcome, and the collateral caveat prints whenever
/// check 6 did not decide. A reader cannot reach a verdict line without reading what it is worth.
#[test]
fn the_ceiling_is_printed_on_every_outcome() {
    let (quote, record) = intact();

    let offline = verify_record(&quote, &record, Some(REGISTRY), None, &[]).render();
    assert!(offline.contains(NOT_ESTABLISHED));
    assert!(offline.contains(WITHOUT_COLLATERAL));

    let mut broken = record.clone();
    broken.quote_sha256_hex = "00".repeat(32);
    let broken = verify_record(&quote, &broken, Some(REGISTRY), None, &[]).render();
    assert!(broken.contains(NOT_ESTABLISHED));
    assert!(broken.contains("BROKEN"));
}

// ── RED 1: the quote is not the one the record names ─────────────────────────────────────────

/// **Check 1 red.** One flipped byte anywhere in the file, and the digest no longer matches. This
/// is the check everything downstream leans on: the digest is what the receipt commitment was
/// computed over, so a record whose bytes are not its bytes says nothing about any turn.
#[test]
fn check_1_goes_red_when_the_file_is_not_the_bytes_the_record_names() {
    let (quote, record) = intact();

    for index in [0usize, REPORT_DATA_OFFSET + 40, quote.len() - 1] {
        let mut tampered = quote.clone();
        tampered[index] ^= 0x01;
        let v = verify_record(&tampered, &record, Some(REGISTRY), None, &[]);
        assert_eq!(
            state(&v, 1),
            CheckState::Fail,
            "flipping byte {index} must break the digest"
        );
        assert!(
            detail(&v, 1).contains("not the same bytes"),
            "the reason names the fault: {}",
            detail(&v, 1)
        );
    }

    // And a record whose LENGTH field was edited while the digest still matches is caught too.
    let mut lying = record.clone();
    lying.quote_len = quote.len() + 1;
    let v = verify_record(&quote, &lying, Some(REGISTRY), None, &[]);
    assert_eq!(state(&v, 1), CheckState::Fail);
    only_failure_is(&v, 1);
}

// ── RED 2: the quote was minted for a different session ──────────────────────────────────────

/// **Check 2 red.** One hex digit of the nonce, one character of the instance key, a
/// self-consistent but unrelated pair, and a quote captured from a DIFFERENT session. Without
/// this check an archived quote would prove only that some enclave signed something, at no
/// particular time, for no particular key.
#[test]
fn check_2_goes_red_on_a_nudged_nonce_a_nudged_key_and_another_sessions_quote() {
    let (quote, record) = intact();

    // One hex digit of the nonce.
    let mut nudged = record.clone();
    let mut nonce = NONCE.to_string();
    nonce.replace_range(0..1, "8");
    assert_ne!(nonce, NONCE);
    nudged.report_data_binding.nonce_hex = nonce;
    let v = verify_record(&quote, &nudged, Some(REGISTRY), None, &[]);
    assert_eq!(state(&v, 2), CheckState::Fail);
    assert!(
        detail(&v, 2).contains("altered"),
        "the reason names the fault: {}",
        detail(&v, 2)
    );
    only_failure_is(&v, 2);

    // A different but equally well-formed instance key.
    let mut other_key = record.clone();
    other_key.report_data_binding.e2e_pubkey_b64 = pubkey(1);
    let v = verify_record(&quote, &other_key, Some(REGISTRY), None, &[]);
    assert_eq!(state(&v, 2), CheckState::Fail);
    only_failure_is(&v, 2);

    // Both swapped for a wholly different, INTERNALLY CONSISTENT pair. An attacker who supplies
    // a matching nonce and key still fails: the quote is what they must match, not each other.
    let mut elsewhere = record.clone();
    elsewhere.report_data_binding.nonce_hex = OTHER_NONCE.to_string();
    elsewhere.report_data_binding.e2e_pubkey_b64 = pubkey(2);
    let v = verify_record(&quote, &elsewhere, Some(REGISTRY), None, &[]);
    assert_eq!(state(&v, 2), CheckState::Fail);
    only_failure_is(&v, 2);

    // A quote from ANOTHER session, swapped in under this record's preimages. Its digest differs
    // too, so this shows checks 1 and 2 both firing on a substitution.
    let other_session = quote_bound_to(OTHER_NONCE, &pubkey(2));
    let v = verify_record(&other_session, &record, Some(REGISTRY), None, &[]);
    assert_eq!(state(&v, 1), CheckState::Fail, "different bytes");
    assert_eq!(state(&v, 2), CheckState::Fail, "different session");
    // The substituted quote is still a real Chutes enclave, so 3 and 5 stay green: the failure is
    // "not THIS session", which is exactly the distinction check 2 exists to draw.
    assert_eq!(state(&v, 3), CheckState::Pass);
    assert_eq!(state(&v, 5), CheckState::Pass);

    // Malformed preimages are refused BEFORE the comparison, so a truncated record says why.
    let mut truncated = record.clone();
    truncated.report_data_binding.nonce_hex = "deadbeef".to_string();
    let v = verify_record(&quote, &truncated, Some(REGISTRY), None, &[]);
    assert_eq!(state(&v, 2), CheckState::Fail);
    assert!(detail(&v, 2).contains("hex string"), "{}", detail(&v, 2));

    let mut not_a_key = record.clone();
    not_a_key.report_data_binding.e2e_pubkey_b64 =
        base64::engine::general_purpose::STANDARD.encode([0u8; 32]);
    let v = verify_record(&quote, &not_a_key, Some(REGISTRY), None, &[]);
    assert_eq!(state(&v, 2), CheckState::Fail);
    assert!(detail(&v, 2).contains("ML-KEM-768"), "{}", detail(&v, 2));
}

// ── RED 3: the enclave is not one the registry publishes ─────────────────────────────────────

/// **Check 3 red.** Point the checker at a registry in which no entry has this MRTD, and it says
/// so instead of quietly matching nothing. Also red when the RECORD names a measurement the
/// attached quote does not fold to, which is the half that ties the claimed code identity to the
/// bytes rather than to the record's own say-so.
#[test]
fn check_3_goes_red_against_a_registry_without_this_enclave_and_a_record_that_lies_about_it() {
    let (quote, record) = intact();

    // A registry whose every entry has a different MRTD: same shape, wrong content.
    let mut entries: serde_json::Value = serde_json::from_str(REGISTRY).unwrap();
    for entry in entries.as_array_mut().unwrap() {
        let mrtd = entry["mrtd"].as_str().unwrap().to_string();
        let flipped = format!(
            "{}{}",
            if mrtd.starts_with('a') { "b" } else { "a" },
            &mrtd[1..]
        );
        entry["mrtd"] = serde_json::Value::String(flipped);
    }
    let foreign = serde_json::to_string(&entries).unwrap();
    let v = verify_record(&quote, &record, Some(&foreign), None, &[]);
    assert_eq!(state(&v, 3), CheckState::Fail);
    assert!(
        detail(&v, 3).contains("match NONE of the"),
        "the reason names the fault: {}",
        detail(&v, 3)
    );
    only_failure_is(&v, 3);

    // An EMPTY registry pins no code identity, so it is a failure and not a match of zero things.
    let v = verify_record(&quote, &record, Some("[]"), None, &[]);
    assert_eq!(state(&v, 3), CheckState::Fail);
    assert!(detail(&v, 3).contains("empty"), "{}", detail(&v, 3));

    // A registry that is not a registry.
    let v = verify_record(&quote, &record, Some("{ nope"), None, &[]);
    assert_eq!(state(&v, 3), CheckState::Fail);
    assert!(detail(&v, 3).contains("did not parse"), "{}", detail(&v, 3));

    // A record naming a measurement the quote's own registers do not fold to.
    let mut lying = record.clone();
    lying.measurement_hex = "7d".repeat(32);
    let v = verify_record(&quote, &lying, Some(REGISTRY), None, &[]);
    assert_eq!(state(&v, 3), CheckState::Fail);
    assert!(
        detail(&v, 3).contains("does not measure"),
        "{}",
        detail(&v, 3)
    );

    // With NO registry the check does not run, and NOT RUN is not a pass.
    let v = verify_record(&quote, &record, None, None, &[]);
    assert_eq!(state(&v, 3), CheckState::NotRun);
    assert_eq!(v.verdict(), Verdict::Unauthenticated);
    assert!(detail(&v, 3).contains("no registry supplied"));
}

// ── RED 4: the stored row was tampered ───────────────────────────────────────────────────────

/// **Check 4 red, and the reason the commitment is stored rather than re-derived.**
///
/// `instance_id` and `tcb_status` are free text that no other check covers: they are not in the
/// quote, so folding registers cannot contradict them and hashing bytes cannot either. Edit one
/// in the archive and the four preimages stop deriving the commitment the receipt bound, while
/// every other check stays green. A checker that re-derived the commitment from the row would
/// derive the EDITED one and report this as clean, which is the whole reason the column exists.
#[test]
fn check_4_goes_red_when_a_stored_row_field_is_edited() {
    let key = pubkey(0);
    let quote = quote_bound_to(NONCE, &key);
    let honest = intact_identity(&quote, NONCE, &key);

    // A TCB downgrade laundered into the record: the row now says a status the receipt never
    // committed to. Nothing else in the record moves.
    let mut downgraded = honest.clone();
    downgraded.tcb_status = "SWHardeningNeeded".to_string();
    let record = NarrationAttestationRecord::of(downgraded);
    let v = verify_record(&quote, &record, Some(REGISTRY), None, &[]);
    assert_eq!(state(&v, 4), CheckState::Fail);
    assert!(
        detail(&v, 4).contains("has been edited since the turn landed"),
        "the reason names the fault: {}",
        detail(&v, 4)
    );
    only_failure_is(&v, 4);

    // A different enclave instance claimed for the same turn.
    let mut reassigned = honest.clone();
    reassigned.instance_id = "1d5fdd83-2e7c-4b6a-9f10-c0ffee000002".to_string();
    let record = NarrationAttestationRecord::of(reassigned);
    let v = verify_record(&quote, &record, Some(REGISTRY), None, &[]);
    assert_eq!(state(&v, 4), CheckState::Fail);
    only_failure_is(&v, 4);

    // The commitment itself edited to some other value.
    let mut forged = honest.clone();
    forged.receipt_commit_hex = "5c".repeat(32);
    let record = NarrationAttestationRecord::of(forged);
    let v = verify_record(&quote, &record, Some(REGISTRY), None, &[]);
    assert_eq!(state(&v, 4), CheckState::Fail);
    only_failure_is(&v, 4);

    // A row from before the column existed carries no commitment. That is a FAILED check, not a
    // skipped one: an archive that cannot tie itself to a turn has not answered the question.
    let mut legacy = honest.clone();
    legacy.receipt_commit_hex = String::new();
    let record = NarrationAttestationRecord::of(legacy);
    let v = verify_record(&quote, &record, Some(REGISTRY), None, &[]);
    assert_eq!(state(&v, 4), CheckState::Fail);
    assert!(
        detail(&v, 4).contains("no receipt commitment"),
        "{}",
        detail(&v, 4)
    );

    // The measurement and the quote digest are covered by checks 3 and 1 as well, so editing one
    // of THOSE lights up two checks. Shown so the coverage is visible rather than assumed.
    let mut wrong_measurement = honest.clone();
    wrong_measurement.measurement_hex = "7d".repeat(32);
    let record = NarrationAttestationRecord::of(wrong_measurement);
    let v = verify_record(&quote, &record, Some(REGISTRY), None, &[]);
    assert_eq!(state(&v, 3), CheckState::Fail);
    assert_eq!(state(&v, 4), CheckState::Fail);
}

// ── RED 5: the chain does not root at Intel ──────────────────────────────────────────────────

/// **Check 5 red.** Corrupt the trust anchor inside the quote's own PCK chain and the check
/// refuses it. Worth exactly what it costs and no more: it says the quote CLAIMS Intel's anchor,
/// it verifies no signature, and a fabricated quote that embeds Intel's public root passes it.
/// That is stated in the check's own detail line rather than left for a reader to infer.
#[test]
fn check_5_goes_red_when_the_pck_chain_does_not_root_at_the_pinned_intel_root() {
    let (quote, record) = intact();
    let v = verify_record(&quote, &record, Some(REGISTRY), None, &[]);
    assert_eq!(state(&v, 5), CheckState::Pass);
    assert!(
        detail(&v, 5).contains("verifies no signature"),
        "the pass says what it is worth: {}",
        detail(&v, 5)
    );

    // Flip one base64 character deep inside the LAST certificate of the embedded chain (the
    // self-signed root). Same length, so the quote still parses; different DER, so the root no
    // longer fingerprints to the pinned Intel SGX Root CA.
    let marker = b"-----BEGIN CERTIFICATE-----";
    let last = (0..quote.len().saturating_sub(marker.len()))
        .filter(|&i| &quote[i..i + marker.len()] == marker)
        .next_back()
        .expect("the fixture embeds a PEM PCK chain");
    let target = last + marker.len() + 40;
    let mut tampered = quote.clone();
    tampered[target] = if tampered[target] == b'A' { b'B' } else { b'A' };
    assert_ne!(tampered, quote);

    // Re-file the record against the tampered bytes so checks 1 and 3 stay green and the failure
    // is attributable to check 5 alone.
    let refiled = NarrationAttestationRecord::of(intact_identity(&tampered, NONCE, &pubkey(0)));
    let v = verify_record(&tampered, &refiled, Some(REGISTRY), None, &[]);
    assert_eq!(
        state(&v, 5),
        CheckState::Fail,
        "a corrupted trust anchor must be refused; report was:\n{}",
        v.render()
    );
    only_failure_is(&v, 5);
}

// ── RED 6: the check that decides authenticity ───────────────────────────────────────────────

/// **Check 6 red, and NOT RUN.** This is the only check that decides whether the quote is
/// genuine, so both of its non-green states matter: unusable collateral is a FAILURE, and absent
/// collateral is an unanswered question that the verdict refuses to round up.
///
/// Its GREEN is not shown here and cannot be: it needs Intel-signed collateral for this quote's
/// platform, fetched from a PCCS. `dregg-tee-verify`'s `real_quote_full_dcap_verify` is where
/// that lives.
#[test]
fn check_6_goes_red_on_unusable_collateral_and_does_not_run_without_any() {
    let (quote, record) = intact();

    // Absent: NOT RUN, and the detail says plainly what is undecided.
    let v = verify_record(&quote, &record, Some(REGISTRY), None, &[]);
    assert_eq!(state(&v, 6), CheckState::NotRun);
    assert!(
        detail(&v, 6).contains("decides whether the quote is genuine"),
        "{}",
        detail(&v, 6)
    );
    assert_ne!(v.verdict(), Verdict::Verified, "NOT RUN is never a pass");

    // Unparseable: a FAILURE, not a skip. Collateral that cannot be read is a broken input, and
    // treating it as "no collateral" would let a corrupt file downgrade itself to a soft pass.
    let v = verify_record(
        &quote,
        &record,
        Some(REGISTRY),
        Some("{ not collateral"),
        &[],
    );
    assert_eq!(state(&v, 6), CheckState::Fail);
    assert!(detail(&v, 6).contains("did not parse"), "{}", detail(&v, 6));
    only_failure_is(&v, 6);

    // Structurally valid but EMPTY collateral: parses, and then the DCAP verification refuses the
    // quote. This is the shape a wrong or expired collateral file arrives in, and it must fail
    // closed rather than verify against nothing.
    let empty = serde_json::to_string(&dregg_tee_verify::QuoteCollateralV3 {
        pck_crl_issuer_chain: String::new(),
        root_ca_crl: vec![],
        pck_crl: vec![],
        tcb_info_issuer_chain: String::new(),
        tcb_info: String::new(),
        tcb_info_signature: vec![],
        qe_identity_issuer_chain: String::new(),
        qe_identity: String::new(),
        qe_identity_signature: vec![],
        pck_certificate_chain: None,
    })
    .unwrap();
    let v = verify_record(&quote, &record, Some(REGISTRY), Some(&empty), &[]);
    assert_eq!(
        state(&v, 6),
        CheckState::Fail,
        "empty collateral must not verify a quote; report was:\n{}",
        v.render()
    );
    only_failure_is(&v, 6);
}
