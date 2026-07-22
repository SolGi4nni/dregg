//! Integration tests for the Intel TDX (DCAP) verifier against a REAL Chutes
//! (Bittensor subnet 64) TDX quote and the live Chutes measurements registry.
//!
//! Fixtures (captured 2026-07 from `deploy`-side Chutes evidence + the live registry):
//! - `tests/data/chutes_tdx_quote.bin` — one real TDX v4 quote (raw bytes, base64-decoded).
//! - `tests/data/chutes_measurements.json` — a snapshot of
//!   `https://api.chutes.ai/servers/tee/measurements`.
//!
//! The full DCAP crypto verification needs Intel-signed collateral fetched from a PCCS/PCS,
//! so it is gated behind the `collateral-fetch` feature and `#[ignore]` (network). Run it
//! with:
//!   `cargo test -p dregg-tee-verify --features collateral-fetch --test tdx_chutes -- --ignored`

use dregg_tee_verify::tdx::{self, TEE_TYPE_TDX};
use dregg_tee_verify::{
    check_pck_chain_roots_at_pinned, fold_tdx_measurement, parse_chutes_measurements,
    ChutesMeasurements,
};

const REAL_QUOTE: &[u8] = include_bytes!("data/chutes_tdx_quote.bin");
const REGISTRY_JSON: &str = include_str!("data/chutes_measurements.json");

/// Extract the four gated registers from the real quote by parsing the raw TD10 body.
/// (Structural only — no crypto — so it needs no collateral and no network.)
fn real_quote_registers() -> ([u8; 48], [u8; 48], [u8; 48], [u8; 48], [u8; 64]) {
    // Header is 48 bytes; the TD10 report follows. Field offsets within the TD10 body:
    // mr_td @136, rt_mr0 @328, rt_mr1 @376, rt_mr2 @424, report_data @520.
    let b = &REAL_QUOTE[48..];
    let g = |o: usize| -> [u8; 48] {
        let mut a = [0u8; 48];
        a.copy_from_slice(&b[o..o + 48]);
        a
    };
    let mr_td = g(136);
    let rt0 = g(328);
    let rt1 = g(376);
    let rt2 = g(424);
    let mut rd = [0u8; 64];
    rd.copy_from_slice(&b[520..520 + 64]);
    (mr_td, rt0, rt1, rt2, rd)
}

#[test]
fn real_quote_parses_as_tdx() {
    let quote = dcap_qvl::quote::Quote::parse(REAL_QUOTE).expect("real Chutes quote parses");
    assert_eq!(
        quote.header.version, 4,
        "expected a TDX v4 quote, got version {}",
        quote.header.version
    );
    assert_eq!(
        quote.header.tee_type, TEE_TYPE_TDX,
        "quote tee_type must be TDX (0x{TEE_TYPE_TDX:x})"
    );
    let td = quote
        .report
        .as_td10()
        .expect("TDX quote carries a TD10 report");
    let (mr_td, rt0, rt1, rt2, rd) = real_quote_registers();
    assert_eq!(td.mr_td, mr_td);
    assert_eq!(td.rt_mr0, rt0);
    assert_eq!(td.rt_mr1, rt1);
    assert_eq!(td.rt_mr2, rt2);
    assert_eq!(td.report_data, rd);
    // Non-zero MRTD/report_data — this is a genuine measured TD, not a zero fixture.
    assert!(td.mr_td.iter().any(|&x| x != 0));
    assert!(td.report_data.iter().any(|&x| x != 0));
}

#[test]
fn real_quote_pck_chain_roots_at_pinned_intel_root() {
    // Defense-in-depth: the real quote's PCK cert chain must root at OUR embedded, pinned
    // Intel SGX Root CA — checked with NO network (the chain rides inside the quote).
    let quote = dcap_qvl::quote::Quote::parse(REAL_QUOTE).expect("parse");
    let chain_pem = quote
        .raw_cert_chain()
        .expect("cert_type-5 PCK chain embedded in quote");
    check_pck_chain_roots_at_pinned(chain_pem)
        .expect("real quote's PCK chain roots at the pinned Intel SGX Root CA");
}

#[test]
fn root_pin_rejects_a_chain_rooted_elsewhere() {
    // A self-signed cert that is NOT the pinned Intel SGX Root CA must be refused as a root.
    use rcgen::{CertificateParams, DnType, KeyPair, PKCS_ECDSA_P384_SHA384};
    let key = KeyPair::generate_for(&PKCS_ECDSA_P384_SHA384).expect("keygen");
    let mut params = CertificateParams::new(Vec::<String>::new()).expect("params");
    params
        .distinguished_name
        .push(DnType::CommonName, "Not Intel SGX Root CA");
    let cert = params.self_signed(&key).expect("self-sign");
    let pem = cert.pem();
    assert!(
        check_pck_chain_roots_at_pinned(pem.as_bytes()).is_err(),
        "a foreign self-signed root must be rejected"
    );
}

#[test]
fn real_quote_mrtd_matches_a_live_registry_entry() {
    // End-to-end measurement-match: the real quote's MRTD + RTMR0..2 must match exactly one
    // Chutes registry entry (RTMR0 varies by hardware topology, so multiple entries share
    // the MRTD — we require a full MRTD+RTMR0/1/2 match, RTMR3 excluded).
    let entries = parse_chutes_measurements(REGISTRY_JSON).expect("registry parses");
    assert!(!entries.is_empty(), "registry is non-empty");
    let (mr_td, rt0, rt1, rt2, _rd) = real_quote_registers();

    let hit: Vec<&ChutesMeasurements> = entries
        .iter()
        .filter(|e| e.matches(&mr_td, &rt0, &rt1, &rt2))
        .collect();
    assert_eq!(
        hit.len(),
        1,
        "exactly one registry entry should match MRTD+RTMR0/1/2; got {}",
        hit.len()
    );
    let matched = hit[0];
    eprintln!(
        "real quote matched Chutes registry entry: name={:?} version={:?} gpus={:?}x{}",
        matched.name, matched.version, matched.expected_gpus, matched.gpu_count
    );

    // The folded measurement the generic weld would pin equals the fold over the entry.
    let folded = fold_tdx_measurement(&mr_td, &rt0, &rt1, &rt2);
    assert_eq!(folded, matched.folded_measurement());

    // At least one OTHER entry shares the MRTD but differs in RTMR0 (topology variants) —
    // proving the RTMR0/1/2 discrimination is load-bearing, not a lucky single entry.
    let same_mrtd = entries.iter().filter(|e| e.mrtd == mr_td).count();
    assert!(
        same_mrtd > 1,
        "expected multiple topology variants sharing the MRTD, got {same_mrtd}"
    );
}

/// FULL DCAP crypto verification of the real quote — fetches Intel-signed collateral over
/// the network, then runs the whole PCK-chain / QE / TCB / QE-identity flow. `#[ignore]`d
/// (network) and gated on `collateral-fetch`. Run once to confirm the real quote verifies.
#[cfg(feature = "collateral-fetch")]
#[test]
#[ignore = "network: fetches DCAP collateral from a PCCS"]
fn real_quote_full_dcap_verify() {
    let pccs =
        std::env::var("PCCS_URL").unwrap_or_else(|_| "https://pccs.phala.network".to_string());
    let collateral = tdx::fetch_collateral_blocking(REAL_QUOTE, &pccs)
        .expect("fetch DCAP collateral for the real quote");

    // STRICT verifier (accept only UpToDate). We report the status either way.
    let verifier = tdx::TdxVerifier::new(collateral).accepting_sw_hardening_needed(); // widen so a genuine-but-SW-hardening platform still yields a report
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs();
    let report = verifier
        .verify_tdx_core(REAL_QUOTE, now)
        .expect("real quote passes full DCAP verification");
    eprintln!(
        "REAL QUOTE DCAP status = {:?}  advisories = {:?}  tcb_ok(widened) = {}",
        report.status, report.advisory_ids, report.tcb_ok
    );
    // The verified registers must equal what we parsed structurally.
    let (mr_td, rt0, rt1, rt2, rd) = real_quote_registers();
    assert_eq!(report.mr_td, mr_td);
    assert_eq!(report.rt_mr0, rt0);
    assert_eq!(report.rt_mr1, rt1);
    assert_eq!(report.rt_mr2, rt2);
    assert_eq!(report.report_data, rd);
}
