//! Intel TDX (DCAP) attestation verifier — the TDX sibling of [`crate::snp`] and
//! [`crate::NitroVerifier`], wired for **Chutes** (Bittensor subnet 64)
//! confidential-compute attestations.
//!
//! A TDX quote is a versioned, ECDSA-signed statement produced by the Intel Quoting
//! Enclave (QE) that a specific **Trust Domain** (a confidential VM) is running with a
//! given set of measurements (`MRTD`, `RTMR0..3`) and 64 bytes of caller-chosen
//! `report_data`. Verifying it is the **DCAP** flow: the quote carries a PCK certificate
//! chain (leaf ← Intel SGX PCK CA ← **Intel SGX Root CA**); the QE report is signed by the
//! PCK key; the attestation key (which signed the TD report) is bound into the QE report;
//! and the TCB status of the platform is decided against Intel-signed collateral (TCB info
//! + QE identity). We do NOT hand-roll any of that crypto — it is delegated to the
//! audited [`dcap_qvl`] crate (`dcap-qvl` 0.5.2, MIT), whose [`dcap_qvl::verify::verify`]
//! runs the whole chain against Intel's embedded root. On top of it this module adds:
//!
//! 1. **a TEE-type gate** — the quote must be `TEE_TYPE_TDX` (`0x81`) or we refuse before
//!    touching the crypto;
//! 2. **a pinned-root defense-in-depth check** — we independently assert the quote's PCK
//!    certificate chain roots at a cert byte-identical (SHA-256) to the **embedded**
//!    `Intel SGX Root CA` (fingerprint
//!    `44A0196B2B99F889B8E149E95B807A350E7424964399E885A7CBB8CCFAB674D3`), the same anchor
//!    `dcap-qvl` uses internally — so a future crate change or a wrong collateral can never
//!    silently reanchor trust;
//! 3. **measurement folding** — `measurement = SHA-256(MRTD ‖ RTMR0 ‖ RTMR1 ‖ RTMR2)`
//!    (RTMR3 is runtime/event-log-extended and non-deterministic per instance, so it is
//!    excluded), mirroring SNP's [`crate::snp::SnpReport::folded_measurement`];
//! 4. **`report_data`** — the first 32 bytes of the TD report's 64-byte `report_data`,
//!    matching SNP's [`crate::snp::SnpReport::report_data_32`] convention;
//! 5. **a strict, operator-widenable TCB gate** — `tcb_ok` is `true` only when the
//!    verified status is in an accepted set (default: `{"UpToDate"}`); any down-level /
//!    out-of-date / configuration-needed / invalid status is `false`, which the
//!    [`crate::attest_data`] weld turns into `TcbBelowPolicy`.
//!
//! ## Freshness — the Chutes nonce path (replay kill)
//!
//! A TDX quote carries **no timestamp**, so there is no wall-clock freshness to check in
//! the trait entry ([`TdxVerifier::verify_report`] passes `SystemTime::now()` only to
//! bound the PCK-chain / collateral validity windows). Freshness instead rides in
//! `report_data`. Chutes binds, **exactly** (chutes-api `api/instance/util.py:1086-1088`,
//! `api/server/util.py`):
//!
//! ```text
//! report_data[0..32] == SHA-256( ascii(nonce_hex_string) ‖ ascii(e2e_pubkey_base64_string) )
//! ```
//!
//! where `nonce_hex_string` is the **64-character hex** attestation nonce the caller chose
//! (`hashlib.sha256((nonce + e2e_pubkey).encode())…`) and `e2e_pubkey_base64_string` is the
//! instance's ML-KEM-768 public key **base64 string exactly as returned by discovery**
//! (`instance.extra["e2e_pubkey"]`) — NOT the raw 1184 key bytes. The enclave writes the raw
//! 32-byte SHA-256 into `report_data[0..32]`; the API hex-encodes the full 64-byte
//! `report_data` (`quote.py:129` `td_report[520:584].hex().upper()`) and compares its first
//! 64 hex chars (`extract_nonce` = `report_data[:64].lower()`) against
//! `sha256(...).hexdigest().lower()`. At the raw-byte level this is precisely
//! `report_data[0..32] == sha256(ascii-concat)`, which is what we recompute here.
//! (`report_data[32..64]` separately binds the enclave TLS cert public-key hash — checked
//! server-side, not here.) [`TdxVerifier::verify_chutes_tdx`] recomputes the nonce/pubkey
//! binding and refuses any quote whose `report_data` does not match — so a captured quote
//! cannot be replayed against a new request, because the new request carries a nonce the old
//! quote never bound. This is the TDX half of the replay fix.

use std::collections::BTreeSet;
use std::time::{SystemTime, UNIX_EPOCH};

use dregg_cell::tee_attest::{TeeAttestationVerifier, TeeQuoteKind, TeeReportClaims};
use sha2::{Digest, Sha256};

use dcap_qvl::quote::Quote;
pub use dcap_qvl::QuoteCollateralV3;

/// TDX TEE type in the quote header. `dcap-qvl`'s own `constants::TEE_TYPE_TDX` is
/// crate-private (only `INTEL_QE_VENDOR_ID` is re-exported), so we mirror the value here —
/// `0x00000081`, confirmed against `dcap-qvl` 0.5.2 `src/constants.rs`
/// (`pub const TEE_TYPE_TDX: u32 = 0x00000081;`). SGX is `0x00000000`.
pub const TEE_TYPE_TDX: u32 = 0x0000_0081;

/// The pinned **Intel SGX Root CA** (PEM) — the trust anchor the whole DCAP PCK chain
/// must root at. Byte-identical to the root `dcap-qvl` embeds and to Intel's published
/// `Intel_SGX_Provisioning_Certification_RootCA.cer`. Pinning it here (as SNP pins the AMD
/// ARK and Nitro pins the AWS root G1) makes the trust anchor an explicit, auditable
/// constant of THIS crate rather than an implicit dependency detail.
pub const INTEL_SGX_ROOT_CA_PEM: &str = include_str!("intel_sgx_root_ca.pem");

/// SHA-256 fingerprint of the DER of [`INTEL_SGX_ROOT_CA_PEM`] — the value asserted
/// against the self-signed root of every quote's PCK chain. Subject
/// `CN=Intel SGX Root CA, O=Intel Corporation`.
pub const INTEL_SGX_ROOT_CA_SHA256: [u8; 32] = [
    0x44, 0xA0, 0x19, 0x6B, 0x2B, 0x99, 0xF8, 0x89, 0xB8, 0xE1, 0x49, 0xE9, 0x5B, 0x80, 0x7A, 0x35,
    0x0E, 0x74, 0x24, 0x96, 0x43, 0x99, 0xE8, 0x85, 0xA7, 0xCB, 0xB8, 0xCC, 0xFA, 0xB6, 0x74, 0xD3,
];

/// The default accepted TCB status — STRICT: only a fully up-to-date platform passes.
pub const DEFAULT_ACCEPTED_STATUS: &str = "UpToDate";

/// Length of a TDX measurement register (`MRTD` / `RTMR0..3`).
pub const MR_LEN: usize = 48;

/// The full, time-independent result of verifying a TDX quote: the DCAP-verified status
/// plus every measurement register and the raw 64-byte `report_data`. Kept richer than
/// [`TeeReportClaims`] so the Chutes measurement/nonce binding can be checked
/// field-by-field with precise errors before folding to the trait's 32-byte claims.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TdxVerifiedReport {
    /// Folded code identity: `SHA-256(MRTD ‖ RTMR0 ‖ RTMR1 ‖ RTMR2)` (RTMR3 excluded).
    pub measurement: [u8; 32],
    /// The TD report's full 64-byte `report_data` (the caller-bound field).
    pub report_data: [u8; 64],
    pub mr_td: [u8; MR_LEN],
    pub rt_mr0: [u8; MR_LEN],
    pub rt_mr1: [u8; MR_LEN],
    pub rt_mr2: [u8; MR_LEN],
    /// Runtime/event-log-extended register — carried for inspection, NEVER gated on.
    pub rt_mr3: [u8; MR_LEN],
    /// The DCAP TCB status string (`"UpToDate"`, `"OutOfDate"`, `"SWHardeningNeeded"`, …).
    pub status: String,
    /// Intel advisory IDs attached to the status (e.g. `INTEL-SA-*`).
    pub advisory_ids: Vec<String>,
    /// Whether `status` is in the verifier's accepted set (the pinned TCB policy).
    pub tcb_ok: bool,
}

impl TdxVerifiedReport {
    /// The first 32 bytes of `report_data` — the bound commitment, matching SNP's
    /// [`crate::snp::SnpReport::report_data_32`].
    pub fn report_data_32(&self) -> [u8; 32] {
        let mut r = [0u8; 32];
        r.copy_from_slice(&self.report_data[..32]);
        r
    }

    /// Fold to the trait's [`TeeReportClaims`].
    pub fn to_claims(&self) -> TeeReportClaims {
        TeeReportClaims {
            measurement: self.measurement,
            report_data: self.report_data_32(),
            tcb_ok: self.tcb_ok,
        }
    }
}

/// `measurement = SHA-256(MRTD ‖ RTMR0 ‖ RTMR1 ‖ RTMR2)`. RTMR3 is deliberately excluded
/// (runtime/event-log-extended — non-deterministic per instance, per Intel/Chutes).
pub fn fold_tdx_measurement(
    mr_td: &[u8; MR_LEN],
    rt_mr0: &[u8; MR_LEN],
    rt_mr1: &[u8; MR_LEN],
    rt_mr2: &[u8; MR_LEN],
) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(mr_td);
    h.update(rt_mr0);
    h.update(rt_mr1);
    h.update(rt_mr2);
    h.finalize().into()
}

/// The Chutes `report_data` binding: `SHA-256( ascii(nonce_hex) ‖ ascii(e2e_pubkey_b64) )`.
///
/// **Both arguments are the ASCII STRINGS Chutes concatenates**, not raw bytes:
/// `nonce_hex` is the 64-char hex attestation-nonce string and `e2e_pubkey_b64` is the
/// base64 ML-KEM-768 public-key string exactly as discovery returns it. This matches
/// chutes-api byte-for-byte (`hashlib.sha256((nonce + e2e_pubkey).encode()).hexdigest()`,
/// `api/instance/util.py:1086-1088`) — the enclave writes the raw 32-byte digest into
/// `report_data[0..32]`, so the verifier recomputes it and requires equality (the
/// replay-kill). Hashing the *strings* (not the decoded key bytes) is the interop-critical
/// point: a verifier that hashed the raw 1184 key bytes would reject every real quote.
pub fn chutes_report_data_binding(nonce_hex: &str, e2e_pubkey_b64: &str) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(nonce_hex.as_bytes());
    h.update(e2e_pubkey_b64.as_bytes());
    h.finalize().into()
}

/// Expected Chutes ML-KEM-768 end-to-end public-key length in RAW bytes (after base64
/// decoding). The binding hashes the base64 STRING, but as a fail-closed sanity check the
/// base64 must decode to exactly this many bytes (a well-formed ML-KEM-768 key).
pub const ML_KEM_768_PUBKEY_LEN: usize = 1184;

/// Length of the Chutes attestation nonce as a hex string (64 hex chars = 32 bytes), per
/// chutes-api `validate_user_nonce` (`api/server/util.py`).
pub const CHUTES_NONCE_HEX_LEN: usize = 64;

/// The Intel TDX (DCAP) attestation verifier. Holds the Intel-signed **collateral**
/// (`QuoteCollateralV3`: PCK CRL chain, root CRL, TCB info + signature, QE identity +
/// signature) the DCAP flow needs, and the accepted-TCB-status policy. Collateral is
/// supplied pre-fetched (production) — the lean verify path touches no network; the
/// optional `collateral-fetch` feature adds a client for tests / tooling.
pub struct TdxVerifier {
    collateral: QuoteCollateralV3,
    accepted_statuses: BTreeSet<String>,
}

impl TdxVerifier {
    /// Build a verifier over pre-fetched `collateral`, STRICT TCB policy (accept only
    /// `"UpToDate"`).
    pub fn new(collateral: QuoteCollateralV3) -> TdxVerifier {
        let mut accepted = BTreeSet::new();
        accepted.insert(DEFAULT_ACCEPTED_STATUS.to_string());
        TdxVerifier {
            collateral,
            accepted_statuses: accepted,
        }
    }

    /// Build from a JSON-serialized [`QuoteCollateralV3`] (the shape a PCCS / Chutes
    /// collateral cache stores). Fail-closed: malformed JSON is an `Err`.
    pub fn from_collateral_json(json: &str) -> Result<TdxVerifier, String> {
        let collateral: QuoteCollateralV3 =
            serde_json::from_str(json).map_err(|e| format!("collateral JSON parse: {e}"))?;
        Ok(TdxVerifier::new(collateral))
    }

    /// Replace the accepted-status set (STRICT default is `{"UpToDate"}`). An operator who
    /// knowingly accepts, e.g., a platform needing SW hardening passes the wider set here —
    /// the widening is explicit, never a default.
    pub fn with_accepted_statuses<I, S>(mut self, statuses: I) -> TdxVerifier
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.accepted_statuses = statuses.into_iter().map(Into::into).collect();
        self
    }

    /// Convenience widening: accept `"UpToDate"` and `"SWHardeningNeeded"` (a common,
    /// deliberately-chosen operator policy for platforms pending a microcode SW mitigation).
    pub fn accepting_sw_hardening_needed(self) -> TdxVerifier {
        self.with_accepted_statuses(["UpToDate", "SWHardeningNeeded"])
    }

    /// The accepted-status set (for inspection / tests).
    pub fn accepted_statuses(&self) -> &BTreeSet<String> {
        &self.accepted_statuses
    }

    /// The time-independent crypto core: parse the quote, gate on TDX, pin the PCK-chain
    /// root, run the full DCAP verification against the pinned collateral at `now_secs`,
    /// and extract the measurement registers + `report_data`. `now_secs` bounds the
    /// PCK-chain and collateral validity windows only (a TDX quote has no timestamp of its
    /// own). Fail-closed at every step.
    pub fn verify_tdx_core(
        &self,
        report_bytes: &[u8],
        now_secs: u64,
    ) -> Result<TdxVerifiedReport, String> {
        // 1. Parse + TEE-type gate.
        let quote = Quote::parse(report_bytes).map_err(|e| format!("TDX quote parse: {e}"))?;
        if quote.header.tee_type != TEE_TYPE_TDX {
            return Err(format!(
                "not a TDX quote: tee_type=0x{:x} (want TEE_TYPE_TDX=0x{:x})",
                quote.header.tee_type, TEE_TYPE_TDX
            ));
        }

        // 2. Pinned-root defense-in-depth: the quote's PCK chain must root at OUR embedded
        //    Intel SGX Root CA, independent of what dcap-qvl trusts internally.
        let cert_chain_pem = quote
            .raw_cert_chain()
            .map_err(|e| format!("TDX quote PCK cert chain (need cert_type 5): {e}"))?;
        check_pck_chain_roots_at_pinned(cert_chain_pem)?;

        // 3. Full DCAP verification (PCK chain → Intel root, QE sig, attestation-key
        //    binding, quote sig, TCB status, QE identity). Delegated to dcap-qvl.
        let verified = dcap_qvl::verify::verify(report_bytes, &self.collateral, now_secs)
            .map_err(|e| format!("DCAP verify failed: {e:#}"))?;

        // 4. Extract the TD report (TD10, or the TD10 base of a TD15).
        let td = verified
            .report
            .as_td10()
            .ok_or("verified quote is not a TDX TD report")?;

        let mr_td = td.mr_td;
        let rt_mr0 = td.rt_mr0;
        let rt_mr1 = td.rt_mr1;
        let rt_mr2 = td.rt_mr2;
        let rt_mr3 = td.rt_mr3;
        let measurement = fold_tdx_measurement(&mr_td, &rt_mr0, &rt_mr1, &rt_mr2);
        let tcb_ok = self.accepted_statuses.contains(&verified.status);

        Ok(TdxVerifiedReport {
            measurement,
            report_data: td.report_data,
            mr_td,
            rt_mr0,
            rt_mr1,
            rt_mr2,
            rt_mr3,
            status: verified.status,
            advisory_ids: verified.advisory_ids,
            tcb_ok,
        })
    }

    /// **The Chutes replay-safe verify.** Runs [`Self::verify_tdx_core`] at wall-clock now,
    /// then binds the result to the caller's fresh `nonce_hex` (64-char hex string) + the
    /// instance `e2e_pubkey_b64` (the base64 pubkey string from discovery), killing replay,
    /// and to the expected registry `expected` measurements. Returns the folded
    /// [`TeeReportClaims`] (`tcb_ok` rides in the claims; the weld enforces it).
    pub fn verify_chutes_tdx(
        &self,
        quote: &[u8],
        nonce_hex: &str,
        e2e_pubkey_b64: &str,
        expected: &ChutesMeasurements,
    ) -> Result<TeeReportClaims, String> {
        let now = now_secs();
        let rep = self.verify_tdx_core(quote, now)?;
        apply_chutes_bindings(&rep, nonce_hex, e2e_pubkey_b64, expected)
    }
}

impl TeeAttestationVerifier for TdxVerifier {
    fn verify_report(
        &self,
        kind: TeeQuoteKind,
        report_bytes: &[u8],
    ) -> Result<TeeReportClaims, String> {
        if kind != TeeQuoteKind::IntelTdx {
            return Err(format!("TdxVerifier handles IntelTdx only, got {kind:?}"));
        }
        // A TDX quote has no timestamp; `now` only bounds cert/collateral validity.
        // Quote freshness (anti-replay) is enforced by the nonce bound into report_data
        // via `verify_chutes_tdx` / the weld's report_data commitment check — NOT here.
        let rep = self.verify_tdx_core(report_bytes, now_secs())?;
        Ok(rep.to_claims())
    }
}

/// Bind an already-DCAP-verified [`TdxVerifiedReport`] to a Chutes request: check the
/// `report_data` nonce binding (replay-kill) and the expected registry measurements. This
/// is the exact security-critical logic [`TdxVerifier::verify_chutes_tdx`] applies after
/// the crypto core; exposed so it is unit-testable in isolation from the DCAP crypto.
///
/// Fail-closed: an empty or non-64-hex nonce string, a base64 pubkey that does not decode to
/// exactly 1184 ML-KEM-768 bytes, a `report_data` that does not equal
/// `SHA-256(ascii(nonce_hex) ‖ ascii(e2e_pubkey_b64))`, or any measurement mismatch (`MRTD`,
/// `RTMR0..2`; RTMR3 is NOT checked) is an `Err`. `tcb_ok` is passed through into the
/// returned claims.
///
/// `nonce_hex` is the 64-char hex attestation-nonce string; `e2e_pubkey_b64` is the base64
/// pubkey string discovery returns. Both are hashed **as ASCII strings** (see
/// [`chutes_report_data_binding`]).
pub fn apply_chutes_bindings(
    rep: &TdxVerifiedReport,
    nonce_hex: &str,
    e2e_pubkey_b64: &str,
    expected: &ChutesMeasurements,
) -> Result<TeeReportClaims, String> {
    use base64::Engine;

    // (a) Nonce binding — the replay-kill. A fresh per-request nonce means a captured
    //     quote cannot satisfy this for a new request. The nonce is a 64-char hex string
    //     (32 bytes), matching chutes-api `validate_user_nonce`.
    if nonce_hex.is_empty() {
        return Err("Chutes nonce is empty (a fresh 64-hex-char nonce is required)".into());
    }
    if nonce_hex.len() != CHUTES_NONCE_HEX_LEN || !nonce_hex.bytes().all(|b| b.is_ascii_hexdigit())
    {
        return Err(format!(
            "Chutes nonce must be a {CHUTES_NONCE_HEX_LEN}-char hex string (32 bytes), got {} chars",
            nonce_hex.len()
        ));
    }
    // The binding hashes the base64 STRING; as a fail-closed sanity check the string must
    // base64-decode to a well-formed 1184-byte ML-KEM-768 key. (We still HASH the string.)
    let decoded = base64::engine::general_purpose::STANDARD
        .decode(e2e_pubkey_b64)
        .map_err(|e| format!("Chutes e2e pubkey is not valid base64: {e}"))?;
    if decoded.len() != ML_KEM_768_PUBKEY_LEN {
        return Err(format!(
            "Chutes e2e pubkey must base64-decode to {ML_KEM_768_PUBKEY_LEN} bytes (ML-KEM-768), got {}",
            decoded.len()
        ));
    }
    let want_rd = chutes_report_data_binding(nonce_hex, e2e_pubkey_b64);
    if rep.report_data_32() != want_rd {
        return Err(
            "report_data is not SHA-256(ascii(nonce_hex) ‖ ascii(e2e_pubkey_b64)): replayed or unbound quote".into(),
        );
    }

    // (b) Measurement match against the expected registry entry — MRTD + RTMR0..2.
    //     RTMR3 (runtime/event-log-extended) is intentionally NOT checked.
    if rep.mr_td != expected.mrtd {
        return Err("MRTD does not match the expected Chutes registry entry".into());
    }
    if rep.rt_mr0 != expected.boot_rtmrs[0] {
        return Err("RTMR0 does not match the expected Chutes registry entry".into());
    }
    if rep.rt_mr1 != expected.boot_rtmrs[1] {
        return Err("RTMR1 does not match the expected Chutes registry entry".into());
    }
    if rep.rt_mr2 != expected.boot_rtmrs[2] {
        return Err("RTMR2 does not match the expected Chutes registry entry".into());
    }

    Ok(rep.to_claims())
}

/// Wall-clock now in seconds (0 if the clock is before the epoch — never negative).
fn now_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// Assert the PCK certificate chain (PEM, leaf → … → root) roots at the pinned
/// [`INTEL_SGX_ROOT_CA_PEM`]: it must contain a self-signed cert whose DER SHA-256 equals
/// the pinned fingerprint, and no OTHER self-signed root. Fail-closed on an empty chain, a
/// non-pinned self-signed root, or no root at all. Public so it can be exercised directly
/// against a real quote's cert chain without network collateral.
pub fn check_pck_chain_roots_at_pinned(cert_chain_pem: &[u8]) -> Result<(), String> {
    use x509_parser::prelude::*;

    let want = INTEL_SGX_ROOT_CA_SHA256;
    let mut saw_any = false;
    let mut found_pinned_root = false;

    for block in x509_parser::pem::Pem::iter_from_buffer(cert_chain_pem) {
        let block = block.map_err(|e| format!("PCK chain PEM parse: {e}"))?;
        if block.label != "CERTIFICATE" {
            return Err(format!(
                "PCK chain block label is {:?}, expected CERTIFICATE",
                block.label
            ));
        }
        saw_any = true;
        let (_, cert) = X509Certificate::from_der(&block.contents)
            .map_err(|e| format!("PCK chain cert parse: {e}"))?;
        // A self-signed cert (issuer == subject) is a trust anchor: it MUST be the pinned
        // Intel SGX Root CA, or the chain is anchored somewhere we do not trust.
        if cert.issuer() == cert.subject() {
            let fp: [u8; 32] = Sha256::digest(&block.contents).into();
            if fp == want {
                found_pinned_root = true;
            } else {
                return Err(
                    "PCK chain contains a self-signed root that is NOT the pinned Intel SGX Root CA"
                        .into(),
                );
            }
        }
    }

    if !saw_any {
        return Err("empty PCK certificate chain".into());
    }
    if !found_pinned_root {
        return Err("PCK chain does not root at the pinned Intel SGX Root CA".into());
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------
// Chutes measurements registry
// ---------------------------------------------------------------------------------------

/// One entry of the Chutes TEE measurements registry
/// (`https://api.chutes.ai/servers/tee/measurements`): the expected `MRTD` + boot/runtime
/// RTMRs for a named server image, with GPU expectations. Parsed from the registry JSON
/// (48-byte hex values, `boot_rtmrs`/`runtime_rtmrs` = `{RTMR0..RTMR3}`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChutesMeasurements {
    pub version: String,
    pub name: String,
    pub mrtd: [u8; MR_LEN],
    /// `[RTMR0, RTMR1, RTMR2, RTMR3]` at boot. Only 0..2 are gated (RTMR3 excluded).
    pub boot_rtmrs: [[u8; MR_LEN]; 4],
    /// `[RTMR0, RTMR1, RTMR2, RTMR3]` extended at runtime (informational).
    pub runtime_rtmrs: [[u8; MR_LEN]; 4],
    pub expected_gpus: Vec<String>,
    pub gpu_count: u32,
}

impl ChutesMeasurements {
    /// Does a verified quote's registers match this entry's `MRTD` + `RTMR0..2`? (RTMR3 is
    /// not checked — runtime/event-log-extended.)
    pub fn matches(
        &self,
        mr_td: &[u8; MR_LEN],
        rt_mr0: &[u8; MR_LEN],
        rt_mr1: &[u8; MR_LEN],
        rt_mr2: &[u8; MR_LEN],
    ) -> bool {
        &self.mrtd == mr_td
            && &self.boot_rtmrs[0] == rt_mr0
            && &self.boot_rtmrs[1] == rt_mr1
            && &self.boot_rtmrs[2] == rt_mr2
    }

    /// The folded code identity this entry pins:
    /// `SHA-256(MRTD ‖ RTMR0 ‖ RTMR1 ‖ RTMR2)` — the value to pin as a generic weld's
    /// `expected_measurement`.
    pub fn folded_measurement(&self) -> [u8; 32] {
        fold_tdx_measurement(
            &self.mrtd,
            &self.boot_rtmrs[0],
            &self.boot_rtmrs[1],
            &self.boot_rtmrs[2],
        )
    }
}

#[derive(serde::Deserialize)]
struct RtmrsWire {
    #[serde(rename = "RTMR0")]
    rtmr0: String,
    #[serde(rename = "RTMR1")]
    rtmr1: String,
    #[serde(rename = "RTMR2")]
    rtmr2: String,
    #[serde(rename = "RTMR3")]
    rtmr3: String,
}

impl RtmrsWire {
    fn to_array(&self) -> Result<[[u8; MR_LEN]; 4], String> {
        Ok([
            hex48(&self.rtmr0, "RTMR0")?,
            hex48(&self.rtmr1, "RTMR1")?,
            hex48(&self.rtmr2, "RTMR2")?,
            hex48(&self.rtmr3, "RTMR3")?,
        ])
    }
}

#[derive(serde::Deserialize)]
struct ChutesWire {
    version: String,
    name: String,
    mrtd: String,
    boot_rtmrs: RtmrsWire,
    runtime_rtmrs: RtmrsWire,
    #[serde(default)]
    expected_gpus: Vec<String>,
    #[serde(default)]
    gpu_count: u32,
}

/// Decode a 48-byte register from a hex string (case-insensitive). Fail-closed on bad hex
/// or a wrong length.
fn hex48(s: &str, what: &str) -> Result<[u8; MR_LEN], String> {
    let bytes = hex::decode(s.trim()).map_err(|e| format!("{what} hex decode: {e}"))?;
    if bytes.len() != MR_LEN {
        return Err(format!(
            "{what} must be {MR_LEN} bytes, got {}",
            bytes.len()
        ));
    }
    let mut out = [0u8; MR_LEN];
    out.copy_from_slice(&bytes);
    Ok(out)
}

impl ChutesWire {
    fn into_measurements(self) -> Result<ChutesMeasurements, String> {
        Ok(ChutesMeasurements {
            mrtd: hex48(&self.mrtd, "mrtd")?,
            boot_rtmrs: self.boot_rtmrs.to_array()?,
            runtime_rtmrs: self.runtime_rtmrs.to_array()?,
            version: self.version,
            name: self.name,
            expected_gpus: self.expected_gpus,
            gpu_count: self.gpu_count,
        })
    }
}

/// Parse the Chutes TEE measurements registry JSON (a top-level array of entries) into
/// typed [`ChutesMeasurements`]. Fail-closed on malformed JSON or a bad hex/length value.
pub fn parse_chutes_measurements(json: &str) -> Result<Vec<ChutesMeasurements>, String> {
    let wire: Vec<ChutesWire> =
        serde_json::from_str(json).map_err(|e| format!("Chutes measurements JSON parse: {e}"))?;
    wire.into_iter()
        .map(ChutesWire::into_measurements)
        .collect()
}

/// Try to decode a quote/evidence field that may be base64 (standard) or hex. Chutes
/// serves the quote base64-encoded; this normalizes to raw bytes. Fail-closed if it is
/// neither.
pub fn decode_quote_field(field: &str) -> Result<Vec<u8>, String> {
    use base64::Engine;
    let t = field.trim();
    if let Ok(b) = base64::engine::general_purpose::STANDARD.decode(t) {
        return Ok(b);
    }
    hex::decode(t).map_err(|_| "quote field is neither valid base64 nor hex".to_string())
}

/// Fetch DCAP collateral for `quote` from a PCCS/PCS URL (e.g. Phala PCCS
/// `https://pccs.phala.network`) using `dcap-qvl`'s default HTTP client, blocking on a
/// short-lived Tokio runtime. Gated behind the `collateral-fetch` feature so the default
/// build (and TCB) stays network-free — production supplies a pre-fetched
/// [`QuoteCollateralV3`]. Used by the real-quote integration test.
#[cfg(feature = "collateral-fetch")]
pub fn fetch_collateral_blocking(
    quote: &[u8],
    pccs_url: &str,
) -> Result<QuoteCollateralV3, String> {
    use dcap_qvl::collateral::CollateralClient;
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(|e| format!("tokio runtime: {e}"))?;
    rt.block_on(async {
        CollateralClient::with_default_http(pccs_url)
            .map_err(|e| format!("collateral client: {e:#}"))?
            .fetch(quote)
            .await
            .map_err(|e| format!("collateral fetch: {e:#}"))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The pinned root fingerprint constant matches the SHA-256 of the embedded PEM's DER.
    #[test]
    fn pinned_root_fingerprint_matches_embedded_pem() {
        let block = x509_parser::pem::Pem::iter_from_buffer(INTEL_SGX_ROOT_CA_PEM.as_bytes())
            .next()
            .expect("embedded root PEM present")
            .expect("embedded root PEM parses");
        let fp: [u8; 32] = Sha256::digest(&block.contents).into();
        assert_eq!(
            fp, INTEL_SGX_ROOT_CA_SHA256,
            "embedded Intel SGX Root CA fingerprint drifted from the pinned constant"
        );
    }

    #[test]
    fn measurement_fold_excludes_rtmr3_and_is_stable() {
        let a = [1u8; MR_LEN];
        let b = [2u8; MR_LEN];
        let c = [3u8; MR_LEN];
        let d = [4u8; MR_LEN];
        let m1 = fold_tdx_measurement(&a, &b, &c, &d);
        // Changing RTMR3 (a 5th, non-input register) cannot change the fold — the fold has
        // no RTMR3 input, so any two reports differing only in RTMR3 fold identically.
        let m2 = fold_tdx_measurement(&a, &b, &c, &d);
        assert_eq!(m1, m2);
        // But changing an INCLUDED register must change it (canary the fold is real).
        let mut a2 = a;
        a2[0] ^= 0xFF;
        assert_ne!(m1, fold_tdx_measurement(&a2, &b, &c, &d));
        let mut c2 = c;
        c2[47] ^= 0x01;
        assert_ne!(m1, fold_tdx_measurement(&a, &b, &c2, &d));
    }

    use base64::Engine as _;

    /// A well-formed 1184-byte ML-KEM-768 public key, base64-encoded (STANDARD), from a
    /// deterministic byte pattern — so `apply_chutes_bindings`' base64/length sanity gate
    /// passes and we exercise the real string-hash path.
    fn valid_pubkey_b64(seed: u8) -> String {
        let bytes: Vec<u8> = (0..ML_KEM_768_PUBKEY_LEN)
            .map(|i| ((i as u32).wrapping_mul(37).wrapping_add(11 + seed as u32) % 256) as u8)
            .collect();
        base64::engine::general_purpose::STANDARD.encode(bytes)
    }

    /// A valid 64-char hex nonce string.
    const NONCE_HEX_A: &str = "931d8dd0add203ac3d8b4fbde75e115278eefcdceac5b87671a748f32364dfcb";
    const NONCE_HEX_B: &str = "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff";

    /// Build a synthetic verified report whose `report_data[0..32]` is the Chutes binding.
    fn synth_report(
        nonce_hex: &str,
        pubkey_b64: &str,
        mrtd: [u8; MR_LEN],
        r0: [u8; MR_LEN],
        r1: [u8; MR_LEN],
        r2: [u8; MR_LEN],
    ) -> TdxVerifiedReport {
        let mut rd = [0u8; 64];
        rd[..32].copy_from_slice(&chutes_report_data_binding(nonce_hex, pubkey_b64));
        // Non-zero second half, mirroring a real Chutes quote.
        for (i, b) in rd[32..].iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(7).wrapping_add(1);
        }
        TdxVerifiedReport {
            measurement: fold_tdx_measurement(&mrtd, &r0, &r1, &r2),
            report_data: rd,
            mr_td: mrtd,
            rt_mr0: r0,
            rt_mr1: r1,
            rt_mr2: r2,
            rt_mr3: [0x99u8; MR_LEN],
            status: "UpToDate".to_string(),
            advisory_ids: vec![],
            tcb_ok: true,
        }
    }

    fn expected_entry(
        mrtd: [u8; MR_LEN],
        r0: [u8; MR_LEN],
        r1: [u8; MR_LEN],
        r2: [u8; MR_LEN],
    ) -> ChutesMeasurements {
        ChutesMeasurements {
            version: "1.3.1".to_string(),
            name: "test".to_string(),
            mrtd,
            boot_rtmrs: [r0, r1, r2, [0xEEu8; MR_LEN]],
            runtime_rtmrs: [[0u8; MR_LEN]; 4],
            expected_gpus: vec!["h200".to_string()],
            gpu_count: 8,
        }
    }

    #[test]
    fn nonce_binding_accepts_matching_and_rejects_tamper() {
        let nonce = NONCE_HEX_A;
        let pubkey = valid_pubkey_b64(0);
        let mrtd = [0x11u8; MR_LEN];
        let r0 = [0x22u8; MR_LEN];
        let r1 = [0x33u8; MR_LEN];
        let r2 = [0x44u8; MR_LEN];
        let rep = synth_report(nonce, &pubkey, mrtd, r0, r1, r2);
        let expected = expected_entry(mrtd, r0, r1, r2);

        // Matching nonce + pubkey + measurements → accept.
        let claims = apply_chutes_bindings(&rep, nonce, &pubkey, &expected)
            .expect("matching binding accepts");
        assert_eq!(claims.report_data, rep.report_data_32());
        assert_eq!(claims.measurement, rep.measurement);
        assert!(claims.tcb_ok);

        // Tampered nonce (different valid 64-hex) → reject (the replay-kill: a captured quote
        // bound the OLD nonce, so a new request's nonce does not match).
        assert!(apply_chutes_bindings(&rep, NONCE_HEX_B, &pubkey, &expected).is_err());

        // Tampered pubkey (same length, different bytes) → reject.
        let bad_pk = valid_pubkey_b64(1);
        assert!(apply_chutes_bindings(&rep, nonce, &bad_pk, &expected).is_err());

        // Non-64-hex nonce → reject (fail-closed on malformed input).
        assert!(apply_chutes_bindings(&rep, "deadbeef", &pubkey, &expected).is_err());
        assert!(apply_chutes_bindings(&rep, "zz".repeat(32).as_str(), &pubkey, &expected).is_err());

        // Base64 that decodes to the wrong length → reject.
        let short_pk = base64::engine::general_purpose::STANDARD.encode([0u8; 32]);
        assert!(apply_chutes_bindings(&rep, nonce, &short_pk, &expected).is_err());
        // Non-base64 pubkey → reject.
        assert!(apply_chutes_bindings(&rep, nonce, "not valid base64 !!!", &expected).is_err());

        // Empty nonce → reject.
        assert!(apply_chutes_bindings(&rep, "", &pubkey, &expected).is_err());
    }

    /// Known-answer test: the binding is byte-for-byte the value chutes-api computes
    /// (`hashlib.sha256((nonce + e2e_pubkey).encode()).digest()`). The two expected digests
    /// below were produced by Python `hashlib` over the SAME inputs (see the lane's KAT
    /// derivation). This is the cross-implementation check that we hash the STRINGS the
    /// Chutes way, and it locks the encoding so a future refactor to raw-byte hashing fails
    /// loudly.
    #[test]
    fn report_data_binding_matches_chutes_python_kat() {
        // (a) chutes-api's own unit-test vector (TEST_GPU_NONCE + "dGVzdF9lMmVfcHVia2V5").
        //     Tests the pure binding function (this short pubkey is not a real 1184-byte key,
        //     so it exercises the formula, not the gate).
        let want_short =
            hex::decode("21a8d04d2de30e7f43a4e76dc8ad397f253d9a788652f005e1f07761c6d14991")
                .unwrap();
        assert_eq!(
            chutes_report_data_binding(NONCE_HEX_A, "dGVzdF9lMmVfcHVia2V5").to_vec(),
            want_short,
            "binding must equal Python sha256((nonce + e2e_pubkey).encode()) for the chutes vector"
        );

        // (b) a realistic 1184-byte ML-KEM-768 pubkey (bytes (i*37+11)%256), base64 STANDARD.
        //     valid_pubkey_b64(0) reproduces exactly those bytes, so its digest must equal the
        //     Python-computed one — and it passes the full gate.
        let pubkey = valid_pubkey_b64(0);
        let want_real =
            hex::decode("a0d271a97bba0245602ba9fd2523226770d33921323d5db07fa5fb95e30da5b3")
                .unwrap();
        assert_eq!(
            chutes_report_data_binding(NONCE_HEX_A, &pubkey).to_vec(),
            want_real,
            "binding for the realistic 1184-byte key must match the Python KAT"
        );

        // And the full verify path accepts a report carrying exactly that digest.
        let mrtd = [0x11u8; MR_LEN];
        let r0 = [0x22u8; MR_LEN];
        let r1 = [0x33u8; MR_LEN];
        let r2 = [0x44u8; MR_LEN];
        let rep = synth_report(NONCE_HEX_A, &pubkey, mrtd, r0, r1, r2);
        assert_eq!(rep.report_data_32().to_vec(), want_real);
        let expected = expected_entry(mrtd, r0, r1, r2);
        assert!(apply_chutes_bindings(&rep, NONCE_HEX_A, &pubkey, &expected).is_ok());
    }

    #[test]
    fn measurement_mismatch_rejects() {
        let nonce = NONCE_HEX_B;
        let pubkey = valid_pubkey_b64(2);
        let mrtd = [0x11u8; MR_LEN];
        let r0 = [0x22u8; MR_LEN];
        let r1 = [0x33u8; MR_LEN];
        let r2 = [0x44u8; MR_LEN];
        let rep = synth_report(nonce, &pubkey, mrtd, r0, r1, r2);

        // Wrong MRTD → reject.
        let mut wrong = expected_entry(mrtd, r0, r1, r2);
        wrong.mrtd[0] ^= 0xFF;
        assert!(apply_chutes_bindings(&rep, nonce, &pubkey, &wrong).is_err());

        // Wrong RTMR1 → reject.
        let mut wrong1 = expected_entry(mrtd, r0, r1, r2);
        wrong1.boot_rtmrs[1][10] ^= 0x01;
        assert!(apply_chutes_bindings(&rep, nonce, &pubkey, &wrong1).is_err());

        // Differing ONLY in RTMR3 (not gated) → still accept.
        let mut only_rtmr3 = expected_entry(mrtd, r0, r1, r2);
        only_rtmr3.boot_rtmrs[3] = [0x00u8; MR_LEN];
        assert!(apply_chutes_bindings(&rep, nonce, &pubkey, &only_rtmr3).is_ok());
    }

    #[test]
    fn root_pin_rejects_empty_and_non_certificate() {
        assert!(check_pck_chain_roots_at_pinned(b"").is_err());
        assert!(check_pck_chain_roots_at_pinned(b"not a pem at all").is_err());
    }

    #[test]
    fn wrong_kind_rejected() {
        // A verifier over empty-ish collateral still refuses a non-TDX kind before crypto.
        let collateral = QuoteCollateralV3 {
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
        };
        let v = TdxVerifier::new(collateral);
        assert!(v.verify_report(TeeQuoteKind::SevSnp, &[0u8; 16]).is_err());
    }

    #[test]
    fn accepted_status_policy_is_strict_by_default_and_widenable() {
        let collateral = QuoteCollateralV3 {
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
        };
        let strict = TdxVerifier::new(collateral);
        assert!(strict.accepted_statuses().contains("UpToDate"));
        assert!(!strict.accepted_statuses().contains("SWHardeningNeeded"));
        let wide = strict.accepting_sw_hardening_needed();
        assert!(wide.accepted_statuses().contains("UpToDate"));
        assert!(wide.accepted_statuses().contains("SWHardeningNeeded"));
        assert!(!wide.accepted_statuses().contains("OutOfDate"));
    }
}
