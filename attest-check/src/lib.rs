//! **The checker for the evidence `/dungeon attestation` hands a player.**
//!
//! ## Why this exists
//!
//! The Discord panel already gives a player two files: the raw Intel TDX quote that covered one
//! narrated turn, and a JSON sidecar naming the four things they can check about it. Four things
//! *named in prose and performed by nobody* is a manual to a verifier, not a verifier. This
//! module is the verifier, and the `dungeon-attest-check` binary is the program that runs
//! it on the two files as they were downloaded.
//!
//! ## Why it lives here, and why it is not a bot command
//!
//! A `/dungeon verify-narration` slash command would ask the player to trust the same bot that
//! produced the artifact to grade it. The artifact exists precisely so that is not necessary. So
//! the primary shape is a program the player runs on their own machine, over their own copy of
//! the bytes, with no network unless they ask for it.
//!
//! It is its OWN crate, above both halves it needs. Check 4 is about the RECEIPT: it recomputes
//! [`dungeon_on_dregg::narrator::tee_provenance_commitment`], whose domain separator and
//! length-prefixed preimage layout belong to the game crate, and restating that hash here would
//! make the checker agree with the emitter only until one of them changed. The TDX half is the
//! mirror image: every quote-side primitive below is a call into `dregg_tee_verify`, the crate
//! that owns the DCAP flow, never a re-implementation of it. Living inside EITHER of them would
//! push the other's dependencies onto every consumer, and `dungeon-on-dregg`'s consumers include
//! the wasm32 browser bundle, which has no business linking a DCAP verifier. See Cargo.toml.
//!
//! The Discord bot renders its own re-check panel from [`verify_record`] too, so the panel and
//! the player's program cannot report different things about the same row.
//!
//! ## The ceiling, which this module is careful not to exceed
//!
//! Checks 1, 2, 3, 4 and 5 all read a record against itself, against Intel's pinned root, and
//! against a published registry. **None of them decides whether the quote is genuine.** Only
//! check 6 does, and it needs Intel-signed DCAP collateral. Every rendering below says so, and
//! the verdict for a run without collateral is not a pass. [`NOT_ESTABLISHED`] states the ceiling
//! that holds even when all six are green.

use serde::{Deserialize, Serialize};

use dregg_tee_verify::tdx::{
    check_chutes_preimages_well_formed, check_pck_chain_roots_at_pinned, parse_chutes_measurements,
    pck_chain_structural_unverified, quote_sha256_hex, recheck_archived_binding,
    registers_structural_unverified, TdxVerifier,
};

use dungeon_on_dregg::narrator::{tee_provenance_commitment, TeeProvenance};

/// **The sentence about what a verified quote does NOT establish.** Printed by every run of the
/// checker, green or red, and carried in the sidecar itself so the file states its own ceiling
/// even when nobody runs the checker.
///
/// It is written to the same ceiling as the `/dungeon` footer (`where the text was produced, not
/// a claim about it`) and must never be widened past it: what the enclave measurement fixes is a
/// PLACE, and the tokens are not covered by any signature anywhere in this system.
pub const NOT_ESTABLISHED: &str =
    "What this does NOT establish: that the words you read are the words that enclave produced. \
     A verified quote fixes WHERE the narration was produced (an enclave whose code identity \
     folds to this measurement, accepted at this TCB verdict) and which key the request was \
     sealed to. It covers no token of the reply, it names no model or weights, and it is not a \
     claim that the narration is true. Prose is not power here either way: only a move the \
     executor admits changes the world.";

/// What checks 1 to 5 are worth on their own, printed whenever check 6 did not run. A quote an
/// attacker fabricated from nothing satisfies all five, because the attacker picks every byte
/// they compare.
pub const WITHOUT_COLLATERAL: &str =
    "Checks 1 to 5 read this record against itself, against the registry you pinned, and against \
     Intel's root certificate. They do NOT decide whether the quote is genuine: no signature is \
     verified by any of them, so a quote fabricated wholesale would pass all five. Check 6 is the \
     one that decides authenticity, and it needs Intel-signed DCAP collateral. Until it runs, \
     treat this as a record that has not been altered, not as an attestation.";

/// The `report_data` binding rule, stated in the sidecar so the file is self-describing.
pub const REPORT_DATA_RULE: &str =
    "report_data[0..32] == SHA-256(ascii(nonce_hex) || ascii(e2e_pubkey_b64))";

/// The receipt-commitment rule, stated in the sidecar.
pub const RECEIPT_BINDING_RULE: &str =
    "BLAKE3(\"dungeon-on-dregg/tee-provenance-v1:\" || measurement || len(instance_id) || \
     instance_id || len(tcb_status) || tcb_status || quote_sha256), bound into the named receipt";

/// What a verified quote DOES establish, stated in the sidecar beside [`NOT_ESTABLISHED`].
pub const WHAT_THIS_ESTABLISHES: &str =
    "WHERE this narration was produced: inside an Intel TDX enclave whose folded code identity is \
     `measurement_hex`, accepted by DCAP at `tcb_status`, holding the ML-KEM key the request was \
     sealed to. The dregg executor, not the model, moves the world.";

/// The command line that checks these two files.
pub const VERIFY_WITH: &str =
    "cargo run -p dregg-attest-check --bin dungeon-attest-check -- --quote <the .bin> --record \
     <this .json> --measurements <a pinned copy of the registry> [--collateral <DCAP collateral \
     JSON>]";

// ─────────────────────────────────────────────────────────────────────────────────────────────
// The sidecar
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// The `report_data` half of the sidecar: the rule and its two preimages.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReportDataBinding {
    /// The rule, spelled out ([`REPORT_DATA_RULE`]).
    pub rule: String,
    /// The fresh 64-hex attestation nonce.
    pub nonce_hex: String,
    /// The base64 ML-KEM-768 instance key the request was sealed to.
    pub e2e_pubkey_b64: String,
}

/// The receipt half of the sidecar: the rule and the commitment the landed receipt binds.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiptBinding {
    /// The rule, spelled out ([`RECEIPT_BINDING_RULE`]).
    pub rule: String,
    /// **The commitment READ OFF THE LANDED RECEIPT**, hex, not a value re-derived from the four
    /// fields above it.
    ///
    /// The distinction is the whole check. A re-derived commitment reproduces whatever the record
    /// currently says, so it agrees with an edited record as happily as an honest one; a value
    /// taken from the receipt is fixed, and every one of the four preimages has to reproduce it.
    /// `None` means the archive holds no such value, which check 4 reports as a FAILURE rather
    /// than as an absent question.
    pub tee_provenance_commit_hex: Option<String>,
}

/// **The JSON sidecar `/dungeon attestation` attaches beside the raw quote**, as one type.
///
/// It is a type and not an ad-hoc `json!` literal for a blunt reason: the bot SERIALIZES this and
/// the checker DESERIALIZES it, so a field the bot renames stops parsing instead of silently
/// reading as absent. Everything in it is either an archived fact or derived from archived facts
/// by [`NarrationAttestationRecord::of`], never prose the model wrote.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct NarrationAttestationRecord {
    /// [`WHAT_THIS_ESTABLISHES`].
    pub what_this_establishes: String,
    /// [`NOT_ESTABLISHED`] — the ceiling travels with the file.
    pub what_this_does_not_establish: String,
    /// The receipt this attestation covered, hex.
    pub receipt_hex: String,
    /// The configuration-derived backend label.
    pub provider: String,
    /// The model id.
    pub model: String,
    /// The enclave instance that served the call.
    pub instance_id: String,
    /// The folded code identity, hex: `SHA-256(MRTD ‖ RTMR0 ‖ RTMR1 ‖ RTMR2)`.
    pub measurement_hex: String,
    /// The DCAP TCB status accepted at narration time.
    pub tcb_status: String,
    /// SHA-256 of the raw quote, hex.
    pub quote_sha256_hex: String,
    /// Length of the raw quote in bytes.
    pub quote_len: usize,
    /// The session binding and its preimages.
    pub report_data_binding: ReportDataBinding,
    /// The receipt binding and its commitment.
    pub receipt_binding: ReceiptBinding,
    /// Where the published measurement registry lives.
    pub measurement_registry: String,
    /// Unix seconds the record was archived.
    pub archived_at_unix: i64,
    /// [`VERIFY_WITH`] — the file says how to check itself.
    pub verify_with: String,
}

/// The archived identity fields a record is built from: everything the bot's archive row holds
/// that is not the quote blob itself.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordIdentity {
    pub receipt_hex: String,
    pub provider: String,
    pub model: String,
    pub instance_id: String,
    pub measurement_hex: String,
    pub tcb_status: String,
    pub quote_sha256_hex: String,
    pub quote_len: usize,
    pub nonce_hex: String,
    pub e2e_pubkey_b64: String,
    /// The commitment the LANDED RECEIPT bound, hex, as the archive stored it. Empty means the
    /// archive has none, and check 4 fails rather than passing vacuously. **Never re-derive this
    /// from the four fields above** — see [`ReceiptBinding::tee_provenance_commit_hex`].
    pub receipt_commit_hex: String,
    pub measurement_registry: String,
    pub archived_at_unix: i64,
}

impl NarrationAttestationRecord {
    /// Build the sidecar from the archived identity fields. Everything DERIVABLE is derived here
    /// (the rules, the two prose ceilings, the verify command) so an emitter cannot write a
    /// wording the checker does not read; the receipt commitment is COPIED, never derived, for
    /// the reason on [`ReceiptBinding::tee_provenance_commit_hex`].
    pub fn of(id: RecordIdentity) -> NarrationAttestationRecord {
        let commit = Some(id.receipt_commit_hex.trim().to_string()).filter(|c| !c.is_empty());
        NarrationAttestationRecord {
            what_this_establishes: WHAT_THIS_ESTABLISHES.to_string(),
            what_this_does_not_establish: NOT_ESTABLISHED.to_string(),
            receipt_hex: id.receipt_hex,
            provider: id.provider,
            model: id.model,
            instance_id: id.instance_id,
            measurement_hex: id.measurement_hex,
            tcb_status: id.tcb_status,
            quote_sha256_hex: id.quote_sha256_hex,
            quote_len: id.quote_len,
            report_data_binding: ReportDataBinding {
                rule: REPORT_DATA_RULE.to_string(),
                nonce_hex: id.nonce_hex,
                e2e_pubkey_b64: id.e2e_pubkey_b64,
            },
            receipt_binding: ReceiptBinding {
                rule: RECEIPT_BINDING_RULE.to_string(),
                tee_provenance_commit_hex: commit,
            },
            measurement_registry: id.measurement_registry,
            archived_at_unix: id.archived_at_unix,
            verify_with: VERIFY_WITH.to_string(),
        }
    }

    /// The [`TeeProvenance`] preimage this record's four attestation fields name, when they
    /// decode. `None` means `measurement_hex` or `quote_sha256_hex` is not 32 bytes of hex.
    pub fn provenance(&self) -> Option<TeeProvenance> {
        Some(TeeProvenance::new(
            hex32(&self.measurement_hex)?,
            self.instance_id.clone(),
            self.tcb_status.clone(),
            hex32(&self.quote_sha256_hex)?,
        ))
    }
}

/// Decode exactly 32 bytes of hex, or `None`.
fn hex32(s: &str) -> Option<[u8; 32]> {
    hex::decode(s.trim()).ok()?.try_into().ok()
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// The checks
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// How one check came out. `NotRun` is deliberately NOT a pass: a check that did not run is an
/// unanswered question, and the verdict treats it as one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckState {
    Pass,
    Fail,
    NotRun,
}

impl CheckState {
    /// The one-word label.
    pub fn label(self) -> &'static str {
        match self {
            CheckState::Pass => "PASS",
            CheckState::Fail => "FAIL",
            CheckState::NotRun => "NOT RUN",
        }
    }

    /// A tick, a cross, or a question mark. `?` and not a tick for `NotRun`, on purpose.
    pub fn glyph(self) -> &'static str {
        match self {
            CheckState::Pass => "✓",
            CheckState::Fail => "✗",
            CheckState::NotRun => "?",
        }
    }
}

/// One numbered check and how it came out.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Check {
    /// The number the panel and the sidecar use for it.
    pub number: u8,
    /// The short name.
    pub name: &'static str,
    pub state: CheckState,
    /// What was actually compared, or why it could not be.
    pub detail: String,
}

impl Check {
    fn new(number: u8, name: &'static str, state: CheckState, detail: impl Into<String>) -> Check {
        Check {
            number,
            name,
            state,
            detail: detail.into(),
        }
    }

    fn from_result(number: u8, name: &'static str, result: Result<String, String>) -> Check {
        match result {
            Ok(detail) => Check::new(number, name, CheckState::Pass, detail),
            Err(why) => Check::new(number, name, CheckState::Fail, why),
        }
    }
}

/// The whole outcome of checking one record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Verification {
    /// The six checks, in order.
    pub checks: Vec<Check>,
}

/// The overall reading, which is never better than its weakest check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// At least one check failed. The record is broken; do not rely on it.
    Broken,
    /// Nothing failed, but the DCAP signature chain was not verified, so authenticity is
    /// UNDECIDED. This is the outcome of an offline run and it is not a pass.
    Unauthenticated,
    /// Every check ran and passed, including the Intel signature chain against collateral.
    Verified,
}

impl Verification {
    /// The failing checks, if any.
    pub fn failures(&self) -> Vec<&Check> {
        self.checks
            .iter()
            .filter(|c| c.state == CheckState::Fail)
            .collect()
    }

    /// The checks that did not run.
    pub fn not_run(&self) -> Vec<&Check> {
        self.checks
            .iter()
            .filter(|c| c.state == CheckState::NotRun)
            .collect()
    }

    /// The overall reading.
    pub fn verdict(&self) -> Verdict {
        if !self.failures().is_empty() {
            Verdict::Broken
        } else if !self.not_run().is_empty() {
            Verdict::Unauthenticated
        } else {
            Verdict::Verified
        }
    }

    /// The sentence for the verdict. Each one names what it is worth, not just whether it is
    /// green: `Unauthenticated` in particular reads as an unanswered question, because that is
    /// what it is.
    pub fn verdict_line(&self) -> String {
        match self.verdict() {
            Verdict::Broken => format!(
                "BROKEN: {} of {} checks FAILED ({}). Do not rely on this record; the failing \
                 lines above say exactly what is wrong with it.",
                self.failures().len(),
                self.checks.len(),
                self.failures()
                    .iter()
                    .map(|c| c.name)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Verdict::Unauthenticated => format!(
                "NOT AUTHENTICATED: {} of {} checks passed and {} did not run. The record is \
                 unaltered and its measurements are the ones it claims. Whether the quote is a \
                 genuine Intel TDX quote is UNDECIDED here.",
                self.checks.len() - self.not_run().len(),
                self.checks.len(),
                self.not_run().len()
            ),
            Verdict::Verified => format!(
                "VERIFIED: all {} checks passed, including the Intel signature chain. This quote \
                 is a genuine TDX quote, minted for this session, from an enclave in the registry \
                 you pinned, and its identity is the one the named receipt commits to.",
                self.checks.len()
            ),
        }
    }

    /// The exit status a program should carry out of this run.
    ///
    /// `0` only when everything ran AND passed. `1` on any failure. `3` when nothing failed but
    /// something did not run, so a script cannot read an offline run as a full pass by looking at
    /// the exit code alone.
    pub fn exit_code(&self) -> i32 {
        match self.verdict() {
            Verdict::Broken => 1,
            Verdict::Unauthenticated => 3,
            Verdict::Verified => 0,
        }
    }

    /// The full report, as the program prints it.
    pub fn render(&self) -> String {
        let mut out = String::new();
        for check in &self.checks {
            out.push_str(&format!(
                "[{}] {:<26} {:<8} {} {}\n",
                check.number,
                check.name,
                check.state.label(),
                check.state.glyph(),
                check.detail
            ));
        }
        out.push('\n');
        out.push_str(&self.verdict_line());
        out.push('\n');
        if self.verdict() != Verdict::Verified {
            out.push('\n');
            out.push_str(WITHOUT_COLLATERAL);
            out.push('\n');
        }
        out.push('\n');
        out.push_str(NOT_ESTABLISHED);
        out.push('\n');
        out
    }
}

/// **Run every check that can be run on these inputs.**
///
/// * `quote` — the raw bytes of the attached `.bin`.
/// * `record` — the parsed sidecar.
/// * `registry_json` — a copy of the Chutes measurements registry. `None` skips check 3, and
///   skipping is reported, never assumed. A registry FETCHED at check time is not a pin; the
///   program takes a file for that reason.
/// * `collateral_json` — Intel-signed DCAP `QuoteCollateralV3`. `None` skips check 6, which is
///   the only check that decides whether the quote is genuine.
/// * `accepted_statuses` — the TCB policy check 6 grades against. Empty means the strict default
///   (`UpToDate` only).
///
/// Every check runs independently: one failure does not suppress the others, because a reader
/// deserves to see the whole shape of a broken record rather than its first symptom.
pub fn verify_record(
    quote: &[u8],
    record: &NarrationAttestationRecord,
    registry_json: Option<&str>,
    collateral_json: Option<&str>,
    accepted_statuses: &[String],
) -> Verification {
    let registers = registers_structural_unverified(quote);

    let checks = vec![
        check_quote_digest(quote, record),
        check_session_binding(quote, record),
        check_measurement_registry(record, registers.as_ref(), registry_json),
        check_receipt_commitment(record),
        check_intel_root_pin(quote),
        check_dcap_chain(
            quote,
            registers.as_ref(),
            collateral_json,
            accepted_statuses,
        ),
    ];
    Verification { checks }
}

/// **Check 1.** `sha256` of the file equals the digest the record states, and the file is the
/// length the record states. The digest is the handle the receipt commitment was computed over,
/// so if this fails nothing downstream of it means anything.
fn check_quote_digest(quote: &[u8], record: &NarrationAttestationRecord) -> Check {
    let actual = quote_sha256_hex(quote);
    let stated = record.quote_sha256_hex.trim().to_ascii_lowercase();
    let result = if actual != stated {
        Err(format!(
            "the file hashes to {actual}, the record says {stated}. These are not the same bytes."
        ))
    } else if quote.len() != record.quote_len {
        Err(format!(
            "the file is {} bytes, the record says {}. The digest matched, so the record's length \
             field is wrong.",
            quote.len(),
            record.quote_len
        ))
    } else {
        Ok(format!(
            "sha256(quote) = {actual}, over {} bytes",
            quote.len()
        ))
    };
    Check::from_result(1, "quote digest", result)
}

/// **Check 2.** The quote's `report_data[0..32]` equals `SHA-256(ascii(nonce) ‖ ascii(pubkey))`
/// over the two strings in the record. This is what makes the quote THIS session's: a captured
/// quote binds the nonce it was minted for, and no other.
///
/// Well-formedness of the two preimages is checked first and fail-closed, so a record whose nonce
/// was truncated reports that rather than a bare mismatch.
fn check_session_binding(quote: &[u8], record: &NarrationAttestationRecord) -> Check {
    let binding = &record.report_data_binding;
    let result = check_chutes_preimages_well_formed(&binding.nonce_hex, &binding.e2e_pubkey_b64)
        .and_then(|()| recheck_archived_binding(quote, &binding.nonce_hex, &binding.e2e_pubkey_b64))
        .map(|()| {
            "report_data[0..32] is SHA-256 of the recorded nonce and instance key, concatenated \
             as ASCII"
                .to_string()
        });
    Check::from_result(2, "session binding", result)
}

/// **Check 3.** The quote's MRTD and RTMR0..2 match an entry in the registry the player pinned,
/// and folding those same four registers reproduces the record's `measurement_hex`.
///
/// The fold is the half that ties the record to the QUOTE: without it a record could name any
/// measurement it liked while attaching a quote measuring something else. RTMR3 is not compared
/// (runtime/event-log-extended, non-deterministic per instance).
fn check_measurement_registry(
    record: &NarrationAttestationRecord,
    registers: Result<&dregg_tee_verify::TdxRegisters, &String>,
    registry_json: Option<&str>,
) -> Check {
    let registers = match registers {
        Ok(r) => r,
        Err(why) => {
            return Check::new(3, "measurement registry", CheckState::Fail, why.to_string());
        }
    };
    let Some(json) = registry_json else {
        return Check::new(
            3,
            "measurement registry",
            CheckState::NotRun,
            format!(
                "no registry supplied. Pass a pinned copy of {} to run this check.",
                record.measurement_registry
            ),
        );
    };

    let folded = hex::encode(registers.folded_measurement());
    if folded != record.measurement_hex.trim().to_ascii_lowercase() {
        return Check::new(
            3,
            "measurement registry",
            CheckState::Fail,
            format!(
                "the quote's registers fold to {folded}, the record says {}. The record names a \
                 code identity the attached quote does not measure.",
                record.measurement_hex
            ),
        );
    }

    let entries = match parse_chutes_measurements(json) {
        Ok(e) => e,
        Err(why) => {
            return Check::new(
                3,
                "measurement registry",
                CheckState::Fail,
                format!("the registry did not parse: {why}"),
            );
        }
    };
    if entries.is_empty() {
        return Check::new(
            3,
            "measurement registry",
            CheckState::Fail,
            "the registry is empty, so it pins no code identity at all".to_string(),
        );
    }
    let hit = entries.iter().find(|e| {
        e.matches(
            &registers.mr_td,
            &registers.rt_mr0,
            &registers.rt_mr1,
            &registers.rt_mr2,
        )
    });
    let result = match hit {
        Some(entry) => Ok(format!(
            "MRTD and RTMR0..2 match registry entry {:?} version {:?}, and fold to {folded}",
            entry.name, entry.version
        )),
        None => Err(format!(
            "MRTD and RTMR0..2 match NONE of the {} registry entries. This enclave is not one the \
             registry you pinned publishes.",
            entries.len()
        )),
    };
    Check::from_result(3, "measurement registry", result)
}

/// **Check 4.** `BLAKE3` over the record's four attestation preimages reproduces the commitment
/// the LANDED RECEIPT bound, using [`dungeon_on_dregg::narrator::tee_provenance_commitment`] itself rather
/// than a restatement of it.
///
/// The stored commitment came off the receipt at land time and is not re-derived from the record,
/// which is what gives this check teeth on the two fields nothing else covers: `measurement_hex`
/// is tied to the quote by check 3 and `quote_sha256_hex` by check 1, but `instance_id` and
/// `tcb_status` are free text, and an edit to either changes the derivation away from the fixed
/// value the receipt holds.
///
/// What it does NOT establish: that the commitment really is on the chain. This compares against
/// a value the archive stored; the receipt itself is a different object. Run `/dungeon verify`,
/// which replays the receipt chain, and compare what it reports for the receipt named here.
fn check_receipt_commitment(record: &NarrationAttestationRecord) -> Check {
    let Some(stated) = record.receipt_binding.tee_provenance_commit_hex.as_ref() else {
        return Check::new(
            4,
            "receipt commitment",
            CheckState::Fail,
            "the record carries no receipt commitment, so nothing here ties it to a turn"
                .to_string(),
        );
    };
    let Some(provenance) = record.provenance() else {
        return Check::new(
            4,
            "receipt commitment",
            CheckState::Fail,
            "measurement_hex or quote_sha256_hex is not 32 bytes of hex, so the commitment cannot \
             be recomputed"
                .to_string(),
        );
    };
    let derived = hex::encode(tee_provenance_commitment(&provenance));
    let result = if derived == stated.trim().to_ascii_lowercase() {
        Ok(format!(
            "the four preimages derive {derived}, the commitment receipt {} bound. Run `/dungeon \
             verify` to replay that receipt chain.",
            short(&record.receipt_hex)
        ))
    } else {
        Err(format!(
            "the four preimages derive {derived}, receipt {} bound {stated}. One of the four \
             attestation fields has been edited since the turn landed.",
            short(&record.receipt_hex)
        ))
    };
    Check::from_result(4, "receipt commitment", result)
}

/// **Check 5.** The PCK certificate chain inside the quote roots at the pinned Intel SGX Root CA.
///
/// Offline and cheap, and worth exactly what it costs: it says the quote CLAIMS Intel's anchor.
/// It verifies no signature, so a fabricated quote that embeds Intel's (public) root passes. It
/// is here because a quote that does not even claim the right anchor is refutable for free.
fn check_intel_root_pin(quote: &[u8]) -> Check {
    let result = pck_chain_structural_unverified(quote)
        .and_then(|chain| check_pck_chain_roots_at_pinned(&chain))
        .map(|()| {
            "the embedded PCK chain contains the pinned Intel SGX Root CA and no other \
             self-signed root (this claims the anchor; it verifies no signature)"
                .to_string()
        });
    Check::from_result(5, "Intel root pin", result)
}

/// **Check 6, the one that decides authenticity.** The full DCAP verification against
/// Intel-signed collateral: PCK chain to the Intel root, QE signature, attestation-key binding,
/// quote signature, TCB status and QE identity, all delegated to `dcap-qvl` through
/// [`TdxVerifier`].
///
/// Also re-reads the verified registers and requires them to equal the ones check 3 read
/// structurally, so a quote whose signed body disagrees with its parsed body cannot pass both.
fn check_dcap_chain(
    quote: &[u8],
    registers: Result<&dregg_tee_verify::TdxRegisters, &String>,
    collateral_json: Option<&str>,
    accepted_statuses: &[String],
) -> Check {
    let Some(json) = collateral_json else {
        return Check::new(
            6,
            "DCAP signature chain",
            CheckState::NotRun,
            "no DCAP collateral supplied. This is the check that decides whether the quote is \
             genuine; without it, the five above are record consistency only."
                .to_string(),
        );
    };
    let verifier = match TdxVerifier::from_collateral_json(json) {
        Ok(v) => v,
        Err(why) => {
            return Check::new(
                6,
                "DCAP signature chain",
                CheckState::Fail,
                format!("the collateral did not parse: {why}"),
            );
        }
    };
    let verifier = if accepted_statuses.is_empty() {
        verifier
    } else {
        verifier.with_accepted_statuses(accepted_statuses.iter().cloned())
    };
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    let report = match verifier.verify_tdx_core(quote, now) {
        Ok(r) => r,
        Err(why) => {
            return Check::new(6, "DCAP signature chain", CheckState::Fail, why);
        }
    };
    if let Ok(structural) = registers {
        if report.mr_td != structural.mr_td
            || report.rt_mr0 != structural.rt_mr0
            || report.rt_mr1 != structural.rt_mr1
            || report.rt_mr2 != structural.rt_mr2
        {
            return Check::new(
                6,
                "DCAP signature chain",
                CheckState::Fail,
                "the VERIFIED registers differ from the ones read structurally, so checks 3 and 6 \
                 are looking at two different reports"
                    .to_string(),
            );
        }
    }
    if !report.tcb_ok {
        return Check::new(
            6,
            "DCAP signature chain",
            CheckState::Fail,
            format!(
                "the signature chain verified, but the TCB status is {:?}, which is not in the \
                 accepted set. The platform is below the policy this check was run under.",
                report.status
            ),
        );
    }
    Check::new(
        6,
        "DCAP signature chain",
        CheckState::Pass,
        format!(
            "the Intel signature chain verifies to the pinned root, TCB status {:?}{}",
            report.status,
            if report.advisory_ids.is_empty() {
                String::new()
            } else {
                format!(", advisories {:?}", report.advisory_ids)
            }
        ),
    )
}

/// The first 16 characters of a hex handle, for a line a person reads.
fn short(hexstr: &str) -> String {
    hexstr.chars().take(16).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn identity() -> RecordIdentity {
        RecordIdentity {
            receipt_hex: "11".repeat(32),
            provider: "chutes-tee".to_string(),
            model: "Qwen/Qwen3-32B-TEE".to_string(),
            instance_id: "1d5fdd83-instance".to_string(),
            measurement_hex: "7d".repeat(32),
            tcb_status: "UpToDate".to_string(),
            quote_sha256_hex: "ab".repeat(32),
            quote_len: 4096,
            nonce_hex: "cd".repeat(32),
            e2e_pubkey_b64: "QVRURVNURUQ=".to_string(),
            receipt_commit_hex: hex::encode(tee_provenance_commitment(&TeeProvenance::new(
                [0x7d; 32],
                "1d5fdd83-instance",
                "UpToDate",
                [0xab; 32],
            ))),
            measurement_registry: "https://api.chutes.ai/servers/tee/measurements".to_string(),
            archived_at_unix: 1_700_000_000,
        }
    }

    /// The sidecar carries the receipt's own commitment through unchanged, and the JSON the bot
    /// writes is the JSON the checker reads back.
    #[test]
    fn the_sidecar_carries_the_receipts_commitment_and_round_trips_as_json() {
        let id = identity();
        let commit = id.receipt_commit_hex.clone();
        let record = NarrationAttestationRecord::of(id);
        assert_eq!(
            record.receipt_binding.tee_provenance_commit_hex.as_deref(),
            Some(commit.as_str())
        );
        assert_eq!(check_receipt_commitment(&record).state, CheckState::Pass);

        let json = serde_json::to_string_pretty(&record).unwrap();
        let back: NarrationAttestationRecord = serde_json::from_str(&json).unwrap();
        assert_eq!(
            back, record,
            "the sidecar the bot writes is the one the checker reads"
        );
    }

    /// The reason the commitment is COPIED and not derived: a derived one would agree with an
    /// edited record. Editing the instance id (which no other check covers) must break check 4.
    #[test]
    fn editing_a_free_text_preimage_breaks_the_receipt_check() {
        let mut id = identity();
        id.instance_id = "1d5fdd83-instancf".to_string();
        let record = NarrationAttestationRecord::of(id);
        let check = check_receipt_commitment(&record);
        assert_eq!(check.state, CheckState::Fail);
        assert!(check.detail.contains("has been edited"), "{}", check.detail);
    }

    /// An archive with no stored commitment fails rather than passing vacuously.
    #[test]
    fn a_missing_receipt_commitment_is_a_failure_not_a_skip() {
        let mut id = identity();
        id.receipt_commit_hex = String::new();
        let record = NarrationAttestationRecord::of(id);
        let check = check_receipt_commitment(&record);
        assert_eq!(check.state, CheckState::Fail);
        assert!(check.detail.contains("no receipt commitment"));
    }

    /// `NotRun` is not a pass, and the exit code says so.
    #[test]
    fn a_check_that_did_not_run_is_not_a_pass() {
        let v = Verification {
            checks: vec![
                Check::new(1, "quote digest", CheckState::Pass, "ok"),
                Check::new(
                    6,
                    "DCAP signature chain",
                    CheckState::NotRun,
                    "no collateral",
                ),
            ],
        };
        assert_eq!(v.verdict(), Verdict::Unauthenticated);
        assert_eq!(v.exit_code(), 3);
        assert!(v.verdict_line().contains("UNDECIDED"));
        assert!(v.render().contains(WITHOUT_COLLATERAL));
        assert!(v.render().contains(NOT_ESTABLISHED));
    }

    /// A failure dominates, whatever else passed.
    #[test]
    fn one_failure_breaks_the_verdict() {
        let v = Verification {
            checks: vec![
                Check::new(1, "quote digest", CheckState::Pass, "ok"),
                Check::new(4, "receipt commitment", CheckState::Fail, "edited"),
                Check::new(6, "DCAP signature chain", CheckState::Pass, "ok"),
            ],
        };
        assert_eq!(v.verdict(), Verdict::Broken);
        assert_eq!(v.exit_code(), 1);
        assert!(v.verdict_line().contains("BROKEN"));
    }

    /// The ceiling sentence prints on a fully green run too. A verified quote still does not
    /// cover the tokens, and that is exactly when a reader is most likely to assume it does.
    #[test]
    fn the_ceiling_prints_even_when_everything_passes() {
        let v = Verification {
            checks: vec![Check::new(1, "quote digest", CheckState::Pass, "ok")],
        };
        assert_eq!(v.verdict(), Verdict::Verified);
        assert_eq!(v.exit_code(), 0);
        let rendered = v.render();
        assert!(rendered.contains(NOT_ESTABLISHED));
        assert!(
            !rendered.contains(WITHOUT_COLLATERAL),
            "the collateral caveat is for runs that skipped check 6"
        );
    }
}
