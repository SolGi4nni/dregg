//! Q2 — the certificate-carrying answer: query results that PROVE they
//! omitted nothing.
//!
//! The shape of the guarantee (the model: `Dregg2.Lightclient.MMR`
//! `server_cannot_omit_position`): the node commits its receipt log under an
//! MMR root; a query answer ships with a [`RangeCertificate`] — the range
//! opening of the receipt positions it was computed FROM. The verifier:
//!
//! 1. checks the opening against a TRUSTED root (obtained out-of-band today;
//!    pinned by `recStateCommit` once the `CommitBindsMMR` weld lands with
//!    THE ROTATION — at which point one light-client check pins it for the
//!    whole history, `light_client_position_non_omission`);
//! 2. concludes the receipt slice is EXACTLY positions `[lo, hi]` of the
//!    genuine log — no receipt hidden, none forged, none reordered;
//! 3. RE-DERIVES the answer: extracts the facts and re-runs the query
//!    locally. The server is not trusted for evaluation at all — the
//!    certificate makes the INPUT complete, recomputation makes the OUTPUT
//!    honest.
//!
//! What completeness means then splits on the CALM grade
//! ([`crate::classify`]):
//! - **Monotone** query: every returned row is FINAL — more receipts can only
//!   add rows, so "provably omitted nothing" holds unconditionally over the
//!   certified range.
//! - **FinalizedDependent** query: the rows are exact FOR THE CERTIFIED
//!   PREFIX — "fresh as of height `fresh_as_of`"; a later receipt (e.g. a
//!   revocation) may retract a row. The annotation travels with the answer.

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::classify::{Classification, classify};
use crate::fact::Height;
use crate::hexutil::serde_hex32;
use crate::mmr::{MmrError, MmrHasher, RangeOpening, verify_range};
use crate::query::{Bindings, Query, QueryError, eval};
use crate::receipt::{ReceiptError, ReceiptRecord, extract_facts};

/// The non-omission certificate for a receipt slice: the committed root the
/// server claims, the dense position range, and the range opening.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RangeCertificate {
    /// The MMR root of the receipt log this opening is against. The verifier
    /// compares it to a root it trusts — it is a CLAIM, not a proof, until
    /// matched.
    #[serde(with = "serde_hex32")]
    pub root: [u8; 32],
    /// First certified position (inclusive, dense `chain_index`).
    pub lo: u64,
    /// Last certified position (inclusive; clipped to the committed length).
    pub hi: u64,
    /// The positional range opening (peak frontier + per-slot paths).
    pub opening: RangeOpening,
}

/// A receipt slice with its non-omission certificate — the certified EDB.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttestedSlice {
    pub receipts: Vec<ReceiptRecord>,
    pub cert: RangeCertificate,
}

/// What an attested answer claims to be COMPLETE over. The non-omission
/// certificate proves the slice is EXACTLY positions `[lo, hi]` of the
/// genuine log (`server_cannot_omit_position`); coverage names how far that
/// range-completeness reaches relative to the WHOLE log:
///
/// - [`Coverage::WholeLog`] — the certified slice is the genuine log's whole
///   prefix `[0, len-1]` (the root-pinned length). For a MONOTONE query this
///   is the unqualified "provably omitted nothing" claim: every row of the
///   genuine log up to its head is present, and rows are final. The verifier
///   ENFORCES `lo == 0` and `hi` reaching the committed head — a server cannot
///   pass off a sub-range answer as a whole-log one.
/// - [`Coverage::Range`] — the answer is complete only over the certified
///   range `[lo, hi]`; rows derivable from positions OUTSIDE it are not
///   claimed. The honest shape for a partial scan (and the only sound shape
///   when the slice is not the full prefix). Rows are still final under append
///   when the query is monotone, but "the answer" is the answer FOR THIS RANGE.
///
/// This is the executable form of the model's `AnswerComplete h lo hi ans`
/// (`Dregg2/Lightclient/MMR.lean` `range_complete`): completeness is always
/// completeness OVER A RANGE; whole-log completeness is the special case
/// `lo = 0 ∧ hi ≥ len-1`, and coverage makes the caller declare which it has
/// and the verifier check it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Coverage {
    /// The certified slice is the whole genuine-log prefix `[0, head]`.
    WholeLog,
    /// Completeness is claimed only over the certified range.
    Range,
}

#[derive(Debug, Error)]
pub enum AttestError {
    #[error("certificate root does not match the trusted root")]
    UntrustedRoot,
    #[error(transparent)]
    Mmr(#[from] MmrError),
    #[error(transparent)]
    Receipt(#[from] ReceiptError),
    #[error("slot {slot}: receipt chain_index {got} != certified dense position {want}")]
    DenseIndex { slot: usize, got: u64, want: u64 },
    #[error(transparent)]
    Query(#[from] QueryError),
    #[error("answer rows do not match local re-evaluation over the certified slice")]
    RowsMismatch,
    #[error("carried classification does not match the classifier's verdict")]
    ClassificationMismatch,
    #[error("carried fresh_as_of {got} != certified slice's height frontier {want}")]
    Freshness { got: Height, want: Height },
    #[error(
        "answer claims whole-log coverage but the certified slice is positions \
         [{lo}, {hi}] of a length-{len} log — not the prefix [0, {head}]"
    )]
    CoverageNotWholeLog {
        lo: u64,
        hi: u64,
        len: u64,
        head: u64,
    },
}

impl AttestedSlice {
    /// Verify the slice against a trusted root: the opening verifies
    /// (`RVerifies` — count + per-slot positional openings) with the
    /// receipts' own `receipt_hash` values as the opened leaves, and each
    /// receipt's `chain_index` IS its certified dense position. On success
    /// the slice is exactly positions `[lo, min(hi, len-1)]` of the genuine
    /// log. Returns the root-pinned log length.
    pub fn verify<H: MmrHasher>(
        &self,
        hasher: &H,
        trusted_root: &[u8; 32],
    ) -> Result<u64, AttestError> {
        if &self.cert.root != trusted_root {
            return Err(AttestError::UntrustedRoot);
        }
        let mut values = Vec::with_capacity(self.receipts.len());
        for (slot, r) in self.receipts.iter().enumerate() {
            let want = self.cert.lo + slot as u64;
            if r.chain_index != want {
                return Err(AttestError::DenseIndex {
                    slot,
                    got: r.chain_index,
                    want,
                });
            }
            values.push(r.receipt_hash_bytes()?);
        }
        let len = verify_range(
            hasher,
            trusted_root,
            self.cert.lo,
            self.cert.hi,
            &values,
            &self.cert.opening,
        )?;
        Ok(len)
    }

    /// The height frontier of the slice — what a finalized-dependent answer
    /// is fresh as of.
    pub fn height_frontier(&self) -> Height {
        self.receipts.iter().map(|r| r.height).max().unwrap_or(0)
    }
}

/// **The certificate-carrying answer** — rows + the CALM annotation + the
/// freshness frontier + the certified EDB slice they were derived from.
/// Self-contained: [`AttestedAnswer::verify`] needs only a trusted root.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AttestedAnswer {
    /// The query the rows answer.
    pub query: Query,
    /// The answer rows (variable bindings, set semantics).
    pub rows: Vec<Bindings>,
    /// The CALM grade: monotone (rows final) vs finalized-dependent (rows
    /// correct as of `fresh_as_of` only).
    pub classification: Classification,
    /// What the answer is complete OVER: the whole genuine-log prefix, or
    /// only the certified range. Enforced by [`AttestedAnswer::verify`]
    /// against the certificate so a sub-range answer cannot pose as whole-log.
    pub coverage: Coverage,
    /// The certified slice's height frontier.
    pub fresh_as_of: Height,
    /// The certified EDB: receipts + their non-omission certificate.
    pub slice: AttestedSlice,
}

/// Evaluate `query` over a certified slice, producing the attested answer with
/// the honest [`Coverage::Range`] claim — complete over the certified range,
/// nothing claimed outside it. (The producer side — the CLI / SDK / node all
/// assemble answers through this so the carried annotation can never drift
/// from the classifier.)
pub fn answer(slice: AttestedSlice, query: Query) -> Result<AttestedAnswer, QueryError> {
    answer_with_coverage(slice, query, Coverage::Range)
}

/// Evaluate `query` over a certified slice that is the WHOLE genuine-log
/// prefix, producing a [`Coverage::WholeLog`] answer. The coverage claim is a
/// promise the verifier checks against the certificate: if the slice turns out
/// NOT to reach the committed head, [`AttestedAnswer::verify`] rejects it
/// (`CoverageNotWholeLog`) — so over-claiming whole-log coverage is caught,
/// not trusted. (For a MONOTONE query a verifying whole-log answer is the
/// unqualified "provably omitted nothing".)
pub fn answer_whole_log(slice: AttestedSlice, query: Query) -> Result<AttestedAnswer, QueryError> {
    answer_with_coverage(slice, query, Coverage::WholeLog)
}

fn answer_with_coverage(
    slice: AttestedSlice,
    query: Query,
    coverage: Coverage,
) -> Result<AttestedAnswer, QueryError> {
    let base = extract_facts(&slice.receipts);
    let rows = eval(&base, &query)?;
    let classification = classify(&query);
    let fresh_as_of = slice.height_frontier();
    Ok(AttestedAnswer {
        query,
        rows,
        classification,
        coverage,
        fresh_as_of,
        slice,
    })
}

impl AttestedAnswer {
    /// Full verification against a trusted root:
    ///
    /// 1. the slice's non-omission certificate verifies (the input was the
    ///    EXACT receipt range — `server_cannot_omit_position`), returning the
    ///    root-pinned log length;
    /// 2. the carried coverage matches the certificate: a [`Coverage::WholeLog`]
    ///    claim requires the certified range to be the whole prefix
    ///    `[0, len-1]` of that root-pinned length — a sub-range answer cannot
    ///    pose as whole-log (`CoverageNotWholeLog`);
    /// 3. the rows equal a local re-evaluation over that certified input
    ///    (evaluation is recomputed, never trusted);
    /// 4. the carried classification and freshness frontier match recomputation.
    pub fn verify<H: MmrHasher>(
        &self,
        hasher: &H,
        trusted_root: &[u8; 32],
    ) -> Result<(), AttestError> {
        // (1) the certified slice is exactly positions [lo, min(hi, len-1)] of
        // the genuine log; `len` is pinned by the trusted root.
        let len = self.slice.verify(hasher, trusted_root)?;
        // (2) coverage vs the certificate. WholeLog must reach BOTH ends: the
        // slice starts at position 0 AND the range's clip covers the head
        // (len-1). Without this a monotone sub-range answer would advertise the
        // unqualified "omitted nothing" while silently dropping the prefix/tail.
        if self.coverage == Coverage::WholeLog {
            let head = len.saturating_sub(1);
            let reaches_head = len == 0 || self.slice.cert.hi >= head;
            if self.slice.cert.lo != 0 || !reaches_head {
                return Err(AttestError::CoverageNotWholeLog {
                    lo: self.slice.cert.lo,
                    hi: self.slice.cert.hi,
                    len,
                    head,
                });
            }
        }
        // (3) recompute the rows over the certified input — evaluation trusted
        // to nobody.
        let base = extract_facts(&self.slice.receipts);
        let rows = eval(&base, &self.query)?;
        if rows != self.rows {
            return Err(AttestError::RowsMismatch);
        }
        // (4) the carried annotations.
        if classify(&self.query) != self.classification {
            return Err(AttestError::ClassificationMismatch);
        }
        let want = self.slice.height_frontier();
        if self.fresh_as_of != want {
            return Err(AttestError::Freshness {
                got: self.fresh_as_of,
                want,
            });
        }
        Ok(())
    }
}
