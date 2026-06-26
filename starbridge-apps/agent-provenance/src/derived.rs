//! # agent-provenance — the ATTESTED-QUERY showcase over the provenance log.
//!
//! A provenance SUMMARY is a derived view: `summary = f(events)`. The committed
//! hash chain of a log ([`entry_digests`](crate::entry_digests)) determines, by a
//! pure function, the log's length, its append cursor, and its chain tip. That is
//! a natural **derived view** — a value that is a verifiable function of the
//! committed events. This module wires the grounded dregg capability that makes
//! such a view's COMPLETENESS unforgeable to a light client:
//!
//! **The attested-query primitive** ([`dregg_query`]) — the log's entries are
//! receipt rows; a query over them carries a NON-OMISSION certificate (a range
//! opening against the receipt-log MMR root, the Rust embodiment of
//! `Dregg2/Lightclient/MMR.lean`'s `server_cannot_omit_position`). A verifier
//! checks the certificate against a trusted root and re-derives the rows, so a
//! verifying answer is provably computed from EXACTLY the committed entry range —
//! nothing hidden, nothing forged, nothing reordered. This is the COMPLETENESS
//! certificate over the log's provenance events: "these are ALL the provenance
//! entries, and I can prove none were omitted".
//!
//! Provenance entries are not balances, so the `dregg_cell::derived`
//! (`SumBalance`) derived-cell wiring the supply-chain showcase carries is not the
//! natural fit here; the attested-query + projection-summary are the provenance
//! log's subset of that showcase.
//!
//! ## What is grounded vs. projected
//!
//! [`summarize`] is the **projection-function form** of the derived view — the
//! pure `f(events)` shape, documented as the model the grounded certificate binds.
//! [`attested_provenance_log`] / [`verify_attested_provenance_log`] are the
//! **grounded attested-query** wiring over the real [`dregg_query`] MMR
//! certificate. Both are exercised in this module's tests.

use dregg_app_framework::{FieldElement, hex_encode_32};
use dregg_query::receipt::EffectSummary;
use dregg_query::{
    AttestError, AttestedAnswer, AttestedSlice, Blake3Mmr, Mmr, Pred, Query, RangeCertificate,
    ReceiptRecord, Term, answer_whole_log,
};
use dregg_types::CellId;

use crate::{entry_digests, entry_slot, verify_chain};

// =============================================================================
// (1) The projection-function form — `summary = f(events)`.
// =============================================================================

/// **A provenance-log summary** — the pure derived view of a log's committed hash
/// chain. Every field is a deterministic function of the claim sequence, so a
/// verifier holding the claims recomputes it exactly. This is the derived-view
/// SHAPE the grounded certificate below certifies against a root.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProvenanceLogSummary {
    /// How many provenance entries the log has committed (the chain length).
    pub length: usize,
    /// The append cursor — the index of the NEXT entry to be written (= the
    /// committed length, the value the log's `HEAD_SLOT` holds).
    pub head: u64,
    /// The chain tip — the latest committed link digest (the genesis-zero digest
    /// for an empty log).
    pub chain_tip: FieldElement,
    /// Whether the committed digests are EXACTLY the honest hash chain of the
    /// claims (every link folds the previous link with the next claim) — the
    /// tamper-evidence / connectedness witness ([`verify_chain`]).
    pub linked: bool,
}

/// **`summarize`** — fold a log's claim sequence into its [`ProvenanceLogSummary`].
/// The projection `f(events)`: the chain tip is the last link digest, the head is
/// the committed length, and `linked` is the [`verify_chain`] re-derivation over
/// the honest chain of these claims.
pub fn summarize(claims: &[FieldElement]) -> ProvenanceLogSummary {
    let digests = entry_digests(claims);
    ProvenanceLogSummary {
        length: claims.len(),
        head: claims.len() as u64,
        chain_tip: digests.last().copied().unwrap_or([0u8; 32]),
        linked: verify_chain(claims, &digests),
    }
}

// =============================================================================
// (2) The grounded attested-query — a completeness certificate over the events.
// =============================================================================

/// The per-entry receipt commitment (the MMR leaf value): a domain-separated
/// digest of the log cell, the committed link digest, and the entry index.
/// Deterministic, so a verifier recomputes the same leaf.
fn provenance_receipt_hash(log: &CellId, link: &FieldElement, index: usize) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-provenance-receipt\x01");
    h.update(log.as_bytes());
    h.update(link);
    h.update(&(index as u64).to_be_bytes());
    *h.finalize().as_bytes()
}

/// Build the receipt rows for a log's committed chain — one [`ReceiptRecord`] per
/// provenance entry, carrying an [`EffectSummary::Field`] for the entry-slot write
/// (the disclosed provenance event the fact extractor reads). The dense
/// `chain_index` is the entry position; the height is the same index (the log's
/// monotone append order).
pub fn provenance_receipts(log: &CellId, claims: &[FieldElement]) -> Vec<ReceiptRecord> {
    let digests = entry_digests(claims);
    let log_hex = hex_encode_32(log.as_bytes());
    digests
        .iter()
        .enumerate()
        .map(|(i, link)| ReceiptRecord {
            chain_index: i as u64,
            receipt_hash: hex_encode_32(&provenance_receipt_hash(log, link, i)),
            height: i as u64,
            agent: log_hex.clone(),
            effects: vec![EffectSummary::Field {
                cell: log_hex.clone(),
                index: entry_slot(i) as u64,
                value: hex_encode_32(link),
            }],
        })
        .collect()
}

/// A query for every committed entry of a log: `field(log, ?slot, ?digest,
/// ?height)`. A pure conjunctive scan (no aggregate, no negation) over the
/// per-entry slots, so the CALM classifier grades it MONOTONE — a verifying
/// whole-log answer is the unqualified "these are ALL the provenance entries, none
/// omitted". The slot is a VARIABLE because each entry lives at a distinct
/// `entry_slot(i)`.
pub fn provenance_log_query(log: &CellId) -> Query {
    Query::new().atom(
        Pred::Field,
        vec![
            Term::sym(hex_encode_32(log.as_bytes())),
            Term::var("slot"),
            Term::var("digest"),
            Term::var("height"),
        ],
    )
}

/// **Produce an attested provenance log** — the grounded `dregg_query` non-omission
/// certificate over a log's committed entries. Builds the receipt-log MMR over the
/// entry receipts, opens the WHOLE prefix, and evaluates [`provenance_log_query`]
/// over the certified slice ([`answer_whole_log`]). Returns the committed MMR
/// `root` (the trusted root a light client pins) and the certificate-carrying
/// [`AttestedAnswer`].
///
/// The answer, once it [`verify`](AttestedAnswer::verify)s against the returned
/// root, is provably computed from EXACTLY the committed entry range — a
/// completeness certificate over the log's provenance history.
pub fn attested_provenance_log(
    log: &CellId,
    claims: &[FieldElement],
) -> ([u8; 32], AttestedAnswer) {
    let receipts = provenance_receipts(log, claims);

    // The receipt-log MMR over the per-entry commitments.
    let mut mmr = Mmr::new(Blake3Mmr);
    for r in &receipts {
        mmr.push(r.receipt_hash_bytes().expect("our own 32-byte hex leaf"));
    }
    let root = mmr.root();
    let len = mmr.len();
    let hi = len.saturating_sub(1);
    let (_values, opening) = mmr.open_range(0, hi);

    let slice = AttestedSlice {
        receipts,
        cert: RangeCertificate {
            root,
            lo: 0,
            hi,
            opening,
        },
    };
    let answer = answer_whole_log(slice, provenance_log_query(log))
        .expect("the provenance-log query evaluates");
    (root, answer)
}

/// **Verify an attested provenance log** against a trusted `root` — the grounded
/// `dregg_query` verifier: the slice's non-omission certificate verifies (the
/// input was the EXACT entry range), the whole-log coverage matches the
/// certificate, and the rows equal a local re-evaluation. A tampered, omitted, or
/// reordered receipt makes this fail ([`AttestError`]).
pub fn verify_attested_provenance_log(
    answer: &AttestedAnswer,
    root: &[u8; 32],
) -> Result<(), AttestError> {
    answer.verify(&Blake3Mmr, root)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::claim_digest;

    fn demo_claims() -> Vec<FieldElement> {
        [
            "model:reasoning-step-1",
            "tool-call:web.search(...)",
            "final:answer",
        ]
        .iter()
        .map(|c| claim_digest(c.as_bytes()))
        .collect()
    }

    fn log_id() -> CellId {
        CellId::from_bytes([7u8; 32])
    }

    // ── (1) the projection-function derived view ─────────────────────────────

    #[test]
    fn summary_is_a_faithful_projection_of_the_chain() {
        let claims = demo_claims();
        let s = summarize(&claims);
        assert_eq!(s.length, 3);
        assert_eq!(s.head, 3);
        assert_eq!(s.chain_tip, *entry_digests(&claims).last().unwrap());
        assert!(s.linked, "the honest chain is a connected hash chain");
    }

    #[test]
    fn an_empty_log_summarizes_to_genesis() {
        let s = summarize(&[]);
        assert_eq!(s.length, 0);
        assert_eq!(s.head, 0);
        assert_eq!(s.chain_tip, [0u8; 32]);
        assert!(s.linked, "the empty chain trivially verifies");
    }

    // ── (2) the grounded attested-query (dregg_query) ────────────────────────

    #[test]
    fn the_attested_provenance_log_verifies_whole_log_completeness() {
        let log = log_id();
        let claims = demo_claims();
        let (root, answer) = attested_provenance_log(&log, &claims);

        // The certificate verifies against the committed root — the answer is
        // provably computed from EXACTLY the genuine entry range (non-omission).
        assert!(verify_attested_provenance_log(&answer, &root).is_ok());
        // One row per committed entry (3 entries).
        assert_eq!(
            answer.rows.len(),
            3,
            "every entry is in the certified answer"
        );
        assert_eq!(answer.coverage, dregg_query::Coverage::WholeLog);
    }

    #[test]
    fn a_tampered_receipt_breaks_the_certificate() {
        let log = log_id();
        let claims = demo_claims();
        let (root, mut answer) = attested_provenance_log(&log, &claims);
        assert!(verify_attested_provenance_log(&answer, &root).is_ok());

        // Tamper a receipt leaf in the certified slice — the MMR opening no longer
        // bags to the trusted root (the server cannot substitute a receipt).
        answer.slice.receipts[1].receipt_hash = hex_encode_32(&[0xAB; 32]);
        assert!(
            verify_attested_provenance_log(&answer, &root).is_err(),
            "a tampered receipt must break the non-omission certificate"
        );
    }

    #[test]
    fn an_omitted_entry_breaks_the_certificate() {
        let log = log_id();
        let claims = demo_claims();
        let (root, mut answer) = attested_provenance_log(&log, &claims);
        assert!(verify_attested_provenance_log(&answer, &root).is_ok());

        // Drop an entry from the certified slice — the dense count no longer matches
        // the root-pinned length (the omission tooth).
        answer.slice.receipts.pop();
        assert!(
            verify_attested_provenance_log(&answer, &root).is_err(),
            "an omitted entry must break the completeness certificate"
        );
    }
}
