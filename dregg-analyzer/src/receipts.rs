//! Receipt-strand / receipt-graph capture analysis.
//!
//! ## Input format ([`ReceiptStrandCapture`])
//!
//! A strand is an ordered chain of the node's own [`dregg_turn::TurnReceipt`]s
//! (the attested who-did-what fact-base a turn produces on commit), in commit
//! order. Each receipt chain-links to its predecessor via
//! `previous_receipt_hash`. A capture is just `Vec<TurnReceipt>` plus, optionally,
//! the executor public key(s) so executor signatures can be verified.
//!
//! ## What is ATTESTED (real verifiers reused)
//!
//!   * **Chain integrity** — we recompute each receipt's hash with the REAL
//!     [`dregg_turn::TurnReceipt::receipt_hash`] (the `dregg-receipt-v3`
//!     domain-separated commitment that binds turn/forest/pre/post-state,
//!     federation, the prior link, and every disclosure bit) and check that
//!     `receipt[i].previous_receipt_hash == receipt[i-1].receipt_hash()`. A
//!     tampered receipt — any field touched — breaks its hash, so the link from
//!     the NEXT receipt no longer matches: the tamper is flagged at the break.
//!   * **Executor signature** (when a key is supplied) — verified against the
//!     real [`dregg_turn::TurnReceipt::canonical_executor_signed_message`] (v3,
//!     which binds the full receipt hash) using real Ed25519.
//!
//! ## What is OBSERVED (analyzer-derived)
//!
//!   * Conservation across the turn history: the `was_burn` disclosure bits
//!     (a `true` is a self-attested non-conservation event) and cumulative
//!     computron spend, surfaced from the chain.
//!   * State continuity: `receipt[i].pre_state_hash == receipt[i-1].post_state_hash`
//!     for a single-agent strand (a gap means a turn was applied off-strand).

use std::collections::HashSet;

use serde::{Deserialize, Serialize};

use dregg_turn::{Finality, TurnReceipt};

use crate::findings::{short_hex, AnalysisReport, Finding, Severity};

/// A captured receipt strand: an ordered chain of committed-turn receipts, with
/// optional executor keys for signature verification.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ReceiptStrandCapture {
    /// The receipts in commit order (each links to its predecessor via
    /// `previous_receipt_hash`).
    pub receipts: Vec<TurnReceipt>,
    /// Executor public keys (32-byte Ed25519), if available, to verify each
    /// receipt's `executor_signature`. Empty ⇒ signatures are reported as
    /// present/absent but not cryptographically checked.
    #[serde(default)]
    pub executor_keys: Vec<[u8; 32]>,
}

/// Analyze a receipt strand, attesting chain integrity against the real
/// `dregg_turn::TurnReceipt::receipt_hash`.
pub fn analyze(capture: &ReceiptStrandCapture) -> AnalysisReport {
    let mut report = AnalysisReport::new("receipts");
    let receipts = &capture.receipts;
    report.summarize("receipts_in_strand", receipts.len());

    if receipts.is_empty() {
        report.push(Finding::observed(
            Severity::Notice,
            "receipts.empty",
            "the receipt strand is empty — nothing to verify",
        ));
        return report;
    }

    // ── ATTEST: chain integrity (real receipt_hash recomputation) ─────────────
    let mut breaks = 0usize;
    let mut prev_hash = receipts[0].receipt_hash();
    // The first receipt may legitimately have no predecessor.
    if let Some(declared) = receipts[0].previous_receipt_hash {
        report.push(Finding::observed(
            Severity::Notice,
            "receipts.partial_strand",
            format!(
                "first captured receipt declares a predecessor ({}) not present in \
                 the capture — this is a strand SUFFIX, not the genesis receipt",
                short_hex(&declared)
            ),
        ));
    }
    for (i, rcpt) in receipts.iter().enumerate().skip(1) {
        match rcpt.previous_receipt_hash {
            Some(link) => {
                if link != prev_hash {
                    breaks += 1;
                    report.push(Finding::verified(
                        Severity::Critical,
                        "dregg_turn::TurnReceipt::receipt_hash",
                        "receipts.chain_break",
                        format!(
                            "chain integrity BROKEN at receipt #{i}: it links to \
                             prev={} but the recomputed hash of receipt #{} is {} \
                             — a receipt in the chain was tampered or reordered \
                             (the v3 receipt hash no longer matches)",
                            short_hex(&link),
                            i - 1,
                            short_hex(&prev_hash),
                        ),
                    ));
                }
            }
            None => {
                breaks += 1;
                report.push(Finding::verified(
                    Severity::Critical,
                    "dregg_turn::TurnReceipt::receipt_hash",
                    "receipts.chain_break",
                    format!(
                        "chain integrity BROKEN at receipt #{i}: it declares NO \
                         predecessor, but it is not the strand head — a link was \
                         severed",
                    ),
                ));
            }
        }
        prev_hash = rcpt.receipt_hash();
    }
    if breaks == 0 {
        report.push(Finding::verified(
            Severity::Info,
            "dregg_turn::TurnReceipt::receipt_hash",
            "receipts.chain_intact",
            format!(
                "receipt-chain integrity VERIFIED: all {} link(s) recompute exactly \
                 against the real dregg-receipt-v3 hash — no receipt was tampered \
                 or reordered",
                receipts.len().saturating_sub(1)
            ),
        ));
    }
    report.summarize("chain_breaks", breaks);

    // ── RECEIPT-LINK GRAPH: the who/where/how structure of the strand ─────────
    // Beyond the prev-hash spine, each receipt is a graph NODE carrying edges:
    // its acting `agent`, its `federation_id` (replay domain), and the cross-cell
    // edges it emitted (introduction exports / routing directives / capability
    // derivations). Every one of these fields is bound into the v3 `receipt_hash`,
    // so on an INTACT chain they are non-strippable — we can report them as the
    // attested graph, not mere self-description.
    analyze_link_graph(receipts, breaks, &mut report);

    // ── ATTEST: executor signatures (when keys supplied) ──────────────────────
    if !capture.executor_keys.is_empty() {
        analyze_executor_sigs(capture, &mut report);
    } else {
        let signed = receipts
            .iter()
            .filter(|r| r.executor_signature.is_some())
            .count();
        report.push(Finding::observed(
            Severity::Info,
            "receipts.executor_sig_presence",
            format!(
                "{signed} of {} receipt(s) carry an executor signature (no executor \
                 key supplied — signatures NOT cryptographically verified; pass \
                 executor_keys to attest them)",
                receipts.len()
            ),
        ));
    }

    // ── OBSERVED: conservation across the turn history ────────────────────────
    let burns = receipts.iter().filter(|r| r.was_burn).count();
    let total_computrons: u128 = receipts.iter().map(|r| r.computrons_used as u128).sum();
    report.summarize("total_computrons_used", total_computrons);
    report.summarize("non_conserving_turns_was_burn", burns);
    if burns == 0 {
        report.push(Finding::observed(
            Severity::Info,
            "receipts.conservation_disclosed",
            "no turn in the strand disclosed a Burn (`was_burn`): every committed \
             turn self-attests value conservation (the disclosure bit is bound \
             into the verified receipt hash, so it cannot be stripped)",
        ));
    } else {
        report.push(Finding::observed(
            Severity::Notice,
            "receipts.burn_disclosed",
            format!(
                "{burns} turn(s) disclosed a Burn (`was_burn = true`): total supply \
                 provably did not balance on those turns. This is a DISCLOSED \
                 (bound, non-strippable) non-conservation, not a hidden one",
            ),
        ));
    }

    // ── OBSERVED: state continuity (pre==post linkage) ────────────────────────
    let mut state_gaps = 0usize;
    for w in receipts.windows(2) {
        if w[1].pre_state_hash != w[0].post_state_hash {
            state_gaps += 1;
        }
    }
    report.summarize("state_continuity_gaps", state_gaps);
    if state_gaps > 0 {
        report.push(Finding::observed(
            Severity::Notice,
            "receipts.state_gap",
            format!(
                "{state_gaps} place(s) where receipt[i].pre_state_hash ≠ \
                 receipt[i-1].post_state_hash — turns were applied to this agent's \
                 cell off-strand (expected if the strand interleaves multiple \
                 agents; a red flag for a single-agent strand)"
            ),
        ));
    }

    report
}

/// Build the receipt-link graph view: the distinct acting agents, the federation
/// domain(s) the strand spans, the finality breakdown, the privacy-path count,
/// and the cross-cell edge totals (introductions / routing / derivations). All of
/// these fields are bound into the v3 receipt hash; when the chain verified
/// intact (`breaks == 0`) the graph is attested non-strippable, otherwise it is
/// surfaced as observed structure.
fn analyze_link_graph(receipts: &[TurnReceipt], breaks: usize, report: &mut AnalysisReport) {
    let chain_intact = breaks == 0;
    let graph_by = "dregg_turn::TurnReceipt::receipt_hash";

    // ── Nodes: distinct acting agents (the strand may interleave several) ──────
    let agents: HashSet<[u8; 32]> = receipts.iter().map(|r| *r.agent.as_bytes()).collect();
    report.summarize("distinct_agents", agents.len());

    // ── Replay domain: federation set. A strand that crosses federations is a ──
    // real signal — a receipt is bound to ONE `federation_id` to PREVENT
    // cross-federation replay, so >1 federation in a single linear strand means
    // the chain stitches distinct domains (expected for a relay log; a red flag
    // for a single-federation audit).
    let federations: HashSet<[u8; 32]> = receipts.iter().map(|r| r.federation_id).collect();
    report.summarize("distinct_federations", federations.len());
    if federations.len() > 1 {
        let f = Finding {
            severity: Severity::Notice,
            attestation: if chain_intact {
                crate::findings::Attestation::Verified { by: graph_by.into() }
            } else {
                crate::findings::Attestation::Observed
            },
            code: "receipts.cross_federation_strand".into(),
            message: format!(
                "the strand spans {} distinct federation_id(s) — receipts are \
                 federation-bound to block cross-federation replay, so a multi-\
                 federation linear strand stitches distinct replay domains \
                 (expected for a relay/aggregation log; a flag for a single-\
                 federation audit)",
                federations.len()
            ),
        };
        report.push(f);
    }

    // ── Finality breakdown: Tentative receipts are solo-mode, pre-quorum ───────
    let tentative = receipts
        .iter()
        .filter(|r| matches!(r.finality, Finality::Tentative))
        .count();
    let finalized = receipts.len() - tentative;
    report.summarize("receipts_final", finalized);
    report.summarize("receipts_tentative", tentative);
    if tentative > 0 {
        report.push(Finding::observed(
            Severity::Notice,
            "receipts.finality_tentative",
            format!(
                "{tentative} of {} receipt(s) are Tentative (solo-mode, awaiting \
                 BFT-quorum validation on rejoin) — safe only under a no-Byzantine \
                 assumption; {finalized} carry Final finality",
                receipts.len()
            ),
        ));
    } else {
        report.push(Finding::observed(
            Severity::Info,
            "receipts.finality_all_final",
            format!("all {} receipt(s) carry Final finality (BFT-quorum backed)", receipts.len()),
        ));
    }

    // ── Privacy path: receipts produced by decrypting an EncryptedTurn ─────────
    let encrypted = receipts.iter().filter(|r| r.was_encrypted).count();
    report.summarize("receipts_encrypted_path", encrypted);

    // ── Cross-cell edges: the graph beyond the linear spine ────────────────────
    let intro_edges: usize = receipts.iter().map(|r| r.introduction_exports.len()).sum();
    let routing_edges: usize = receipts.iter().map(|r| r.routing_directives.len()).sum();
    let derivation_edges: usize = receipts.iter().map(|r| r.derivation_records.len()).sum();
    let consumed_caps: usize = receipts.iter().map(|r| r.consumed_capabilities.len()).sum();
    report.summarize("introduction_export_edges", intro_edges);
    report.summarize("routing_directive_edges", routing_edges);
    report.summarize("capability_derivation_edges", derivation_edges);
    report.summarize("consumed_capability_edges", consumed_caps);

    let total_edges = intro_edges + routing_edges + derivation_edges;
    report.push(Finding {
        severity: Severity::Info,
        attestation: if chain_intact {
            crate::findings::Attestation::Verified { by: graph_by.into() }
        } else {
            crate::findings::Attestation::Observed
        },
        code: "receipts.link_graph".into(),
        message: format!(
            "receipt-link graph: {} node(s) over {} agent(s) and {} federation(s); \
             {} cross-cell edge(s) ({intro_edges} introduction, {routing_edges} \
             routing, {derivation_edges} derivation) + {consumed_caps} consumed-\
             capability authority edge(s){}",
            receipts.len(),
            agents.len(),
            federations.len(),
            total_edges,
            if chain_intact {
                " — every edge is bound into the verified receipt hash"
            } else {
                " (chain broken: edges are observed, not attested)"
            },
        ),
    });
}

/// Verify each receipt's executor signature against the supplied keys using the
/// real canonical v3 message. A signature that verifies under ANY supplied key
/// is accepted (a federation may rotate executors).
fn analyze_executor_sigs(capture: &ReceiptStrandCapture, report: &mut AnalysisReport) {
    use ed25519_dalek::{Signature, Verifier, VerifyingKey};

    let keys: Vec<VerifyingKey> = capture
        .executor_keys
        .iter()
        .filter_map(|k| VerifyingKey::from_bytes(k).ok())
        .collect();

    let mut verified = 0usize;
    let mut bad = 0usize;
    let mut missing = 0usize;
    for (i, rcpt) in capture.receipts.iter().enumerate() {
        let Some(sig_bytes) = &rcpt.executor_signature else {
            missing += 1;
            continue;
        };
        let Ok(sig_arr): Result<[u8; 64], _> = sig_bytes.as_slice().try_into() else {
            bad += 1;
            report.push(Finding::verified(
                Severity::Critical,
                "ed25519_dalek::Verifier",
                "receipts.executor_sig_malformed",
                format!("receipt #{i} executor_signature is not 64 bytes"),
            ));
            continue;
        };
        let sig = Signature::from_bytes(&sig_arr);
        let msg = rcpt.canonical_executor_signed_message();
        if keys.iter().any(|vk| vk.verify(&msg, &sig).is_ok()) {
            verified += 1;
        } else {
            bad += 1;
            report.push(Finding::verified(
                Severity::Critical,
                "dregg_turn::TurnReceipt::canonical_executor_signed_message",
                "receipts.executor_sig_invalid",
                format!(
                    "receipt #{i}: executor signature does NOT verify under any \
                     supplied executor key (forged, wrong key, or the receipt was \
                     tampered after signing) — turn_hash {}",
                    short_hex(&rcpt.turn_hash)
                ),
            ));
        }
    }
    report.summarize("executor_sigs_verified", verified);
    report.summarize("executor_sigs_invalid", bad);
    report.summarize("executor_sigs_missing", missing);
    if bad == 0 {
        report.push(Finding::verified(
            Severity::Info,
            "dregg_turn::TurnReceipt::canonical_executor_signed_message",
            "receipts.executor_sigs_ok",
            format!(
                "{verified} executor signature(s) VERIFIED against supplied key(s) \
                 via the real v3 canonical message; {missing} receipt(s) carried no \
                 signature"
            ),
        ));
    }
}
