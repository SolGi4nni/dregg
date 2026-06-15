//! Optional network/gossip capture analysis — peer behavior + eclipse-risk.
//!
//! ## Input format ([`NetworkCapture`])
//!
//! A best-effort capture of who-talked-to-whom during dissemination: a list of
//! [`GossipObservation`]s (a block id, the peer it was received from, and the
//! local wall-clock). This is the one source the analyzer does NOT attest with a
//! cryptographic verifier — gossip is a liveness signal, not a safety one — so
//! every finding here is honestly `Observed`. Its value is surfacing the
//! eclipse-risk shape (am I hearing about blocks from a healthily diverse set of
//! peers, or is one peer my sole source of truth?).

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::findings::{AnalysisReport, Finding, Severity, short_hex};

/// One observed gossip reception: a block, from whom, when.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GossipObservation {
    /// The block id (32 bytes) that was received.
    pub block_id: [u8; 32],
    /// The peer (node pubkey, 32 bytes) it was received from.
    pub from_peer: [u8; 32],
    /// Local wall-clock (unix millis) of reception. Informational.
    #[serde(default)]
    pub at_ms: i64,
}

/// A captured gossip/dissemination trace.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NetworkCapture {
    pub observations: Vec<GossipObservation>,
}

/// Analyze a gossip capture for peer behavior + eclipse-risk signals (all
/// observed, no cryptographic attestation — gossip is liveness, not safety).
pub fn analyze(capture: &NetworkCapture) -> AnalysisReport {
    let mut report = AnalysisReport::new("network");
    let obs = &capture.observations;
    report.summarize("gossip_observations", obs.len());

    if obs.is_empty() {
        report.push(Finding::observed(
            Severity::Notice,
            "network.empty",
            "no gossip observations captured",
        ));
        return report;
    }

    // Distinct peers + per-peer reception share.
    let mut per_peer: HashMap<[u8; 32], usize> = HashMap::new();
    let mut distinct_blocks: HashMap<[u8; 32], usize> = HashMap::new();
    for o in obs {
        *per_peer.entry(o.from_peer).or_default() += 1;
        *distinct_blocks.entry(o.block_id).or_default() += 1;
    }
    report.summarize("distinct_peers", per_peer.len());
    report.summarize("distinct_blocks_seen", distinct_blocks.len());

    // Blocks heard from only ONE peer: an eclipse adversary that is your sole
    // source for a block can withhold it (a liveness/eclipse hazard). Count how
    // many distinct blocks had a single distinct source.
    let mut block_sources: HashMap<[u8; 32], std::collections::HashSet<[u8; 32]>> = HashMap::new();
    for o in obs {
        block_sources
            .entry(o.block_id)
            .or_default()
            .insert(o.from_peer);
    }
    let single_sourced = block_sources.values().filter(|s| s.len() == 1).count();
    report.summarize("single_sourced_blocks", single_sourced);

    // Eclipse-risk heuristic: if one peer is the source of a dominant share of
    // receptions (or you have very few distinct peers), you are eclipse-exposed.
    let total = obs.len();
    let (top_peer, top_count) = per_peer
        .iter()
        .max_by_key(|(_, c)| **c)
        .map(|(p, c)| (*p, *c))
        .unwrap();
    let top_share = top_count as f64 / total as f64;
    report.summarize("top_peer_share", format!("{:.0}%", top_share * 100.0));

    if per_peer.len() < 2 {
        report.push(Finding::observed(
            Severity::Notice,
            "network.eclipse_single_peer",
            format!(
                "ECLIPSE RISK: all {total} block reception(s) came from a SINGLE \
                 peer ({}) — that peer is your sole view of the DAG and can \
                 withhold or delay any block (a liveness, not safety, hazard)",
                short_hex(&top_peer)
            ),
        ));
    } else if top_share > 0.8 {
        report.push(Finding::observed(
            Severity::Notice,
            "network.eclipse_dominant_peer",
            format!(
                "ECLIPSE-RISK SIGNAL: peer {} supplied {:.0}% of all receptions — a \
                 dominant single source narrows your dissemination diversity",
                short_hex(&top_peer),
                top_share * 100.0
            ),
        ));
    } else {
        report.push(Finding::observed(
            Severity::Info,
            "network.diverse_dissemination",
            format!(
                "dissemination diversity looks healthy: {} distinct peer(s), top \
                 peer share {:.0}%",
                per_peer.len(),
                top_share * 100.0
            ),
        ));
    }

    if single_sourced > 0 {
        report.push(Finding::observed(
            Severity::Notice,
            "network.single_sourced_blocks",
            format!(
                "{single_sourced} distinct block(s) were heard from only ONE peer — \
                 if that peer is adversarial it could have withheld them from you"
            ),
        ));
    }

    report
}
