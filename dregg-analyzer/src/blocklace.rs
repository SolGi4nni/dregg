//! Blocklace-DAG capture analysis.
//!
//! ## Input format ([`BlocklaceCapture`])
//!
//! A capture of a running node's blocklace is the node's own
//! [`dregg_blocklace::finality::CheckpointData`] (the exact struct
//! `persist::blocklace_store` writes to disk and `Blocklace::from_checkpoint`
//! consumes for peer catch-up) plus the consensus *context* a finality analysis
//! needs: the `participants` (the reference group / constitution member set used
//! for `tau` wave-leader election and the supermajority threshold) and the
//! ordering `wavelength`. Serialized as JSON or postcard.
//!
//! ## What is ATTESTED (real verifiers reused)
//!
//!   * **Block signatures + causal closure + equivocation** —
//!     [`dregg_blocklace::finality::Blocklace::from_checkpoint`] is the node's
//!     AUTHENTICATING loader: it runs real Ed25519 `verify_signature` on every
//!     block, enforces causal closure, and runs the real incomparability-based
//!     `detect_equivocation`. We feed the capture straight through it. A forged
//!     signature ⇒ the loader rejects the capture (we surface the exact error).
//!     A planted fork ⇒ the loader's `equivocators` set names the creator.
//!   * **Quorum threshold** — [`dregg_blocklace::supermajority_threshold`], THE
//!     one `⌊2n/3⌋+1` formula (the unified threshold from #170; the federation
//!     layer delegates to it).
//!   * **Finality / total order** — [`dregg_blocklace::ordering::tau_with_config`],
//!     the real Cordial-Miners ordering. We report how far finality has
//!     progressed (ordered prefix length, finalized turn count) from its output.
//!
//! ## What is OBSERVED (analyzer-derived structure)
//!
//!   * Causal-order reconstruction stats (frontier width, max chain depth).
//!   * Quorum-formation progress (how many distinct creators are represented).

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

use dregg_blocklace::finality::{Block, Blocklace, CheckpointData, Payload};
use dregg_blocklace::ordering::{OrderingConfig, tau_with_config};
use dregg_blocklace::supermajority_threshold;
// The ORDERING layer (`tau`) runs on the unsigned ordering-projection blocklace
// (`dregg_blocklace::Blocklace`, the `lib` type), which is DISTINCT from the
// authenticated `finality::Blocklace` the capture decodes to (different hash
// schemes). We authenticate on the finality lace, then project into the ordering
// lace exactly as the node's `blocklace_sync::build_ordering_blocklace` does.
use dregg_blocklace::{Block as OBlock, BlockId as OBlockId, Blocklace as OBlocklace};
use ed25519_dalek::SigningKey;

use crate::findings::{AnalysisReport, Finding, Severity, short_hex};

/// A captured blocklace DAG plus the consensus context a finality analysis
/// needs. This is the node's own checkpoint format ([`CheckpointData`]) lifted
/// with the reference-group participants and ordering wavelength.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BlocklaceCapture {
    /// The node's checkpoint: serialized blocks + tips/equivocators/ordering
    /// metadata. Exactly what `persist` writes and `from_checkpoint` reads.
    pub checkpoint: CheckpointData,
    /// The reference-group / constitution participant set (creator pubkeys) used
    /// for `tau` wave-leader election and the supermajority threshold.
    pub participants: Vec<[u8; 32]>,
    /// Ordering wavelength (rounds per wave). `None` ⇒ the protocol default (3).
    #[serde(default)]
    pub wavelength: Option<u64>,
}

impl BlocklaceCapture {
    fn ordering_config(&self) -> OrderingConfig {
        match self.wavelength {
            Some(w) => OrderingConfig { wavelength: w },
            None => OrderingConfig::default(),
        }
    }
}

/// Analyze a blocklace capture, attesting every checkable claim against the real
/// `dregg_blocklace` verifiers.
pub fn analyze(capture: &BlocklaceCapture) -> AnalysisReport {
    let mut report = AnalysisReport::new("blocklace");

    let n = capture.participants.len();
    let threshold = supermajority_threshold(n);
    report.summarize("participants", n);
    report.summarize(
        "quorum_threshold",
        format!("{threshold} (⌊2n/3⌋+1, the unified #170 supermajority)"),
    );
    report.summarize("blocks_in_capture", capture.checkpoint.blocks.len());

    // ── Pre-decode raw blocks for structural (observed) analysis ──────────────
    let raw: Vec<Block> = capture
        .checkpoint
        .blocks
        .iter()
        .filter_map(|b| Block::from_bytes(b))
        .collect();
    if raw.len() != capture.checkpoint.blocks.len() {
        report.push(Finding::observed(
            Severity::Critical,
            "blocklace.malformed_block",
            format!(
                "{} of {} captured blocks failed to deserialize as a dregg block",
                capture.checkpoint.blocks.len() - raw.len(),
                capture.checkpoint.blocks.len()
            ),
        ));
    }

    // ── ATTEST: feed the capture through the node's AUTHENTICATING loader ──────
    // `from_checkpoint` runs real Ed25519 verify_signature on every block,
    // enforces causal closure, and runs the real equivocation detection. We
    // supply a throwaway self-key (we are not a participant, only an auditor).
    let auditor_key = SigningKey::from_bytes(&[7u8; 32]);
    let lace = match Blocklace::from_checkpoint(&capture.checkpoint, auditor_key, threshold) {
        Ok(lace) => {
            report.push(Finding::verified(
                Severity::Info,
                "dregg_blocklace::finality::Blocklace::from_checkpoint",
                "blocklace.authenticated",
                format!(
                    "all {} block(s) passed real Ed25519 signature authentication \
                     and causal-closure; the DAG admits as a valid blocklace",
                    lace.len()
                ),
            ));
            Some(lace)
        }
        Err(e) => {
            // A forged signature, a dangling predecessor, or a malformed block:
            // the same rejection the live peer-receive path would issue.
            report.push(Finding::verified(
                Severity::Critical,
                "dregg_blocklace::finality::Blocklace::from_checkpoint",
                "blocklace.authentication_failed",
                format!(
                    "the captured DAG is NOT a valid blocklace — the node's own \
                     authenticating loader rejected it: {e}"
                ),
            ));
            None
        }
    };

    // ── ATTEST: equivocation evidence (real detect_equivocation) ──────────────
    // The authenticating loader populated `equivocators` via the real
    // incomparability check. (If the loader rejected the whole capture above we
    // re-derive from the trusted loader so we can still report the fork.)
    // When the authenticating loader admitted the capture we probe its lace for
    // the fork witness; when it rejected (a forged sig) we fall back to the
    // trusted loader purely to still ATTRIBUTE the fork. Keep that fallback lace
    // alive so the fork-witness probe below has something to detect against.
    let trusted_fallback: Option<Blocklace> = if lace.is_none() {
        Blocklace::from_checkpoint_trusted(
            &capture.checkpoint,
            SigningKey::from_bytes(&[7u8; 32]),
            threshold,
        )
        .ok()
    } else {
        None
    };
    let lace_for_forks: Option<&Blocklace> = lace.as_ref().or(trusted_fallback.as_ref());
    let equivocators: HashSet<[u8; 32]> = lace_for_forks
        .map(|l| l.equivocators().clone())
        .unwrap_or_default();
    report.summarize("equivocators_detected", equivocators.len());
    if equivocators.is_empty() {
        report.push(Finding::verified(
            Severity::Info,
            "dregg_blocklace::finality::Blocklace::detect_equivocation",
            "blocklace.no_equivocation",
            "no equivocation detected: no creator presented two causally-\
             incomparable blocks (the real incomparability test passed for all)",
        ));
    } else {
        for creator in &equivocators {
            // Find the conflicting blocks for an attributable, witnessed message.
            let forks: Vec<&Block> = raw.iter().filter(|b| &b.creator == creator).collect();
            report.push(Finding::verified(
                Severity::Critical,
                "dregg_blocklace::finality::Blocklace::detect_equivocation",
                "blocklace.equivocation",
                format!(
                    "EQUIVOCATION by creator {} — {} block(s) by this creator are \
                     causally incomparable (a fork); the creator's honest tip is \
                     withdrawn and the fork retained as attributable evidence",
                    short_hex(creator),
                    forks.len()
                ),
            ));

            // ── ATTEST: the concrete FORK WITNESS (the EquivocationProof pair) ──
            // Re-run the REAL `detect_equivocation` to extract the authentic
            // incomparable witness pair (block_a ∥ block_b) the protocol would
            // present as slashable evidence — not a reconstruction. We probe each
            // of this creator's blocks against the loaded lace; the first that
            // yields a proof names the two conflicting block ids + their seqs.
            if let Some(lace) = lace_for_forks {
                if let Some(proof) = fork_witness(lace, &forks) {
                    report.push(Finding::verified(
                        Severity::Critical,
                        "dregg_blocklace::finality::Blocklace::detect_equivocation",
                        "blocklace.equivocation_fork_witness",
                        format!(
                            "  fork witness for {}: block_a=(id {}, seq {}) ∥ \
                             block_b=(id {}, seq {}) are causally incomparable \
                             (neither is in the other's causal past) — this pair IS \
                             the slashable equivocation proof",
                            short_hex(&proof.creator),
                            short_hex(&proof.block_a.id().0),
                            proof.block_a.seq,
                            short_hex(&proof.block_b.id().0),
                            proof.block_b.seq,
                        ),
                    ));
                }
            }
        }
        report.summarize(
            "equivocation_forks",
            equivocators
                .iter()
                .map(|c| raw.iter().filter(|b| &b.creator == c).count())
                .sum::<usize>(),
        );
    }

    // ── ATTEST: finality / total order via the real `tau` ─────────────────────
    if let Some(lace) = &lace {
        // Project the authenticated finality lace into the unsigned ordering lace
        // (the exact node `build_ordering_blocklace` path), then run real `tau`.
        let (ordering_lace, ord_to_fin) = build_ordering_blocklace(lace);
        let order = tau_with_config(
            &ordering_lace,
            &capture.participants,
            &capture.ordering_config(),
        );
        report.summarize("tau_ordered_blocks", order.len());
        let finalized_turns = order
            .iter()
            .filter(|oid| {
                ord_to_fin
                    .get(*oid)
                    .and_then(|fid| lace.get(fid))
                    .map(|b| !block_is_heartbeat(b))
                    .unwrap_or(false)
            })
            .count();
        report.summarize("finalized_turns", finalized_turns);
        report.push(Finding::verified(
            Severity::Info,
            "dregg_blocklace::ordering::tau_with_config",
            "blocklace.finality_progress",
            format!(
                "real Cordial-Miners ordering finalized {} of {} block(s) into a \
                 total order ({finalized_turns} carry turns/data); {} block(s) \
                 remain in the unfinalized frontier",
                order.len(),
                lace.len(),
                lace.len().saturating_sub(order.len()),
            ),
        ));

        // ── OBSERVED: quorum-formation progress ───────────────────────────────
        let creators: HashSet<[u8; 32]> = raw.iter().map(|b| b.creator).collect();
        let honest_creators: HashSet<[u8; 32]> =
            creators.difference(&equivocators).copied().collect();
        report.summarize("distinct_creators", creators.len());
        let quorum_formed = honest_creators.len() >= threshold;
        report.push(Finding::observed(
            if quorum_formed {
                Severity::Info
            } else {
                Severity::Notice
            },
            "blocklace.quorum_formation",
            format!(
                "{} distinct honest creator(s) represented vs quorum threshold {} — \
                 supermajority {} formed",
                honest_creators.len(),
                threshold,
                if quorum_formed { "IS" } else { "is NOT yet" },
            ),
        ));

        // ── OBSERVED: causal-order reconstruction stats ───────────────────────
        let depth = max_chain_depth(lace, &raw);
        report.summarize("frontier_width", lace.tips().len());
        report.summarize("max_causal_depth", depth);
    }

    report
}

/// Recover the authentic equivocation witness pair for a creator by re-running
/// the REAL [`Blocklace::detect_equivocation`] over that creator's blocks. The
/// loader retains both fork blocks as attributable evidence, so probing any one
/// against the lace yields the `EquivocationProof { block_a ∥ block_b }` the
/// protocol would slash on. Returns the first conflicting pair found.
fn fork_witness(
    lace: &Blocklace,
    creator_blocks: &[&Block],
) -> Option<dregg_blocklace::finality::EquivocationProof> {
    creator_blocks
        .iter()
        .find_map(|&b| lace.detect_equivocation(b))
}

/// A block whose payload carries no turn/data (an `Ack`-only heartbeat) is not a
/// "finalized turn" for finality-progress reporting. Mirrors
/// `ordering::finalized_turns`'s non-empty-payload filter intent.
fn block_is_heartbeat(b: &Block) -> bool {
    use dregg_blocklace::finality::Payload;
    matches!(b.payload, Payload::Ack)
}

/// Project the authenticated finality lace into the unsigned ordering-projection
/// blocklace `tau` operates on, mirroring the node's
/// `blocklace_sync::build_ordering_blocklace` exactly (different hash schemes, so
/// predecessors are translated and a reverse map is returned).
fn build_ordering_blocklace(
    finality_lace: &Blocklace,
) -> (
    OBlocklace,
    HashMap<OBlockId, dregg_blocklace::finality::BlockId>,
) {
    let mut ordering_lace = OBlocklace::new();
    let mut fin_to_ord: HashMap<dregg_blocklace::finality::BlockId, OBlockId> = HashMap::new();
    let mut ord_to_fin: HashMap<OBlockId, dregg_blocklace::finality::BlockId> = HashMap::new();

    let mut blocks: Vec<(&dregg_blocklace::finality::BlockId, &Block)> =
        finality_lace.iter().collect();
    blocks.sort_by(|(_, a), (_, b)| a.seq.cmp(&b.seq).then_with(|| a.creator.cmp(&b.creator)));

    for (finality_id, block) in blocks {
        let predecessors: Vec<OBlockId> = block
            .predecessors
            .iter()
            .filter_map(|p| fin_to_ord.get(p).copied())
            .collect();
        let payload = match &block.payload {
            Payload::Turn(data) => data.clone(),
            Payload::TurnBundle(bundle) => bundle.signed_turn.clone(),
            Payload::Ack => vec![],
            Payload::Checkpoint { root, height } => {
                let mut buf = Vec::with_capacity(40);
                buf.extend_from_slice(root);
                buf.extend_from_slice(&height.to_le_bytes());
                buf
            }
            Payload::MembershipVote { .. } => vec![0x04],
            Payload::Data(data) => data.clone(),
        };
        let ordering_block = OBlock::new(block.creator, block.seq, predecessors, payload);
        let ordering_id = ordering_block.id();
        let _ = ordering_lace.insert_unverified(ordering_block);
        fin_to_ord.insert(*finality_id, ordering_id);
        ord_to_fin.insert(ordering_id, *finality_id);
    }
    (ordering_lace, ord_to_fin)
}

/// Longest causal chain depth in the DAG (observed structure metric).
fn max_chain_depth(lace: &Blocklace, raw: &[Block]) -> usize {
    use dregg_blocklace::finality::BlockId;
    // memoized DFS over predecessors.
    let mut depth: HashMap<BlockId, usize> = HashMap::new();
    fn d(
        id: BlockId,
        lace: &Blocklace,
        memo: &mut HashMap<BlockId, usize>,
        stack: &mut HashSet<BlockId>,
    ) -> usize {
        if let Some(v) = memo.get(&id) {
            return *v;
        }
        if !stack.insert(id) {
            return 0; // cycle guard (a valid DAG has none, but be safe)
        }
        let here = match lace.get(&id) {
            Some(b) => {
                1 + b
                    .predecessors
                    .iter()
                    .map(|p| d(*p, lace, memo, stack))
                    .max()
                    .unwrap_or(0)
            }
            None => 0,
        };
        stack.remove(&id);
        memo.insert(id, here);
        here
    }
    let mut stack = HashSet::new();
    raw.iter()
        .map(|b| d(b.id(), lace, &mut depth, &mut stack))
        .max()
        .unwrap_or(0)
}
