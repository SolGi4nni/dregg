//! Persist/WAL commit-log capture analysis (replay/recovery + crash overlay).
//!
//! ## Input format ([`WalCapture`])
//!
//! The node's durable, append-only commit log is a sequence of the node's own
//! [`dregg_persist::commit_log::CommitRecord`]s — one per finalized turn applied
//! to the ledger, keyed by a dense gap-free commit ordinal. A capture is the
//! `Vec<CommitRecord>` (in ordinal order) plus the durable `commit_cursor` the
//! node read at capture time (so we can model the crash-recovery overlay).
//!
//! ## What is ATTESTED / CHECKED (the log's own crash-consistency invariants)
//!
//! The commit log is engineered so that across an arbitrary crash:
//!   * `commit_cursor() == commit_log.len()` (no torn cursor),
//!   * every ordinal in `0..cursor` resolves to a record (dense, gap-free),
//!   * the cursor advances once per applied turn inside the atomic transaction.
//!
//! This analyzer checks those invariants over the capture directly (the same
//! conditions [`dregg_persist`]'s `IndexAuditReport::ok` and the module's
//! crash-consistency contract assert). A violation means the capture is a TORN
//! or CORRUPTED log — precisely the failure the commit log exists to make
//! impossible, so seeing it is a real anomaly.
//!
//! ## What is the RECOVERY OVERLAY (replay analysis)
//!
//!   * The replay set: records at `ordinal >= cursor` would be re-applied on
//!     restart (idempotently). We surface how many turns recovery would replay
//!     and from which block high-water mark (`block_executed_up_to`).
//!   * `ledger_root` continuity: each record binds the post-state root; the
//!     chain of roots is the convergence trail recovery asserts.

use serde::{Deserialize, Serialize};

use dregg_persist::commit_log::CommitRecord;

use crate::findings::{short_hex, AnalysisReport, Finding, Severity};

/// A captured WAL / commit-log: the durable commit records in ordinal order plus
/// the durable commit cursor at capture time.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WalCapture {
    /// The commit records, expected in ascending ordinal order.
    pub records: Vec<CommitRecord>,
    /// The durable `commit_cursor` the node read at capture time. For a
    /// crash-consistent store this MUST equal `records.len()`. A value below it
    /// models a crash mid-batch: records at `ordinal >= cursor` are the replay
    /// set. `None` ⇒ assume `records.len()` (a clean, fully-flushed capture).
    #[serde(default)]
    pub commit_cursor: Option<u64>,
}

/// Analyze a WAL capture for crash-consistency + replay/recovery.
pub fn analyze(capture: &WalCapture) -> AnalysisReport {
    let mut report = AnalysisReport::new("wal");
    let records = &capture.records;
    let len = records.len() as u64;
    let cursor = capture.commit_cursor.unwrap_or(len);
    report.summarize("commit_records", len);
    report.summarize("commit_cursor", cursor);

    if records.is_empty() {
        report.push(Finding::observed(
            Severity::Notice,
            "wal.empty",
            "the commit log is empty — a fresh node (nothing applied yet)",
        ));
        return report;
    }

    // ── CHECK: dense, gap-free, ascending ordinals ────────────────────────────
    // `ordinal == n` MUST mean exactly n turns were applied before it: ordinals
    // are 0,1,2,... with no gaps and no repeats.
    let mut ordinal_violations = 0usize;
    for (expected, rec) in records.iter().enumerate() {
        if rec.ordinal != expected as u64 {
            ordinal_violations += 1;
            report.push(Finding::verified(
                Severity::Critical,
                "dregg_persist::commit_log (dense-ordinal invariant)",
                "wal.ordinal_gap",
                format!(
                    "commit log is not dense/gap-free: record at position {expected} \
                     carries ordinal {} (expected {expected}) — a torn or corrupted \
                     log; recovery's gap-free resume contract is violated",
                    rec.ordinal
                ),
            ));
        }
    }
    if ordinal_violations == 0 {
        report.push(Finding::verified(
            Severity::Info,
            "dregg_persist::commit_log (dense-ordinal invariant)",
            "wal.ordinals_dense",
            format!("all {len} commit ordinal(s) are dense, ascending, and gap-free"),
        ));
    }

    // ── CHECK: cursor agrees with log length (no torn cursor) ─────────────────
    if cursor == len {
        report.push(Finding::verified(
            Severity::Info,
            "dregg_persist::commit_log (commit_cursor == log.len)",
            "wal.cursor_consistent",
            format!(
                "commit_cursor ({cursor}) == commit_log length ({len}): the cursor \
                 is not torn ahead of (or behind) the durable record set — a \
                 crash-consistent log"
            ),
        ));
    } else if cursor < len {
        // Records at ordinal >= cursor are the replay set (the atomic-commit
        // contract: such a record's transaction may not have advanced the
        // cursor; it is re-applied idempotently on restart).
        report.push(Finding::observed(
            Severity::Notice,
            "wal.replay_pending",
            format!(
                "commit_cursor ({cursor}) is BELOW log length ({len}): {} record(s) \
                 at ordinal >= {cursor} are the crash-recovery REPLAY set — recovery \
                 re-applies them idempotently on restart",
                len - cursor
            ),
        ));
    } else {
        report.push(Finding::verified(
            Severity::Critical,
            "dregg_persist::commit_log (commit_cursor == log.len)",
            "wal.cursor_torn",
            format!(
                "commit_cursor ({cursor}) is AHEAD of the durable log length ({len}): \
                 the cursor claims more turns committed than records exist — a TORN \
                 cursor, exactly the lost-finalized-turn hazard the commit log \
                 exists to prevent"
            ),
        ));
    }

    // ── RECOVERY OVERLAY: replay set + block high-water mark ───────────────────
    if cursor < len {
        let replay = &records[cursor as usize..];
        let resume_from = records
            .get(cursor.saturating_sub(1) as usize)
            .map(|r| r.block_executed_up_to)
            .unwrap_or(0);
        report.summarize("replay_turns", replay.len());
        report.summarize("recovery_resumes_block_hwm", resume_from);

        // Per-record replay detail: the EXACT turns recovery would re-apply, with
        // their ordinal / height / block anchor / creator / post-state root, plus
        // the cells each would re-touch. This is the actionable replay overlay —
        // an operator can see precisely what restart re-executes idempotently.
        let replay_cells: usize = replay.iter().map(|r| r.touched_cells.len()).sum();
        report.summarize("replay_touched_cells", replay_cells);
        report.push(Finding::observed(
            Severity::Notice,
            "wal.replay_overlay",
            format!(
                "REPLAY OVERLAY — recovery re-applies {} turn(s) at ordinal >= \
                 {cursor} (idempotently): {}; re-touching {replay_cells} cell-\
                 snapshot(s). The first replay turn anchors block {} (creator {}); \
                 recovery resumes block processing from block-hwm {resume_from}.",
                replay.len(),
                replay_overlay_detail(replay),
                replay
                    .first()
                    .map(|r| short_hex(&r.block_id))
                    .unwrap_or_else(|| "—".into()),
                replay
                    .first()
                    .map(|r| short_hex(&r.creator))
                    .unwrap_or_else(|| "—".into()),
            ),
        ));
    } else {
        report.summarize("replay_turns", 0);
        report.summarize("replay_touched_cells", 0);
    }
    if let Some(last) = records.last() {
        report.summarize("latest_height", last.height);
        report.summarize("latest_ledger_root", short_hex(&last.ledger_root));
        report.summarize("latest_block_hwm", last.block_executed_up_to);
    }

    // ── CHECK: per-record self-coherence + monotone block high-water mark ─────
    let mut height_regressions = 0usize;
    let mut hwm_regressions = 0usize;
    let mut prev_height: Option<u64> = None;
    let mut prev_hwm: Option<u64> = None;
    for rec in records {
        if let Some(ph) = prev_height {
            if rec.height < ph {
                height_regressions += 1;
            }
        }
        if let Some(pw) = prev_hwm {
            // The block high-water mark is monotone non-decreasing: each turn's
            // `block_executed_up_to` is >= the previous turn's.
            if rec.block_executed_up_to < pw {
                hwm_regressions += 1;
                report.push(Finding::verified(
                    Severity::Critical,
                    "dregg_persist::commit_log (monotone block_executed_up_to)",
                    "wal.hwm_regression",
                    format!(
                        "commit ordinal {} regresses the block high-water mark \
                         ({} < previous {pw}) — a turn was recorded as committed \
                         against an EARLIER block cursor than a prior turn; the \
                         recovery anchor is non-monotone",
                        rec.ordinal, rec.block_executed_up_to
                    ),
                ));
            }
        }
        prev_height = Some(rec.height);
        prev_hwm = Some(rec.block_executed_up_to);
    }
    report.summarize("touched_cells_total", records.iter().map(|r| r.touched_cells.len()).sum::<usize>());
    if height_regressions > 0 {
        report.push(Finding::observed(
            Severity::Notice,
            "wal.height_regression",
            format!(
                "{height_regressions} record(s) commit at a height below a prior \
                 record's — expected when several ROUTE-level turns share an \
                 attested height, but worth noting"
            ),
        ));
    }
    if hwm_regressions == 0 {
        report.push(Finding::verified(
            Severity::Info,
            "dregg_persist::commit_log (monotone block_executed_up_to)",
            "wal.hwm_monotone",
            "the block high-water mark is monotone non-decreasing across the log: \
             the recovery anchor never moves backward",
        ));
    }

    // ── RECOVERY OVERLAY: the ledger_root convergence trail ───────────────────
    // Each record binds the canonical ledger root AFTER its turn — the chain of
    // roots is the convergence trail recovery asserts (replay must reach the same
    // root). We surface the trail and flag a STAGNANT root: a record that touched
    // cells yet left the ledger root unchanged from its predecessor is a real
    // anomaly (a mutation that did not move the authenticated state — a torn
    // commit or a root not recomputed over the write).
    let mut root_stalls = 0usize;
    for w in records.windows(2) {
        if w[1].ledger_root == w[0].ledger_root && !w[1].touched_cells.is_empty() {
            root_stalls += 1;
            report.push(Finding::verified(
                Severity::Critical,
                "dregg_persist::commit_log (ledger_root convergence trail)",
                "wal.root_stall",
                format!(
                    "commit ordinal {} touched {} cell(s) yet left the ledger root \
                     UNCHANGED ({}) — a mutation that did not advance the \
                     authenticated state; the convergence trail recovery replays \
                     against would not reproduce the write",
                    w[1].ordinal,
                    w[1].touched_cells.len(),
                    short_hex(&w[1].ledger_root),
                ),
            ));
        }
    }
    let distinct_roots = {
        let mut s = std::collections::HashSet::new();
        for r in records {
            s.insert(r.ledger_root);
        }
        s.len()
    };
    report.summarize("distinct_ledger_roots", distinct_roots);
    if root_stalls == 0 {
        report.push(Finding::verified(
            Severity::Info,
            "dregg_persist::commit_log (ledger_root convergence trail)",
            "wal.root_trail_coherent",
            format!(
                "the ledger-root convergence trail is coherent: {distinct_roots} \
                 distinct root(s) across {len} record(s); every cell-touching turn \
                 advanced the authenticated root (no stagnant-root mutation) — \
                 recovery replay can reproduce this exact trail"
            ),
        ));
    }

    report
}

/// Render a compact `[ordinal h=<height> b=<hwm>]` list of the replay set (capped
/// so a large batch stays readable) for the recovery-overlay finding.
fn replay_overlay_detail(replay: &[CommitRecord]) -> String {
    const CAP: usize = 8;
    let mut parts: Vec<String> = replay
        .iter()
        .take(CAP)
        .map(|r| format!("[#{} h={} b={}]", r.ordinal, r.height, r.block_executed_up_to))
        .collect();
    if replay.len() > CAP {
        parts.push(format!("…(+{} more)", replay.len() - CAP));
    }
    parts.join(" ")
}
