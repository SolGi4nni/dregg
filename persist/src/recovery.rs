//! State recovery from persistent storage.
//!
//! On startup, a node can call `recover_federation_state()` to reload all
//! persisted state into memory. This allows seamless restart without losing
//! the revocation set, attested roots, or token state.

use redb::ReadableTableMetadata;

use crate::federation::StoredAttestedRoot;
use crate::{PersistentStore, Result};

/// The complete recovered state from a persistent store, suitable for
/// re-initializing in-memory data structures after a restart.
#[derive(Clone, Debug)]
pub struct RecoveredState {
    /// All revoked token IDs (from the revocation table).
    pub revoked_tokens: Vec<String>,
    /// The latest attested root (highest block height), if any.
    pub latest_root: Option<StoredAttestedRoot>,
    /// Total number of stored token chains.
    pub token_count: u64,
    /// Total number of audit events.
    pub audit_count: u64,
    /// Total number of revoked tokens.
    pub revocation_count: u64,
    /// Total number of attested roots.
    pub attested_root_count: u64,
}

impl PersistentStore {
    /// Recover the full federation state from disk.
    ///
    /// This loads all revocations, the latest attested root, and summary counts
    /// for tokens and audit events. Use this on startup to re-initialize
    /// in-memory state.
    pub fn recover_federation_state(&self) -> Result<RecoveredState> {
        let revoked_tokens = self.list_revocations()?;
        let latest_root = self.latest_attested_root()?;
        let token_count = self.token_count()?;
        let audit_count = self.audit_count()?;
        let revocation_count = revoked_tokens.len() as u64;
        let attested_root_count = self.attested_root_count()?;

        Ok(RecoveredState {
            revoked_tokens,
            latest_root,
            token_count,
            audit_count,
            revocation_count,
            attested_root_count,
        })
    }

    /// Check the integrity of the store by verifying internal consistency.
    ///
    /// Checks:
    /// - Audit sequence counter matches actual log entries.
    /// - Latest root height metadata is consistent with stored roots.
    /// - All token chains have valid continuity (each step's old_root matches
    ///   the previous step's new_root).
    pub fn check_integrity(&self) -> Result<IntegrityReport> {
        let mut report = IntegrityReport {
            audit_sequence_ok: true,
            root_height_ok: true,
            chain_continuity_ok: true,
            errors: Vec::new(),
        };

        // Check audit sequence.
        // After pruning, the monotonic sequence counter (audit_count / next_seq) may
        // exceed the actual number of log entries since pruned entries are removed but
        // the counter is never decremented. The invariant is: next_seq >= len.
        let claimed_count = self.audit_count()?;
        let read_txn = self.db.begin_read()?;
        let log_table = read_txn.open_table(crate::tables::AUDIT_LOG)?;
        let actual_count = log_table.len()?;
        if claimed_count < actual_count {
            report.audit_sequence_ok = false;
            report.errors.push(format!(
                "audit sequence counter ({claimed_count}) < actual entries ({actual_count}): counter must be >= entry count"
            ));
        }
        drop(log_table);

        // Check root height metadata.
        let meta = read_txn.open_table(crate::tables::METADATA)?;
        let claimed_height = meta
            .get(crate::tables::META_LATEST_ROOT_HEIGHT)
            .ok()
            .flatten()
            .map(|g| g.value());
        drop(meta);

        let roots_table = read_txn.open_table(crate::tables::ATTESTED_ROOTS)?;
        if let Some(claimed_h) = claimed_height {
            if roots_table.get(claimed_h)?.is_none() {
                report.root_height_ok = false;
                report.errors.push(format!(
                    "metadata claims latest root height {claimed_h} but no root exists at that height"
                ));
            }
        }
        drop(roots_table);
        drop(read_txn);

        // Check token chain continuity.
        let token_ids = self.list_tokens()?;
        for token_id in &token_ids {
            if let Some(chain) = self.load_token_chain(token_id)? {
                if !chain.steps.is_empty() {
                    // First step's old_root must match initial_root.
                    if chain.steps[0].old_root != chain.initial_root {
                        report.chain_continuity_ok = false;
                        report.errors.push(format!(
                            "token {:?}: first step old_root != initial_root",
                            &token_id[..4]
                        ));
                    }

                    // Each subsequent step chains correctly.
                    for i in 1..chain.steps.len() {
                        if chain.steps[i].old_root != chain.steps[i - 1].new_root {
                            report.chain_continuity_ok = false;
                            report.errors.push(format!(
                                "token {:?}: step {} old_root != step {} new_root",
                                &token_id[..4],
                                i,
                                i - 1
                            ));
                        }
                    }

                    // Last step's new_root must match current_root.
                    if chain.steps.last().unwrap().new_root != chain.current_root {
                        report.chain_continuity_ok = false;
                        report.errors.push(format!(
                            "token {:?}: last step new_root != current_root",
                            &token_id[..4]
                        ));
                    }
                }
            }
        }

        Ok(report)
    }
}

/// Report from an integrity check.
#[derive(Clone, Debug)]
pub struct IntegrityReport {
    /// Whether the audit sequence counter is consistent.
    pub audit_sequence_ok: bool,
    /// Whether the latest root height metadata is consistent.
    pub root_height_ok: bool,
    /// Whether all token chains have correct continuity.
    pub chain_continuity_ok: bool,
    /// Detailed error messages for any failures.
    pub errors: Vec<String>,
}

impl IntegrityReport {
    /// Whether all checks passed.
    pub fn is_ok(&self) -> bool {
        self.audit_sequence_ok && self.root_height_ok && self.chain_continuity_ok
    }
}
