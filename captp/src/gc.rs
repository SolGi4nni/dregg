//! Distributed reference counting and garbage collection for CapTP.
//!
//! When a federation exports a capability to a peer (via introduction or sturdy ref
//! enliven), the exporter tracks that the peer holds a reference. When the peer no
//! longer needs it, it sends a `DropRef` message. The exporter decrements the count;
//! at zero, the export entry can be cleaned up.
//!
//! # Two sides
//!
//! - **Export GC** (`ExportGcManager`): tracks who holds references to OUR capabilities.
//! - **Import GC** (`ImportGcManager`): tracks what WE hold from remote federations,
//!   and when to send `DropRef` messages.
//!
//! # TODO(unified-lace): migrate FederationId keys to StrandId
//! GC tracking should be keyed by StrandId (the bilateral peer), not FederationId
//! (the group). This is Phase B of the unified lace migration.

use std::collections::HashMap;

use dregg_types::CellId;
use serde::{Deserialize, Serialize};

use crate::{FederationId, StrandId};

/// Decide a `process_drop` verdict (StillHeld / CanRevoke / Invalid) via the VERIFIED Lean export
/// `dregg_captp_process_drop` (= `Dregg2.Exec.CapTPGCConcrete.processDrop`). Returns `Some(verdict)`
/// when the gate ran, or `None` when it is unavailable (feature off / archive lacks the export) so the
/// caller falls back to the native Rust mutation's own verdict.
///
/// The cell's holder-table is interned to the gate's wire `"H=<fed:count:s=n+...|...>;f=<fed>;s=<s>"`,
/// mapping each 32-byte `FederationId` to a small index and reusing each `SessionId` u64 directly
/// (the Lean gate compares fed/session by identity, so any injective interning preserves the verdict).
/// Built `--features lean-gate`; a stub returning `None` otherwise.
#[cfg(feature = "lean-gate")]
fn verified_drop_verdict(
    entry: Option<&ExportEntry>,
    from_federation: FederationId,
    session: SessionId,
) -> Option<DropResult> {
    if !dregg_lean_ffi::distributed_exports_available() {
        return None;
    }
    // No export entry for the cell ⇒ the gate would see an empty holder-table; the queried fed is
    // absent ⇒ Invalid (matches the native `exports.get(&cell_id) == None` reject).
    let entry = match entry {
        Some(e) => e,
        None => return Some(DropResult::Invalid),
    };

    // Intern federations to small ids; the queried fed gets its own id (added if absent so the gate
    // sees an absent-holder Invalid rather than a parse failure).
    let mut fed_ids: HashMap<[u8; 32], usize> = HashMap::new();
    for fed in entry.holders.keys() {
        let next = fed_ids.len();
        fed_ids.entry(fed.0).or_insert(next);
    }
    let q_fed = {
        let next = fed_ids.len();
        *fed_ids.entry(from_federation.0).or_insert(next)
    };

    let holders_wire: Vec<String> = entry
        .holders
        .iter()
        .map(|(fed, rc)| {
            let id = fed_ids[&fed.0];
            let buckets: String = {
                let mut bs: Vec<(SessionId, u64)> =
                    rc.sessions.iter().map(|(s, n)| (*s, *n)).collect();
                bs.sort_unstable();
                bs.iter()
                    .map(|(s, n)| format!("{s}={n}"))
                    .collect::<Vec<_>>()
                    .join("+")
            };
            format!("{id}:{}:{buckets}", rc.count)
        })
        .collect();
    let wire = format!("H={};f={q_fed};s={session}", holders_wire.join("|"));

    let out = dregg_lean_ffi::shadow_captp_process_drop(&wire).ok()?;
    // Reply: "S=<tag>;t=<postTotal>" — tag 0=stillHeld 1=canRevoke 2=invalid; "ERR" ⇒ fail-closed.
    let tag_seg = out.split(';').next()?.strip_prefix("S=")?;
    match tag_seg {
        "0" => Some(DropResult::StillHeld),
        "1" => Some(DropResult::CanRevoke),
        // tag 2 (invalid) or any unexpected reply ⇒ fail-closed Invalid.
        _ => Some(DropResult::Invalid),
    }
}

/// Stub when the `lean-gate` feature is off: the verified gate is unavailable, so the native Rust
/// mutation's verdict decides. Referenced unconditionally in `process_drop_inner`.
#[cfg(not(feature = "lean-gate"))]
fn verified_drop_verdict(
    _entry: Option<&ExportEntry>,
    _from_federation: FederationId,
    _session: SessionId,
) -> Option<DropResult> {
    None
}

// =============================================================================
// Export-side GC
// =============================================================================

/// A session identifier for tracking which CapTP session created an export.
///
/// Each time a CapTP session is established (via CapHello), a new session ID is
/// generated. DropRef messages are only accepted from the same session that
/// created the export, preventing Byzantine nodes on different sessions from
/// interfering with GC state.
pub type SessionId = u64;

/// Per-holder reference count with activity tracking.
///
/// # Per-ref (per-session) session scoping — F-12 fix
///
/// References are tracked **per session**, not collapsed onto a single
/// `session_id` for the whole holder. `sessions` maps each session id that has
/// minted a reference to the number of refs minted under THAT session. The
/// holder's total `count` is the sum of these per-session buckets.
///
/// This is what makes session validation honest under re-export: a re-export to
/// the same federation on a NEW session adds a bucket for the new session and
/// leaves every existing session's bucket (and its drop rights) untouched. The
/// original session keeps the right to drop exactly the refs IT minted, and the
/// new session can only drop refs it minted — neither can drop the other's.
/// (Before this fix a single per-holder `session_id` was overwritten by the most
/// recent export, so a re-export silently transferred drop rights for ALL of the
/// holder's refs to the new session — the F-12 finding.)
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RefCount {
    /// How many references this holder has to the capability (the sum over
    /// `sessions`). Kept as a maintained field so existing readers (and the
    /// `total_refs == Σ count` invariant) are unchanged.
    pub count: u64,
    /// The block height at which this holder last acquired a reference.
    pub last_activity: u64,
    /// Per-session reference counts: `session_id -> refs minted under it`.
    /// A DropRef carrying `session_id = s` may only decrement `sessions[s]`.
    /// The sum of all buckets is `count`.
    pub sessions: HashMap<SessionId, u64>,
}

impl RefCount {
    /// The session bucket of this holder, if it minted any refs under `session`.
    pub fn session_count(&self, session: SessionId) -> u64 {
        self.sessions.get(&session).copied().unwrap_or(0)
    }
}

/// Export table entry: tracks who holds references to one of our capabilities.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExportEntry {
    /// The cell being exported.
    pub cell_id: CellId,
    /// Per-federation reference counts.
    pub holders: HashMap<FederationId, RefCount>,
    /// Sum of all holder reference counts.
    pub total_refs: u64,
    /// Block height when this export was first created.
    pub exported_at: u64,
}

/// Result of processing a `DropRef` message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DropResult {
    /// The export still has references from other holders.
    StillHeld,
    /// All references have been dropped; the export can be revoked/cleaned up.
    CanRevoke,
    /// The drop was invalid (unknown federation or over-decrement).
    Invalid,
}

/// The GC manager for one federation's exports.
///
/// Tracks which remote federations hold references to our capabilities,
/// enabling distributed garbage collection via `DropRef` messages.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ExportGcManager {
    exports: HashMap<CellId, ExportEntry>,
}

impl ExportGcManager {
    /// Create a new empty export GC manager.
    pub fn new() -> Self {
        Self {
            exports: HashMap::new(),
        }
    }

    /// Record that we exported a capability to a peer federation.
    ///
    /// Called when a capability is introduced to a peer (via 3-party handoff,
    /// sturdy ref enliven, or direct export).
    ///
    /// The `session_id` ties this export to a specific CapTP session. Only
    /// DropRef messages carrying the same session_id will be accepted for this
    /// holder, preventing Byzantine nodes from interfering via stale or forged
    /// session credentials.
    pub fn record_export(
        &mut self,
        cell_id: CellId,
        to_federation: FederationId,
        current_height: u64,
    ) {
        self.record_export_with_session(cell_id, to_federation, current_height, 0)
    }

    /// Record an export with an explicit session ID for session-level validation.
    ///
    /// This is the primary entry point for session-aware code. The `session_id`
    /// must match when processing a DropRef to prevent cross-session interference.
    pub fn record_export_with_session(
        &mut self,
        cell_id: CellId,
        to_federation: FederationId,
        current_height: u64,
        session_id: SessionId,
    ) {
        let entry = self.exports.entry(cell_id).or_insert_with(|| ExportEntry {
            cell_id,
            holders: HashMap::new(),
            total_refs: 0,
            exported_at: current_height,
        });

        let ref_count = entry
            .holders
            .entry(to_federation)
            .or_insert_with(|| RefCount {
                count: 0,
                last_activity: current_height,
                sessions: HashMap::new(),
            });

        ref_count.count += 1;
        ref_count.last_activity = current_height;
        // F-12: mint the ref into THIS session's bucket. A re-export under a new
        // session adds to (or creates) that session's bucket and never touches the
        // buckets of other sessions, so the original session keeps its drop rights.
        *ref_count.sessions.entry(session_id).or_insert(0) += 1;
        entry.total_refs += 1;
    }

    /// Process a `DropRef` from a peer (they no longer hold the reference).
    ///
    /// Decrements the count for the given federation. If total_refs reaches 0,
    /// returns `DropResult::CanRevoke` indicating the export is dead and can be
    /// cleaned up. Returns `DropResult::Invalid` if the federation doesn't hold
    /// a reference or the cell isn't exported.
    ///
    /// **DENIED (F-11): the session-free drop path is closed.**
    ///
    /// A DropRef with no session credential can never be authenticated as coming
    /// from the holder that minted the ref, so accepting it is a premature-reclaim
    /// hole: any caller who knew `(cell_id, victim_federation)` could decrement the
    /// victim's refcount and, at zero, force a `CanRevoke` of a still-wanted
    /// capability. This is exactly the F-11 finding. The method is retained only so
    /// legacy call sites compile; it now **fails closed** — it performs NO mutation
    /// and always returns [`DropResult::Invalid`]. Callers MUST present a session via
    /// [`process_drop_with_session`] (or [`process_drop_by_strand`]).
    #[deprecated(
        since = "0.2.0",
        note = "session-free drops are denied (F-11 premature-reclaim); use process_drop_with_session"
    )]
    pub fn process_drop(&mut self, _cell_id: CellId, _from_federation: FederationId) -> DropResult {
        // Fail-closed: no session ⇒ no authority to drop. Never mutates state.
        DropResult::Invalid
    }

    /// Process a `DropRef` with session-level validation.
    ///
    /// The `session_id` must match the session under which the export was created.
    /// If the session_id does not match, the drop is rejected as `DropResult::Invalid`,
    /// preventing Byzantine nodes on different sessions from interfering with GC state.
    pub fn process_drop_with_session(
        &mut self,
        cell_id: CellId,
        from_federation: FederationId,
        session_id: SessionId,
    ) -> DropResult {
        self.process_drop_inner(cell_id, from_federation, session_id)
    }

    /// Internal: process a drop with **mandatory** per-session validation (F-11/F-12).
    ///
    /// `session` identifies which session is requesting the drop. The decrement is
    /// applied to that session's bucket ONLY (`RefCount.sessions[session]`):
    ///
    /// * unknown cell / unknown holder ⇒ `Invalid` (no mutation);
    /// * the session minted no refs on this holder (`sessions[session]` absent or 0)
    ///   ⇒ `Invalid` (no mutation) — this is the Byzantine / wrong-session reject
    ///   AND the F-11 unauthenticated-drop reject (a forged/absent session decrements
    ///   nothing);
    /// * otherwise decrement `sessions[session]` and the holder's `count` and the
    ///   cell's `total_refs` by exactly one, removing emptied buckets / holders /
    ///   exports at zero.
    ///
    /// Because the decrement is scoped to the requesting session's own bucket, the
    /// original session keeps the right to drop the refs it minted even after a
    /// re-export under a different session, and a session can never drop refs another
    /// session minted (F-12).
    fn process_drop_inner(
        &mut self,
        cell_id: CellId,
        from_federation: FederationId,
        session: SessionId,
    ) -> DropResult {
        // STRONG-FORM swap: when the verified Lean GC gate is linked (`--features lean-gate`,
        // `Dregg2.Exec.DistributedExports::dregg_captp_process_drop` =
        // `CapTPGCConcrete.processDrop`), the AUTHORITATIVE verdict (StillHeld / CanRevoke / Invalid)
        // comes from the verified Lean — so the F-11/F-12 session-refcount logic is decided BY the
        // verified rule. The native Rust mutation below stays as the DIFFERENTIAL sibling and applies
        // the state change EXACTLY when the gate's verdict is not Invalid (an Invalid drop mutates
        // nothing, matching `processDrop`'s no-mutation-on-invalid contract). When the gate is
        // unavailable, the native mutation decides (its return value is the verdict).
        let verified = verified_drop_verdict(self.exports.get(&cell_id), from_federation, session);

        // If the verified gate ran and says Invalid, fail-closed WITHOUT mutating (the F-11 reject).
        if matches!(verified, Some(DropResult::Invalid)) {
            return DropResult::Invalid;
        }

        let entry = match self.exports.get_mut(&cell_id) {
            Some(e) => e,
            None => return DropResult::Invalid,
        };

        let ref_count = match entry.holders.get_mut(&from_federation) {
            Some(rc) => rc,
            None => return DropResult::Invalid,
        };

        // F-11/F-12: the requesting session may only drop refs IT minted. A wrong,
        // forged, or absent session bucket (count 0) authorizes nothing.
        let bucket = match ref_count.sessions.get_mut(&session) {
            Some(b) if *b > 0 => b,
            _ => return DropResult::Invalid,
        };

        *bucket -= 1;
        if *bucket == 0 {
            ref_count.sessions.remove(&session);
        }
        ref_count.count -= 1;
        entry.total_refs -= 1;

        // Clean up the holder entry if they have no more refs
        if ref_count.count == 0 {
            entry.holders.remove(&from_federation);
        }

        let native = if entry.total_refs == 0 {
            DropResult::CanRevoke
        } else {
            DropResult::StillHeld
        };

        // The verified gate (when available) is AUTHORITATIVE for the verdict; the native mutation
        // above is the differential. They agree by construction (`captp_process_drop_eq`); on the
        // off chance the gate errored mid-run we keep the native verdict.
        verified.unwrap_or(native)
    }

    /// Find exports that haven't been accessed in `max_idle_blocks` blocks.
    ///
    /// Returns cell IDs of exports where ALL holders have been idle for longer
    /// than the threshold. These are candidates for proactive GC (sending a
    /// "are you still there?" probe or revoking).
    pub fn stale_exports(&self, max_idle_blocks: u64, current_height: u64) -> Vec<CellId> {
        self.exports
            .values()
            .filter(|entry| {
                entry
                    .holders
                    .values()
                    .all(|rc| current_height.saturating_sub(rc.last_activity) > max_idle_blocks)
            })
            .map(|entry| entry.cell_id)
            .collect()
    }

    /// Clean up: remove all entries with zero total references.
    ///
    /// Returns the cell IDs that were removed.
    pub fn gc_sweep(&mut self) -> Vec<CellId> {
        let dead: Vec<CellId> = self
            .exports
            .iter()
            .filter(|(_, entry)| entry.total_refs == 0)
            .map(|(cell_id, _)| *cell_id)
            .collect();

        for cell_id in &dead {
            self.exports.remove(cell_id);
        }

        dead
    }

    /// Get the export entry for a cell, if it exists.
    pub fn get(&self, cell_id: &CellId) -> Option<&ExportEntry> {
        self.exports.get(cell_id)
    }

    /// Returns the number of active exports being tracked.
    pub fn len(&self) -> usize {
        self.exports.len()
    }

    /// Returns true if there are no exports being tracked.
    pub fn is_empty(&self) -> bool {
        self.exports.is_empty()
    }

    // =========================================================================
    // Strand-keyed methods (Phase B: unified lace migration)
    // =========================================================================

    /// Record that we exported a capability to a specific strand.
    ///
    /// In the unified lace model, exports are tracked per-strand (bilateral)
    /// rather than per-group. This wraps the strand ID into a `FederationId`
    /// internally for storage compatibility.
    ///
    /// Prefer this over [`record_export`] for new code.
    pub fn record_export_by_strand(
        &mut self,
        cell_id: CellId,
        to_strand: StrandId,
        current_height: u64,
        session_id: SessionId,
    ) {
        self.record_export_with_session(
            cell_id,
            FederationId(to_strand),
            current_height,
            session_id,
        )
    }

    /// Process a `DropRef` keyed by strand ID with session validation.
    ///
    /// In the unified lace model, drops come from a strand, not a group.
    /// This wraps the strand ID into a `FederationId` for internal lookup.
    ///
    /// Prefer this over [`process_drop_with_session`] for new code.
    pub fn process_drop_by_strand(
        &mut self,
        cell_id: CellId,
        from_strand: StrandId,
        session_id: SessionId,
    ) -> DropResult {
        self.process_drop_with_session(cell_id, FederationId(from_strand), session_id)
    }
}

// =============================================================================
// Import-side GC
// =============================================================================

/// Import table entry: tracks what WE hold from a remote federation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ImportEntry {
    /// The remote federation that exported this capability to us.
    pub remote_federation: FederationId,
    /// The cell ID on the remote federation.
    pub remote_cell_id: CellId,
    /// How many local c-list entries / bearers reference this import.
    pub local_refs: u64,
}

/// A message to send to a remote federation indicating we dropped a reference.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DropMessage {
    /// The remote federation to notify.
    pub target_federation: FederationId,
    /// The cell ID we are dropping.
    pub cell_id: CellId,
}

/// Manages imports from remote federations and generates `DropRef` messages
/// when all local references to an import are released.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ImportGcManager {
    imports: HashMap<(FederationId, CellId), ImportEntry>,
}

impl ImportGcManager {
    /// Create a new empty import GC manager.
    pub fn new() -> Self {
        Self {
            imports: HashMap::new(),
        }
    }

    /// Record that we now hold a reference to a remote capability.
    ///
    /// Called when we enliven a sturdy ref, receive a capability via introduction,
    /// or accept a handoff certificate.
    pub fn record_import(&mut self, federation: FederationId, cell_id: CellId) {
        let entry = self
            .imports
            .entry((federation, cell_id))
            .or_insert_with(|| ImportEntry {
                remote_federation: federation,
                remote_cell_id: cell_id,
                local_refs: 0,
            });

        entry.local_refs += 1;
    }

    /// A local reference was dropped (capability removed from c-list, bearer expired, etc.).
    ///
    /// Decrements `local_refs`. If it reaches 0, returns `Some(DropMessage)` which
    /// should be sent to the remote federation to release their export entry.
    /// Returns `None` if there are still local references remaining, or if the
    /// import doesn't exist.
    pub fn local_ref_dropped(
        &mut self,
        federation: FederationId,
        cell_id: CellId,
    ) -> Option<DropMessage> {
        let key = (federation, cell_id);
        let entry = self.imports.get_mut(&key)?;

        if entry.local_refs == 0 {
            return None;
        }

        entry.local_refs -= 1;

        if entry.local_refs == 0 {
            self.imports.remove(&key);
            Some(DropMessage {
                target_federation: federation,
                cell_id,
            })
        } else {
            None
        }
    }

    /// Get the import entry for a specific remote capability, if it exists.
    pub fn get(&self, federation: &FederationId, cell_id: &CellId) -> Option<&ImportEntry> {
        self.imports.get(&(*federation, *cell_id))
    }

    /// Returns the number of imports being tracked.
    pub fn len(&self) -> usize {
        self.imports.len()
    }

    /// Returns true if there are no imports being tracked.
    pub fn is_empty(&self) -> bool {
        self.imports.is_empty()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn fed_a() -> FederationId {
        FederationId([0xAA; 32])
    }

    fn fed_b() -> FederationId {
        FederationId([0xBB; 32])
    }

    fn fed_c() -> FederationId {
        FederationId([0xCC; 32])
    }

    fn cell_1() -> CellId {
        CellId([0x11; 32])
    }

    fn cell_2() -> CellId {
        CellId([0x22; 32])
    }

    // --- Export GC tests ---

    #[test]
    fn export_single_holder_drop_to_zero() {
        let mut mgr = ExportGcManager::new();
        let cell = cell_1();
        let fed = fed_a();

        mgr.record_export(cell, fed, 100);
        assert_eq!(mgr.get(&cell).unwrap().total_refs, 1);

        // record_export mints under session 0; drop on session 0 reclaims.
        let result = mgr.process_drop_with_session(cell, fed, 0);
        assert_eq!(result, DropResult::CanRevoke);
        assert_eq!(mgr.get(&cell).unwrap().total_refs, 0);
    }

    #[test]
    fn export_multiple_holders_drop_one_still_held() {
        let mut mgr = ExportGcManager::new();
        let cell = cell_1();

        mgr.record_export(cell, fed_a(), 100);
        mgr.record_export(cell, fed_b(), 101);
        assert_eq!(mgr.get(&cell).unwrap().total_refs, 2);

        // Drop from A (session 0): B still holds it
        let result = mgr.process_drop_with_session(cell, fed_a(), 0);
        assert_eq!(result, DropResult::StillHeld);
        assert_eq!(mgr.get(&cell).unwrap().total_refs, 1);

        // Drop from B (session 0): now can revoke
        let result = mgr.process_drop_with_session(cell, fed_b(), 0);
        assert_eq!(result, DropResult::CanRevoke);
    }

    #[test]
    fn export_multiple_refs_same_holder() {
        let mut mgr = ExportGcManager::new();
        let cell = cell_1();
        let fed = fed_a();

        // Same federation imports the cap twice (e.g., two different sturdy refs)
        mgr.record_export(cell, fed, 100);
        mgr.record_export(cell, fed, 105);
        assert_eq!(mgr.get(&cell).unwrap().total_refs, 2);
        assert_eq!(mgr.get(&cell).unwrap().holders[&fed].count, 2);

        // First drop (session 0): still held
        let result = mgr.process_drop_with_session(cell, fed, 0);
        assert_eq!(result, DropResult::StillHeld);

        // Second drop (session 0): can revoke
        let result = mgr.process_drop_with_session(cell, fed, 0);
        assert_eq!(result, DropResult::CanRevoke);
    }

    #[test]
    fn export_drop_invalid_unknown_federation() {
        let mut mgr = ExportGcManager::new();
        let cell = cell_1();

        mgr.record_export(cell, fed_a(), 100);

        // C never held this
        let result = mgr.process_drop_with_session(cell, fed_c(), 0);
        assert_eq!(result, DropResult::Invalid);
    }

    #[test]
    fn export_drop_invalid_unknown_cell() {
        let mut mgr = ExportGcManager::new();

        let result = mgr.process_drop_with_session(cell_1(), fed_a(), 0);
        assert_eq!(result, DropResult::Invalid);
    }

    #[test]
    fn stale_export_detection() {
        let mut mgr = ExportGcManager::new();
        let cell = cell_1();
        let cell2 = cell_2();

        mgr.record_export(cell, fed_a(), 100);
        mgr.record_export(cell2, fed_b(), 200);

        // At height 250, max_idle = 100: cell (last activity 100) is stale,
        // cell2 (last activity 200) is not
        let stale = mgr.stale_exports(100, 250);
        assert_eq!(stale.len(), 1);
        assert!(stale.contains(&cell));

        // At height 350, both are stale
        let stale = mgr.stale_exports(100, 350);
        assert_eq!(stale.len(), 2);
    }

    #[test]
    fn gc_sweep_removes_zero_ref_entries() {
        let mut mgr = ExportGcManager::new();
        let cell = cell_1();
        let cell2 = cell_2();

        mgr.record_export(cell, fed_a(), 100);
        mgr.record_export(cell2, fed_b(), 100);

        // Drop cell's only ref (session 0)
        mgr.process_drop_with_session(cell, fed_a(), 0);

        // Sweep: should remove cell (0 refs) but keep cell2 (1 ref)
        let swept = mgr.gc_sweep();
        assert_eq!(swept.len(), 1);
        assert!(swept.contains(&cell));
        assert_eq!(mgr.len(), 1);
        assert!(mgr.get(&cell2).is_some());
    }

    // --- Import GC tests ---

    #[test]
    fn import_single_ref_drop_generates_message() {
        let mut mgr = ImportGcManager::new();
        let fed = fed_a();
        let cell = cell_1();

        mgr.record_import(fed, cell);
        assert_eq!(mgr.get(&fed, &cell).unwrap().local_refs, 1);

        let msg = mgr.local_ref_dropped(fed, cell);
        assert_eq!(
            msg,
            Some(DropMessage {
                target_federation: fed,
                cell_id: cell,
            })
        );
        // Import entry should be cleaned up
        assert!(mgr.get(&fed, &cell).is_none());
        assert!(mgr.is_empty());
    }

    #[test]
    fn import_multiple_refs_drop_one_no_message() {
        let mut mgr = ImportGcManager::new();
        let fed = fed_a();
        let cell = cell_1();

        mgr.record_import(fed, cell);
        mgr.record_import(fed, cell);
        assert_eq!(mgr.get(&fed, &cell).unwrap().local_refs, 2);

        // First drop: still have a local ref
        let msg = mgr.local_ref_dropped(fed, cell);
        assert_eq!(msg, None);
        assert_eq!(mgr.get(&fed, &cell).unwrap().local_refs, 1);

        // Second drop: generates message
        let msg = mgr.local_ref_dropped(fed, cell);
        assert!(msg.is_some());
    }

    #[test]
    fn import_drop_nonexistent_returns_none() {
        let mut mgr = ImportGcManager::new();

        let msg = mgr.local_ref_dropped(fed_a(), cell_1());
        assert_eq!(msg, None);
    }

    // --- Session-level validation tests (Bug 1 fix) ---

    #[test]
    fn export_drop_rejected_from_wrong_session() {
        let mut mgr = ExportGcManager::new();
        let cell = cell_1();
        let fed = fed_a();

        // Export on session 42
        mgr.record_export_with_session(cell, fed, 100, 42);
        assert_eq!(mgr.get(&cell).unwrap().total_refs, 1);

        // Attempt drop with session 99 (wrong session) — must be rejected
        let result = mgr.process_drop_with_session(cell, fed, 99);
        assert_eq!(result, DropResult::Invalid);

        // Total refs must be unchanged (drop was rejected)
        assert_eq!(mgr.get(&cell).unwrap().total_refs, 1);

        // Correct session succeeds
        let result = mgr.process_drop_with_session(cell, fed, 42);
        assert_eq!(result, DropResult::CanRevoke);
    }

    /// F-11: the legacy session-free `process_drop` is now DENIED (fail-closed).
    /// It can never reclaim — a session credential is mandatory.
    #[test]
    #[allow(deprecated)]
    fn export_legacy_process_drop_is_denied_fail_closed() {
        let mut mgr = ExportGcManager::new();
        let cell = cell_1();
        let fed = fed_a();

        // record_export mints under session 0; the holder really exists.
        mgr.record_export(cell, fed, 100);
        assert_eq!(mgr.get(&cell).unwrap().total_refs, 1);

        // The session-free path is denied and performs NO mutation.
        let result = mgr.process_drop(cell, fed);
        assert_eq!(result, DropResult::Invalid);
        assert_eq!(
            mgr.get(&cell).unwrap().total_refs,
            1,
            "denied legacy drop must not mutate the refcount"
        );

        // The session-aware path (session 0, the one record_export minted under) works.
        let result = mgr.process_drop_with_session(cell, fed, 0);
        assert_eq!(result, DropResult::CanRevoke);
    }

    /// F-12: a re-export under a NEW session does NOT supersede the existing
    /// session's drop rights. Each session can drop exactly the refs it minted,
    /// and only those — sessions are tracked per-ref, not collapsed per-holder.
    #[test]
    fn export_reexport_does_not_steal_original_session_drop_rights() {
        let mut mgr = ExportGcManager::new();
        let cell = cell_1();
        let fed = fed_a();

        // Two refs minted under session 1.
        mgr.record_export_with_session(cell, fed, 100, 1);
        mgr.record_export_with_session(cell, fed, 100, 1);
        // A re-export under session 2 (a reconnect): adds a THIRD ref in session 2's
        // bucket; it does NOT touch session 1's two refs.
        mgr.record_export_with_session(cell, fed, 200, 2);
        assert_eq!(mgr.get(&cell).unwrap().total_refs, 3);
        assert_eq!(mgr.get(&cell).unwrap().holders[&fed].session_count(1), 2);
        assert_eq!(mgr.get(&cell).unwrap().holders[&fed].session_count(2), 1);

        // The ORIGINAL session 1 KEEPS its drop rights — it can still drop the two
        // refs it minted (this was the F-12 bug: previously rejected as Invalid).
        assert_eq!(
            mgr.process_drop_with_session(cell, fed, 1),
            DropResult::StillHeld
        );
        assert_eq!(
            mgr.process_drop_with_session(cell, fed, 1),
            DropResult::StillHeld
        );
        // Session 1's bucket is now empty; a further session-1 drop is rejected
        // (it cannot reach into session 2's ref).
        assert_eq!(
            mgr.process_drop_with_session(cell, fed, 1),
            DropResult::Invalid
        );
        assert_eq!(mgr.get(&cell).unwrap().total_refs, 1);

        // Session 2 can drop ONLY the ref it minted; the last ref reclaims.
        assert_eq!(
            mgr.process_drop_with_session(cell, fed, 2),
            DropResult::CanRevoke
        );
    }

    /// F-12: the NEW session cannot drop refs the ORIGINAL session minted.
    #[test]
    fn export_new_session_cannot_drop_other_sessions_refs() {
        let mut mgr = ExportGcManager::new();
        let cell = cell_1();
        let fed = fed_a();

        // One ref under session 1, then one re-export under session 2.
        mgr.record_export_with_session(cell, fed, 100, 1);
        mgr.record_export_with_session(cell, fed, 200, 2);
        assert_eq!(mgr.get(&cell).unwrap().total_refs, 2);

        // Session 2 drops its own ref → still held (session 1's ref remains).
        assert_eq!(
            mgr.process_drop_with_session(cell, fed, 2),
            DropResult::StillHeld
        );
        // Session 2 has nothing left to drop; it CANNOT reach session 1's ref.
        assert_eq!(
            mgr.process_drop_with_session(cell, fed, 2),
            DropResult::Invalid
        );
        assert_eq!(
            mgr.get(&cell).unwrap().total_refs,
            1,
            "session 1's ref must survive an over-drop attempt by session 2"
        );
        // Only session 1 can drop its own ref.
        assert_eq!(
            mgr.process_drop_with_session(cell, fed, 1),
            DropResult::CanRevoke
        );
    }

    #[test]
    fn byzantine_node_different_session_cannot_drop_others_refs() {
        let mut mgr = ExportGcManager::new();
        let cell = cell_1();

        // Federation A exports on session 10
        mgr.record_export_with_session(cell, fed_a(), 100, 10);
        // Federation B exports on session 20
        mgr.record_export_with_session(cell, fed_b(), 100, 20);

        assert_eq!(mgr.get(&cell).unwrap().total_refs, 2);

        // Byzantine B tries to drop A's ref using B's session — rejected
        // (from_federation=fed_a but session=20 doesn't match A's session=10)
        let result = mgr.process_drop_with_session(cell, fed_a(), 20);
        assert_eq!(result, DropResult::Invalid);
        assert_eq!(mgr.get(&cell).unwrap().total_refs, 2);

        // A can drop its own ref with correct session
        let result = mgr.process_drop_with_session(cell, fed_a(), 10);
        assert_eq!(result, DropResult::StillHeld);
    }

    // --- Import GC tests ---

    #[test]
    fn import_multiple_federations_independent() {
        let mut mgr = ImportGcManager::new();
        let cell = cell_1();

        mgr.record_import(fed_a(), cell);
        mgr.record_import(fed_b(), cell);

        // Drop from A: only generates message for A
        let msg = mgr.local_ref_dropped(fed_a(), cell);
        assert_eq!(
            msg,
            Some(DropMessage {
                target_federation: fed_a(),
                cell_id: cell,
            })
        );

        // B still tracked
        assert!(mgr.get(&fed_b(), &cell).is_some());
        assert_eq!(mgr.len(), 1);
    }
}
