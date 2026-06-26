//! **The comms-PD chat source** — the real, executor-backed [`ChatSource`] the
//! interactive deos-chat surface drives.
//!
//! This is where the chat UI's membrane affordances become REAL instead of mock.
//! The deos-matrix [`ChatSource`](deos_matrix::source::ChatSource) trait carries
//! the chat transport (rooms / timeline / send) PLUS the executor seam
//! (`mint_membrane` / `rehydrate_drive_stitch` / `membrane_capable`). The bare
//! transport sources (a live `MatrixHandle`, or the offline recorded sync) hold no
//! executor, so they return `MembraneUnavailable`, fail-closed — never a mock
//! envelope. THIS source holds a live [`World`] (the comms-PD's own executor) and
//! implements the membrane operations against genuine `dregg_cell::Cell` frusta:
//!
//!   * **mint** — forks the held world and culls a real [`MembraneFrustum`] in
//!     view of a focus cell (the "screenshot of the moment"), wrapped in the SAME
//!     `MembraneEnvelope` wire shape the Matrix message carries.
//!   * **rehydrate + drive + stitch** — opens a received envelope into a real
//!     `World` fork (anti-substitution root tooth, fail-closed), drives a real
//!     verified turn on it, and stitches the real diff back through the
//!     branch-and-stitch settlement gate (clean fold + a conflict surfaced as a
//!     `ConflictObject` + over-authorized lossy-drop), returning a human summary.
//!
//! All chat-transport calls delegate to an inner [`ChatSource`] (the real wire:
//! a logged-in `MatrixHandle`, or — for the no-homeserver cockpit demo — the
//! recorded sync). The membrane operations are ALWAYS executor-real here.

use std::sync::Mutex;

use deos_matrix::membrane::MembraneEnvelope;
use deos_matrix::source::ChatSource;
use deos_matrix::{DreggObject, Result, RoomSummary, TimelineMessage};

use dregg_cell::CellId;

use crate::shared_fork::{MembraneError, MembraneFrustum};
use crate::world::World;

/// The comms-PD chat source: an inner transport + a live executor world for the
/// real membrane operations.
pub struct CommsPdSource {
    /// The chat transport (rooms/timeline/send) — the world-backed `WorldChatSource`
    /// (rooms are cells, send is a real turn), or a live `MatrixHandle`.
    inner: std::sync::Arc<dyn ChatSource>,
    /// The comms-PD's own executor world — the moment the membrane snapshots and
    /// the substrate a received membrane rehydrates/drives/stitches against. Held
    /// behind a `Mutex` so the `Send + Sync` `ChatSource` can drive it.
    world: Mutex<World>,
    /// The focus cell the "screenshot a moment" mint culls around (a real cell in
    /// `world`). The frustum is always in view of THIS cell — anti-amplification.
    focus: CellId,
    /// Max hops the frustum cull follows from the focus (the far plane).
    depth: u8,
    /// Posted membrane messages: `(room_id, event_id, sender, REAL envelope)`. A
    /// membrane is a transient capability token (a screenshot of the moment), not
    /// durable chat state — held here as genuine executor-minted bytes, merged into
    /// the timeline so the card the user clicks carries real `Cell` frusta.
    posted: Mutex<Vec<(String, String, String, MembraneEnvelope)>>,
}

impl CommsPdSource {
    /// Build a comms-PD source over an inner transport + a live executor world.
    /// `focus` is the cell the "screenshot a moment" mint culls around; `depth` is
    /// the frustum's far plane.
    pub fn new(
        inner: std::sync::Arc<dyn ChatSource>,
        world: World,
        focus: CellId,
        depth: u8,
    ) -> Self {
        CommsPdSource {
            inner,
            world: Mutex::new(world),
            focus,
            depth,
            posted: Mutex::new(Vec::new()),
        }
    }

    /// Build a default summary line for a settled stitch.
    fn settle_summary(root: [u8; 32], merged: usize, dropped: usize) -> String {
        let mut s = String::with_capacity(8);
        for b in &root[..4] {
            s.push_str(&format!("{b:02x}"));
        }
        if dropped == 0 {
            format!("settled root {s}… · {merged} atom(s) folded clean")
        } else {
            format!("settled root {s}… · {merged} folded · {dropped} conflict-object(s) surfaced")
        }
    }
}

impl ChatSource for CommsPdSource {
    // --- transport: delegate to the inner (real) source ----------------------
    fn whoami(&self) -> Option<String> {
        self.inner.whoami()
    }
    fn rooms(&self) -> Result<Vec<RoomSummary>> {
        self.inner.rooms()
    }
    fn timeline(&self, room_id: &str, limit: u16) -> Result<Vec<TimelineMessage>> {
        use deos_matrix::client::{EventState, MessageKind, TimelineMessage};
        // The real text timeline off the world-chat (rooms are cells, each message a
        // real turn), then append the REAL membrane messages posted to this room
        // (genuine executor-minted envelopes). No mock anywhere.
        let mut tl = self.inner.timeline(room_id, limit)?;
        // Membranes render at the tail (most recent): just past the last message's
        // display time (a sensible day/time label, not a degenerate u64::MAX).
        let mut tail_ts = tl.iter().map(|m| m.timestamp_ms).max().unwrap_or(0);
        let posted = self.posted.lock().unwrap();
        for (rid, event_id, sender, env) in posted.iter() {
            if rid == room_id {
                tail_ts = tail_ts.saturating_add(1);
                tl.push(TimelineMessage {
                    event_id: event_id.clone(),
                    sender: sender.clone(),
                    body: env.text_fallback(),
                    timestamp_ms: tail_ts,
                    kind: MessageKind::Membrane,
                    state: EventState::Live,
                    reactions: Vec::new(),
                    reply_to: None,
                    thread_root: None,
                    membrane: Some(env.clone()),
                    object: None,
                });
            }
        }
        Ok(tl)
    }
    fn send(&self, room_id: &str, body: &str) -> Result<String> {
        self.inner.send(room_id, body)
    }
    fn send_membrane(
        &self,
        room_id: &str,
        _body: &str,
        membrane: MembraneEnvelope,
    ) -> Result<String> {
        // Record the REAL executor-minted membrane as a posted message in this room.
        // (A live `MatrixHandle` inner would ALSO POST it over the wire; the
        // world-chat inner is local-sovereign, so the post lives in this comms-PD.)
        let event_id = {
            let mut s = String::from("mem-");
            for b in &membrane.frustum_root[..6] {
                s.push_str(&format!("{b:02x}"));
            }
            s
        };
        let sender = self
            .whoami()
            .unwrap_or_else(|| "@me:deos.local".to_string());
        self.posted
            .lock()
            .unwrap()
            .push((room_id.to_string(), event_id.clone(), sender, membrane));
        Ok(event_id)
    }
    fn send_object(&self, room_id: &str, body: &str, object: DreggObject) -> Result<String> {
        self.inner.send_object(room_id, body, object)
    }
    fn sync(&self) -> Result<()> {
        self.inner.sync()
    }
    fn room_cell(&self, room_id: &str) -> deos_matrix::cell::RoomCell {
        self.inner.room_cell(room_id)
    }
    fn identity(&self, user_id: &str) -> deos_matrix::cell::IdentityCell {
        self.inner.identity(user_id)
    }
    fn typing(&self, room_id: &str) -> Vec<String> {
        self.inner.typing(room_id)
    }
    fn read_by(&self, room_id: &str) -> Vec<String> {
        self.inner.read_by(room_id)
    }

    // --- the REAL membrane operations (executor-backed) ----------------------
    fn membrane_capable(&self) -> bool {
        true
    }

    fn mint_membrane(&self, _room_id: &str) -> Result<MembraneEnvelope> {
        // Fork the live world (a deep clone + the genuine executor) and cull a real
        // frustum in view of the focus cell — the screenshot of the moment.
        let world = self.world.lock().unwrap();
        let fork = world.fork();
        let frustum = MembraneFrustum::mint(&fork, self.focus, self.depth);
        let root = frustum.frustum_root();
        let snapshot = frustum.to_snapshot_bytes();
        Ok(MembraneEnvelope {
            version: MembraneEnvelope::VERSION,
            frustum_root: root,
            sturdyref: {
                let mut s = String::from("dregg://fork/");
                for b in &root[..4] {
                    s.push_str(&format!("{b:02x}"));
                }
                s
            },
            lineage: self.focus.0.to_vec(),
            snapshot,
            cut: deos_matrix::membrane::FrustumCut {
                focus_cell: self.focus.0,
                max_depth: self.depth,
                authority_bounded: true,
                cell_count: frustum.cells.len() as u32,
            },
            cursor: deos_matrix::membrane::WitnessCursor {
                height: frustum.minted_height,
                commit_index: 0,
            },
        })
    }

    fn rehydrate_drive_stitch(&self, membrane: &MembraneEnvelope) -> Result<String> {
        use crate::branch_stitch::{BranchCap, SettleOutcome, Stitch};

        // (1) Forward-compat + anti-substitution: refuse a newer wire version or a
        //     substituted snapshot, fail-closed (NEVER trust a mismatched frustum).
        if !membrane.is_rehydratable() {
            return Err(deos_matrix::Error::Other(
                "membrane wire version is newer than this build — refusing (fail-closed)".into(),
            ));
        }
        let frustum = MembraneFrustum::from_snapshot_bytes(&membrane.snapshot)
            .map_err(|e: MembraneError| deos_matrix::Error::Other(e.to_string()))?;
        let mut fork = frustum
            .rehydrate(membrane.frustum_root)
            .map_err(|e: MembraneError| deos_matrix::Error::Other(e.to_string()))?;

        // (2) DRIVE a real verified turn on the rehydrated fork. We drive the focus
        //     cell of the received frustum (the cell in view), a value-preserving
        //     `SetField` — committed against the fork's verified executor.
        let focus = CellId(membrane.cut.focus_cell);
        // Pick a real cell present in the fork to write (the focus if present, else
        // the first cell) so the drive is a genuine mutation, not a no-op.
        let target = if fork.ledger().get(&focus).is_some() {
            focus
        } else {
            match fork.ledger().iter().next() {
                Some((id, _)) => *id,
                None => {
                    return Err(deos_matrix::Error::Other(
                        "rehydrated fork is empty — nothing to drive".into(),
                    ));
                }
            }
        };
        let drive = fork.turn(
            target,
            vec![crate::world::set_field(target, 0, [0xD7u8; 32])],
        );
        if !fork.commit_turn(drive).is_committed() {
            return Err(deos_matrix::Error::Other(
                "the driven turn was refused by the fork executor (fail-closed)".into(),
            ));
        }

        // (3) STITCH the REAL driven diff back through the settlement gate. The
        //     clean part folds (LUB); the settlement gate governs conferred
        //     authority (an over-authorized confer is a lossy ConflictObject).
        let (baseline, driven) = frustum.driven_graphs(&fork);
        fn cell_key(id: &CellId) -> u64 {
            let b = id.as_bytes();
            u64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]])
        }
        // Confer back only the cells the frustum genuinely held (in-authority); the
        // settlement gate re-checks each at the tip.
        let conferred: Vec<BranchCap> = frustum
            .cells
            .iter()
            .map(|c| BranchCap {
                target: cell_key(&c.id()),
                debit_reach: false,
            })
            .collect();
        let stitch = Stitch {
            main: baseline,
            branch: driven.clone(),
            conferred: conferred.clone(),
        };
        match stitch.settle(&conferred, None) {
            SettleOutcome::Settled(merged) => Ok(Self::settle_summary(
                fork.state_root(),
                merged.atoms.len(),
                0,
            )),
            SettleOutcome::Refused {
                over_authorized_target,
            } => {
                // An over-authorized confer is a lossy-drop surfaced as a conflict —
                // transparent, fail-closed (NOT a silent overwrite).
                let mut s =
                    String::from("over-authorized confer refused (lossy-drop) at cell key 0x");
                s.push_str(&format!("{over_authorized_target:016x}"));
                Ok(s)
            }
        }
    }

    fn backend_label(&self) -> &'static str {
        "firmament-comms-pd"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world_chat::WorldChatSource;

    /// The real wiring under test: a `WorldChatSource` transport (the chat IS the
    /// world) wrapped by the comms-PD source over a fork of the SAME chat world.
    /// Returns `(source, room_id)` — NO mock anywhere.
    fn wired_source() -> (CommsPdSource, String) {
        let world_chat = WorldChatSource::seeded("@ember:deos.local");
        let room_id = world_chat.rooms().unwrap()[0].room_id.to_string();
        let membrane_world = world_chat.fork_world();
        let focus = world_chat.me_cell();
        let transport: std::sync::Arc<dyn ChatSource> = std::sync::Arc::new(world_chat);
        let source = CommsPdSource::new(transport, membrane_world, focus, 3);
        (source, room_id)
    }

    #[test]
    fn comms_pd_source_mints_and_rehydrates_a_real_membrane_through_the_seam() {
        // The interactive seam, end to end through the `ChatSource` trait, over a
        // REAL world-chat transport: the comms-PD source MINTS a real executor
        // membrane (the screenshot of the moment) and REHYDRATES+DRIVES+STITCHES it —
        // NO mock envelope, NO recorded sync anywhere.
        let (source, room_id) = wired_source();
        assert!(
            source.membrane_capable(),
            "the comms-PD source is executor-backed"
        );
        assert_eq!(source.backend_label(), "firmament-comms-pd");

        // MINT — a genuine frustum of real cells in view of the focus.
        let env = source
            .mint_membrane(&room_id)
            .expect("mint a real membrane");
        assert!(
            env.cut.cell_count >= 1,
            "the frustum culled real cells (the focus + its reach)"
        );
        assert_eq!(env.version, MembraneEnvelope::VERSION);

        // SEND the real membrane → it appears in the timeline as a Membrane card
        // carrying genuine bytes (the interactive "⬡ attach membrane" path).
        let id = source
            .send_membrane(&room_id, "", env.clone())
            .expect("post the real membrane");
        assert!(!id.is_empty());
        let tl = source.timeline(&room_id, 80).expect("timeline");
        let card = tl
            .iter()
            .find(|m| m.membrane.is_some())
            .expect("a real membrane card is in the timeline");
        assert_eq!(
            card.membrane.as_ref().unwrap(),
            &env,
            "the card carries the EXACT real envelope"
        );

        // REHYDRATE + DRIVE + STITCH — the received side, all real, returns a settled
        // summary (the clean fold of B's real driven turn).
        let summary = source
            .rehydrate_drive_stitch(&env)
            .expect("rehydrate + drive + stitch the real membrane");
        assert!(
            summary.contains("settled root") || summary.contains("lossy-drop"),
            "the stitch returns a real settled/conflict summary, got: {summary}"
        );
    }

    #[test]
    fn comms_pd_rehydrate_fails_closed_on_a_substituted_snapshot() {
        // Fail-closed (no mock leniency): a substituted snapshot whose root no longer
        // matches is REFUSED before a single cell is trusted.
        let (source, room_id) = wired_source();
        let mut env = source.mint_membrane(&room_id).expect("mint");
        // Substitute the frustum root to a value the snapshot does NOT reproduce —
        // the anti-substitution tooth must refuse before trusting a single cell. (A
        // trailing-byte append would be ignored by postcard and re-derive the same
        // root, so we tamper the CLAIMED root directly: a substituted-snapshot proxy.)
        env.frustum_root[0] ^= 0xff;
        let err = source.rehydrate_drive_stitch(&env).unwrap_err();
        assert!(
            err.to_string().contains("mismatch")
                || err.to_string().contains("malformed")
                || err.to_string().contains("frustum"),
            "a substituted snapshot is refused fail-closed, got: {err}"
        );
    }

    #[test]
    fn bare_transport_source_is_not_membrane_capable() {
        // The honest no-executor case: a bare transport (the world-chat alone, or a
        // live MatrixHandle with no comms-PD world) is NOT membrane-capable and
        // returns MembraneUnavailable — NEVER a mock envelope.
        let world_chat = WorldChatSource::seeded("@ember:deos.local");
        assert!(
            !world_chat.membrane_capable(),
            "a bare transport holds no executor"
        );
        assert!(
            world_chat.mint_membrane("!deoslab:deos.local").is_err(),
            "no mock mint"
        );
    }
}
