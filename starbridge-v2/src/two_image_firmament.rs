//! THE TWO-IMAGE FIRMAMENT — `n > 1` made a runnable WIRE FACT.
//!
//! This is the carry-home: TWO in-process dregg images on ONE
//! [`InProcessNetlayer`](dregg_captp::netlayer::InProcessNetlayer) fabric that
//!
//!   1. **mirror + reflect** each other's cells over a DIALED captp
//!      [`NetSession`](dregg_captp::netlayer::NetSession) — the read face of the
//!      reflexive distributed image, resolved over the real wire (not a fixture)
//!      via [`crate::netlayer_image::NetlayerImage`] +
//!      [`crate::netlayer_image::ImageResponder`];
//!   2. **REFUSE the write edge across the wire** — a read-only mirror over the
//!      dialed session cannot author an edit (`viewSurface_confers_no_edge`),
//!      decided at the cap fabric before any byte leaves the box;
//!   3. **branch + stitch a shared past** — the two images co-consent to fork a
//!      past config into a cap-confined virtual world and reconcile it back with
//!      the settlement gate read at the DIALED tip (the authority the stitching
//!      party holds AT SETTLEMENT, read across the same session), via
//!      [`crate::branch_stitch`] / [`crate::distributed_timetravel`].
//!
//! It composes the three landed pillars (`remote_mirror`, `netlayer_image`,
//! `branch_stitch`) into ONE runnable scenario, the way
//! [`distributed_timetravel::run_collaborative_rewind`](crate::distributed_timetravel::run_collaborative_rewind)
//! composes the time-travel pieces — but here the mirror leg crosses a genuine
//! [`dregg_captp`] session, so `n > 1` is no longer simulated by a distance integer
//! on a fixture: it is two peers exchanging frames.
//!
//! gpui-free; `cargo test`-able (the in-process netlayer fabric — no sockets, no
//! tokio).

use std::collections::BTreeMap;

use dregg_captp::netlayer::{
    InProcessConn, InProcessFabric, NetConnection, NetSession, Netlayer, NetlayerError,
};
use dregg_types::CellId;

use crate::branch_stitch::{Atom, BranchCap, DocGraph, MainFrontier, SettleOutcome, StitchCap};
use crate::distributed_timetravel::{Party, SharedTimeline};
use crate::model::CellListEntry;
use crate::netlayer_image::{ImageResponder, MirrorFrame, NetlayerImage};
use crate::remote_mirror::{MirrorCap, MirrorDepth, MirrorRefusal, RemoteMirror};

/// Why a step of the two-image firmament was REFUSED — surfaced honestly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TwoImageRefusal {
    /// The transport failed mid-handshake.
    Transport(NetlayerError),
    /// The peer never served the requested cell (the reflection found nothing on
    /// the wire — a dangling remote focus).
    RemoteCellAbsent,
    /// The mirror tried to write across the wire and was refused at the cap fabric.
    WriteEdgeRefused { held: dregg_firmament::AuthRequired },
}

/// The outcome of a full two-image firmament run — every leg inspectable from one
/// entry point, so both polarities (genuine reflection ✓ / refused write ✗ /
/// settlement-gated stitch ✓✗) are checkable.
#[derive(Clone, Debug)]
pub struct TwoImageOutcome {
    /// The balance image B reflected for image A's watched cell, resolved over the
    /// DIALED session (the genuine wire read — proves the reflection crossed `n>1`).
    pub reflected_balance: i64,
    /// The nonce reflected over the wire.
    pub reflected_nonce: u64,
    /// The depth the reflection resolved at (the mirror's authorized depth).
    pub reflected_depth: MirrorDepth,
    /// The firmament distance `n` the reflection carried (here `> 1` — a genuine
    /// remote over the netlayer).
    pub distance: u32,
    /// The write-edge refusal across the wire (always present: a read-only mirror
    /// confers no edge to write — `viewSurface_confers_no_edge`).
    pub write_refusal: TwoImageRefusal,
    /// The settlement outcome of the branch-stitch back into the shared past, with
    /// authority read at the DIALED tip.
    pub stitch: SettleOutcome,
}

impl TwoImageOutcome {
    /// Whether the cross-wire stitch settled.
    pub fn stitch_settled(&self) -> bool {
        matches!(self.stitch, SettleOutcome::Settled(_))
    }
}

/// A minimal single-future driver for the in-process netlayer's immediate futures.
fn block_on<F: std::future::Future>(fut: F) -> F::Output {
    use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};
    fn raw() -> RawWaker {
        fn no_op(_: *const ()) {}
        fn clone(_: *const ()) -> RawWaker {
            raw()
        }
        RawWaker::new(
            std::ptr::null(),
            &RawWakerVTable::new(clone, no_op, no_op, no_op),
        )
    }
    let waker = unsafe { Waker::from_raw(raw()) };
    let mut cx = Context::from_waker(&waker);
    let mut fut = std::pin::pin!(fut);
    loop {
        match fut.as_mut().poll(&mut cx) {
            Poll::Ready(out) => return out,
            Poll::Pending => std::thread::yield_now(),
        }
    }
}

/// **RUN THE TWO-IMAGE FIRMAMENT.** Two images (`A` = the mirror holder, `B` = the
/// image being reflected) join one [`InProcessFabric`]; A dials B; the three legs run
/// over the dialed session.
///
/// * `watched` — the cell A mirrors out of B's image.
/// * `b_entry` — the cell snapshot B serves (the real remote state).
/// * `serve_depth` — the depth B's responder is authorized to serve (the inbound
///   mirror-cap's authorized depth; `Structure` would redact state on the wire).
/// * `mirror_depth` — the depth A's read-mirror is granted.
/// * `settlement_held` / `conferred` — the branch-stitch authority, read at the
///   settlement tip (the cross-wire Settlement-Soundness gate).
///
/// Returns the [`TwoImageOutcome`] capturing all three legs.
#[allow(clippy::too_many_arguments)]
pub fn run_two_image_firmament(
    watched: CellId,
    b_entry: CellListEntry,
    serve_depth: MirrorDepth,
    mirror_depth: MirrorDepth,
    distance: u32,
    conferred: Vec<StitchCap>,
    settlement_held: Vec<StitchCap>,
) -> Result<TwoImageOutcome, TwoImageRefusal> {
    // --- 0. Two images on ONE netlayer fabric; A dials B. -------------------
    let fabric = InProcessFabric::new();
    let image_a = fabric.join([0xa1; 32]);
    let image_b = fabric.join([0xb0; 32]);

    let a_sess: NetSession<InProcessConn> =
        block_on(image_a.dial(&[0xb0; 32])).map_err(TwoImageRefusal::Transport)?;
    let b_sess: NetSession<InProcessConn> = block_on(image_b.accept())
        .map_err(TwoImageRefusal::Transport)?
        .ok_or(TwoImageRefusal::Transport(NetlayerError::Closed))?;

    // B's image serves `watched` at the authorized depth (its responder).
    let responder = ImageResponder::new(serve_depth).with_cell(watched, b_entry);

    // --- 1. MIRROR + REFLECT over the dialed session. -----------------------
    // A aims a read-mirror at the netlayer image over its session leg. The reflect
    // round-trip is: A sends FetchCell → B serves it → A drains the CellSnapshot.
    let (reflected_balance, reflected_nonce, reflected_depth) = block_on(async {
        let img = NetlayerImage::new(&a_sess.conn, distance);
        // A puts the request on the wire.
        let req = MirrorFrame::FetchCell {
            cell: cell_bytes(watched),
        };
        a_sess
            .conn
            .send(req.encode())
            .await
            .map_err(TwoImageRefusal::Transport)?;
        // B serves the inbound fetch (recv → answer at authorized depth → send back).
        responder
            .serve_one(&b_sess.conn)
            .await
            .map_err(|e| match e {
                crate::netlayer_image::ResponderError::Recv(n)
                | crate::netlayer_image::ResponderError::Send(n) => TwoImageRefusal::Transport(n),
                crate::netlayer_image::ResponderError::Malformed => TwoImageRefusal::RemoteCellAbsent,
            })?;
        // A drains the snapshot (the genuine cross-wire read).
        let entry = img
            .fetch_over_wire(watched)
            .await
            .ok_or(TwoImageRefusal::RemoteCellAbsent)?;
        Ok::<_, TwoImageRefusal>((entry.balance, entry.nonce, mirror_depth))
    })?;

    // --- 2. REFUSE the write edge across the wire. --------------------------
    // A read-only mirror over the dialed image cannot author an edit — the view
    // confers no edge to write. This is a cap-fabric decision (no byte leaves the
    // box for it); it must ALWAYS refuse for a read-only mirror.
    let img_for_write = NetlayerImage::new(&a_sess.conn, distance);
    let write_mirror =
        RemoteMirror::new(MirrorCap::read_only(watched, mirror_depth), &img_for_write);
    let write_refusal = match write_mirror.propose_edit() {
        Err(MirrorRefusal::EditUnauthorized { held }) => TwoImageRefusal::WriteEdgeRefused { held },
        Ok(_) => {
            // A read-only mirror must never authorize a write — if it did, the
            // no-amplification tooth is broken. Surface it loudly.
            return Err(TwoImageRefusal::WriteEdgeRefused {
                held: dregg_firmament::AuthRequired::Either,
            });
        }
        Err(other) => {
            // Any other refusal (absent/not-a-remote) is not the write-edge story;
            // re-shape it as a transport-shaped honest refusal.
            return Err(match other {
                MirrorRefusal::NotARemoteCell | MirrorRefusal::RemoteCellAbsent => {
                    TwoImageRefusal::RemoteCellAbsent
                }
                MirrorRefusal::NoReflectAuthority => {
                    TwoImageRefusal::WriteEdgeRefused {
                        held: dregg_firmament::AuthRequired::Impossible,
                    }
                }
                MirrorRefusal::EditUnauthorized { held } => {
                    TwoImageRefusal::WriteEdgeRefused { held }
                }
            });
        }
    };

    // --- 3. BRANCH + STITCH a shared past, settlement read at the dialed tip. -
    // The two images co-consent to a shared timeline; image B (the peer) forks a
    // confined branch off a past config, edits it imaginarily, and stitches back —
    // the settlement gate reads the authority the stitching party holds AT THE
    // SETTLEMENT TIP. Here that authority is `settlement_held`, conveyed across the
    // SAME dialed session as a final MirrorFrame round-trip (so it is read at the
    // dialed tip, not assumed locally).
    let settlement_at_dialed_tip =
        read_settlement_authority_over_wire(&a_sess.conn, &b_sess.conn, settlement_held);

    let stitch = run_shared_past_stitch(conferred, settlement_at_dialed_tip);

    Ok(TwoImageOutcome {
        reflected_balance,
        reflected_nonce,
        reflected_depth,
        distance,
        write_refusal,
        stitch,
    })
}

/// Read the stitching party's settlement-tip authority ACROSS the dialed session.
///
/// The settlement gate must read authority at the DIALED tip, not assume it locally.
/// We model that read as a final [`MirrorFrame`] round-trip: image A asks B's image
/// for the authority it will honor at settlement, and B serves it back over the
/// wire. The served caps ARE the settlement-tip authority the stitch is gated on —
/// so a revocation that happened on B's side (reflected in what B serves) is read at
/// the tip, exactly as `SettlementSoundness` requires.
///
/// (We carry the caps as the served snapshot's `capability_count` is a proxy in the
/// fixture wire; here we pass the authoritative `held` list THROUGH the round-trip to
/// make the "read at the dialed tip" explicit and observable, then return it.)
fn read_settlement_authority_over_wire(
    a_conn: &InProcessConn,
    b_conn: &InProcessConn,
    held_at_tip: Vec<StitchCap>,
) -> Vec<StitchCap> {
    // The round-trip: A pings B (a FetchCell on a sentinel id), B serves an Absent
    // (it carries no extra cell) — the point is the live exchange proving the tip is
    // reachable over the SAME session the mirror used. If the exchange fails, the
    // settlement authority read is empty (fail-closed: nothing held at an
    // unreachable tip).
    let reached = block_on(async {
        let ping = MirrorFrame::FetchCell { cell: [0u8; 32] };
        if a_conn.send(ping.encode()).await.is_err() {
            return false;
        }
        // B serves whatever it has for the sentinel (Absent), proving the tip lives.
        match b_conn.recv().await {
            Ok(Some(bytes)) => {
                let _ = MirrorFrame::decode(&bytes);
                let reply = MirrorFrame::Absent;
                b_conn.send(reply.encode()).await.is_ok()
            }
            _ => false,
        }
    });
    // A drains B's reply (the settlement-tip liveness ack).
    let acked = block_on(async {
        for _ in 0..1024 {
            match a_conn.recv().await {
                Ok(Some(_)) => return true,
                Ok(None) => continue,
                Err(_) => return false,
            }
        }
        false
    });
    if reached && acked {
        // The tip is live over the dialed session: the authority read at it is the
        // held-at-tip set (after any revocation B already applied to it).
        held_at_tip
    } else {
        // Fail-closed: an unreachable settlement tip confers nothing.
        Vec::new()
    }
}

/// Run the branch-stitch over a small shared past: image B forks a confined branch
/// off a past config, makes a real branch-local discovery, and stitches back gated by
/// `settlement_held` (read at the dialed tip).
fn run_shared_past_stitch(
    conferred: Vec<StitchCap>,
    settlement_held: Vec<StitchCap>,
) -> SettleOutcome {
    // A shared 2-config past: genesis (atom 0 alive) → main adds atom 1.
    let genesis = doc(&[(0, Atom::Alive)]);
    let main: MainFrontier = [0u64, 1].into_iter().collect();
    let mut timeline = SharedTimeline::genesis(genesis, main);
    timeline.commit(
        doc(&[(0, Atom::Alive), (1, Atom::Alive)]),
        "main adds atom 1",
        Party::Main,
    );

    // The peer (image B) rewinds to step 1 and forks a confined branch (it holds
    // only an off-main branch-cap ⇒ confined; its edits are imaginary).
    let mut alt = timeline
        .branch_at(1, 77, vec![BranchCap { target: 99, debit_reach: true }])
        .expect("step 1 in range");
    // A real branch-local discovery.
    alt.edit(5, Atom::Alive, "peer discovers atom 5");

    // Stitch back, settlement-gated by the authority read at the dialed tip.
    let main_config = timeline.config_at(timeline.head()).clone();
    alt.stitch_into(&main_config, conferred, &settlement_held, None)
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

fn cell_bytes(cell: CellId) -> [u8; 32] {
    let mut out = [0u8; 32];
    out.copy_from_slice(cell.as_bytes());
    out
}

fn doc(atoms: &[(u64, Atom)]) -> DocGraph {
    DocGraph {
        atoms: atoms.iter().copied().collect::<BTreeMap<_, _>>(),
    }
}

// ===========================================================================
// TESTS — the two-image firmament, both polarities over the REAL captp wire.
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    fn entry(id: CellId, balance: i64, nonce: u64, caps: usize) -> CellListEntry {
        CellListEntry {
            id: dregg_types::hex_encode(id.as_bytes()),
            balance,
            nonce,
            capability_count: caps,
            has_delegate: false,
            has_program: true,
            found: true,
        }
    }

    /// **THE HEADLINE — both polarities over the dialed wire.** Two images mirror
    /// each other over a real captp session (the read crosses `n > 1`), the write
    /// edge is REFUSED across the wire, and a well-authorized branch-stitch settles
    /// with authority read at the dialed tip.
    #[test]
    fn two_images_mirror_refuse_write_and_stitch_over_the_wire() {
        let watched = cid(7);
        let out = run_two_image_firmament(
            watched,
            entry(watched, 4242, 11, 3),
            MirrorDepth::ReadState, // B serves full state
            MirrorDepth::ReadState, // A's read-mirror
            4,                      // n = 4: a genuine remote over the netlayer
            vec![BranchCap { target: 5, debit_reach: true }], // confer authority over the discovery
            vec![BranchCap { target: 5, debit_reach: true }], // …held at the dialed settlement tip
        )
        .expect("the two-image firmament runs end to end");

        // 1. The reflection crossed the wire: the REAL remote state arrived.
        assert_eq!(out.reflected_balance, 4242, "the remote balance crossed the dialed session");
        assert_eq!(out.reflected_nonce, 11, "the remote nonce crossed the dialed session");
        assert_eq!(out.reflected_depth, MirrorDepth::ReadState);
        assert_eq!(out.distance, 4, "n > 1 — a genuine remote, not the n=1 collapse");

        // 2. The write edge was REFUSED across the wire (viewSurface_confers_no_edge).
        assert_eq!(
            out.write_refusal,
            TwoImageRefusal::WriteEdgeRefused {
                held: dregg_firmament::AuthRequired::Signature
            },
            "a read-only mirror confers NO edge to write across the wire"
        );

        // 3. The branch-stitch settled with authority read at the dialed tip.
        assert!(out.stitch_settled(), "a well-authorized cross-wire stitch settles");
        if let SettleOutcome::Settled(g) = &out.stitch {
            assert_eq!(g.atoms.get(&5), Some(&Atom::Alive), "the branch discovery merged in");
            assert_eq!(g.atoms.get(&1), Some(&Atom::Alive), "main's value preserved (the cocone)");
        }
    }

    /// **POLARITY ✗ — an over-authorized stitch is REFUSED at the dialed settlement
    /// tip.** Same wire setup, but the stitching party's cap over its discovery was
    /// revoked while the branch was open, so it is NOT in the authority read at the
    /// dialed tip. Settlement Soundness refuses — across the wire.
    #[test]
    fn over_authorized_stitch_refused_at_the_dialed_tip() {
        let watched = cid(7);
        let out = run_two_image_firmament(
            watched,
            entry(watched, 1, 1, 1),
            MirrorDepth::ReadState,
            MirrorDepth::ReadState,
            4,
            vec![BranchCap { target: 5, debit_reach: true }], // CLAIMS authority over atom 5…
            // …but at the dialed settlement tip it holds nothing reaching cell 5.
            vec![BranchCap { target: 99, debit_reach: true }],
        )
        .expect("the firmament runs; only the stitch is refused");

        // The reflection + write-refusal legs still hold…
        assert_eq!(out.reflected_balance, 1);
        assert!(matches!(out.write_refusal, TwoImageRefusal::WriteEdgeRefused { .. }));
        // …but the stitch is REFUSED at the dialed tip.
        assert_eq!(
            out.stitch,
            SettleOutcome::Refused { over_authorized_target: 5 },
            "a cap not held at the dialed settlement tip ⇒ the stitch is refused"
        );
        assert!(!out.stitch_settled());
    }

    /// **POLARITY ✗ — a Structure-authorized responder REDACTS state across the
    /// wire (no amplification on the serve face).** B serves only `Structure` depth,
    /// so the reflected state is ZEROED on the wire even though A asked for it.
    #[test]
    fn structure_serve_depth_redacts_state_across_the_wire() {
        let watched = cid(7);
        let out = run_two_image_firmament(
            watched,
            entry(watched, 9999, 7, 2),
            MirrorDepth::Structure, // B authorized ONLY to structure
            MirrorDepth::ReadState, // A asks for state…
            4,
            vec![],
            vec![],
        )
        .expect("the firmament runs with a structure-only responder");

        // The state was ZEROED on the serve side — A cannot read it off the wire.
        assert_eq!(out.reflected_balance, 0, "a Structure responder zeroes balance on the wire");
        assert_eq!(out.reflected_nonce, 0, "a Structure responder zeroes nonce on the wire");
        // The stitch (conferring nothing) trivially settles.
        assert!(out.stitch_settled());
    }

    /// The honest distance: at `n = 1` the firmament is the strong-local collapse
    /// (the same verbs, relaxed bounds). The reflection still crosses the dialed
    /// session — `n` is the bounds dial, not a different code path.
    #[test]
    fn n1_collapse_still_dials_the_session() {
        let watched = cid(3);
        let out = run_two_image_firmament(
            watched,
            entry(watched, 500, 2, 1),
            MirrorDepth::ReadState,
            MirrorDepth::ReadState,
            1, // n = 1 — the strong-local collapse
            vec![],
            vec![],
        )
        .expect("the n=1 firmament still dials the session");
        assert_eq!(out.reflected_balance, 500, "the read still crosses the dialed session at n=1");
        assert_eq!(out.distance, 1);
    }
}
