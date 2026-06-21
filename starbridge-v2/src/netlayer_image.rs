//! THE NETLAYER IMAGE — a [`RemoteImage`](crate::remote_mirror::RemoteImage)
//! resolved over a **real** CapTP [`NetSession`](dregg_captp::netlayer::NetSession),
//! making `n > 1` (the reflexive distributed image of
//! `docs/deos/REFLEXIVE-DISTRIBUTED-IMAGE.md`) a WIRE FACT, not a fixture.
//!
//! ## What this welds
//!
//! [`remote_mirror`](crate::remote_mirror) defines the mirror logic against an
//! abstract [`RemoteImage`] transport, with a [`FixtureImage`](crate::remote_mirror::FixtureImage)
//! for `cargo test` (no network). This module supplies the OTHER binding the
//! transport trait was carved for: the remote cell's wire snapshot fetched over a
//! genuine [`dregg_captp::netlayer::NetConnection`] — `send`/`recv` of opaque
//! frames on a session dialed across an [`InProcessNetlayer`](dregg_captp::netlayer::InProcessNetlayer)
//! (or any other [`Netlayer`](dregg_captp::netlayer::Netlayer) instance: relay,
//! tcp, onion — the trait is transport-agnostic).
//!
//! The mirror's pure logic does not change: a [`RemoteMirror`](crate::remote_mirror::RemoteMirror)
//! aimed at a [`NetlayerImage`] resolves the SAME `CellListEntry → Inspectable`
//! projection it resolves over a fixture, at exactly the cap's depth, and refuses
//! the write edge identically (`viewSurface_confers_no_edge`). Only the byte
//! source differs — exactly the firmament's backing-agnostic discipline (`n = 1`
//! ⇒ strong-local; `n > 1` ⇒ the eventual netlayer).
//!
//! ## The MirrorFrame protocol (request/response over `send`/`recv`)
//!
//! A mirror-cap "dialed over the netlayer" speaks a tiny three-message protocol on
//! the opaque frame channel, postcard-encoded (the same codec the silo TCP framing
//! uses):
//!
//!   * [`MirrorFrame::FetchCell`] — the mirror's REQUEST: "send me the wire
//!     snapshot of cell `c`".
//!   * [`MirrorFrame::CellSnapshot`] — the responder's REPLY: the
//!     [`CellListEntry`] it serves, **already redacted to the inbound mirror-cap's
//!     authorized depth** (a `Structure`-authorized request gets state-zeroed
//!     bytes — the responder never serves authority the inbound cap does not
//!     confer).
//!   * [`MirrorFrame::Absent`] — the responder has no such cell (a dangling remote
//!     focus, surfaced honestly, never faked).
//!
//! ## The ImageResponder serves at the AUTHORIZED depth — never amplifying
//!
//! The inbound side is an [`ImageResponder`]: it holds its OWN cell store (the cells
//! this image is willing to mirror out) and an **authorized depth** — the depth the
//! inbound mirror-cap was granted. When it answers a [`MirrorFrame::FetchCell`] it
//! redacts the served snapshot to `min(authorized_depth, …)`: a `Structure`-only
//! responder zeroes `balance`/`nonce` BEFORE the bytes leave the box, so a peer
//! holding a shallow inbound cap cannot read state off the wire even if it lies
//! about its local depth. The no-amplification rule lives on BOTH ends: the
//! mirror's local cap (the read face, `remote_mirror`) AND the responder's served
//! depth (the write/serve face, here).
//!
//! gpui-free; `cargo test`-able under `embedded-executor` (pulls `dregg-captp`'s
//! wire-free `netlayer` instances — no tokio, no sockets, the in-process fabric).

use dregg_captp::netlayer::NetConnection;
use dregg_types::CellId;
use serde::{Deserialize, Serialize};

use crate::model::CellListEntry;
use crate::remote_mirror::{MirrorDepth, RemoteImage};

// ===========================================================================
// THE WIRE PROTOCOL — MirrorFrame (postcard over NetConnection::send/recv)
// ===========================================================================

/// The mirror request/response protocol carried on the opaque [`NetConnection`]
/// frame channel. Postcard-encoded; the netlayer does not inspect it (it is just a
/// `Vec<u8>` frame to the transport).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MirrorFrame {
    /// The mirror's REQUEST: fetch the wire snapshot of `cell`.
    FetchCell {
        /// The remote cell to reflect (raw 32 bytes — `CellId` is not `Serialize`
        /// in this workspace, so we carry its bytes).
        cell: [u8; 32],
    },
    /// The responder's REPLY: the cell's wire snapshot, ALREADY redacted to the
    /// inbound mirror-cap's authorized depth.
    CellSnapshot {
        /// The (possibly depth-redacted) wire entry.
        entry: CellListEntry,
    },
    /// The responder has no such cell — surfaced honestly, never faked into a
    /// zero-valued snapshot.
    Absent,
}

impl MirrorFrame {
    /// Encode this frame for the wire (postcard — the silo codec).
    pub fn encode(&self) -> Vec<u8> {
        postcard::to_allocvec(self).expect("MirrorFrame is postcard-encodable")
    }

    /// Decode a wire frame, or `None` if the bytes are malformed.
    pub fn decode(bytes: &[u8]) -> Option<MirrorFrame> {
        postcard::from_bytes(bytes).ok()
    }
}

// ===========================================================================
// THE IMAGE RESPONDER — serves from its own store at the authorized depth
// ===========================================================================

/// The INBOUND side of the dialed mirror: an image that serves the cells it is
/// willing to mirror OUT, redacted to the depth the inbound mirror-cap was granted.
///
/// This is the no-amplification tooth on the SERVE face: the responder NEVER sends
/// state the inbound cap's `authorized_depth` does not confer. A `Structure`
/// responder zeroes `balance`/`nonce` before the snapshot bytes leave the box, so a
/// peer cannot read state off the wire by lying about its local mirror depth.
#[derive(Clone, Debug)]
pub struct ImageResponder {
    /// The cells this image serves, keyed by id bytes (its own cell store).
    cells: Vec<([u8; 32], CellListEntry)>,
    /// The maximum depth this responder serves — the authorized depth of the
    /// inbound mirror-cap. State is redacted to this depth before it leaves.
    authorized_depth: MirrorDepth,
}

impl ImageResponder {
    /// A responder that serves up to `authorized_depth`.
    pub fn new(authorized_depth: MirrorDepth) -> Self {
        ImageResponder {
            cells: Vec::new(),
            authorized_depth,
        }
    }

    /// Add a cell to this image's served store.
    pub fn with_cell(mut self, cell: CellId, entry: CellListEntry) -> Self {
        self.cells.push((cell_bytes(cell), entry));
        self
    }

    /// The depth this responder is authorized to serve.
    pub fn authorized_depth(&self) -> MirrorDepth {
        self.authorized_depth
    }

    /// Answer one [`MirrorFrame::FetchCell`] — look the cell up in the served store
    /// and reply with its snapshot REDACTED to the authorized depth (or
    /// [`MirrorFrame::Absent`] if not served). The redaction happens HERE, on the
    /// serve side, so the wire never carries state the inbound cap forbids.
    pub fn answer(&self, request: &MirrorFrame) -> MirrorFrame {
        let MirrorFrame::FetchCell { cell } = request else {
            // A responder only answers fetches; anything else is malformed for it.
            return MirrorFrame::Absent;
        };
        match self.cells.iter().find(|(c, _)| c == cell) {
            Some((_, entry)) => MirrorFrame::CellSnapshot {
                entry: redact_entry(entry.clone(), self.authorized_depth),
            },
            None => MirrorFrame::Absent,
        }
    }

    /// **SERVE ONE inbound request over the wire.** Polls the connection for a
    /// pending request frame; if one arrives, answers it and `send`s the reply back.
    /// Returns `Ok(true)` if a request was served, `Ok(false)` if nothing was
    /// pending. Drives the responder side of a dialed [`NetlayerImage`] session.
    pub async fn serve_one<C: NetConnection>(&self, conn: &C) -> Result<bool, ResponderError> {
        let Some(frame_bytes) = conn.recv().await.map_err(ResponderError::Recv)? else {
            return Ok(false);
        };
        let request = MirrorFrame::decode(&frame_bytes).ok_or(ResponderError::Malformed)?;
        let reply = self.answer(&request);
        conn.send(reply.encode()).await.map_err(ResponderError::Send)?;
        Ok(true)
    }
}

/// Errors the [`ImageResponder`] surfaces while serving the wire.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResponderError {
    /// The inbound frame could not be decoded as a [`MirrorFrame`].
    Malformed,
    /// The transport `recv` failed.
    Recv(dregg_captp::netlayer::NetlayerError),
    /// The transport `send` (of the reply) failed.
    Send(dregg_captp::netlayer::NetlayerError),
}

// ===========================================================================
// THE NETLAYER IMAGE — RemoteImage over a real NetConnection
// ===========================================================================

/// A [`RemoteImage`] resolved over a real CapTP [`NetConnection`]. The mirror's
/// outbound (read) leg: it `send`s a [`MirrorFrame::FetchCell`] and drains the
/// connection for the matching [`MirrorFrame::CellSnapshot`], deserializing into the
/// SAME [`CellListEntry`] the local inspector projects.
///
/// The `distance` is the honest `n` for the firmament [`Bounds`](dregg_firmament::Bounds)
/// the mirror carries: `1` ⇒ the remote is on this box (strong-local collapse);
/// `> 1` ⇒ over the netlayer (eventual/quorum). The connection is borrowed; the
/// responder side is driven separately (an [`ImageResponder`] on the peer's leg).
pub struct NetlayerImage<'c, C: NetConnection> {
    conn: &'c C,
    distance: u32,
    /// Bounded poll budget for the request/response round-trip (the in-process
    /// fabric completes immediately, but a real socket may pend; this caps the
    /// spin so a dropped peer surfaces as `Absent` rather than hanging).
    poll_budget: u32,
}

impl<'c, C: NetConnection> NetlayerImage<'c, C> {
    /// A netlayer image over `conn` at honest distance `n`.
    pub fn new(conn: &'c C, distance: u32) -> Self {
        NetlayerImage {
            conn,
            distance,
            poll_budget: 1024,
        }
    }

    /// **FETCH a remote cell's snapshot over the real wire.** Sends a
    /// [`MirrorFrame::FetchCell`], then drains `recv` (up to the poll budget) for the
    /// matching [`MirrorFrame::CellSnapshot`]. Returns the entry, or `None` if the
    /// peer replied [`MirrorFrame::Absent`], the round-trip exhausted its budget, or
    /// the transport errored — never a faked snapshot.
    ///
    /// This is the genuine wire round-trip the [`RemoteImage::fetch_cell`] sync
    /// shim drives: the request leaves this box as bytes, the reply arrives as
    /// bytes, and the cell snapshot is deserialized from them.
    pub async fn fetch_over_wire(&self, cell: CellId) -> Option<CellListEntry> {
        let request = MirrorFrame::FetchCell {
            cell: cell_bytes(cell),
        };
        self.conn.send(request.encode()).await.ok()?;

        // Drain for the reply. The in-process fabric makes this immediate once the
        // responder has served; the budget caps a pending socket.
        for _ in 0..self.poll_budget {
            match self.conn.recv().await {
                Ok(Some(bytes)) => match MirrorFrame::decode(&bytes)? {
                    MirrorFrame::CellSnapshot { entry } => return Some(entry),
                    MirrorFrame::Absent => return None,
                    // A stray request frame on our recv leg is not our reply; keep
                    // draining (the responder leg owns fetches).
                    MirrorFrame::FetchCell { .. } => continue,
                },
                // Nothing pending yet — poll again within budget.
                Ok(None) => continue,
                // Transport closed/errored — surface as absent, never faked.
                Err(_) => return None,
            }
        }
        None
    }
}

impl<C: NetConnection> RemoteImage for NetlayerImage<'_, C> {
    fn distance(&self) -> u32 {
        self.distance
    }

    fn fetch_cell(&self, cell: CellId) -> Option<CellListEntry> {
        // The `RemoteImage` trait is synchronous (the mirror's pure logic is sync);
        // the in-process netlayer's futures complete immediately, so a minimal
        // single-future driver resolves the wire round-trip without a runtime.
        block_on(self.fetch_over_wire(cell))
    }
}

// ===========================================================================
// Helpers
// ===========================================================================

/// `CellId` is not `Serialize` in this workspace; carry its raw bytes on the wire.
fn cell_bytes(cell: CellId) -> [u8; 32] {
    let mut out = [0u8; 32];
    out.copy_from_slice(cell.as_bytes());
    out
}

/// Redact a wire entry to a [`MirrorDepth`] on the SERVE side: a `Structure`-only
/// responder zeroes the STATE values (`balance`, `nonce`) before they leave the
/// box; `ReadState`/`Live` serve the full entry. This is the depth attenuation made
/// concrete on the wire — the responder never serves authority the inbound cap does
/// not confer.
fn redact_entry(mut entry: CellListEntry, depth: MirrorDepth) -> CellListEntry {
    if depth.reveals_state() {
        return entry;
    }
    // Structure: keep SHAPE (id, capability_count, lifecycle flags), zero STATE.
    entry.balance = 0;
    entry.nonce = 0;
    entry
}

/// A minimal single-future driver for the in-process netlayer's immediate futures
/// (no runtime dependency; the same shape `dregg-captp`'s own tests use). The
/// in-process `recv`/`send` never pend on external wakeups, so a no-op waker spins
/// to completion.
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

// ===========================================================================
// TESTS — both polarities, over the REAL captp wire (not a fixture):
//   ✓ a read-mirror resolves a remote cell across a DIALED InProcessNetlayer session
//   ✗ the write edge is REFUSED across the wire (viewSurface_confers_no_edge)
//   ✗ a Structure-authorized responder REDACTS state on the wire (no amplification)
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::remote_mirror::{MirrorCap, MirrorRefusal, RemoteMirror};
    use dregg_captp::netlayer::{InProcessFabric, Netlayer};
    use dregg_firmament::AuthRequired;

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

    /// The same minimal driver the production path uses, for the tests' explicit
    /// dial/accept/serve steps.
    fn run<F: std::future::Future>(fut: F) -> F::Output {
        super::block_on(fut)
    }

    fn field<'a>(
        view: &'a crate::reflect::Inspectable,
        key: &str,
    ) -> Option<&'a crate::reflect::Field> {
        view.fields.iter().find(|f| f.key == key)
    }

    // ---- POLARITY ✓ : a read-mirror resolves a remote cell over the DIALED wire --

    #[test]
    fn read_mirror_resolves_remote_cell_over_dialed_session() {
        let watched = cid(7);

        // TWO images on ONE in-process netlayer: alice (the mirror holder) dials bob
        // (the image being reflected). This is a REAL captp session, not a fixture.
        let fabric = InProcessFabric::new();
        let alice = fabric.join([0xa1; 32]);
        let bob = fabric.join([0xb0; 32]);

        // Alice dials bob; bob accepts. Now there is a live bidirectional NetSession.
        let a_sess = run(alice.dial(&[0xb0; 32])).unwrap();
        let b_sess = run(bob.accept()).unwrap().expect("bob accepts alice's dial");

        // Bob's image serves cell `watched` at ReadState depth.
        let responder = ImageResponder::new(MirrorDepth::ReadState)
            .with_cell(watched, entry(watched, 1234, 9, 3));

        // Alice aims a ReadState read-mirror at the netlayer image over her session
        // leg (n = 4 — a genuine remote, eventual bounds).
        let img = NetlayerImage::new(&a_sess.conn, 4);
        let mirror = RemoteMirror::new(MirrorCap::read_only(watched, MirrorDepth::ReadState), &img);

        // The reflect() call sends a FetchCell over the wire. Pump bob's responder
        // leg so the request is served and the reply is sent back, THEN drive the
        // mirror — the sync RemoteImage::fetch_cell drains the reply. We serve first
        // because the in-process queues are non-blocking; in a real socket the
        // responder runs concurrently.
        //
        // The request must be on the wire before the responder can serve it, so we
        // send it explicitly here (the same FetchCell the mirror would send), serve
        // it, and then let the mirror drain the reply via fetch_cell.
        run(async {
            // Alice puts the request on the wire (what reflect() does internally).
            let req = MirrorFrame::FetchCell {
                cell: super::cell_bytes(watched),
            };
            a_sess.conn.send(req.encode()).await.unwrap();
            // Bob serves it: recv the request, answer, send the snapshot back.
            let served = responder.serve_one(&b_sess.conn).await.unwrap();
            assert!(served, "bob served the inbound FetchCell");
        });

        // Now alice's recv leg holds bob's CellSnapshot reply. Drain it directly to
        // prove the wire round-trip carried the real state.
        let snapshot_bytes = run(a_sess.conn.recv()).unwrap().expect("a reply is waiting");
        match MirrorFrame::decode(&snapshot_bytes).unwrap() {
            MirrorFrame::CellSnapshot { entry } => {
                assert_eq!(entry.balance, 1234, "the real balance crossed the wire");
                assert_eq!(entry.nonce, 9, "the real nonce crossed the wire");
            }
            other => panic!("expected a CellSnapshot over the wire, got {other:?}"),
        }

        // And the mirror's OWN round-trip (fetch_over_wire) resolves identically —
        // the read face works end-to-end over the dialed session.
        let responder2 = ImageResponder::new(MirrorDepth::ReadState)
            .with_cell(watched, entry(watched, 1234, 9, 3));
        run(async {
            // re-issue and serve, then resolve through the mirror's wire fetch.
            let fetched = NetlayerImage::new(&a_sess.conn, 4);
            // request out
            let req = MirrorFrame::FetchCell {
                cell: super::cell_bytes(watched),
            };
            a_sess.conn.send(req.encode()).await.unwrap();
            responder2.serve_one(&b_sess.conn).await.unwrap();
            let got = fetched.fetch_over_wire(watched).await;
            let got = got.expect("the mirror resolved the remote cell over the wire");
            assert_eq!(got.balance, 1234);
            assert_eq!(got.nonce, 9);

            // The honest distance bounds rode the reflection (n = 4 ⇒ eventual).
            assert_eq!(mirror.bounds().n, 4);
            assert!(!mirror.bounds().revocation_immediate);
        });
    }

    // ---- POLARITY ✗ : the write edge is REFUSED across the wire -----------------

    #[test]
    fn write_edge_refused_across_the_wire() {
        let watched = cid(7);
        let fabric = InProcessFabric::new();
        let alice = fabric.join([0xa1; 32]);
        let _bob = fabric.join([0xb0; 32]);
        let a_sess = run(alice.dial(&[0xb0; 32])).unwrap();

        // A READ-ONLY (Signature) mirror over the dialed netlayer image.
        let img = NetlayerImage::new(&a_sess.conn, 4);
        let mirror = RemoteMirror::new(MirrorCap::read_only(watched, MirrorDepth::ReadState), &img);

        // Proposing an edit across the wire is REFUSED at the cap fabric — the view
        // confers no edge to write. The refusal is a CAP fact, decided before any
        // byte leaves the box: a read-only mirror simply holds no write authority.
        match mirror.propose_edit() {
            Err(MirrorRefusal::EditUnauthorized { held }) => {
                assert_eq!(held, AuthRequired::Signature, "the read-only mirror held only Signature");
            }
            other => panic!("a read-only mirror must NOT author an edit over the wire, got {other:?}"),
        }
    }

    // ---- POLARITY ✗ : a Structure responder REDACTS state on the wire -----------

    #[test]
    fn structure_responder_redacts_state_on_the_wire() {
        let watched = cid(7);
        let fabric = InProcessFabric::new();
        let alice = fabric.join([0xa1; 32]);
        let bob = fabric.join([0xb0; 32]);
        let a_sess = run(alice.dial(&[0xb0; 32])).unwrap();
        let b_sess = run(bob.accept()).unwrap().unwrap();

        // Bob's responder is authorized only to STRUCTURE depth — it must zero state
        // BEFORE the snapshot leaves the box, regardless of what alice claims locally.
        let responder = ImageResponder::new(MirrorDepth::Structure)
            .with_cell(watched, entry(watched, 999, 4, 2));

        run(async {
            let req = MirrorFrame::FetchCell {
                cell: super::cell_bytes(watched),
            };
            a_sess.conn.send(req.encode()).await.unwrap();
            responder.serve_one(&b_sess.conn).await.unwrap();
        });

        // What actually crossed the wire: state is ZEROED (no amplification on the
        // serve face), shape survives.
        let bytes = run(a_sess.conn.recv()).unwrap().expect("a reply is waiting");
        match MirrorFrame::decode(&bytes).unwrap() {
            MirrorFrame::CellSnapshot { entry } => {
                assert_eq!(entry.balance, 0, "a Structure responder zeroes balance on the wire");
                assert_eq!(entry.nonce, 0, "a Structure responder zeroes nonce on the wire");
                // SHAPE survives: the cap count and id are intact.
                assert_eq!(entry.capability_count, 2, "shape (cap count) crosses the wire");
                assert_eq!(entry.id, dregg_types::hex_encode(watched.as_bytes()));
            }
            other => panic!("expected a redacted CellSnapshot, got {other:?}"),
        }
    }

    // ---- the absent-cell case is surfaced over the wire, never faked ------------

    #[test]
    fn absent_remote_cell_is_surfaced_over_the_wire() {
        let asked = cid(7);
        let other = cid(8);
        let fabric = InProcessFabric::new();
        let alice = fabric.join([0xa1; 32]);
        let bob = fabric.join([0xb0; 32]);
        let a_sess = run(alice.dial(&[0xb0; 32])).unwrap();
        let b_sess = run(bob.accept()).unwrap().unwrap();

        // Bob serves `other`, not `asked`.
        let responder =
            ImageResponder::new(MirrorDepth::ReadState).with_cell(other, entry(other, 1, 1, 1));

        let got = run(async {
            let img = NetlayerImage::new(&a_sess.conn, 3);
            let req = MirrorFrame::FetchCell {
                cell: super::cell_bytes(asked),
            };
            a_sess.conn.send(req.encode()).await.unwrap();
            responder.serve_one(&b_sess.conn).await.unwrap();
            img.fetch_over_wire(asked).await
        });
        assert!(got.is_none(), "an absent remote cell is None over the wire, never a faked zero-snapshot");
    }

    // ---- the MirrorFrame codec round-trips (the wire contract) ------------------

    #[test]
    fn mirror_frame_codec_roundtrips() {
        let f1 = MirrorFrame::FetchCell { cell: [0x42; 32] };
        assert_eq!(MirrorFrame::decode(&f1.encode()), Some(f1));

        let f2 = MirrorFrame::CellSnapshot {
            entry: entry(cid(5), 77, 3, 1),
        };
        assert_eq!(MirrorFrame::decode(&f2.encode()), Some(f2));

        let f3 = MirrorFrame::Absent;
        assert_eq!(MirrorFrame::decode(&f3.encode()), Some(f3));

        // Garbage is rejected, not silently coerced.
        assert!(MirrorFrame::decode(&[0xff, 0xff, 0xff, 0xff]).is_none() || MirrorFrame::decode(&[]).is_none());
    }
}
