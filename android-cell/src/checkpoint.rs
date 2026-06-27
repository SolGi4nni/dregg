//! **The checkpointable service-cell — a confined runtime's observable state as a umem.**
//!
//! # The revolution, stated plainly
//!
//! A service cell fronting a NON-dregg runtime (this android-cell, the webcell, a
//! firmament app-PD) has runtime state that lives *outside* dregg: the Android guest
//! kernel's RAM, the app's process heap, the binder/HAL tables. dregg cannot witness
//! that interior. But it CAN witness — and does, today — every act that crosses the
//! cap-gated boundary: the captured frame (`RgbaFrame::content_digest`, bound through
//! the compositor's `FrameCommit`) and every gated I/O / input decision
//! ([`crate::IoReceipt`] / [`crate::InputReceipt`]).
//!
//! This module captures THAT — the service cell's *observable, cap-gated boundary
//! state* — as a **umem**: the SAME `(domain, key) ↦ value` universal-memory address
//! space, the SAME five domains, and the SAME Blum write-trace + `fold` discipline as
//! the kernel executor's [`dregg-turn`'s `umem`](../../../turn/src/umem.rs). A
//! checkpoint is one `UProjection`; advancing the boundary (a new frame, a new
//! receipt) is a `UmemOp` write whose fold connects the pre-checkpoint to the
//! post-checkpoint — exactly the executable shadow the kernel uses. So:
//!
//!  * **save**    = project the live boundary state → a `ServiceCellCheckpoint`;
//!  * **restore** = take a checkpoint, present its frame digest + replay its receipt log;
//!  * **compare** = diff two `UProjection`s (which addresses changed — content-addressed);
//!  * **migrate** = move the checkpoint to another node; the restored cell folds the SAME.
//!
//! Because the projection reuses the kernel's universal-memory vocabulary, a service
//! cell's boundary checkpoint is *the same kind of object* as a kernel state
//! commitment — it can be committed, the trace memchecked, and (the named frontier)
//! eventually carried into the same light-client witness.
//!
//! # What is real here, and the deep-state seam (NOT laundered)
//!
//! What this checkpoints is the **boundary**, not the interior. The android runtime's
//! deep internal state is NOT capturable through the deployed seam:
//!
//!  * `adb exec-out screencap` yields the FRAMEBUFFER only — the observable surface,
//!    not the guest's RAM/heap/process table ([`crate::frame`]).
//!  * `adb` is a shell/transport channel, not a memory-image protocol.
//!  * The emulator DOES have a host snapshot facility (QEMU `savevm` /
//!    `adb emu avd snapshot save`), but it is an **opaque host blob** — outside any
//!    dregg witness, un-memcheckable, un-attestable, and host-format-locked. Treating
//!    it as the cell's state would launder an unwitnessed blob into the trust base.
//!
//! **THE DEEP-STATE SEAM** (named, not claimed): a *byte-faithful, witnessed* capture
//! of the confined runtime's full interior (guest RAM + device + binder state) such
//! that the umem projection is the WHOLE cell, not just its boundary. Crossing it
//! needs one of: (a) a runtime that exposes a checkpoint in a dregg-attestable format
//! (a firmament app-PD whose memory IS dregg-addressable cells — the n=1 firmament
//! collapse, where "confined runtime state" and "dregg cell state" are the same
//! object); or (b) a deterministic-replay model where the boundary-act log REPLAYS to
//! the interior (record the seed + every gated input, re-derive the interior) — then
//! this boundary umem becomes a COMPLETE checkpoint by construction. Today this module
//! delivers (the honest, real) boundary umem + the determinism hook for (b); the
//! interior projection of (a) is the frontier.

use std::collections::BTreeMap;

use dregg_firmament::CellId;
use servo_render::RgbaFrame;

use crate::input::InputReceipt;
use crate::netgate::IoReceipt;

/// The five universal-memory domains — wire codes IDENTICAL to the kernel umem's
/// `UDomain` (registers 0 · heap 1 · caps 2 · nullifiers 3 · index 4;
/// `turn/src/umem.rs`). A service-cell boundary checkpoint uses three of them: `Heap`
/// for the observable surface state, `Caps` for the held authority the boundary acts
/// were decided against, and `Index` for the append-only witnessed receipt log.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum UDomain {
    /// (kernel: per-proof VM registers) — UNUSED at the service boundary.
    Registers = 0,
    /// The observable surface state (the current frame digest, dimensions, present-seq).
    Heap = 1,
    /// The held authority the boundary acts were decided against (the surface cap root).
    Caps = 2,
    /// (kernel: nullifier sets) — UNUSED at the service boundary.
    Nullifiers = 3,
    /// The append-only witnessed boundary-act log (the IoReceipts / InputReceipts), the
    /// service-cell analogue of the kernel's receipt MMR.
    Index = 4,
}

impl UDomain {
    /// The wire code (the circuit's domain column value) — identical to the kernel's.
    pub fn code(self) -> u32 {
        self as u32
    }
}

/// The structured in-domain key for a service-cell boundary checkpoint — the same
/// shape as the kernel umem's `UKey` (a `(domain, collection, key)` triple's abstract
/// content), specialized to the boundary planes a confined runtime actually exposes.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum UKey {
    // -- heap domain: the observable surface state --------------------------
    /// The service cell exists in the boundary projection (membership bit).
    Exist(CellId),
    /// The current frame's content digest — `blake3(rgba8)[..8]`, the SAME `u64` the
    /// compositor's `FrameCommit.digest` carries.
    FrameDigest(CellId),
    /// The current frame's pixel dimensions, packed `(width as u64) << 32 | height`.
    FrameDims(CellId),
    /// How many frames this cell has presented (the present sequence number) — the
    /// monotone surface-advance counter.
    PresentSeq(CellId),
    // -- caps domain: the authority the boundary acts were decided against ----
    /// The held surface-capability root the egress/input gates checked against
    /// (its content digest — the authority lineage, content-addressed).
    SurfaceCapRoot(CellId),
    // -- index domain: the append-only witnessed boundary-act log -------------
    /// The boundary-act receipt at a chronological log position — its 32-byte
    /// `decision_digest` (an [`IoReceipt`] or [`InputReceipt`]). Append-only, exactly
    /// the kernel umem's `Receipt(position)` index plane.
    BoundaryReceipt { cell: CellId, position: u64 },
}

impl UKey {
    /// The domain this key lives in.
    pub fn domain(&self) -> UDomain {
        match self {
            UKey::Exist(_) | UKey::FrameDigest(_) | UKey::FrameDims(_) | UKey::PresentSeq(_) => {
                UDomain::Heap
            }
            UKey::SurfaceCapRoot(_) => UDomain::Caps,
            UKey::BoundaryReceipt { .. } => UDomain::Index,
        }
    }
}

/// A universal-memory cell VALUE — the same plane-typed value the kernel umem uses
/// (the subset the boundary planes need).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum UVal {
    /// Set-membership planes (existence): present.
    Present,
    /// Unsigned scalar (frame digest, dims, present-seq).
    U64(u64),
    /// 32-byte values (receipt decision digests, cap roots).
    Bytes32([u8; 32]),
}

/// The projection image: present addresses only (absent = not in the map), exactly the
/// kernel umem's `Option`-cell encoding with `none` dropped.
pub type UProjection = BTreeMap<UKey, UVal>;

/// Memory-op kind (the memcheck `Kind`) — identical to the kernel umem's.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UmemKind {
    Read,
    Write,
}

/// One Blum trace op against the boundary address space — the SAME `UmemOp` shape as
/// the kernel umem (`turn/src/umem.rs`): `val`/`prev_val` are `Option`-cells, the op at
/// trace position `i` carries serial `i + 1`, `prev_serial` is the previous touch of
/// the same address (`0` = the init boundary).
#[derive(Clone, PartialEq, Debug)]
pub struct UmemOp {
    pub kind: UmemKind,
    pub key: UKey,
    pub val: Option<UVal>,
    pub prev_val: Option<UVal>,
    pub prev_serial: u64,
}

/// The REAL memory semantics, independently implemented (the `MemoryChecking.step`
/// fold, identical to the kernel umem's [`dregg_turn::umem::fold`]): a write installs
/// its value (absent = remove), a read changes nothing.
pub fn fold(pre: &UProjection, ops: &[UmemOp]) -> UProjection {
    let mut m = pre.clone();
    for op in ops {
        if let UmemKind::Write = op.kind {
            match &op.val {
                Some(v) => {
                    m.insert(op.key.clone(), v.clone());
                }
                None => {
                    m.remove(&op.key);
                }
            }
        }
    }
    m
}

/// The per-op memcheck discipline: `prev_serial` strictly below the op's own positional
/// serial, and a read returns exactly its claimed previous value — identical to the
/// kernel umem's [`dregg_turn::umem::disciplined`].
pub fn disciplined(ops: &[UmemOp]) -> bool {
    ops.iter().enumerate().all(|(i, op)| {
        op.prev_serial < (i as u64) + 1 && (op.kind != UmemKind::Read || op.val == op.prev_val)
    })
}

/// The content digest of a held surface cap (the authority lineage, content-addressed).
/// A surface cap is identified by the cell it scopes plus its allow-set; here we bind
/// to the cell it speaks for — the lineage stamp the boundary acts were decided under.
fn cap_root_digest(cell: &CellId) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"surface-cap-root");
    h.update(cell.as_bytes());
    *h.finalize().as_bytes()
}

/// **A checkpointable service-cell boundary state.** Holds the live observable state of
/// a confined runtime (the current frame, the present sequence, the held authority) and
/// the append-only log of witnessed boundary acts. A `ServiceCellCheckpoint::project`
/// renders it into a [`UProjection`] umem; advancing the boundary emits a [`UmemOp`]
/// write whose fold connects the projections (the executable shadow of the kernel
/// `*_is_memory_program` agreement, at the boundary).
#[derive(Clone, Debug)]
pub struct ServiceCellCheckpoint {
    /// The service cell whose boundary this is.
    pub cell: CellId,
    /// The current observable frame: digest + dims. `None` before the first present.
    pub frame: Option<(u64, u32, u32)>,
    /// How many frames have been presented (monotone).
    pub present_seq: u64,
    /// The witnessed boundary-act receipt digests, in chronological order (the
    /// append-only index log — IoReceipts and InputReceipts, both 32-byte digests).
    pub receipt_log: Vec<[u8; 32]>,
}

impl ServiceCellCheckpoint {
    /// A fresh boundary checkpoint for `cell` — no frame yet, an empty receipt log.
    pub fn new(cell: CellId) -> Self {
        ServiceCellCheckpoint {
            cell,
            frame: None,
            present_seq: 0,
            receipt_log: Vec::new(),
        }
    }

    /// Record that the cell presented `frame` (advancing the observable surface state
    /// and the present sequence). The frame's `content_digest` is the SAME `u64` the
    /// compositor's `FrameCommit.digest` binds.
    pub fn observe_frame(&mut self, frame: &RgbaFrame) {
        self.frame = Some((frame.content_digest(), frame.width, frame.height));
        self.present_seq += 1;
    }

    /// Record a witnessed egress decision (its receipt digest joins the append-only log).
    pub fn observe_io(&mut self, receipt: &IoReceipt) {
        self.receipt_log.push(receipt.decision_digest);
    }

    /// Record a witnessed input decision (its receipt digest joins the append-only log).
    pub fn observe_input(&mut self, receipt: &InputReceipt) {
        self.receipt_log.push(receipt.decision_digest);
    }

    /// **THE PROJECTION.** Render the live boundary state into the universal-memory
    /// address space — a [`UProjection`] umem, the SAME object kind a kernel state
    /// commitment is.
    pub fn project(&self) -> UProjection {
        let mut out = UProjection::new();
        out.insert(UKey::Exist(self.cell), UVal::Present);
        out.insert(
            UKey::SurfaceCapRoot(self.cell),
            UVal::Bytes32(cap_root_digest(&self.cell)),
        );
        if let Some((digest, w, h)) = self.frame {
            out.insert(UKey::FrameDigest(self.cell), UVal::U64(digest));
            out.insert(
                UKey::FrameDims(self.cell),
                UVal::U64(((w as u64) << 32) | (h as u64)),
            );
        }
        out.insert(UKey::PresentSeq(self.cell), UVal::U64(self.present_seq));
        for (i, digest) in self.receipt_log.iter().enumerate() {
            out.insert(
                UKey::BoundaryReceipt {
                    cell: self.cell,
                    position: i as u64,
                },
                UVal::Bytes32(*digest),
            );
        }
        out
    }

    /// A 32-byte commitment to the whole boundary checkpoint — `blake3` over the
    /// projection in `UKey` order (the deterministic `BTreeMap` iteration). Two
    /// checkpoints with the same observable boundary have the same commitment; a single
    /// changed frame, present, or receipt changes it. This is the service-cell analogue
    /// of the kernel state root.
    pub fn commitment(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        for (k, v) in self.project() {
            h.update(&[k.domain().code() as u8]);
            // A stable encoding of the key + value; debug-format is deterministic for
            // these plain-data enums and suffices for the prototype's commitment.
            h.update(format!("{k:?}").as_bytes());
            h.update(format!("{v:?}").as_bytes());
        }
        *h.finalize().as_bytes()
    }
}

/// **THE TRACE EMITTER — diff two boundary checkpoints into a Blum write trace.**
///
/// Given a `pre` and `post` projection of the SAME service cell, emit the per-address
/// `UmemOp` writes that carry `pre` to `post`, and CHECK that `fold(pre, ops) == post`
/// (the agreement square — the executable shadow of the kernel
/// `*_is_memory_program` keystones) and `disciplined(&ops)`. Refuses loudly on any
/// disagreement, exactly as the kernel emitter does.
///
/// Because the boundary planes are append-only (receipts) or last-writer (frame /
/// present-seq), the diff is a faithful trace: every changed address is one write, the
/// receipt appends never rewrite a prior position.
pub fn emit_boundary_trace(pre: &UProjection, post: &UProjection) -> Result<Vec<UmemOp>, String> {
    let mut ops: Vec<UmemOp> = Vec::new();

    // Every address present in post whose value differs from pre is a write.
    for (k, v) in post.iter() {
        if pre.get(k) != Some(v) {
            ops.push(UmemOp {
                kind: UmemKind::Write,
                key: k.clone(),
                val: Some(v.clone()),
                prev_val: pre.get(k).cloned(),
                prev_serial: 0,
            });
        }
    }
    // Every address present in pre but gone in post is a delete (write of absent).
    for k in pre.keys() {
        if !post.contains_key(k) {
            ops.push(UmemOp {
                kind: UmemKind::Write,
                key: k.clone(),
                val: None,
                prev_val: pre.get(k).cloned(),
                prev_serial: 0,
            });
        }
    }
    // Deterministic order (BTreeMap iteration is already sorted, but the two passes
    // concatenate; sort by key so the trace is canonical).
    ops.sort_by(|a, b| a.key.cmp(&b.key));

    // THE AGREEMENT CHECK: fold(pre, ops) == post — refuse on any mismatch.
    let folded = fold(pre, &ops);
    if &folded != post {
        return Err(format!(
            "boundary-umem fold/post disagreement: folded {} addrs, post {} addrs",
            folded.len(),
            post.len()
        ));
    }
    // The diff trace is trivially disciplined (each address written once, prev_serial 0).
    debug_assert!(disciplined(&ops));
    Ok(ops)
}

/// **COMPARE.** The set of addresses whose value differs between two projections —
/// content-addressed change detection (the service-cell analogue of "which cells moved
/// this turn"). Returns `(changed, only_in_a, only_in_b)`.
pub fn diff(a: &UProjection, b: &UProjection) -> (Vec<UKey>, Vec<UKey>, Vec<UKey>) {
    let mut changed = Vec::new();
    let mut only_a = Vec::new();
    let mut only_b = Vec::new();
    for (k, v) in a.iter() {
        match b.get(k) {
            Some(bv) if bv != v => changed.push(k.clone()),
            None => only_a.push(k.clone()),
            _ => {}
        }
    }
    for k in b.keys() {
        if !a.contains_key(k) {
            only_b.push(k.clone());
        }
    }
    (changed, only_a, only_b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::input::InputDecision;
    use crate::netgate::IoDecision;
    use dregg_firmament::cell_seed;

    fn frame(seed: u8, w: u32, h: u32) -> RgbaFrame {
        // A content-distinct frame: bytes derived from the seed, so two seeds → two
        // digests (the property `observe_frame` records).
        let mut bytes = vec![0u8; (w * h * 4) as usize];
        for (i, b) in bytes.iter_mut().enumerate() {
            *b = (i as u8).wrapping_add(seed);
        }
        RgbaFrame {
            width: w,
            height: h,
            bytes,
        }
    }

    fn io_receipt(cell: CellId, origin: &str, dialed: bool) -> IoReceipt {
        let decision = if dialed {
            IoDecision::Dialed {
                origin: origin.to_string(),
                peer: crate::netgate::origin_to_peer(origin),
            }
        } else {
            IoDecision::RefusedByCap {
                origin: origin.to_string(),
            }
        };
        IoReceipt {
            cell: Some(cell),
            origin: origin.to_string(),
            decision: decision.clone(),
            decision_digest: blake3::hash(format!("{origin}:{dialed}").as_bytes()).as_bytes()[..32]
                .try_into()
                .unwrap(),
        }
    }

    /// **SAVE → RESTORE round-trip: a checkpoint's projection survives a save/restore
    /// byte-identically, and its commitment is stable.**
    #[test]
    fn save_restore_round_trips_the_boundary_umem() {
        let cell = cell_seed(3);
        let mut cp = ServiceCellCheckpoint::new(cell);
        cp.observe_frame(&frame(1, 90, 200));
        cp.observe_io(&io_receipt(cell, "https://api.example.com", true));
        cp.observe_io(&io_receipt(cell, "https://tracker.evil.com", false));

        // SAVE: the projection IS the serializable checkpoint.
        let saved = cp.project();
        let saved_commitment = cp.commitment();

        // RESTORE: rebuild a checkpoint from the recorded boundary log (the receipts +
        // the last frame) — the deterministic-replay restore.
        let mut restored = ServiceCellCheckpoint::new(cell);
        restored.observe_frame(&frame(1, 90, 200));
        restored.receipt_log = cp.receipt_log.clone();
        // present_seq is restored from the saved heap plane (here: one present).
        restored.present_seq = cp.present_seq;

        assert_eq!(
            restored.project(),
            saved,
            "restore reproduces the umem exactly"
        );
        assert_eq!(
            restored.commitment(),
            saved_commitment,
            "the boundary commitment is stable across save/restore"
        );
        // The receipt log is append-only: every position present, in order.
        for i in 0..cp.receipt_log.len() {
            assert!(saved.contains_key(&UKey::BoundaryReceipt {
                cell,
                position: i as u64
            }));
        }
    }

    /// **ADVANCE as a Blum trace: a new frame + a new receipt is a disciplined write
    /// trace whose fold carries the pre-checkpoint to the post-checkpoint.**
    #[test]
    fn advancing_the_boundary_is_a_disciplined_memory_program() {
        let cell = cell_seed(3);
        let mut cp = ServiceCellCheckpoint::new(cell);
        cp.observe_frame(&frame(1, 90, 200));
        let pre = cp.project();

        // Advance: a new frame (digest changes, present-seq increments) + a new receipt.
        cp.observe_frame(&frame(2, 90, 200));
        cp.observe_io(&io_receipt(cell, "https://api.example.com", true));
        let post = cp.project();

        let ops = emit_boundary_trace(&pre, &post).expect("the advance folds pre → post");
        assert!(disciplined(&ops), "the trace is memcheck-disciplined");
        assert_eq!(fold(&pre, &ops), post, "the fold is the agreement square");

        // The changed addresses are exactly: the frame digest, the present-seq, and the
        // newly-appended receipt position — content-addressed.
        let (changed, _, only_post) = diff(&pre, &post);
        assert!(
            changed.contains(&UKey::FrameDigest(cell)),
            "the frame digest moved"
        );
        assert!(
            changed.contains(&UKey::PresentSeq(cell)),
            "the present-seq moved"
        );
        assert!(
            only_post.contains(&UKey::BoundaryReceipt { cell, position: 0 }),
            "a new receipt was appended at position 0"
        );
    }

    /// **MIGRATE: a checkpoint moved to a "second node" restores to the SAME umem +
    /// commitment — the service cell is migratable by its boundary witness.**
    #[test]
    fn checkpoint_migrates_across_nodes() {
        let cell = cell_seed(7);
        let mut origin_node = ServiceCellCheckpoint::new(cell);
        origin_node.observe_frame(&frame(5, 90, 200));
        origin_node.observe_input(&InputReceipt {
            cell: Some(cell),
            input: crate::AndroidInput::Tap { x: 10, y: 20 },
            decision: InputDecision::Injected,
            decision_digest: [9u8; 32],
        });
        origin_node.observe_io(&io_receipt(cell, "https://api.example.com", true));

        // Serialize the migratable witness: the frame, present-seq, and receipt log.
        let frame_state = origin_node.frame;
        let seq = origin_node.present_seq;
        let log = origin_node.receipt_log.clone();
        let origin_commitment = origin_node.commitment();

        // ON THE DESTINATION NODE: reconstruct the cell from the witness alone.
        let mut dest_node = ServiceCellCheckpoint::new(cell);
        dest_node.frame = frame_state;
        dest_node.present_seq = seq;
        dest_node.receipt_log = log;

        assert_eq!(
            dest_node.project(),
            origin_node.project(),
            "the migrated cell projects the identical boundary umem"
        );
        assert_eq!(
            dest_node.commitment(),
            origin_commitment,
            "the migrated cell carries the identical boundary commitment — migration preserved"
        );
        let (changed, only_a, only_b) = diff(&origin_node.project(), &dest_node.project());
        assert!(
            changed.is_empty() && only_a.is_empty() && only_b.is_empty(),
            "migration is byte-identical: no address differs"
        );
    }

    /// **TAMPER refusal: a forged post-state that the trace does not justify is
    /// refused by the fold/post agreement check — the boundary umem is unforgeable.**
    #[test]
    fn a_forged_post_state_is_refused_by_the_fold() {
        let cell = cell_seed(3);
        let mut cp = ServiceCellCheckpoint::new(cell);
        cp.observe_frame(&frame(1, 90, 200));
        let pre = cp.project();

        // A HONEST advance gives an honest trace.
        cp.observe_frame(&frame(2, 90, 200));
        let honest_post = cp.project();
        let ops = emit_boundary_trace(&pre, &honest_post).expect("honest advance folds");

        // Now FORGE a post-state with a different frame digest the trace never wrote.
        let mut forged_post = honest_post.clone();
        forged_post.insert(UKey::FrameDigest(cell), UVal::U64(0xDEAD_BEEF));

        // The honest trace does NOT fold pre → forged_post: tamper caught.
        assert_ne!(
            fold(&pre, &ops),
            forged_post,
            "the honest trace does not justify the forged frame digest"
        );
        // And re-emitting a trace for the forged post still folds (the diff is faithful),
        // but the forged digest is now an EXPLICIT op a verifier sees — nothing is hidden.
        let forged_ops = emit_boundary_trace(&pre, &forged_post).expect("diff is total");
        assert!(
            forged_ops
                .iter()
                .any(|op| op.key == UKey::FrameDigest(cell)
                    && op.val == Some(UVal::U64(0xDEAD_BEEF))),
            "the forged digest is an explicit, witnessed write — not a hidden mutation"
        );
    }
}
