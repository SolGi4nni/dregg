//! LIVE-REPAINT-ON-TURN — the executor-PD → compositor-PD repaint loop, on the
//! semihost [`EmulatedKernel`] (`docs/desktop-os-research/SEL4-INTERACTIVE-
//! COCKPIT.md §3`).
//!
//! ## What this is (the seam this closes)
//!
//! The executor-PD ([`crate::executor_pd`]) runs a real verified turn and writes
//! a receipt to `commit_out`. The compositor-PD ([`crate::compositor_pd`])
//! composites a surface's `content_digest` into the framebuffer it SOLELY holds,
//! gated by the verified scene authority. Before this module the two halves were
//! both green but **disconnected**: a committed turn did not cause the focused
//! cell to re-paint. `SEL4-INTERACTIVE-COCKPIT.md §3` names exactly that gap.
//!
//! This module wires the loop across the PD boundary:
//!
//! ```text
//!   ┌────────────────┐  turn_in (DMA)   ┌──────────────────┐
//!   │  compositor-PD │ ───────────────▶ │   executor-PD    │
//!   │  (framebuffer, │                  │  (verified turn) │
//!   │   scene auth)  │ ◀─────────────── │                  │
//!   └────────────────┘  repaint_out +   └──────────────────┘
//!         ▲  CH_REPAINT (notify)         the dirty-region signal
//!         └── on the dirty notify: present() the changed region
//! ```
//!
//! 1. **Trigger + execute** — a turn is staged + run through the executor-PD
//!    ([`crate::executor_pd::ExecutorPd::step_staged_turn`]). On COMMIT the
//!    executor PROJECTS a [`DirtyRegion`] (which surface changed, its new
//!    source-state-root + content-digest) into a shared `repaint_out` region and
//!    `notify`s the compositor over a [`crate::microkit_facade::Channel`]. On a
//!    REJECTED turn it projects NOTHING and notifies NOTHING (fail-closed — a
//!    refused turn re-paints nothing).
//! 2. **Repaint** — the compositor-PD's `notified` arm reads the [`DirtyRegion`]
//!    out of `repaint_out`, builds the corresponding
//!    [`crate::compositor_pd::Present`], and runs the scene gate + composite
//!    ([`crate::compositor_pd::CompositorPd::present`]). The framebuffer the
//!    compositor SOLELY holds advances at exactly the dirty region — the focused
//!    cell re-paints the instant the turn lands.
//!
//! This is the SAME idea as the deos `deos-js/src/signals.rs` dirty-set →
//! repaint-hook model (a committed turn folds its events into a dirty set that
//! drives the repaint), lifted across the seL4 PD boundary: the "dirty-set" is a
//! [`DirtyRegion`] in a shared region, and the "repaint hook" is the compositor's
//! `present()` fired by an IPC notify. The dirty-set lives in `repaint_out`; the
//! signal is the genuine [`crate::microkit_facade::Channel::notify`] the 2-PD
//! notify slice (`tests/boot_pds.rs`) proves.
//!
//! ## Reuse, not reinvention (the WELD method)
//!
//! Every primitive here already exists and is proven:
//! - the executor's `turn_in → step → commit_out` ([`crate::executor_pd`]),
//! - the compositor's scene-gated `present()` ([`crate::compositor_pd`]),
//! - the cross-PD `notify` / shared-region `Channel` (`tests/boot_pds.rs`,
//!   `microkit_facade.rs`).
//!
//! This module adds ONLY the PROJECTION (a committed turn ⟼ a [`DirtyRegion`])
//! and the wire that carries it (`encode_dirty`/`decode_dirty` + the
//! `repaint_out` region + the notify edge) — the missing glue, NOT a new
//! primitive. The projection is deliberately the SAME shape the compositor's
//! `Present` already keys off (`source_state_root` + `content_digest`), so the
//! compositor's draw path is UNCHANGED.
//!
//! ## Fidelity (honestly labeled — NOT laundered)
//!
//! [`REPAINT_FIDELITY`] states it plainly. The loop is REAL on the semihost: a
//! genuine committed turn through the executor's [`crate::executor_pd::TurnRunner`]
//! projects a dirty region that the compositor's GENUINE scene gate admits,
//! advancing the framebuffer the compositor SOLELY holds — a turn DOES re-paint
//! the glass, provably (two framebuffer snapshots differ at exactly the dirty
//! region; a rejected turn leaves it byte-identical). What is NOT verified here
//! is the same graphics frontier the compositor names (F1/F2/F3 in
//! [`crate::compositor_pd::CompositorPd::FIDELITY`]): the framebuffer is a host
//! buffer, not a scanned-out panel; binding scanned-out pixels to the digest is
//! the named hardware-trust frontier, NOT solved here. The AUTHORITY path — a
//! turn's commit drives a scene-gated present — is what this module makes real.

use std::vec::Vec;

use dregg_types::CellId;

use crate::compositor_pd::{label_of, Present, RegionId};
use crate::executor_pd::ServedTurn;

/// The honest fidelity statement for the repaint loop — it travels WITH the code
/// (the don't-launder-vacuity discipline). The executor→compositor repaint is
/// REAL on the semihost (a genuine committed turn drives a genuine scene-gated
/// present that advances the framebuffer); the PIXELS' last hop to a scanned-out
/// panel is the graphics frontier the compositor already names, NOT solved here.
pub const REPAINT_FIDELITY: &str = "\
    LIVE-REPAINT-ON-TURN is REAL on the semihost: a genuine committed turn \
    through the executor-PD's TurnRunner projects a DirtyRegion that the \
    compositor-PD's GENUINE scene authority (T1/T2/T3) admits, advancing the \
    framebuffer the compositor SOLELY holds — a turn re-paints the glass, \
    provably (the framebuffer differs at exactly the dirty region; a REJECTED \
    turn leaves it byte-identical, fail-closed). What is NOT solved here is the \
    same graphics frontier the compositor names (F1/F2/F3): the framebuffer is a \
    HOST buffer, not a scanned-out panel. The AUTHORITY path (a turn's commit \
    drives a scene-gated present) is what this loop makes real; the same PD \
    source runs on real seL4 once the Microkit assembly wires the two PDs + the \
    repaint_out region + the notify edge (deos-live.system), with no new \
    primitive.";

/// **THE DIRTY-REGION SIGNAL** — what a committed turn projects toward the
/// compositor: which surface changed, and the new state it now projects. This is
/// the PD-boundary form of the deos `signals.rs` dirty-set entry (a touched slot
/// → the bindings that must re-render); here a touched cell → the surface that
/// must re-present.
///
/// The executor-PD writes this into `repaint_out` and notifies the compositor;
/// the compositor reads it and turns it into a [`Present`] (the repaint). It is
/// deliberately the SAME shape the compositor's `Present` keys off
/// (`source_state_root` + a `content_digest`), so the compositor's draw path is
/// unchanged — only its TRIGGER moves from "static bake" to "this signal".
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DirtyRegion {
    /// The surface that changed — the cell whose turn committed. The compositor
    /// looks this owner up in its scene to find the surface's owned region-set
    /// (T1) and current frame digest.
    pub owner: CellId,
    /// The NEW cell state-root the turn advanced to (the light-client-checkable
    /// bind — the compositor's T2 label binds to it, and a light client can
    /// verify the presented content against it). Projected from the turn's
    /// receipt.
    pub new_source_state_root: u64,
    /// The NEW content digest the surface now shows (the projection of
    /// `new_source_state_root`). The compositor composites this into the dirty
    /// region; it must differ from the surface's current digest for the present
    /// to advance the frame (the compositor's `NoFrameAdvance` leg).
    pub new_content_digest: u64,
}

impl DirtyRegion {
    /// Build the [`Present`] this dirty region asks the compositor to commit, for
    /// a surface owning `target` regions. The declared label is the GENUINE
    /// owner-binding ([`label_of`]) — the projection declares the honest binding
    /// the compositor's T2 gate then checks; it does NOT claim focus (a repaint
    /// driven by a turn is a content advance, not a focus assertion — focus is an
    /// input concern, §2). The compositor still gates this present against its
    /// scene (a repaint of a region the surface does not own is REFUSED, exactly
    /// like any other present — the turn cannot paint outside its cell's glass).
    pub fn to_present(&self, target: Vec<RegionId>) -> Present {
        Present {
            target,
            source_state_root: self.new_source_state_root,
            declared_label: label_of(&self.owner, self.new_source_state_root),
            claims_focus: false,
            new_digest: self.new_content_digest,
        }
    }
}

/// **PROJECT a committed turn into a [`DirtyRegion`]** — the executor's projection
/// of "this turn changed cell `owner`'s state" into "the compositor must re-paint
/// `owner`'s surface with this new digest." Returns `None` for a REJECTED turn
/// (a refused turn re-paints NOTHING — fail-closed, the same sense as the
/// executor writing no receipt and the compositor logging no frame).
///
/// The new state-root + content-digest are derived from the committed receipt
/// bytes (`receipt_digest`): on a real PD the receipt carries the turn's
/// `newStateRoot` (the verified post-state commitment), and the content digest is
/// the renderer's projection of it; here we fold the receipt bytes into both,
/// which is faithful to the binding discipline (a DIFFERENT post-state ⟹ a
/// DIFFERENT root ⟹ a DIFFERENT digest ⟹ a genuine frame advance) without
/// pulling in the heavy `TurnReceipt` codec. The fidelity is the BINDING (every
/// distinct committed state re-paints to a distinct frame), not this particular
/// fold — exactly as `compositor_pd::label_of` is renderer-agnostic.
pub fn project_dirty_from_turn(owner: &CellId, served: &ServedTurn) -> Option<DirtyRegion> {
    let receipt = served.receipt()?; // None ⟹ rejected ⟹ no dirty region.
    let root = receipt_digest(receipt);
    Some(DirtyRegion {
        owner: *owner,
        new_source_state_root: root,
        // The content digest is the renderer's projection of the new state-root;
        // mix the owner in so two cells reaching the same root still get distinct
        // frames (the renderer paints per-surface). Renderer-agnostic — the
        // BINDING (distinct committed state ⟹ distinct frame) is the fidelity.
        new_content_digest: root.wrapping_mul(1_000_003).wrapping_add(owner_scalar(owner)),
    })
}

/// Fold a committed receipt's bytes into a u64 state-root projection — the
/// stand-in for reading the receipt's `newStateRoot` field without the heavy
/// codec. A different receipt ⟹ a different root (the binding the compositor's
/// T2 + frame-advance legs rely on). FNV-1a over the bytes (deterministic,
/// dependency-free — the firmament's minimal-dep discipline).
fn receipt_digest(receipt: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in receipt {
        h ^= b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01B3);
    }
    // Guard against the degenerate empty-receipt root being 0 (a 0 digest means
    // "never composited" in the framebuffer; a committed turn must advance).
    if h == 0 {
        0x9E37_79B9_7F4A_7C15
    } else {
        h
    }
}

/// Fold an owner [`CellId`] into a u64 scalar (so per-surface content digests
/// differ even at the same root). The SAME splitmix-fold sense as
/// `compositor_pd::label_of`, narrowed to u64.
fn owner_scalar(owner: &CellId) -> u64 {
    let mut acc: u64 = 0;
    for chunk in owner.as_bytes().chunks(8) {
        let mut w = [0u8; 8];
        w[..chunk.len()].copy_from_slice(chunk);
        acc = acc
            .wrapping_mul(0x100_0000_01B3)
            .wrapping_add(u64::from_le_bytes(w));
    }
    acc
}

// ─────────────────────────── the repaint_out wire ───────────────────────────
//
// The executor-PD writes the projected DirtyRegion into the shared `repaint_out`
// region (the compositor's R view), then notifies the compositor over the repaint
// channel. The compositor reads it and presents. The framing is hand-rolled +
// dependency-free, the SAME discipline as `compositor_pd::encode_present` and the
// net-client's `[len][msg]` turn framing.

/// Encode a [`DirtyRegion`] into the `repaint_out` bytes. Layout:
/// owner(32) ‖ new_source_state_root(8) ‖ new_content_digest(8), little-endian.
pub fn encode_dirty(d: &DirtyRegion) -> Vec<u8> {
    let mut v = Vec::with_capacity(32 + 8 + 8);
    v.extend_from_slice(d.owner.as_bytes());
    v.extend_from_slice(&d.new_source_state_root.to_le_bytes());
    v.extend_from_slice(&d.new_content_digest.to_le_bytes());
    v
}

/// Decode a [`DirtyRegion`] from the `repaint_out` bytes (the inverse of
/// [`encode_dirty`]). Returns `None` on a malformed frame — which the compositor
/// treats as no repaint (fail-closed; a garbage dirty signal never advances the
/// frame).
pub fn decode_dirty(b: &[u8]) -> Option<DirtyRegion> {
    let owner = CellId::from_bytes(b.get(0..32)?.try_into().ok()?);
    let new_source_state_root = u64::from_le_bytes(b.get(32..40)?.try_into().ok()?);
    let new_content_digest = u64::from_le_bytes(b.get(40..48)?.try_into().ok()?);
    Some(DirtyRegion {
        owner,
        new_source_state_root,
        new_content_digest,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compositor_pd::cell_seed;
    use crate::executor_pd::ServedTurn;

    fn committed(receipt: Vec<u8>) -> ServedTurn {
        ServedTurn::Committed { receipt }
    }

    fn rejected() -> ServedTurn {
        ServedTurn::Rejected {
            reason: "non-attenuating".to_string(),
        }
    }

    #[test]
    fn a_committed_turn_projects_a_dirty_region_a_rejected_one_does_not() {
        let wallet = cell_seed(1);
        // A committed turn projects a dirty region for its owner.
        let d = project_dirty_from_turn(&wallet, &committed(vec![2, 1, 0xCC]))
            .expect("a committed turn projects a dirty region");
        assert_eq!(d.owner, wallet);
        // A rejected turn projects NOTHING (fail-closed — no repaint).
        assert!(
            project_dirty_from_turn(&wallet, &rejected()).is_none(),
            "a rejected turn projects no dirty region (re-paints nothing)"
        );
    }

    #[test]
    fn distinct_committed_states_re_paint_to_distinct_frames() {
        // The binding the compositor's frame-advance + T2 legs rely on: two
        // DIFFERENT committed receipts ⟹ two DIFFERENT content digests (a genuine
        // frame advance), and two DIFFERENT owners at the same root ⟹ distinct
        // per-surface frames.
        let wallet = cell_seed(1);
        let browser = cell_seed(2);
        let d1 = project_dirty_from_turn(&wallet, &committed(vec![2, 1, 0xCC])).unwrap();
        let d2 = project_dirty_from_turn(&wallet, &committed(vec![2, 0, 0xCC])).unwrap();
        assert_ne!(
            d1.new_content_digest, d2.new_content_digest,
            "distinct committed states re-paint to distinct frames"
        );
        let d3 = project_dirty_from_turn(&browser, &committed(vec![2, 1, 0xCC])).unwrap();
        assert_ne!(
            d1.new_content_digest, d3.new_content_digest,
            "two surfaces at the same root re-paint to distinct frames"
        );
    }

    #[test]
    fn the_dirty_present_declares_the_genuine_owner_label() {
        // The projection declares the GENUINE owner-binding (T2) — an honest
        // repaint, not a spoof; and it does NOT claim focus (a content advance,
        // not an input assertion).
        let wallet = cell_seed(1);
        let d = project_dirty_from_turn(&wallet, &committed(vec![2, 1, 0xCC])).unwrap();
        let p = d.to_present(vec![10, 11]);
        assert_eq!(p.target, vec![10, 11]);
        assert_eq!(p.declared_label, label_of(&wallet, d.new_source_state_root));
        assert!(!p.claims_focus, "a repaint is a content advance, not a focus claim");
        assert_eq!(p.new_digest, d.new_content_digest);
    }

    #[test]
    fn dirty_wire_round_trips() {
        let d = DirtyRegion {
            owner: cell_seed(7),
            new_source_state_root: 0xDEAD_BEEF_CAFE,
            new_content_digest: 0x0123_4567_89AB_CDEF,
        };
        let back = decode_dirty(&encode_dirty(&d)).expect("round-trips");
        assert_eq!(back, d);
    }

    #[test]
    fn malformed_dirty_frame_decodes_to_none() {
        assert!(
            decode_dirty(&[0u8; 10]).is_none(),
            "a short frame is a no-repaint (fail-closed)"
        );
    }

    #[test]
    fn an_empty_receipt_still_advances_the_frame() {
        // Degenerate guard: an empty committed receipt must not project a 0 digest
        // (0 = "never composited" in the framebuffer; a commit must advance).
        let wallet = cell_seed(1);
        let d = project_dirty_from_turn(&wallet, &committed(vec![])).unwrap();
        assert_ne!(d.new_content_digest, 0, "a committed turn always advances the frame");
    }
}
