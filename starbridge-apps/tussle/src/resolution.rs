//! The **deterministic frame resolution** — a pure function over the two revealed joint vectors and
//! the figures' positions, producing position deltas, the contact (if any), and the contact score
//! deltas as a balanced ring of legs for the verified joint turn.
//!
//! This is the "cell-program" of a frame: a SIMPLE, DETERMINISTIC joint-combat resolution (NOT
//! rigid-body physics). Joints apply directional influence; figures move along a 1-D strip; when
//! they make contact the figure landing the stronger drive scores, modulated by the opponent's
//! brace. Determinism + simplicity = on the path to verifiable: the same revealed moves always
//! produce the same outcome (the reproducibility tooth), and the score deltas it emits are folded
//! through the VERIFIED per-asset executor.
//!
//! ## The resolution, precisely
//!
//! For each figure, from its [`JointVector`](crate::JointVector):
//!   - **forward drive** `= Σ joint.drive()` — `Contract` is `+1` (toward the opponent), `Extend`
//!     is `-1` (away), `Relax`/`Hold` are `0`.
//!   - **brace** `= #joints that brace` — each `Hold` cancels one unit of the OPPONENT'S forward
//!     drive at contact (a defensive lock).
//!
//! The figures sit on a 1-D strip, `f0` at a smaller coordinate than `f1`. Each figure steps by its
//! forward drive toward the other (`f0` moves `+drive`, `f1` moves `-drive`), clamped so they cannot
//! pass through each other. **Contact** occurs this frame iff, after stepping, the gap between them
//! is `<= CONTACT_GAP`. On contact, each figure's **effective hit** is `max(0, forward_drive −
//! opponent.brace)`; the figure with the strictly greater effective hit lands the blow and is
//! awarded `points = winner_hit − loser_hit` (a clash where both push equally cancels — no score).
//!
//! The score award is a single balanced leg: `points` of [`SCORE_ASSET`](crate::SCORE_ASSET) move
//! from the neutral [`SCORE_BANK`] into the scoring figure's score column — a conserving transfer the
//! verified executor admits.

use crate::{FigureId, JointVector, MoveSeal, SCORE_ASSET, VerifiedLeg};

/// A neutral **score bank** cell — the source the verified executor moves points FROM when a figure
/// scores. Awarding points as a bank→figure transfer (rather than minting) keeps the joint turn
/// conserving: the bank's column falls exactly as the scorer's rises. A live account in the match
/// ledger, distinct from either figure id.
pub const SCORE_BANK: FigureId = 0xBA;

/// The gap (in strip units) at or below which the two figures are in **contact** this frame. With a
/// small starting separation and unit drives, a couple of forward frames brings them into contact.
pub const CONTACT_GAP: i64 = 1;

/// A detected **contact** between the two figures in a frame — who landed the blow and how hard.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Contact {
    /// The figure that landed the stronger drive (the scorer).
    pub striker: FigureId,
    /// The figure that took the blow.
    pub struck: FigureId,
    /// The points awarded — the margin `winner_hit − loser_hit` (always `>= 1` for a real contact;
    /// a perfectly cancelled clash produces NO `Contact` at all). `i128` to match the verified
    /// ledger's signed amount domain (the score-leg amount).
    pub points: i128,
}

/// The full deterministic outcome of resolving one frame: the figures' new positions, the contact
/// (if any), and the **score legs** — the balanced ring the verified executor folds for the joint
/// turn. With no contact (or a cancelled clash) the ring is empty (a conserving no-op fold).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrameResolution {
    /// The figures' new positions after this frame, in player order `(f0, f1)`.
    pub new_positions: (i64, i64),
    /// The contact this frame, if the figures clashed with a decisive margin.
    pub contact: Option<Contact>,
    /// The balanced score-delta ring — `0` or `1` legs (bank → scorer). Folded through the verified
    /// per-asset executor by [`crate::Frame::resolve`].
    pub score_legs: Vec<VerifiedLeg>,
}

/// The net **forward drive** of a joint vector — `Σ joint.drive()`. `+` is toward the opponent.
pub fn forward_drive(joints: &JointVector) -> i32 {
    joints.iter().map(|j| j.drive()).sum()
}

/// The **brace** of a joint vector — the number of joints that brace (each `Hold` cancels one unit
/// of the opponent's forward drive at contact).
pub fn brace(joints: &JointVector) -> i32 {
    joints.iter().filter(|j| j.braces()).count() as i32
}

/// **The deterministic frame resolution.** A pure function of the two figures' `(id, position,
/// joints)` — no clock, no randomness, no hidden state — so the same revealed moves always produce
/// the same [`FrameResolution`] (the reproducibility tooth). `a` is the player-0 figure (at the
/// smaller coordinate), `b` is player-1.
///
/// Steps each figure by its forward drive toward the other (clamped so they cannot cross), detects
/// contact within [`CONTACT_GAP`], and — on a decisive clash — emits a single balanced score leg
/// (bank → striker) for the verified joint turn.
pub fn resolve_contact(
    a: (FigureId, i64, &JointVector),
    b: (FigureId, i64, &JointVector),
) -> FrameResolution {
    let (a_id, a_pos, a_joints) = a;
    let (b_id, b_pos, b_joints) = b;

    let a_drive = forward_drive(a_joints);
    let b_drive = forward_drive(b_joints);
    let a_brace = brace(a_joints);
    let b_brace = brace(b_joints);

    // `a` is at the smaller coordinate; it moves +drive toward `b`, `b` moves -drive toward `a`.
    // Clamp so they never pass through each other (they stop at a touching gap).
    let mut a_next = a_pos + a_drive as i64;
    let mut b_next = b_pos - b_drive as i64;
    if a_next > b_next {
        // Would cross — clamp both to the midpoint-ish touching position (deterministic: floor/ceil).
        let mid = a_pos + b_pos;
        a_next = mid.div_euclid(2);
        b_next = a_next + 1;
    }
    let gap = b_next - a_next;

    // Contact iff the figures are within CONTACT_GAP after stepping.
    let mut contact = None;
    let mut score_legs = Vec::new();
    if gap <= CONTACT_GAP {
        // Effective hit = forward drive reduced by the opponent's brace, floored at 0.
        let a_hit = (a_drive - b_brace).max(0);
        let b_hit = (b_drive - a_brace).max(0);
        match a_hit.cmp(&b_hit) {
            std::cmp::Ordering::Greater => {
                let points = (a_hit - b_hit) as i128;
                contact = Some(Contact {
                    striker: a_id,
                    struck: b_id,
                    points,
                });
                score_legs.push(score_leg(a_id, points));
            }
            std::cmp::Ordering::Less => {
                let points = (b_hit - a_hit) as i128;
                contact = Some(Contact {
                    striker: b_id,
                    struck: a_id,
                    points,
                });
                score_legs.push(score_leg(b_id, points));
            }
            std::cmp::Ordering::Equal => {
                // A cancelled clash — equal effective hits, no score, empty ring (still conserving).
            }
        }
    }

    FrameResolution {
        new_positions: (a_next, b_next),
        contact,
        score_legs,
    }
}

/// The single balanced **score leg** — `points` of [`SCORE_ASSET`] from the neutral [`SCORE_BANK`]
/// into the scoring figure's column. A conserving transfer the verified executor admits (the bank
/// column falls exactly as the scorer's rises).
fn score_leg(scorer: FigureId, points: i128) -> VerifiedLeg {
    VerifiedLeg {
        from: SCORE_BANK,
        to: scorer,
        asset: SCORE_ASSET,
        amount: points,
    }
}

/// (Reserved) the public, fog-of-war datum a third party sees about a sealed move — its seal. Kept
/// here so the resolution module's public surface names the fog-of-war boundary alongside the
/// outcome it produces. The joints behind it are computationally unrecoverable.
pub type SealedDatum = MoveSeal;
