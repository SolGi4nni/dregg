//! # `legc_layout` — the SHAPE-INDEPENDENT Rust mirror of `AutomataflLegCEmit.NGen`.
//!
//! Every family base of the Lean **Leg C** descriptor (`automataflLegCDescN n`,
//! `metatheory/Dregg2/Circuit/Emit/AutomataflLegCEmit.lean`) is computed HERE from `n` by the SAME
//! formulas the emit uses — never a hardcoded column index. Leg C is Leg R's FRONT HALF (`[0, CAR0)`,
//! spliced in numeral-for-numeral) plus a STATE-TRANSITION TAIL (`[CAR0, LEGC_WIDTH)`). So the front
//! half is [`crate::resolve_layout::ResolveLayout`] verbatim (embedded as `r`), and this file adds
//! only the tail bases: the packed IN/OUT board felts, the `marksIn`/`marksOut` blocks, the clash
//! delta `cs`, the destination one-hots, the per-move query block, and the seat-indexed
//! locked/waiting table.
//!
//! House law #1: the AIR is authored in Lean. This module authors ZERO constraints — it only
//! reproduces the Lean layout's ARITHMETIC so a trace can be filled into the proven object. The one
//! fail-closed guard is [`LegCLayout::width`] == `desc.trace_width` (plus [`LegCLayout::pi_count`] ==
//! `desc.public_input_count`), which turns a silent mis-fill into a visible `Err`.
//!
//! Cross-reference (`AutomataflLegCEmit.lean`, working tree): `LEGC0`/`cPackInFelt`/`MARKS0`/`CS0`/
//! `TSEL0`/`MVQ0`/`SEAT0`/`LEGC_WIDTH` at §2 (lines ~162-230); the PI bases `piMarksIn`..
//! `LEGC_PI_COUNT` at §3 (lines ~244-253). The 250 dead lanes are the two dropped `OCC_BLOCK_WIDTH`
//! windows `[NGen.occBase n 0, NGen.RES0 n)` (`[413, 663)` at `n = 11`).

use crate::resolve_layout::ResolveLayout;

/// `AutomataflLegCEmit.LEGC_SEATS` — the seats Leg C adjudicates. The front half is a TWO-move
/// block, so this is `2` (the design's M1 2-player row / §2.3 collapse). M9 widens it.
pub const LEGC_SEATS: usize = 2;
/// `AutomataflLegCEmit.SEAT_WIDTH` — the per-seat locked/waiting lane count
/// (`[lockedIn ‖ lockedOut ‖ waitingIn ‖ waitingOut]` = 5 + 5 + 1 + 1).
const SEAT_WIDTH: usize = 12;
/// `AutomataflLegCEmit.MVQ_WIDTH` — the per-move query block width
/// (`inMarksFrm ‖ inMarksTo ‖ legal ‖ csFrm ‖ csTo ‖ inClash`).
const MVQ_WIDTH: usize = 6;

/// The precomputed family anchors for board size `n`. `r` carries the entire Leg-R front half; the
/// remaining fields are the Leg C tail bases, each a `def` of the same name in the Lean emit.
#[derive(Clone, Debug)]
pub struct LegCLayout {
    /// The Leg-R front half, verbatim (Leg C keeps Leg R's column indices `[0, CAR0)`).
    pub r: ResolveLayout,
    /// `LEGC0 n = NGen.CAR0 n` — where Leg R's dropped resolution tail began; Leg C's tail base.
    pub legc0: usize,
    /// `MARKS0 n`.
    pub marks0: usize,
    /// `CS0 n`.
    pub cs0: usize,
    /// `TSEL0 n`.
    pub tsel0: usize,
    /// `MVQ0 n`.
    pub mvq0: usize,
    /// `SEAT0 n`.
    pub seat0: usize,
    /// `LEGC_WIDTH n`.
    pub width: usize,
}

impl LegCLayout {
    /// Build the layout for board size `n`, computing every anchor by the Lean `AutomataflLegCEmit`
    /// formulas off the embedded [`ResolveLayout`] front half.
    pub fn new(n: usize) -> Self {
        let r = ResolveLayout::new(n);
        let kk = r.kk;
        let rfc = r.rfc;
        let legc0 = r.car0; // LEGC0 = NGen.CAR0
        let marks0 = legc0 + 2 * rfc; // MARKS0 = LEGC0 + 2·RFC
        let cs0 = marks0 + 2 * kk + 2 * rfc; // CS0 = MARKS0 + 2·KK + 2·RFC
        let tsel0 = cs0 + kk; // TSEL0 = CS0 + KK
        let tsel_width = 2 * n; // TSEL_WIDTH
        let mvq0 = tsel0 + 2 * tsel_width; // MVQ0 = TSEL0 + 2·TSEL_WIDTH
        let seat0 = mvq0 + 2 * MVQ_WIDTH; // SEAT0 = MVQ0 + 2·MVQ_WIDTH
        let width = seat0 + SEAT_WIDTH * LEGC_SEATS; // LEGC_WIDTH
        Self {
            r,
            legc0,
            marks0,
            cs0,
            tsel0,
            mvq0,
            seat0,
            width,
        }
    }

    /// `LEGC_WIDTH n` — the base trace width. Fail-closed against `desc.trace_width`.
    pub fn width(&self) -> usize {
        self.width
    }

    /// `LEGC_PI_COUNT n`. Fail-closed against `desc.public_input_count`.
    pub fn pi_count(&self) -> usize {
        self.pi_waiting_out() + LEGC_SEATS
    }

    // -- The 250 dead lanes: the two dropped occlusion blocks `[NGen.occBase n 0, NGen.RES0 n)`.
    //    Leg C splices Leg R's front-half column indices but drops `validateOcclusion`, leaving these
    //    two `OCC_BLOCK_WIDTH` windows allocated, unconstrained and read by nothing (emit §"The
    //    price"). They are filled with `0`. --
    /// First dead column (`NGen.occBase n 0`).
    pub fn dead_lo(&self) -> usize {
        self.r.occ_base(0)
    }
    /// One past the last dead column (`NGen.RES0 n`).
    pub fn dead_hi(&self) -> usize {
        self.r.res0
    }

    // -- §2 board commitment (Leg C's own felt columns). --
    /// `cPackInFelt n j` — the packed OLD board felt `j`.
    pub fn c_pack_in_felt(&self, j: usize) -> usize {
        self.legc0 + j
    }
    /// `cPackOutFelt n j` — the packed FROZEN OUT board felt `j`.
    pub fn c_pack_out_felt(&self, j: usize) -> usize {
        self.legc0 + self.r.rfc + j
    }

    // -- §2 marks block (`marksIn` ‖ `marksOut`, each `cells ‖ felts`). --
    /// `cMarksInCell n c` — `marksIn` indicator cell `c` (linear index `y·n + x`).
    pub fn c_marks_in_cell(&self, c: usize) -> usize {
        self.marks0 + c
    }
    /// `cMarksInFelt n j` — `marksIn` packed felt `j`.
    pub fn c_marks_in_felt(&self, j: usize) -> usize {
        self.marks0 + self.r.kk + j
    }
    /// `cMarksOutCell n c` — `marksOut` indicator cell `c`.
    pub fn c_marks_out_cell(&self, c: usize) -> usize {
        self.marks0 + self.r.kk + self.r.rfc + c
    }
    /// `cMarksOutFelt n j` — `marksOut` packed felt `j`.
    pub fn c_marks_out_felt(&self, j: usize) -> usize {
        self.marks0 + 2 * self.r.kk + self.r.rfc + j
    }

    // -- §2 the clash delta `cs`. --
    /// `cCsCell n c` — `1` exactly on the conflicted coordinate(s) `cs` of THIS round.
    pub fn c_cs_cell(&self, c: usize) -> usize {
        self.cs0 + c
    }

    // -- §2 the destination one-hots (Leg C's own; Leg R's live in the dropped occlusion block). --
    /// `cTSelRow n w j` — destination-ROW selector `j` of move `w` (one-hot at `cTy`).
    pub fn c_tsel_row(&self, w: usize, j: usize) -> usize {
        self.tsel0 + (2 * self.r.n) * w + j
    }
    /// `cTSelCol n w j` — destination-COLUMN selector `j` of move `w` (one-hot at `cTx`).
    pub fn c_tsel_col(&self, w: usize, j: usize) -> usize {
        self.tsel0 + (2 * self.r.n) * w + self.r.n + j
    }

    // -- §2 the per-move query block. --
    /// `cInMarksFrm n w` — `marksIn[frm[w]]`.
    pub fn c_in_marks_frm(&self, w: usize) -> usize {
        self.mvq0 + MVQ_WIDTH * w
    }
    /// `cInMarksTo n w` — `marksIn[to[w]]`.
    pub fn c_in_marks_to(&self, w: usize) -> usize {
        self.mvq0 + MVQ_WIDTH * w + 1
    }
    /// `cLegal n w` — `¬inMarksFrm ∧ ¬inMarksTo`, pinned to `1`.
    pub fn c_legal(&self, w: usize) -> usize {
        self.mvq0 + MVQ_WIDTH * w + 2
    }
    /// `cCsFrm n w` — `cs[frm[w]]`.
    pub fn c_cs_frm(&self, w: usize) -> usize {
        self.mvq0 + MVQ_WIDTH * w + 3
    }
    /// `cCsTo n w` — `cs[to[w]]`.
    pub fn c_cs_to(&self, w: usize) -> usize {
        self.mvq0 + MVQ_WIDTH * w + 4
    }
    /// `cInClash n w` — `cs[frm] ∨ cs[to]` (this move is dropped, its seat re-enters).
    pub fn c_in_clash(&self, w: usize) -> usize {
        self.mvq0 + MVQ_WIDTH * w + 5
    }

    // -- §2 the seat-indexed locked/waiting table. --
    /// `cLockedInBit n s`.
    pub fn c_locked_in_bit(&self, s: usize) -> usize {
        self.seat0 + SEAT_WIDTH * s
    }
    /// `cLockedInFx n s`.
    pub fn c_locked_in_fx(&self, s: usize) -> usize {
        self.seat0 + SEAT_WIDTH * s + 1
    }
    /// `cLockedInFy n s`.
    pub fn c_locked_in_fy(&self, s: usize) -> usize {
        self.seat0 + SEAT_WIDTH * s + 2
    }
    /// `cLockedInTx n s`.
    pub fn c_locked_in_tx(&self, s: usize) -> usize {
        self.seat0 + SEAT_WIDTH * s + 3
    }
    /// `cLockedInTy n s`.
    pub fn c_locked_in_ty(&self, s: usize) -> usize {
        self.seat0 + SEAT_WIDTH * s + 4
    }
    /// `cLockedOutBit n s`.
    pub fn c_locked_out_bit(&self, s: usize) -> usize {
        self.seat0 + SEAT_WIDTH * s + 5
    }
    /// `cLockedOutFx n s`.
    pub fn c_locked_out_fx(&self, s: usize) -> usize {
        self.seat0 + SEAT_WIDTH * s + 6
    }
    /// `cLockedOutFy n s`.
    pub fn c_locked_out_fy(&self, s: usize) -> usize {
        self.seat0 + SEAT_WIDTH * s + 7
    }
    /// `cLockedOutTx n s`.
    pub fn c_locked_out_tx(&self, s: usize) -> usize {
        self.seat0 + SEAT_WIDTH * s + 8
    }
    /// `cLockedOutTy n s`.
    pub fn c_locked_out_ty(&self, s: usize) -> usize {
        self.seat0 + SEAT_WIDTH * s + 9
    }
    /// `cWaitingInBit n s`.
    pub fn c_waiting_in_bit(&self, s: usize) -> usize {
        self.seat0 + SEAT_WIDTH * s + 10
    }
    /// `cWaitingOutBit n s`.
    pub fn c_waiting_out_bit(&self, s: usize) -> usize {
        self.seat0 + SEAT_WIDTH * s + 11
    }

    // -- §3 the PI ABI (append-only past Leg R's `[0, AUTO_PI_BASE + 2)`). --
    /// `NGen.AUTO_PI_BASE n = 16 + 2·RFC` — Leg R's window end; the automaton `(ax, ay)` PI base.
    pub fn auto_pi_base(&self) -> usize {
        self.r.auto_pi_base()
    }
    /// The PI window base of `pack(board) IN` (`= COMMIT_PI_BASE = 16`).
    pub fn pi_pack_in(&self) -> usize {
        16
    }
    /// The PI window base of `pack(board) OUT` (`= 16 + RFC`; frozen: gated equal to IN).
    pub fn pi_pack_out(&self) -> usize {
        16 + self.r.rfc
    }
    /// `piMarksIn n = AUTO_PI_BASE n + 2`.
    pub fn pi_marks_in(&self) -> usize {
        self.auto_pi_base() + 2
    }
    /// `piMarksOut n`.
    pub fn pi_marks_out(&self) -> usize {
        self.pi_marks_in() + self.r.rfc
    }
    /// `piLockedIn n`.
    pub fn pi_locked_in(&self) -> usize {
        self.pi_marks_out() + self.r.rfc
    }
    /// `piLockedOut n`.
    pub fn pi_locked_out(&self) -> usize {
        self.pi_locked_in() + 5 * LEGC_SEATS
    }
    /// `piWaitingIn n`.
    pub fn pi_waiting_in(&self) -> usize {
        self.pi_locked_out() + 5 * LEGC_SEATS
    }
    /// `piWaitingOut n`.
    pub fn pi_waiting_out(&self) -> usize {
        self.pi_waiting_in() + LEGC_SEATS
    }
}

/// The by-name loader identity of the Lean Leg C descriptor for board size `n`. Byte-pinned for
/// `n ∈ {5, 11}` in `AutomataflLegCGolden`; `n = 5` is the audit-witness board (D4a/D4b), `n = 11`
/// the deployed stock game.
pub fn legc_descriptor_name(n: usize) -> String {
    format!("dregg-automatafl-legc-n{n}")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The GOLDEN-SHAPE canary: every base computed purely from `n = 11` by the emit formulas
    /// matches the Lean `#guard`s in `AutomataflLegCEmit.lean` §7 — the fail-closed guard that turns
    /// a layout drift into a visible mismatch rather than a silent mis-fill.
    #[test]
    fn n11_layout_matches_emitted_descriptor_shape() {
        let l = LegCLayout::new(11);
        assert_eq!(l.width(), 1208, "LEGC_WIDTH 11");
        assert_eq!(l.pi_count(), 78, "LEGC_PI_COUNT 11");
        // The tail bases (emit §7 #guards).
        assert_eq!(l.legc0, 729, "LEGC0 11 == NGen.CAR0 11");
        assert_eq!(l.marks0, 747, "MARKS0 11");
        assert_eq!(l.cs0, 1007, "CS0 11");
        assert_eq!(l.tsel0, 1128, "TSEL0 11");
        assert_eq!(l.mvq0, 1172, "MVQ0 11");
        assert_eq!(l.seat0, 1184, "SEAT0 11");
        assert_eq!(l.r.c_surv(), 728, "cSurv is the last front-half column");
        // The 250-lane dead window.
        assert_eq!(l.dead_lo(), 413, "NGen.occBase 11 0");
        assert_eq!(l.dead_hi(), 663, "NGen.RES0 11");
        assert_eq!(
            l.dead_hi() - l.dead_lo(),
            250,
            "the two dropped OCC_BLOCK_WIDTH windows"
        );
        // The PI window, lane for lane (emit §7).
        assert_eq!(l.auto_pi_base(), 34);
        assert_eq!(l.pi_marks_in(), 36);
        assert_eq!(l.pi_marks_out(), 45);
        assert_eq!(l.pi_locked_in(), 54);
        assert_eq!(l.pi_locked_out(), 64);
        assert_eq!(l.pi_waiting_in(), 74);
        assert_eq!(l.pi_waiting_out(), 76);
    }

    /// The n=5 audit-witness board (D4a collide / D4b fork) matches the byte-golden shape
    /// (536w / 50pi) the emit §7 pins.
    #[test]
    fn n5_layout_matches_byte_golden() {
        let l = LegCLayout::new(5);
        assert_eq!(l.width(), 536, "LEGC_WIDTH 5");
        assert_eq!(l.pi_count(), 50, "LEGC_PI_COUNT 5");
    }

    /// The tail bases tile with no gap or overlap, mirroring the Lean layout: the last front column
    /// (`cSurv`) abuts `LEGC0`, and the seat table closes the trace.
    #[test]
    fn family_bases_tile() {
        let l = LegCLayout::new(11);
        assert_eq!(l.r.c_surv() + 1, l.legc0, "cSurv abuts the tail");
        assert_eq!(
            l.c_pack_out_felt(l.r.rfc - 1) + 1,
            l.marks0,
            "pack felts abut MARKS0"
        );
        assert_eq!(l.c_marks_out_felt(l.r.rfc - 1) + 1, l.cs0, "marks abut CS0");
        assert_eq!(l.c_cs_cell(l.r.kk - 1) + 1, l.tsel0, "cs abuts TSEL0");
        assert_eq!(
            l.c_tsel_col(1, l.r.n - 1) + 1,
            l.mvq0,
            "dest one-hots abut MVQ0"
        );
        assert_eq!(l.c_in_clash(1) + 1, l.seat0, "the query block abuts SEAT0");
        assert_eq!(
            l.c_waiting_out_bit(LEGC_SEATS - 1) + 1,
            l.width(),
            "the seat table closes the row"
        );
    }
}
