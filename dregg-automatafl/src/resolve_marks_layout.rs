//! # `resolve_marks_layout` — the SHAPE-INDEPENDENT Rust mirror of the RESOLVE-MARKS tail.
//!
//! The marks-carrying resolve descriptor (`automataflResolveMarksDescN n`,
//! `metatheory/Dregg2/Circuit/Emit/AutomataflResolveMarksCapstone.lean`) is `automataflResolveDescN
//! n`'s constraints VERBATIM plus a MARKS TAIL at fresh columns above `R_WIDTH n`. This module mirrors
//! ONLY the tail's column arithmetic (`RM0`/`rMarksInCell`/`rMarksInFelt`/`RTSEL0`/`rTSelRow`/
//! `rTSelCol`/`RMVQ0`/`rInMarksFrm`/`rInMarksTo`/`rLegal`/`RM_WIDTH`, §1 of the capstone); the resolve
//! body's geometry is the shared [`ResolveLayout`], reached through the embedded `r` field. So the
//! marks-descriptor witness fills the resolve columns by the EXISTING resolve solver and the tail
//! columns by the same "solve the descriptor's own gates" discipline.
//!
//! House law #1: the AIR is authored in Lean. This module authors ZERO constraints — it only
//! reproduces the Lean tail layout's ARITHMETIC so a trace can be filled into the proven object. The
//! one fail-closed guard is [`ResolveMarksLayout::width`] == `desc.trace_width`.
//!
//! Cross-reference (capstone §1): `RM0 n = R_WIDTH n`, `rMarksInCell n c = RM0 + c`, `rMarksInFelt n
//! j = RM0 + KK + j`, `RTSEL0 n = RM0 + KK + RFC`, `rTSelRow/rTSelCol n w j`, `RMVQ0 n = RTSEL0 +
//! 2·(2n)`, `rInMarksFrm/rInMarksTo/rLegal n w`, `RM_WIDTH n = RMVQ0 + 3·2`, `rPiMarksIn n =
//! R_PI_COUNT n`, `piCount = R_PI_COUNT n + feltCount n`.

use crate::resolve_layout::ResolveLayout;

/// The precomputed marks-tail anchors for board size `n`, wrapping the resolve layout `r`.
#[derive(Clone, Debug)]
pub struct ResolveMarksLayout {
    /// The underlying resolve descriptor's layout (columns `[0, R_WIDTH n)`).
    pub r: ResolveLayout,
    /// `RM0 n = R_WIDTH n` — the marks tail's base column.
    pub rm0: usize,
    /// `RTSEL0 n = RM0 + KK + RFC` — base of the destination one-hot block.
    pub rtsel0: usize,
    /// `RMVQ0 n = RTSEL0 + 2·(2n)` — base of the per-move marks-query block.
    pub rmvq0: usize,
    /// `RM_WIDTH n = RMVQ0 + 3·2` — the marks-descriptor trace width.
    pub width: usize,
}

impl ResolveMarksLayout {
    /// Build the marks layout for board size `n`, computing every tail anchor by the capstone §1
    /// formulas off the resolve layout.
    pub fn new(n: usize) -> Self {
        let r = ResolveLayout::new(n);
        let rm0 = r.width; // RM0 = R_WIDTH
        let rtsel0 = rm0 + r.kk + r.rfc; // RTSEL0 = RM0 + KK + RFC
        let rmvq0 = rtsel0 + 2 * (2 * n); // RMVQ0 = RTSEL0 + 2·(2n)
        let width = rmvq0 + 3 * 2; // RM_WIDTH = RMVQ0 + 3·2
        Self {
            r,
            rm0,
            rtsel0,
            rmvq0,
            width,
        }
    }

    /// `RM_WIDTH n` — the marks-descriptor trace width. Fail-closed against `desc.trace_width`.
    pub fn width(&self) -> usize {
        self.width
    }

    /// `piCount = R_PI_COUNT n + feltCount n` (the resolve PIs plus the appended `marksIn` window).
    pub fn pi_count(&self) -> usize {
        self.r.pi_count() + self.r.rfc
    }

    // -- §1 the marks tail columns. --
    /// `rMarksInCell n c` — `marksIn` indicator cell `c` (linear index `y·n + x`).
    pub fn r_marks_in_cell(&self, c: usize) -> usize {
        self.rm0 + c
    }
    /// `rMarksInFelt n j` — `marksIn` packed felt `j`.
    pub fn r_marks_in_felt(&self, j: usize) -> usize {
        self.rm0 + self.r.kk + j
    }
    /// `rTSelRow n w j` — destination-ROW selector `j` of move `w` (one-hot at `cTy`).
    pub fn r_tsel_row(&self, w: usize, j: usize) -> usize {
        self.rtsel0 + (2 * self.r.n) * w + j
    }
    /// `rTSelCol n w j` — destination-COLUMN selector `j` of move `w` (one-hot at `cTx`).
    pub fn r_tsel_col(&self, w: usize, j: usize) -> usize {
        self.rtsel0 + (2 * self.r.n) * w + self.r.n + j
    }
    /// `rInMarksFrm n w` — `marksIn[frm[w]]` (the source-endpoint marks read).
    pub fn r_in_marks_frm(&self, w: usize) -> usize {
        self.rmvq0 + 3 * w
    }
    /// `rInMarksTo n w` — `marksIn[to[w]]` (the destination-endpoint marks read).
    pub fn r_in_marks_to(&self, w: usize) -> usize {
        self.rmvq0 + 3 * w + 1
    }
    /// `rLegal n w` — `¬inMarksFrm ∧ ¬inMarksTo`, pinned to `1`.
    pub fn r_legal(&self, w: usize) -> usize {
        self.rmvq0 + 3 * w + 2
    }

    // -- §6 the PI ABI (append-only past Leg R's `[0, R_PI_COUNT n)`). --
    /// `rPiMarksIn n = R_PI_COUNT n` — the published `marksIn` window base.
    pub fn pi_marks_in(&self) -> usize {
        self.r.pi_count()
    }
}

/// The by-name loader identity of the Lean resolve-marks descriptor for board size `n`. Emitted for
/// `n ∈ {2, 11}` (`metatheory/EmitByName.lean`).
pub fn resolve_marks_descriptor_name(n: usize) -> &'static str {
    match n {
        2 => "dregg-automatafl-resolve-marks-n2",
        11 => "dregg-automatafl-resolve-marks-n11",
        _ => "dregg-automatafl-resolve-marks-unknown",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The GOLDEN-SHAPE canary: the marks layout computed purely from `n = 11` by the capstone §1
    /// formulas matches the emitted n=11 descriptor's 1453-wide trace and 45-PI ABI.
    #[test]
    fn n11_layout_matches_emitted_descriptor_shape() {
        let l = ResolveMarksLayout::new(11);
        assert_eq!(l.rm0, 1273, "RM0 = R_WIDTH 11");
        assert_eq!(
            l.width(),
            1453,
            "RM_WIDTH 11 must equal the emitted trace_width"
        );
        assert_eq!(l.pi_count(), 45, "R_PI_COUNT 11 (36) + feltCount 11 (9)");
        assert_eq!(l.pi_marks_in(), 36, "rPiMarksIn 11 = R_PI_COUNT 11");
        // The tail tiles: RTSEL0 = RM0 + KK + RFC; RMVQ0 = RTSEL0 + 2·(2n); RM_WIDTH = RMVQ0 + 6.
        assert_eq!(l.rtsel0, 1273 + 121 + 9);
        assert_eq!(l.rmvq0, l.rtsel0 + 2 * (2 * 11));
        assert_eq!(l.width(), l.rmvq0 + 6);
        // The last query column is the final trace column.
        assert_eq!(l.r_legal(1) + 1, l.width());
    }

    /// The n=2 minimal instance matches the byte-golden (460w / 21pi).
    #[test]
    fn n2_layout_matches_byte_golden() {
        let l = ResolveMarksLayout::new(2);
        assert_eq!(l.width(), 460, "RM_WIDTH 2 == the byte-golden 460");
        assert_eq!(l.pi_count(), 21);
        assert_eq!(l.pi_marks_in(), 20, "R_PI_COUNT 2");
    }
}
