//! # `step_marks_layout` — the SHAPE-INDEPENDENT Rust mirror of the STEP-MARKS window.
//!
//! The marks-carrying step descriptor (`automataflStepMarksDescN n`,
//! `metatheory/Dregg2/Circuit/Emit/AutomataflStepMarksCapstone.lean`) is `automataflStepDescN n`'s
//! constraints VERBATIM plus a FROZEN MARKS WINDOW at fresh columns above `A_WIDTH_N n`. This module
//! mirrors ONLY the window's column arithmetic (`SM0`/`sMarksInCell`/`sMarksInFelt`/`SM_WIDTH`/
//! `sPiMarksIn`, §1 of the capstone); the step body's geometry is the shared [`StepLayout`], reached
//! through the embedded `s` field. So the marks-descriptor witness fills the step columns by the
//! EXISTING step solver and the marks window by the same "solve the descriptor's own gates" discipline.
//!
//! House law #1: the AIR is authored in Lean. This module authors ZERO constraints — it only
//! reproduces the Lean window layout's ARITHMETIC so a trace can be filled into the proven object. The
//! one fail-closed guard is [`StepMarksLayout::width`] == `desc.trace_width`.
//!
//! Cross-reference (capstone §1): `SM0 n = A_WIDTH_N n`, `sMarksInCell n c = SM0 + c`, `sMarksInFelt n
//! j = SM0 + n² + j`, `SM_WIDTH n = SM0 + n² + feltCount n`, `sPiMarksIn n = A_PI_COUNT_N n`,
//! `piCount = A_PI_COUNT_N n + feltCount n`. The marks freeze (`sPiMarksOut n = sPiMarksIn n`) is
//! structural: the step publishes the window ONCE and both the IN and OUT windows read it.

use crate::step_layout::StepLayout;

/// The precomputed marks-window anchors for board size `n`, wrapping the step layout `s`.
#[derive(Clone, Debug)]
pub struct StepMarksLayout {
    /// The underlying step (Leg A) descriptor's layout (columns `[0, A_WIDTH_N n)`).
    pub s: StepLayout,
    /// `SM0 n = A_WIDTH_N n` — the marks window's base column.
    pub sm0: usize,
    /// `SM_WIDTH n = SM0 + n² + feltCount n` — the marks-descriptor trace width.
    pub width: usize,
}

impl StepMarksLayout {
    /// Build the marks layout for board size `n`, computing every window anchor by the capstone §1
    /// formulas off the step layout.
    pub fn new(n: usize) -> Self {
        let s = StepLayout::new(n);
        let sm0 = s.width(); // SM0 = A_WIDTH_N
        let width = sm0 + s.kk + s.afc; // SM_WIDTH = SM0 + n² + feltCount n
        Self { s, sm0, width }
    }

    /// `SM_WIDTH n` — the marks-descriptor trace width. Fail-closed against `desc.trace_width`.
    pub fn width(&self) -> usize {
        self.width
    }

    /// `piCount = A_PI_COUNT_N n + feltCount n` (the step PIs plus the appended `marksIn` window).
    pub fn pi_count(&self) -> usize {
        self.s.pi_count() + self.s.afc
    }

    // -- §1 the marks window columns. --
    /// `sMarksInCell n c` — `marksIn` indicator cell `c` (linear index `y·n + x`).
    pub fn s_marks_in_cell(&self, c: usize) -> usize {
        self.sm0 + c
    }
    /// `sMarksInFelt n j` — `marksIn` packed felt `j`.
    pub fn s_marks_in_felt(&self, j: usize) -> usize {
        self.sm0 + self.s.kk + j
    }

    // -- §6 the PI ABI (append-only past Leg A's `[0, A_PI_COUNT_N n)`). --
    /// `sPiMarksIn n = A_PI_COUNT_N n` — the published `marksIn` window base.
    pub fn pi_marks_in(&self) -> usize {
        self.s.pi_count()
    }
    /// `sPiMarksOut n = sPiMarksIn n` — the OUT window's marks slice reads the SAME published window
    /// (the step publishes marks ONCE; `marksOut = marksIn` by construction, the M6 freeze).
    pub fn pi_marks_out(&self) -> usize {
        self.pi_marks_in()
    }
}

/// The by-name loader identity of the Lean step-marks descriptor for board size `n`. Emitted for
/// `n ∈ {2, 11}` (`metatheory/EmitByName.lean`).
pub fn step_marks_descriptor_name(n: usize) -> &'static str {
    match n {
        2 => "dregg-automatafl-step-marks-n2",
        11 => "dregg-automatafl-step-marks-n11",
        _ => "dregg-automatafl-step-marks-unknown",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The GOLDEN-SHAPE canary: the marks layout computed purely from `n = 11` by the capstone §1
    /// formulas matches the emitted n=11 descriptor's 810-wide trace and 47-PI ABI.
    #[test]
    fn n11_layout_matches_emitted_descriptor_shape() {
        let l = StepMarksLayout::new(11);
        assert_eq!(l.sm0, 680, "SM0 = A_WIDTH_N 11");
        assert_eq!(
            l.width(),
            810,
            "SM_WIDTH 11 must equal the emitted trace_width"
        );
        assert_eq!(l.pi_count(), 47, "A_PI_COUNT_N 11 (38) + feltCount 11 (9)");
        assert_eq!(l.pi_marks_in(), 38, "sPiMarksIn 11 = A_PI_COUNT_N 11");
        assert_eq!(
            l.pi_marks_out(),
            l.pi_marks_in(),
            "marks frozen: one window"
        );
        // The window tiles: cells [SM0, SM0+n²), felts [SM0+n², SM0+n²+AFC).
        assert_eq!(l.s_marks_in_cell(0), 680);
        assert_eq!(l.s_marks_in_cell(120), 800);
        assert_eq!(l.s_marks_in_felt(0), 680 + 121);
        assert_eq!(l.s_marks_in_felt(8) + 1, l.width());
    }

    /// The n=2 minimal instance matches the byte-golden (261w / 23pi).
    #[test]
    fn n2_layout_matches_byte_golden() {
        let l = StepMarksLayout::new(2);
        assert_eq!(l.width(), 261, "SM_WIDTH 2 == the byte-golden 261");
        assert_eq!(l.pi_count(), 23);
        assert_eq!(l.pi_marks_in(), 22, "A_PI_COUNT_N 2");
    }
}
