//! # `step_layout` — the SHAPE-INDEPENDENT Rust mirror of `AutomataflStepEmit.NGen`.
//!
//! Every column of the Lean-emitted automaton-step (D1, Leg A) descriptor
//! (`automataflStepDescN n`, `metatheory/Dregg2/Circuit/Emit/AutomataflStepEmit.lean`,
//! `namespace NGen` + `§4d`) is computed HERE from `n` by the SAME formulas the emit uses — never a
//! hardcoded index. This is the STEP analog of [`crate::resolve_layout::ResolveLayout`]: it lets the
//! step witness generator ([`crate::witness`]) SEED the non-affine gadget columns (the automaton
//! one-hots, the ray hits, the decision fields, the `forced_ge0` range blocks) at their exact
//! columns and then SOLVE the affine remainder from the descriptor's own gates — with NO dependency
//! on the (now-deleted) hand-authored Rust AIR / `Builder`.
//!
//! House law #1: the AIR is authored in Lean. This module authors ZERO constraints — it only
//! reproduces the Lean layout's ARITHMETIC so a trace can be filled into the proven object. The one
//! fail-closed guard is [`StepLayout::width`] == `desc.trace_width`, which turns a silent mis-fill
//! into a visible `Err`.
//!
//! Cross-reference (`AutomataflStepEmit.lean`, working tree): the `NGen` front-end defs
//! (`A_FRONT_WIDTH`, `rayBase`, `selRow`, …) at ~618-738; the `n`-parametric back-end bases
//! (`A_DECIDE_X_BASE`/`A_CHOOSE_BASE`/`A_STEP_BASE`/`A_BACK_TAIL`) at ~757-770; the per-block internal
//! offsets in `decideAxisConstraints`/`chooseOffsetConstraints`/`stepConstraints` at ~474-836; the
//! packed-commitment + `nax`/`nay` tail (`packFeltBase`, `newAutoBase`, `NAXcol`) at ~882-903.

/// `NGen.SMALL_RBITS` — the narrow range width (distances / coordinates).
pub const SMALL_RBITS: usize = 5;
/// `NGen`/`chooseOffset` `SCORE_RBITS` — the score-compare range width.
pub const SCORE_RBITS: usize = 20;
/// `AutomataflStepEmit.SCORE_PRI` — the priority coefficient of the emit's `scoreHead`.
pub const SCORE_PRI: i64 = 100_000;
/// `AutomataflStepEmit.SCORE_ATT` — the attractor-distance coefficient of the emit's `scoreHead`.
pub const SCORE_ATT: i64 = 100;

/// The emitted score head `variant·SCORE_PRI − att·SCORE_ATT − rep` (`AutomataflStepEmit.scoreHead`),
/// evaluated on a decision the LEAN reported.
///
/// ⚑ This is TRACE ARITHMETIC, not a game rule. The offset a decision pair induces is chosen by the
/// Lean (`chooseOffsetCfg`, read off [`crate::rules::sense`]); this function exists only because the
/// descriptor's `choose_offset` block spends two `forced_ge0` witnesses on the SIGN of
/// `score_x − score_y`, and a witness generator must fill them at the emit's own coefficients. It
/// belongs to the layout mirror for the same reason every column formula here does.
///
/// The field conventions the Lean wire uses already zero the irrelevant tiebreak key (`fromRepulsor`
/// carries `att = 0`, `towardAttractor` carries `rep = 0`, `none` both), so this single formula
/// reproduces `decisionCmp`'s order — priority first, then the reversed distances — over the range the
/// emit's `SCORE_ATT` radix supports.
pub fn decision_score(d: &crate::board::Decision) -> i64 {
    d.variant as i64 * SCORE_PRI - d.att_dist as i64 * SCORE_ATT - d.rep_dist as i64
}
/// `decide_axis` block width (constant in `n`): `A_DA_W`.
const A_DA_W: usize = 47;
/// `choose_offset` block width (constant in `n`): `A_CO_W`.
const A_CO_W: usize = 57;

/// `COORD_RBITS n = ⌈log2 (n−1)⌉ + 1` (`NGen.COORD_RBITS`) — the per-coordinate bit width. Mirrors
/// [`crate::resolve_layout::coord_rbits`] verbatim.
pub fn coord_rbits(n: usize) -> usize {
    if n <= 1 {
        1
    } else {
        let m = (n - 1) as u32;
        (u32::BITS - 1 - m.leading_zeros()) as usize + 1
    }
}

/// `AutomataflCommit.feltCount n = ⌈n²/15⌉` (`AFC`): the packed base-4 commitment felts per board.
pub fn felt_count(n: usize) -> usize {
    (n * n + 14) / 15
}

/// The step (Leg A) descriptor's column layout at board size `n`, every base a `def` of the Lean
/// `AutomataflStepEmit` (`NGen.*` for the trace body, `§4d` for the packed tail + `nax`/`nay`).
#[derive(Clone, Debug)]
pub struct StepLayout {
    /// Board edge.
    pub n: usize,
    /// `KK = n²`.
    pub kk: usize,
    /// `COORD_RBITS n`.
    pub cr: usize,
    /// `AFC = ⌈n²/15⌉`.
    pub afc: usize,
    /// `A_FRONT_WIDTH n`.
    pub front: usize,
    /// `A_STEP_BASE n` (`choose_offset` base is `step_base − A_CO_W`; decide bases derive off `front`).
    pub step_base: usize,
    /// `A_BACK_TAIL n` = `packFeltBase n`.
    pub back_tail: usize,
}

impl StepLayout {
    /// Build the layout for board size `n`, computing every anchor by the `NGen` / `§4d` formulas.
    pub fn new(n: usize) -> Self {
        let kk = n * n;
        let cr = coord_rbits(n);
        let afc = felt_count(n);
        // A_FRONT_WIDTH n = 2·KK + 2 + 4·cr + 2n + (3n+4)·4.
        let ray_w = 3 * n + 4;
        let front = 2 * kk + 2 + 4 * cr + 2 * n + ray_w * 4;
        // Back-end bases: decide_x = front, decide_y = front + A_DA_W, choose = front + 2·A_DA_W,
        // step = front + 2·A_DA_W + A_CO_W.
        let step_base = front + 2 * A_DA_W + A_CO_W;
        let a_st_w = 35 + 4 * n;
        let back_tail = step_base + a_st_w;
        Self {
            n,
            kk,
            cr,
            afc,
            front,
            step_base,
            back_tail,
        }
    }

    /// `A_WIDTH_N n = packFeltBase + 2·AFC + 2` (the two `nax`/`nay` columns close the row).
    pub fn width(&self) -> usize {
        self.back_tail + 2 * self.afc + 2
    }

    /// `A_PI_COUNT_N n = AUTO_PI_BASE + 4 = 16 + 2·AFC + 4`.
    pub fn pi_count(&self) -> usize {
        16 + 2 * self.afc + 4
    }

    // -- §2 board + automaton position + coordinate decompositions. --
    /// `old n i` — old board cell `i` (columns `0..KK`).
    pub fn old(&self, i: usize) -> usize {
        i
    }
    /// `new n i` — claimed-next board cell `i` (columns `KK..2·KK`).
    pub fn new_cell(&self, i: usize) -> usize {
        self.kk + i
    }
    /// `AX` — witnessed automaton x.
    pub fn ax(&self) -> usize {
        2 * self.kk
    }
    /// `AY` — witnessed automaton y.
    pub fn ay(&self) -> usize {
        2 * self.kk + 1
    }
    /// `axLoBit` bit `k` (the lower edge decomposition of `ax`).
    pub fn ax_lo(&self, k: usize) -> usize {
        2 * self.kk + 2 + k
    }
    /// `axHiBit` bit `k` (the upper edge `(n−1) − ax`).
    pub fn ax_hi(&self, k: usize) -> usize {
        2 * self.kk + 2 + self.cr + k
    }
    /// `ayLoBit` bit `k`.
    pub fn ay_lo(&self, k: usize) -> usize {
        2 * self.kk + 2 + 2 * self.cr + k
    }
    /// `ayHiBit` bit `k`.
    pub fn ay_hi(&self, k: usize) -> usize {
        2 * self.kk + 2 + 3 * self.cr + k
    }
    /// `selRow y` — the auto ROW one-hot (pinned to `ay`).
    pub fn sel_row(&self, y: usize) -> usize {
        2 * self.kk + 2 + 4 * self.cr + y
    }
    /// `selCol x` — the auto COLUMN one-hot (pinned to `ax`).
    pub fn sel_col(&self, x: usize) -> usize {
        2 * self.kk + 2 + 4 * self.cr + self.n + x
    }

    // -- §2 ray blocks (`RAY_W n = 3n+4` per ray). --
    /// `rayBase n d`.
    fn ray_base(&self, d: usize) -> usize {
        2 * self.kk + 2 + 4 * self.cr + 2 * self.n + (3 * self.n + 4) * d
    }
    /// `rIb n d kk` — the in-bounds bit for ray `d`, step `kk ∈ {1..n}`.
    pub fn r_ib(&self, d: usize, kk: usize) -> usize {
        self.ray_base(d) + 2 * (kk - 1)
    }
    /// `rHit n d kk` — the hit one-hot bit for ray `d`, step `kk`.
    pub fn r_hit(&self, d: usize, kk: usize) -> usize {
        self.ray_base(d) + 2 * self.n + (kk - 1)
    }
    /// `rInv n d` — the `cond_nonzero` witnessed inverse for ray `d`.
    pub fn r_inv(&self, d: usize) -> usize {
        self.ray_base(d) + 3 * self.n + 3
    }

    // -- §4c.1 back-end block bases. --
    /// `A_DECIDE_X_BASE n` / `A_DECIDE_Y_BASE n` — the `decide_axis(xdec|ydec)` block bases.
    pub fn decide_base(&self, axis: usize) -> usize {
        self.front + axis * A_DA_W
    }
    /// `A_CHOOSE_BASE n`.
    pub fn choose_base(&self) -> usize {
        self.step_base - A_CO_W
    }

    // -- decide_axis internal offsets (relative to a block base `b`). --
    /// `pos` (`b+1`).
    pub fn dec_pos(&self, b: usize) -> usize {
        b + 1
    }
    /// `variant` (`b`).
    pub fn dec_variant(&self, b: usize) -> usize {
        b
    }
    /// `att` (`b+2`).
    pub fn dec_att(&self, b: usize) -> usize {
        b + 2
    }
    /// `rep` (`b+3`).
    pub fn dec_rep(&self, b: usize) -> usize {
        b + 3
    }
    /// `ipw[j]` — the `pw`-alphabet one-hot (`b+4 .. b+7`).
    pub fn dec_ipw(&self, b: usize, j: usize) -> usize {
        b + 4 + j
    }
    /// `inw[j]` — the `nw`-alphabet one-hot (`b+7 .. b+10`).
    pub fn dec_inw(&self, b: usize, j: usize) -> usize {
        b + 7 + j
    }
    /// The six `decide_axis` `forced_ge0` blocks as `(ib_col, bit0_col)` pairs:
    /// `gpd, gnd, lt, gt, le, gm`. Each `bit` run is `SMALL_RBITS` wide.
    pub fn dec_ge0(&self, b: usize) -> [(usize, usize); 6] {
        [
            (b + 10, b + 11), // gpd
            (b + 16, b + 17), // gnd
            (b + 22, b + 23), // lt
            (b + 28, b + 29), // gt
            (b + 34, b + 35), // le
            (b + 41, b + 42), // gm
        ]
    }

    // -- choose_offset internal offsets (relative to `A_CHOOSE_BASE n`). --
    /// `sgt` ib column.
    pub fn co_sgt(&self) -> usize {
        self.choose_base()
    }
    /// `slt` ib column.
    pub fn co_slt(&self) -> usize {
        self.choose_base() + 21
    }
    /// `xmove` ib column.
    pub fn co_xmove(&self) -> usize {
        self.choose_base() + 42
    }
    /// `ymove` ib column.
    pub fn co_ymove(&self) -> usize {
        self.choose_base() + 48
    }

    // -- step block internal offsets (relative to `A_STEP_BASE n = s`). --
    /// The four target-edge `forced_ge0` blocks as `(ib_col, bit0_col)`: `bx0, bx1, by0, by1`.
    pub fn step_edge_ge0(&self) -> [(usize, usize); 4] {
        let s = self.step_base;
        [
            (s, s + 1),
            (s + 6, s + 7),
            (s + 12, s + 13),
            (s + 18, s + 19),
        ]
    }
    /// `tib` — target-in-bounds product bit.
    pub fn step_tib(&self) -> usize {
        self.step_base + 24
    }
    /// `selTargRowRead j` — the target-read row one-hot (gated by `tib`).
    pub fn step_targ_row_read(&self, j: usize) -> usize {
        self.step_base + 26 + j
    }
    /// `selTargColRead j` — the target-read column one-hot (gated by `tib`).
    pub fn step_targ_col_read(&self, j: usize) -> usize {
        self.step_base + 26 + self.n + j
    }
    /// `nzIb` — the `[tcell ≥ 1]` `forced_ge0` ib column (bits at `+1 .. +1+SMALL_RBITS`).
    pub fn step_nz_ib(&self) -> usize {
        self.step_base + 26 + 2 * self.n
    }
    /// The `nzIb` bit-`0` column.
    pub fn step_nz_bit0(&self) -> usize {
        self.step_base + 27 + 2 * self.n
    }
    /// `m` — the move-mask column.
    pub fn step_m(&self) -> usize {
        self.step_base + 34 + 2 * self.n
    }
    /// `selTargRowUpd j` — the board-update row one-hot (gated by `m`).
    pub fn step_targ_row_upd(&self, j: usize) -> usize {
        self.step_base + 35 + 2 * self.n + j
    }
    /// `selTargColUpd j` — the board-update column one-hot (gated by `m`).
    pub fn step_targ_col_upd(&self, j: usize) -> usize {
        self.step_base + 35 + 3 * self.n + j
    }

    // -- §4d packed commitment + nax/nay tail. --
    /// `packOldFelt j`.
    pub fn pack_old_felt(&self, j: usize) -> usize {
        self.back_tail + j
    }
    /// `packNewFelt j`.
    pub fn pack_new_felt(&self, j: usize) -> usize {
        self.back_tail + self.afc + j
    }
    /// `NAXcol` — the new automaton x (`nax = ax + m·ox`).
    pub fn nax(&self) -> usize {
        self.back_tail + 2 * self.afc
    }
    /// `NAYcol` — the new automaton y.
    pub fn nay(&self) -> usize {
        self.back_tail + 2 * self.afc + 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The GOLDEN-SHAPE canary: the layout width + PI count computed purely from `n` by the `NGen`
    /// formulas matches the emitted descriptors (`AutomataflStepEmit` `#guard`s: `A_WIDTH_N 2 = 256`,
    /// `A_WIDTH_N 11 = 680`, `NAXcol 11 = 678`).
    #[test]
    fn shape_matches_emitted_step_descriptors() {
        let l2 = StepLayout::new(2);
        assert_eq!(l2.width(), 256, "A_WIDTH_N 2");
        assert_eq!(l2.pi_count(), 22, "A_PI_COUNT_N 2");
        assert_eq!(l2.front, 58, "A_FRONT_WIDTH 2");
        assert_eq!(l2.step_base, 209, "A_STEP_BASE 2");
        assert_eq!(l2.back_tail, 252, "A_BACK_TAIL 2");
        assert_eq!(l2.step_m(), 247, "maskCol 2");

        let l11 = StepLayout::new(11);
        assert_eq!(l11.width(), 680, "A_WIDTH_N 11");
        assert_eq!(l11.pi_count(), 38, "A_PI_COUNT_N 11");
        assert_eq!(l11.cr, 4, "COORD_RBITS 11");
        assert_eq!(l11.afc, 9, "feltCount 11");
        assert_eq!(l11.nax(), 678, "NAXcol 11");
        assert_eq!(l11.nay(), 679, "NAYcol 11");
        assert_eq!(l11.step_m(), 637, "maskCol 11");
    }

    /// The choose-offset base reduces to the frozen numeral at `n = 2` (`A_CHOOSE_BASE 2 = 152`).
    #[test]
    fn choose_base_frozen_numeral() {
        assert_eq!(StepLayout::new(2).choose_base(), 152);
        assert_eq!(StepLayout::new(2).co_slt(), 173);
        assert_eq!(StepLayout::new(2).co_xmove(), 194);
    }
}
