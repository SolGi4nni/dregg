//! # `resolve_layout` — the SHAPE-INDEPENDENT Rust mirror of `AutomataflResolveEmit.NGen`.
//!
//! Every family base of the Lean Leg-R (`old → mid`) resolve descriptor
//! (`automataflResolveDescN n`, `metatheory/Dregg2/Circuit/Emit/AutomataflResolveEmit.lean`,
//! `namespace NGen`) is computed HERE from `n` by the SAME formulas the emit uses — never a
//! hardcoded column index. The descriptor is under a concurrent cutover (dead `V2`/`V3` families
//! being removed); binding to the FAMILY (`layout.c_mid_v4(c)`) rather than the offset means the
//! witness-gen stays correct by construction as the descriptor shrinks. The one fail-closed guard
//! is [`ResolveLayout::width`] == `desc.trace_width`, which turns a silent mis-fill into a
//! compile-time-visible `Err`.
//!
//! House law #1: the AIR is authored in Lean. This module authors ZERO constraints — it only
//! reproduces the Lean layout's ARITHMETIC so a trace can be filled into the proven object.
//!
//! Cross-reference (line numbers `@` the working tree): `NGen.KK` .. `NGen.R_WIDTH` at
//! `AutomataflResolveEmit.lean:1436-1651`, the packed-commitment felts via
//! `AutomataflCommit.feltCount` (`AutomataflCommit.lean:54`).

/// `NGen.RBITS` — the wide range width (holds `2·(n−1)²` and `3n` through `n = 16`).
pub const RBITS: usize = 9;
/// `NGen.SMALL_RBITS` — the narrow range width (the particle alphabet `{0,1,2,3}`).
pub const SMALL_RBITS: usize = 5;
/// `NGen.AUTO_CODE` — the automaton particle code.
pub const AUTO_CODE: i64 = 3;

/// `⌈log2 (n−1)⌉ + 1` (`NGen.COORD_RBITS`): the per-coordinate bit width. `Nat.log2 (n-1)` is
/// `⌊log2 (n-1)⌋`; at `n ≤ 1` the emit clamps to `1`.
pub fn coord_rbits(n: usize) -> usize {
    if n <= 1 {
        1
    } else {
        // Nat.log2 (n-1) = floor(log2 (n-1)); +1. (Width the leading-zero count against `u32`,
        // not `usize` — a `usize::BITS` mismatch here silently widens every cr-bearing block.)
        let m = (n - 1) as u32;
        (u32::BITS - 1 - m.leading_zeros()) as usize + 1
    }
}

/// `AutomataflCommit.feltCount n = ⌈n²/15⌉` (`NGen.RFC`): the packed base-4 commitment felts/board.
pub fn felt_count(n: usize) -> usize {
    (n * n + 14) / 15
}

/// The fixed narrow widths, `n`-independent (`NGen.EQ_BLOCK_WIDTH`, `NZ_WIDTH`, `INCL_MV_WIDTH`,
/// `NL_PIECE_WIDTH`, `NLV2_PIECE_WIDTH`).
const fn eq_block_width() -> usize {
    3 + RBITS
}
const fn nz_width() -> usize {
    2 * (1 + SMALL_RBITS)
}
const fn incl_mv_width() -> usize {
    2 + RBITS
}
const fn nl_piece_width() -> usize {
    3 + SMALL_RBITS
}

/// The precomputed family anchors for board size `n`. Each field is a Lean `NGen` `def` of the
/// same name (block bases like `RES0`, `SEL0`, `FT0`, `MH0`, `INCL0`, `V4_0`); the per-index
/// members (`old`, `c_line`, `w_dst_row`, `c_mid_v4`, …) are METHODS deriving off these anchors,
/// exactly as the emit's `def cLine (o k)` derives off `occVec o`.
#[derive(Clone, Debug)]
pub struct ResolveLayout {
    /// Board edge.
    pub n: usize,
    /// `KK = n²`.
    pub kk: usize,
    /// `COORD_RBITS`.
    pub cr: usize,
    /// `RFC = ⌈n²/15⌉`.
    pub rfc: usize,
    /// `AUTO_BLOCK_WIDTH`.
    pub abw: usize,
    /// `MV_BLOCK_WIDTH`.
    pub mvbw: usize,
    /// `OCC_BLOCK_WIDTH`.
    pub occbw: usize,
    /// `RES0` — first adjudication-tail column (after both occlusion blocks).
    pub res0: usize,
    /// `SEL0`.
    pub sel0: usize,
    /// `CAR0`.
    pub car0: usize,
    /// `FT0`.
    pub ft0: usize,
    /// `WR0`.
    pub wr0: usize,
    /// `MH0` — first packed-felt column.
    pub mh0: usize,
    /// `INCL0`.
    pub incl0: usize,
    /// `NL0`.
    pub nl0: usize,
    /// `RESR0`.
    pub resr0: usize,
    /// `resEqBase`.
    pub res_eq_base: usize,
    /// `RESR_LOGIC`.
    pub resr_logic: usize,
    /// `RESR_END` (== `CV2_0`).
    pub resr_end: usize,
    /// `CV2_0`.
    pub cv2_0: usize,
    /// `MV2_END` (== `V3_0`).
    pub mv2_end: usize,
    /// `FTV2_0` (== `V3_0`).
    pub ftv2_0: usize,
    /// `WRV2_0`.
    pub wrv2_0: usize,
    /// `NLV2_0`.
    pub nlv2_0: usize,
    /// `CV3_0`.
    pub cv3_0: usize,
    /// `RESRV2_0`.
    pub resrv2_0: usize,
    /// `resEqV2Base`.
    pub res_eq_v2_base: usize,
    /// `RESRV2_LOGIC`.
    pub resrv2_logic: usize,
    /// `RESRV2_END` (== `V4_0`).
    pub resrv2_end: usize,
    /// `V4_0`.
    pub v4_0: usize,
    /// `CV4_0`.
    pub cv4_0: usize,
    /// `MIDV4_0`.
    pub midv4_0: usize,
    /// `R_WIDTH` (== `MV4_END`).
    pub width: usize,
}

impl ResolveLayout {
    /// Build the layout for board size `n`, computing every anchor by the `NGen` formulas.
    pub fn new(n: usize) -> Self {
        let kk = n * n;
        let cr = coord_rbits(n);
        let rfc = felt_count(n);
        let abw = 2 + 4 * cr + 2 * n; // AUTO_BLOCK_WIDTH
        let mvbw = 4 + 8 * cr + 6 + 1 + 2 * n; // MV_BLOCK_WIDTH
        let occbw = 3 * eq_block_width() + 7 * n + 3 + RBITS; // OCC_BLOCK_WIDTH
        let res0 = 2 * kk + 1 + abw + mvbw * 2 + occbw * 2; // RES0
        let sel0 = res0 + nz_width() + 4 * eq_block_width(); // SEL0
        let car0 = sel0 + 6; // CAR0
        let ft0 = car0 + 4; // FT0
        let wr0 = ft0 + 14; // WR0
        let mh0 = wr0 + (4 * n) * 2; // MH0 = WR0 + WR_PIECE_WIDTH*2
        let incl0 = mh0 + 2 * rfc; // INCL0
        let nl0 = incl0 + 2 * incl_mv_width(); // NL0
        let resr0 = nl0 + 2 * nl_piece_width(); // RESR0
        let res_eq_base = resr0 + 4; // resEqBase
        let resr_logic = res_eq_base + eq_block_width(); // RESR_LOGIC
        let resr_end = resr_logic + 12; // RESR_END
        let cv2_0 = resr_end; // CV2_0
        let mv2_end = cv2_0 + 6; // MV2_END
        let v3_0 = mv2_end; // V3_0
        let ftv2_0 = v3_0; // FTV2_0
        let wrv2_0 = ftv2_0 + 10; // WRV2_0
        let nlv2_0 = wrv2_0 + 2 * (2 * n); // NLV2_0 = WRV2_0 + WRV2_PIECE_WIDTH*2
        let cv3_0 = nlv2_0 + 2 * nl_piece_width(); // CV3_0 (NLV2_PIECE_WIDTH == NL_PIECE_WIDTH)
        let resrv2_0 = cv3_0 + 2; // RESRV2_0
        let res_eq_v2_base = resrv2_0 + 4; // resEqV2Base
        let resrv2_logic = res_eq_v2_base + eq_block_width(); // RESRV2_LOGIC
        let resrv2_end = resrv2_logic + 12; // RESRV2_END
        let v4_0 = resrv2_end; // V4_0 (== MV3_END)
        let cv4_0 = v4_0 + 4; // CV4_0
        let midv4_0 = cv4_0 + 2; // MIDV4_0
        let width = midv4_0 + 2 * kk; // MV4_END == R_WIDTH
        Self {
            n,
            kk,
            cr,
            rfc,
            abw,
            mvbw,
            occbw,
            res0,
            sel0,
            car0,
            ft0,
            wr0,
            mh0,
            incl0,
            nl0,
            resr0,
            res_eq_base,
            resr_logic,
            resr_end,
            cv2_0,
            mv2_end,
            ftv2_0,
            wrv2_0,
            nlv2_0,
            cv3_0,
            resrv2_0,
            res_eq_v2_base,
            resrv2_logic,
            resrv2_end,
            v4_0,
            cv4_0,
            midv4_0,
            width,
        }
    }

    /// `NGen.R_WIDTH n` — the base trace width. Fail-closed against `desc.trace_width`.
    pub fn width(&self) -> usize {
        self.width
    }

    /// `NGen.R_PI_COUNT n = AUTO_PI_BASE + 2`.
    pub fn pi_count(&self) -> usize {
        self.auto_pi_base() + 2
    }

    // -- §0 board / shared columns. --
    /// `old n i` — the old board cell `i` (`0 ≤ i < KK`).
    pub fn old(&self, i: usize) -> usize {
        i
    }
    /// `mid n i` — the leg-7 mid board cell `i` (== `KK + i`).
    pub fn mid(&self, i: usize) -> usize {
        self.kk + i
    }
    /// `ONE` — the constant-1 column.
    pub fn one(&self) -> usize {
        2 * self.kk
    }
    /// `AX_C` — witnessed automaton x.
    pub fn ax_c(&self) -> usize {
        2 * self.kk + 1
    }
    /// `AY_C` — witnessed automaton y.
    pub fn ay_c(&self) -> usize {
        2 * self.kk + 2
    }
    /// `axLo` bit `k`.
    pub fn ax_lo(&self, k: usize) -> usize {
        2 * self.kk + 3 + k
    }
    /// `axHi` bit `k`.
    pub fn ax_hi(&self, k: usize) -> usize {
        2 * self.kk + 3 + self.cr + k
    }
    /// `ayLo` bit `k`.
    pub fn ay_lo(&self, k: usize) -> usize {
        2 * self.kk + 3 + 2 * self.cr + k
    }
    /// `ayHi` bit `k`.
    pub fn ay_hi(&self, k: usize) -> usize {
        2 * self.kk + 3 + 3 * self.cr + k
    }
    /// `selAutoRow y`.
    pub fn sel_auto_row(&self, y: usize) -> usize {
        2 * self.kk + 3 + 4 * self.cr + y
    }
    /// `selAutoCol x`.
    pub fn sel_auto_col(&self, x: usize) -> usize {
        2 * self.kk + 3 + 4 * self.cr + self.n + x
    }

    // -- §4 per-move validity block. --
    /// `mvBase which`.
    pub fn mv_base(&self, which: usize) -> usize {
        2 * self.kk + 1 + self.abw + self.mvbw * which
    }
    /// `cFx b`.
    pub fn c_fx(&self, b: usize) -> usize {
        b
    }
    /// `cFy b`.
    pub fn c_fy(&self, b: usize) -> usize {
        b + 1
    }
    /// `cTx b`.
    pub fn c_tx(&self, b: usize) -> usize {
        b + 2
    }
    /// `cTy b`.
    pub fn c_ty(&self, b: usize) -> usize {
        b + 3
    }
    /// `cFxLo b` bit `k`.
    pub fn c_fx_lo(&self, b: usize, k: usize) -> usize {
        b + 4 + k
    }
    /// `cFxHi b` bit `k`.
    pub fn c_fx_hi(&self, b: usize, k: usize) -> usize {
        b + 4 + self.cr + k
    }
    /// `cFyLo b` bit `k`.
    pub fn c_fy_lo(&self, b: usize, k: usize) -> usize {
        b + 4 + 2 * self.cr + k
    }
    /// `cFyHi b` bit `k`.
    pub fn c_fy_hi(&self, b: usize, k: usize) -> usize {
        b + 4 + 3 * self.cr + k
    }
    /// `cTxLo b` bit `k`.
    pub fn c_tx_lo(&self, b: usize, k: usize) -> usize {
        b + 4 + 4 * self.cr + k
    }
    /// `cTxHi b` bit `k`.
    pub fn c_tx_hi(&self, b: usize, k: usize) -> usize {
        b + 4 + 5 * self.cr + k
    }
    /// `cTyLo b` bit `k`.
    pub fn c_ty_lo(&self, b: usize, k: usize) -> usize {
        b + 4 + 6 * self.cr + k
    }
    /// `cTyHi b` bit `k`.
    pub fn c_ty_hi(&self, b: usize, k: usize) -> usize {
        b + 4 + 7 * self.cr + k
    }
    /// `mvPost b`.
    pub fn mv_post(&self, b: usize) -> usize {
        b + 4 + 8 * self.cr
    }
    /// `cDsq b`.
    pub fn c_dsq(&self, b: usize) -> usize {
        self.mv_post(b)
    }
    /// `cDistinctInv b`.
    pub fn c_distinct_inv(&self, b: usize) -> usize {
        self.mv_post(b) + 1
    }
    /// `cFa b`.
    pub fn c_fa(&self, b: usize) -> usize {
        self.mv_post(b) + 2
    }
    /// `cFnaInv b`.
    pub fn c_fna_inv(&self, b: usize) -> usize {
        self.mv_post(b) + 3
    }
    /// `cTa b`.
    pub fn c_ta(&self, b: usize) -> usize {
        self.mv_post(b) + 4
    }
    /// `cTnaInv b`.
    pub fn c_tna_inv(&self, b: usize) -> usize {
        self.mv_post(b) + 5
    }
    /// `cFp b`.
    pub fn c_fp(&self, b: usize) -> usize {
        self.mv_post(b) + 6
    }
    /// `cSelRow b j`.
    pub fn c_sel_row(&self, b: usize, j: usize) -> usize {
        self.mv_post(b) + 7 + j
    }
    /// `cSelCol b j`.
    pub fn c_sel_col(&self, b: usize, j: usize) -> usize {
        self.mv_post(b) + 7 + self.n + j
    }

    // -- §4.5 per-move occlusion block. --
    /// `occBase which`.
    pub fn occ_base(&self, which: usize) -> usize {
        2 * self.kk + 1 + self.abw + self.mvbw * 2 + self.occbw * which
    }
    /// `cIvDsq o`.
    pub fn c_iv_dsq(&self, o: usize) -> usize {
        o
    }
    /// `cIvNeq o`.
    pub fn c_iv_neq(&self, o: usize) -> usize {
        o + 1
    }
    /// `ivNeqBit o k`.
    pub fn iv_neq_bit(&self, o: usize, k: usize) -> usize {
        o + 2 + k
    }
    /// `cIv o`.
    pub fn c_iv(&self, o: usize) -> usize {
        o + 2 + RBITS
    }
    /// `occVec o`.
    pub fn occ_vec(&self, o: usize) -> usize {
        o + eq_block_width()
    }
    /// `cLine o k`.
    pub fn c_line(&self, o: usize, k: usize) -> usize {
        self.occ_vec(o) + k
    }
    /// `cEty o j`.
    pub fn c_ety(&self, o: usize, j: usize) -> usize {
        self.occ_vec(o) + self.n + j
    }
    /// `cEtx o j`.
    pub fn c_etx(&self, o: usize, j: usize) -> usize {
        self.occ_vec(o) + 2 * self.n + j
    }
    /// `cEfrom o j`.
    pub fn c_efrom(&self, o: usize, j: usize) -> usize {
        self.occ_vec(o) + 3 * self.n + j
    }
    /// `cEto o j`.
    pub fn c_eto(&self, o: usize, j: usize) -> usize {
        self.occ_vec(o) + 4 * self.n + j
    }
    /// `cSeg o k`.
    pub fn c_seg(&self, o: usize, k: usize) -> usize {
        self.occ_vec(o) + 5 * self.n + k
    }
    /// `occEq o`.
    pub fn occ_eq(&self, o: usize) -> usize {
        self.occ_vec(o) + 6 * self.n
    }
    /// `cEqxDsq o`.
    pub fn c_eqx_dsq(&self, o: usize) -> usize {
        self.occ_eq(o)
    }
    /// `cEqxNeq o`.
    pub fn c_eqx_neq(&self, o: usize) -> usize {
        self.occ_eq(o) + 1
    }
    /// `eqxBit o k`.
    pub fn eqx_bit(&self, o: usize, k: usize) -> usize {
        self.occ_eq(o) + 2 + k
    }
    /// `cEqx o`.
    pub fn c_eqx(&self, o: usize) -> usize {
        self.occ_eq(o) + 2 + RBITS
    }
    /// `cEqyDsq o`.
    pub fn c_eqy_dsq(&self, o: usize) -> usize {
        self.occ_eq(o) + eq_block_width()
    }
    /// `cEqyNeq o`.
    pub fn c_eqy_neq(&self, o: usize) -> usize {
        self.occ_eq(o) + eq_block_width() + 1
    }
    /// `eqyBit o k`.
    pub fn eqy_bit(&self, o: usize, k: usize) -> usize {
        self.occ_eq(o) + eq_block_width() + 2 + k
    }
    /// `cEqy o`.
    pub fn c_eqy(&self, o: usize) -> usize {
        self.occ_eq(o) + eq_block_width() + 2 + RBITS
    }
    /// `occTail o`.
    pub fn occ_tail(&self, o: usize) -> usize {
        self.occ_eq(o) + 2 * eq_block_width()
    }
    /// `cOg o`.
    pub fn c_og(&self, o: usize) -> usize {
        self.occ_tail(o)
    }
    /// `cOsrc o j`.
    pub fn c_osrc(&self, o: usize, j: usize) -> usize {
        self.occ_tail(o) + 1 + j
    }
    /// `cMsum o`.
    pub fn c_msum(&self, o: usize) -> usize {
        self.occ_tail(o) + 1 + self.n
    }
    /// `cOcc o`.
    pub fn c_occ(&self, o: usize) -> usize {
        self.occ_tail(o) + 2 + self.n
    }
    /// `occBit o k`.
    pub fn occ_bit(&self, o: usize, k: usize) -> usize {
        self.occ_tail(o) + 3 + self.n + k
    }

    // -- §4.6 leg 3: source non-vacuum. --
    /// `cAnz`.
    pub fn c_anz(&self) -> usize {
        self.res0
    }
    /// `anzBit k`.
    pub fn anz_bit(&self, k: usize) -> usize {
        self.res0 + 1 + k
    }
    /// `cBnz`.
    pub fn c_bnz(&self) -> usize {
        self.res0 + 1 + SMALL_RBITS
    }
    /// `bnzBit k`.
    pub fn bnz_bit(&self, k: usize) -> usize {
        self.res0 + 2 + SMALL_RBITS + k
    }

    // -- §4.6 leg 4: pattern eq-coords + selection. --
    /// `eqBase i`.
    pub fn eq_base(&self, i: usize) -> usize {
        self.res0 + nz_width() + eq_block_width() * i
    }
    /// `cEqDsq e`.
    pub fn c_eq_dsq(&self, e: usize) -> usize {
        e
    }
    /// `cEqNeq e`.
    pub fn c_eq_neq(&self, e: usize) -> usize {
        e + 1
    }
    /// `eqBitAt e k`.
    pub fn eq_bit_at(&self, e: usize, k: usize) -> usize {
        e + 2 + k
    }
    /// `cEqBit e`.
    pub fn c_eq_bit(&self, e: usize) -> usize {
        e + 2 + RBITS
    }
    /// `cFork`.
    pub fn c_fork(&self) -> usize {
        self.sel0
    }
    /// `cNeqFf`.
    pub fn c_neq_ff(&self) -> usize {
        self.sel0 + 1
    }
    /// `cCol1`.
    pub fn c_col1(&self) -> usize {
        self.sel0 + 2
    }
    /// `cCol2`.
    pub fn c_col2(&self) -> usize {
        self.sel0 + 3
    }
    /// `cCollide`.
    pub fn c_collide(&self) -> usize {
        self.sel0 + 4
    }
    /// `cSurv`.
    pub fn c_surv(&self) -> usize {
        self.sel0 + 5
    }

    // -- §4.6 leg 5: carries. --
    /// `cSa1`.
    pub fn c_sa1(&self) -> usize {
        self.car0
    }
    /// `cCarryA`.
    pub fn c_carry_a(&self) -> usize {
        self.car0 + 1
    }
    /// `cSb1`.
    pub fn c_sb1(&self) -> usize {
        self.car0 + 2
    }
    /// `cCarryB`.
    pub fn c_carry_b(&self) -> usize {
        self.car0 + 3
    }
    /// `carryCol i`.
    pub fn carry_col(&self, i: usize) -> usize {
        if i == 0 {
            self.c_carry_a()
        } else {
            self.c_carry_b()
        }
    }

    // -- §4.6 leg 6: flow-through chain. --
    /// `cNBnz`.
    pub fn c_n_bnz(&self) -> usize {
        self.ft0
    }
    /// `cNOccb`.
    pub fn c_n_occb(&self) -> usize {
        self.ft0 + 1
    }
    /// `cNEqba`.
    pub fn c_n_eqba(&self) -> usize {
        self.ft0 + 2
    }
    /// `cFa1`.
    pub fn c_fa1(&self) -> usize {
        self.ft0 + 3
    }
    /// `cFa2`.
    pub fn c_fa2(&self) -> usize {
        self.ft0 + 4
    }
    /// `cFa3`.
    pub fn c_fa3(&self) -> usize {
        self.ft0 + 5
    }
    /// `cFtA`.
    pub fn c_ft_a(&self) -> usize {
        self.ft0 + 6
    }
    /// `cNAnz`.
    pub fn c_n_anz(&self) -> usize {
        self.ft0 + 7
    }
    /// `cNOcca`.
    pub fn c_n_occa(&self) -> usize {
        self.ft0 + 8
    }
    /// `cNEqab`.
    pub fn c_n_eqab(&self) -> usize {
        self.ft0 + 9
    }
    /// `cFb1`.
    pub fn c_fb1(&self) -> usize {
        self.ft0 + 10
    }
    /// `cFb2`.
    pub fn c_fb2(&self) -> usize {
        self.ft0 + 11
    }
    /// `cFb3`.
    pub fn c_fb3(&self) -> usize {
        self.ft0 + 12
    }
    /// `cFtB`.
    pub fn c_ft_b(&self) -> usize {
        self.ft0 + 13
    }
    /// The `ft` column of piece `i`.
    pub fn ft_col(&self, i: usize) -> usize {
        if i == 0 { self.c_ft_a() } else { self.c_ft_b() }
    }

    // -- §4.6 leg 7: write-mid one-hots. --
    /// `wSrcRow i j`.
    pub fn w_src_row(&self, i: usize, j: usize) -> usize {
        self.wr0 + (4 * self.n) * i + j
    }
    /// `wSrcCol i j`.
    pub fn w_src_col(&self, i: usize, j: usize) -> usize {
        self.wr0 + (4 * self.n) * i + self.n + j
    }
    /// `wDstRow i j`.
    pub fn w_dst_row(&self, i: usize, j: usize) -> usize {
        self.wr0 + (4 * self.n) * i + 2 * self.n + j
    }
    /// `wDstCol i j`.
    pub fn w_dst_col(&self, i: usize, j: usize) -> usize {
        self.wr0 + (4 * self.n) * i + 3 * self.n + j
    }
    /// `particleCol i` (== `cFp (mvBase i)`).
    pub fn particle_col(&self, i: usize) -> usize {
        self.c_fp(self.mv_base(i))
    }

    // -- leg 8: packed commitment. --
    /// `packOldFelt j`.
    pub fn pack_old_felt(&self, j: usize) -> usize {
        self.mh0 + j
    }
    /// `packMidFelt j`.
    pub fn pack_mid_felt(&self, j: usize) -> usize {
        self.mh0 + self.rfc + j
    }

    // -- CHUNK-1: inclusive occlusion. --
    /// `inclBase w`.
    pub fn incl_base(&self, w: usize) -> usize {
        self.incl0 + incl_mv_width() * w
    }
    /// `cMsumIncl w`.
    pub fn c_msum_incl(&self, w: usize) -> usize {
        self.incl_base(w)
    }
    /// `cOccIncl w`.
    pub fn c_occ_incl(&self, w: usize) -> usize {
        self.incl_base(w) + 1
    }
    /// `occInclBit w k`.
    pub fn occ_incl_bit(&self, w: usize, k: usize) -> usize {
        self.incl_base(w) + 2 + k
    }

    // -- CHUNK-1: non-leaver. --
    /// `nlBase i`.
    pub fn nl_base(&self, i: usize) -> usize {
        self.nl0 + nl_piece_width() * i
    }
    /// `cLandOld i`.
    pub fn c_land_old(&self, i: usize) -> usize {
        self.nl_base(i)
    }
    /// `cLandNz i`.
    pub fn c_land_nz(&self, i: usize) -> usize {
        self.nl_base(i) + 1
    }
    /// `landNzBit i k`.
    pub fn land_nz_bit(&self, i: usize, k: usize) -> usize {
        self.nl_base(i) + 2 + k
    }
    /// `cNonLeave i`.
    pub fn c_non_leave(&self, i: usize) -> usize {
        self.nl_base(i) + 2 + SMALL_RBITS
    }

    // -- CHUNK-1: resolvable surface. --
    /// `cDestX i`.
    pub fn c_dest_x(&self, i: usize) -> usize {
        self.resr0 + 2 * i
    }
    /// `cDestY i`.
    pub fn c_dest_y(&self, i: usize) -> usize {
        self.resr0 + 2 * i + 1
    }
    /// `cResEq`.
    pub fn c_res_eq(&self) -> usize {
        self.c_eq_bit(self.res_eq_base)
    }
    /// `cIdent`.
    pub fn c_ident(&self) -> usize {
        self.resr_logic
    }
    /// `cBothCarry`.
    pub fn c_both_carry(&self) -> usize {
        self.resr_logic + 1
    }
    /// `cMc1`.
    pub fn c_mc1(&self) -> usize {
        self.resr_logic + 2
    }
    /// `cNotIdent`.
    pub fn c_not_ident(&self) -> usize {
        self.resr_logic + 3
    }
    /// `cMerge`.
    pub fn c_merge(&self) -> usize {
        self.resr_logic + 4
    }
    /// `cBadA`.
    pub fn c_bad_a(&self) -> usize {
        self.resr_logic + 5
    }
    /// `cBadB`.
    pub fn c_bad_b(&self) -> usize {
        self.resr_logic + 6
    }
    /// `cNMerge`.
    pub fn c_n_merge(&self) -> usize {
        self.resr_logic + 7
    }
    /// `cNBadA`.
    pub fn c_n_bad_a(&self) -> usize {
        self.resr_logic + 8
    }
    /// `cNBadB`.
    pub fn c_n_bad_b(&self) -> usize {
        self.resr_logic + 9
    }
    /// `cR1`.
    pub fn c_r1(&self) -> usize {
        self.resr_logic + 10
    }
    /// `cResolvable`.
    pub fn c_resolvable(&self) -> usize {
        self.resr_logic + 11
    }

    // -- CHUNK-3: corrected carry. --
    /// `cv2Base i`.
    pub fn cv2_base(&self, i: usize) -> usize {
        self.cv2_0 + 3 * i
    }
    /// `cCv1 i`.
    pub fn c_cv1(&self, i: usize) -> usize {
        self.cv2_base(i)
    }
    /// `cCv2 i`.
    pub fn c_cv2(&self, i: usize) -> usize {
        self.cv2_base(i) + 1
    }
    /// `cCarryV2 i`.
    pub fn c_carry_v2(&self, i: usize) -> usize {
        self.cv2_base(i) + 2
    }

    // -- CHUNK-5: corrected flow-through. --
    /// `cNOccIb`.
    pub fn c_n_occ_ib(&self) -> usize {
        self.ftv2_0
    }
    /// `cFtV2a1`.
    pub fn c_ft_v2a1(&self) -> usize {
        self.ftv2_0 + 1
    }
    /// `cFtV2a2`.
    pub fn c_ft_v2a2(&self) -> usize {
        self.ftv2_0 + 2
    }
    /// `cFtV2a3`.
    pub fn c_ft_v2a3(&self) -> usize {
        self.ftv2_0 + 3
    }
    /// `cFtV2A`.
    pub fn c_ft_v2_a(&self) -> usize {
        self.ftv2_0 + 4
    }
    /// `cNOccIa`.
    pub fn c_n_occ_ia(&self) -> usize {
        self.ftv2_0 + 5
    }
    /// `cFtV2b1`.
    pub fn c_ft_v2b1(&self) -> usize {
        self.ftv2_0 + 6
    }
    /// `cFtV2b2`.
    pub fn c_ft_v2b2(&self) -> usize {
        self.ftv2_0 + 7
    }
    /// `cFtV2b3`.
    pub fn c_ft_v2b3(&self) -> usize {
        self.ftv2_0 + 8
    }
    /// `cFtV2B`.
    pub fn c_ft_v2_b(&self) -> usize {
        self.ftv2_0 + 9
    }
    /// The corrected `ftV2` column of piece `i`.
    pub fn ft_v2_col(&self, i: usize) -> usize {
        if i == 0 {
            self.c_ft_v2_a()
        } else {
            self.c_ft_v2_b()
        }
    }

    // -- CHUNK-5: corrected dst one-hots. --
    /// `wDstV2Row i j`.
    pub fn w_dst_v2_row(&self, i: usize, j: usize) -> usize {
        self.wrv2_0 + (2 * self.n) * i + j
    }
    /// `wDstV2Col i j`.
    pub fn w_dst_v2_col(&self, i: usize, j: usize) -> usize {
        self.wrv2_0 + (2 * self.n) * i + self.n + j
    }

    // -- CHUNK-5: corrected non-leaver. --
    /// `nlV2Base i`.
    pub fn nl_v2_base(&self, i: usize) -> usize {
        self.nlv2_0 + nl_piece_width() * i
    }
    /// `cLandOldV2 i`.
    pub fn c_land_old_v2(&self, i: usize) -> usize {
        self.nl_v2_base(i)
    }
    /// `cLandNzV2 i`.
    pub fn c_land_nz_v2(&self, i: usize) -> usize {
        self.nl_v2_base(i) + 1
    }
    /// `landNzV2Bit i k`.
    pub fn land_nz_v2_bit(&self, i: usize, k: usize) -> usize {
        self.nl_v2_base(i) + 2 + k
    }
    /// `cNonLeaveV2 i`.
    pub fn c_non_leave_v2(&self, i: usize) -> usize {
        self.nl_v2_base(i) + 2 + SMALL_RBITS
    }

    // -- CHUNK-5: corrected carry V3. --
    /// `cCarryV3 i`.
    pub fn c_carry_v3(&self, i: usize) -> usize {
        self.cv3_0 + i
    }

    // -- CHUNK-5: corrected resolvable surface. --
    /// `cDestV2X i`.
    pub fn c_dest_v2_x(&self, i: usize) -> usize {
        self.resrv2_0 + 2 * i
    }
    /// `cDestV2Y i`.
    pub fn c_dest_v2_y(&self, i: usize) -> usize {
        self.resrv2_0 + 2 * i + 1
    }
    /// `cResEqV2`.
    pub fn c_res_eq_v2(&self) -> usize {
        self.c_eq_bit(self.res_eq_v2_base)
    }
    /// `cIdentV2`.
    pub fn c_ident_v2(&self) -> usize {
        self.resrv2_logic
    }
    /// `cBothCarryV2`.
    pub fn c_both_carry_v2(&self) -> usize {
        self.resrv2_logic + 1
    }
    /// `cMc1V2`.
    pub fn c_mc1_v2(&self) -> usize {
        self.resrv2_logic + 2
    }
    /// `cNotIdentV2`.
    pub fn c_not_ident_v2(&self) -> usize {
        self.resrv2_logic + 3
    }
    /// `cMergeV2`.
    pub fn c_merge_v2(&self) -> usize {
        self.resrv2_logic + 4
    }
    /// `cBadV2A`.
    pub fn c_bad_v2_a(&self) -> usize {
        self.resrv2_logic + 5
    }
    /// `cBadV2B`.
    pub fn c_bad_v2_b(&self) -> usize {
        self.resrv2_logic + 6
    }
    /// `cNMergeV2`.
    pub fn c_n_merge_v2(&self) -> usize {
        self.resrv2_logic + 7
    }
    /// `cNBadV2A`.
    pub fn c_n_bad_v2_a(&self) -> usize {
        self.resrv2_logic + 8
    }
    /// `cNBadV2B`.
    pub fn c_n_bad_v2_b(&self) -> usize {
        self.resrv2_logic + 9
    }
    /// `cR1V2`.
    pub fn c_r1_v2(&self) -> usize {
        self.resrv2_logic + 10
    }
    /// `cResolvableV2`.
    pub fn c_resolvable_v2(&self) -> usize {
        self.resrv2_logic + 11
    }

    // -- CHUNK-6: 2-cycle detector + final board. --
    /// `cTwoCyc1`.
    pub fn c_two_cyc1(&self) -> usize {
        self.v4_0
    }
    /// `cTwoCyc2`.
    pub fn c_two_cyc2(&self) -> usize {
        self.v4_0 + 1
    }
    /// `cTwoCyc`.
    pub fn c_two_cyc(&self) -> usize {
        self.v4_0 + 2
    }
    /// `cNTwoCyc`.
    pub fn c_n_two_cyc(&self) -> usize {
        self.v4_0 + 3
    }
    /// `cCarryV4 i`.
    pub fn c_carry_v4(&self, i: usize) -> usize {
        self.cv4_0 + i
    }
    /// The 2-cycle-gated carry column of piece `i`.
    pub fn carry_v4_col(&self, i: usize) -> usize {
        self.c_carry_v4(i)
    }
    /// `cWBoardV4 c`.
    pub fn c_w_board_v4(&self, c: usize) -> usize {
        self.midv4_0 + c
    }
    /// `cMidV4 c` — the FINAL corrected mid board cell (== `roundStep`'s board).
    pub fn c_mid_v4(&self, c: usize) -> usize {
        self.midv4_0 + self.kk + c
    }

    // -- PI ABI. --
    /// `AUTO_PI_BASE = 16 + 2·RFC`.
    pub fn auto_pi_base(&self) -> usize {
        16 + 2 * self.rfc
    }
    /// The PI window base of `pack(old)` (== `COMMIT_PI_BASE = 16`).
    pub fn pack_in_pi_base(&self) -> usize {
        16
    }
    /// The PI window base of `pack(mid)` (== `16 + RFC`).
    pub fn pack_out_pi_base(&self) -> usize {
        16 + self.rfc
    }
}

/// The by-name loader identity of the Lean Leg-R resolve descriptor for board size `n`. Emitted
/// for `n ∈ {2, 11}` (`metatheory/EmitByName.lean`).
pub fn resolve_descriptor_name(n: usize) -> &'static str {
    match n {
        2 => "dregg-automatafl-resolve-n2",
        11 => "dregg-automatafl-resolve-n11",
        _ => "dregg-automatafl-resolve-unknown",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The GOLDEN-SHAPE canary: the layout width computed purely from `n = 11` by the `NGen`
    /// formulas matches the emitted n=11 descriptor's 1273-wide trace, and the PI count matches
    /// the 36-PI ABI. This is the fail-closed guard that turns the V2/V3 cutover into a visible
    /// mismatch rather than a silent mis-fill.
    #[test]
    fn n11_layout_matches_emitted_descriptor_shape() {
        let l = ResolveLayout::new(11);
        assert_eq!(
            l.width(),
            1273,
            "R_WIDTH 11 must equal the emitted trace_width"
        );
        assert_eq!(
            l.pi_count(),
            36,
            "R_PI_COUNT 11 must equal the emitted PI count"
        );
        assert_eq!(l.rfc, 9, "feltCount 11 = ⌈121/15⌉ = 9");
        assert_eq!(l.cr, 4, "COORD_RBITS 11 = ⌊log2 10⌋ + 1 = 4");
        assert_eq!(l.auto_pi_base(), 34, "AUTO_PI_BASE 11 = 16 + 2·9");
    }

    /// The n=2 instance matches the byte-golden `automataflResolveDesc` (441w / 20pi).
    #[test]
    fn n2_layout_matches_byte_golden() {
        let l = ResolveLayout::new(2);
        assert_eq!(l.width(), 441, "R_WIDTH 2 == the byte-golden 441");
        assert_eq!(l.pi_count(), 20);
        assert_eq!(l.rfc, 1);
        assert_eq!(l.cr, 1);
    }

    /// A tiling canary mirroring the Lean `#guard`s: the packed felts abut the CHUNK-1 tail
    /// (`packMidFelt (RFC-1) + 1 == INCL0`), and the occlusion blocks abut `RES0`.
    #[test]
    fn family_bases_tile() {
        let l = ResolveLayout::new(11);
        assert_eq!(l.pack_mid_felt(l.rfc - 1) + 1, l.incl0);
        assert_eq!(l.c_resolvable() + 1, l.cv2_0);
        assert_eq!(l.mid(l.kk - 1) + 1, l.one());
        // MIDV4 tail is the last block: cMidV4 (KK-1) is the final trace column.
        assert_eq!(l.c_mid_v4(l.kk - 1) + 1, l.width());
    }
}
