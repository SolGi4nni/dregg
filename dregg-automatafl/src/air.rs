//! The hand-authored automatafl board-transition AIR, staged D1/D2/D3. Each stage
//! is built together with its honest witness by driving the reference oracle
//! (`crate::reference`); `Builder::air_accepts` then re-checks the emitted DSL
//! constraints over that row. Translation validation: the reference computes the
//! next board OFF-circuit; the AIR RE-CHECKS `new == apply_turn(old, moves)` with
//! low-degree gates + random-access board reads (one-hot dot products) + a
//! bit-decomposition range gadget for the automaton's distance comparisons.

use dregg_circuit::dsl::circuit::ColumnKind;

use crate::builder::{Builder, Head};
use crate::reference::{
    self as r, AUTO, Board, DIRS, SCORE_ATT, SCORE_PRI, automaton_sense, automaton_step,
};

/// Placeholder cell-state door roots for the AIR SELF-TESTS (`air_accepts`, size/refinement).
/// The door prefix `[old8 ‖ new8]` is opaque to the board AIR — it is `add_pi`'d and
/// fold-connected to the leg's real rotated roots, never constrained here — so any 8-felt
/// values serve the fast battery. The FOLD driver supplies the leg's GENUINE roots instead.
pub fn placeholder_roots() -> (
    [dregg_circuit::field::BabyBear; 8],
    [dregg_circuit::field::BabyBear; 8],
) {
    use dregg_circuit::field::BabyBear;
    (
        core::array::from_fn(|i| BabyBear::new(100 + i as u32)),
        core::array::from_fn(|i| BabyBear::new(200 + i as u32)),
    )
}

/// Range width for the score comparison (scores < 4*PRI ≈ 4e5 < 2^19).
const SCORE_RBITS: usize = 20;
/// Range width for small distance/coordinate comparisons (values < N ≤ 9 < 2^4).
const SMALL_RBITS: usize = 5;

/// Allocate board columns from a board's cells; returns the K column indices.
fn alloc_board(b: &mut Builder, tag: &str, board: &Board) -> Vec<usize> {
    (0..board.n * board.n)
        .map(|i| {
            b.alloc(
                format!("{tag}_{i}"),
                ColumnKind::Value,
                board.cells[i] as i128,
            )
        })
        .collect()
}

/// The score head `variant*PRI - att*ATT - rep` (linear in the decision columns).
fn score_head(variant: usize, att: usize, rep: usize) -> Head {
    Head::lin(SCORE_PRI as i128, variant)
        .add_lin(-(SCORE_ATT as i128), att)
        .add_lin(-1, rep)
}

/// Validate + emit the per-axis decision (`evaluate_axis`) as witnessed fields
/// `(variant, pos, att, rep)`, checked against the two rays via the 9-case truth
/// table gated by one-hot indicators on `(pw, nw)`, with `dist>1` / `dist` compares
/// discharged by the range gadget. Returns the four column indices.
#[allow(clippy::too_many_arguments)]
fn decide_axis(
    b: &mut Builder,
    tag: &str,
    pw_col: usize,
    nw_col: usize,
    pd_col: usize,
    nd_col: usize,
    pw: usize,
    nw: usize,
    pd: usize,
    nd: usize,
    dec: &r::Decision,
) -> (usize, usize, usize, usize) {
    // Witnessed decision fields.
    let variant = b.alloc(format!("{tag}_var"), ColumnKind::Value, dec.variant as i128);
    b.assert_member(variant, &[0, 1, 2, 3]);
    let pos = b.alloc(format!("{tag}_pos"), ColumnKind::Binary, dec.pos as i128);
    b.assert_binary(pos);
    let att = b.alloc(
        format!("{tag}_att"),
        ColumnKind::Value,
        dec.att_dist as i128,
    );
    let rep = b.alloc(
        format!("{tag}_rep"),
        ColumnKind::Value,
        dec.rep_dist as i128,
    );

    // One-hot indicators on pw, nw over {0,1,2}.
    let ipw = b.one_hot(&format!("{tag}_ipw"), 3, pw, &Head::lin(1, pw_col));
    let inw = b.one_hot(&format!("{tag}_inw"), 3, nw, &Head::lin(1, nw_col));

    // Guard / comparison bits (independently forced correct by the range gadget).
    // gpd = [pd>1], gnd = [nd>1].
    let gpd = b.forced_ge0(
        &format!("{tag}_gpd"),
        &Head::lin(1, pd_col).add_const(-2),
        pd as i128 - 2,
        SMALL_RBITS,
    );
    let gnd = b.forced_ge0(
        &format!("{tag}_gnd"),
        &Head::lin(1, nd_col).add_const(-2),
        nd as i128 - 2,
        SMALL_RBITS,
    );
    // lt = [pd<nd], gt = [pd>nd], le = [pd<=nd].
    let lt = b.forced_ge0(
        &format!("{tag}_lt"),
        &Head::lin(1, nd_col).add_lin(-1, pd_col).add_const(-1),
        nd as i128 - pd as i128 - 1,
        SMALL_RBITS,
    );
    let gt = b.forced_ge0(
        &format!("{tag}_gt"),
        &Head::lin(1, pd_col).add_lin(-1, nd_col).add_const(-1),
        pd as i128 - nd as i128 - 1,
        SMALL_RBITS,
    );
    let le = b.forced_ge0(
        &format!("{tag}_le"),
        &Head::lin(1, nd_col).add_lin(-1, pd_col),
        nd as i128 - pd as i128,
        SMALL_RBITS,
    );
    // min(pd,nd) = le*pd + (1-le)*nd.
    let minv = pd.min(nd);
    let min_col = b.alloc(format!("{tag}_min"), ColumnKind::Value, minv as i128);
    // min - (le*pd + (1-le)*nd) == 0  =>  min - le*pd - nd + le*nd == 0
    b.assert_zero(
        &Head::lin(1, min_col)
            .add_prod(-1, vec![le, pd_col])
            .add_lin(-1, nd_col)
            .add_prod(1, vec![le, nd_col]),
    );
    // gmin = [min>1].
    let gmin = b.forced_ge0(
        &format!("{tag}_gmin"),
        &Head::lin(1, min_col).add_const(-2),
        minv as i128 - 2,
        SMALL_RBITS,
    );

    // The 9-case truth table. For each (i,j) in {0,1,2}^2, under gate ipw[i]*inw[j]
    // assert the four fields equal evaluate_axis's result for that case. Formulas use
    // the guard/cmp bit columns; when a variant is None every field is 0.
    // A formula field is given as a Head; we assert gate*(field_col - formula) == 0 by
    // expanding into `gate` products.
    let assert_case = |b: &mut Builder, gate: &[usize], field_col: usize, formula: &Head| {
        // (field_col - formula) * gate == 0, gate = product of the gate columns.
        let mut h = Head::zero();
        // + field_col * gate
        {
            let mut cols = gate.to_vec();
            cols.push(field_col);
            h = h.add_prod(1, cols);
        }
        // - formula * gate
        for (coeff, cols) in &formula.terms {
            let mut cc = gate.to_vec();
            cc.extend(cols.iter().copied());
            h = h.add_prod(-coeff, cc);
        }
        if formula.constant != 0 {
            let mut cc = gate.to_vec();
            h = h.add_prod(-formula.constant, cc.drain(..).collect());
        }
        b.assert_zero(&h);
    };

    // Case formula tables, indexed by (pw=i, nw=j). Each returns (var,pos,att,rep) Heads.
    // VAC=0, REP=1, ATT=2.
    let zero = Head::zero();
    let cases: [((usize, usize), [Head; 4]); 9] = [
        // (2,1) ATT,REP: UP if gpd. var=3gpd,pos=gpd,att=gpd*pd,rep=gpd*nd
        (
            (2, 1),
            [
                Head::lin(3, gpd),
                Head::lin(1, gpd),
                Head::zero().add_prod(1, vec![gpd, pd_col]),
                Head::zero().add_prod(1, vec![gpd, nd_col]),
            ],
        ),
        // (1,2) REP,ATT: UP if gnd. var=3gnd,pos=0,att=gnd*nd,rep=gnd*pd
        (
            (1, 2),
            [
                Head::lin(3, gnd),
                zero.clone(),
                Head::zero().add_prod(1, vec![gnd, nd_col]),
                Head::zero().add_prod(1, vec![gnd, pd_col]),
            ],
        ),
        // (1,1) REP,REP: FromRep if pd!=nd. var=2(lt+gt),pos=gt,att=0,rep=(lt+gt)*min
        (
            (1, 1),
            [
                Head::lin(2, lt).add_lin(2, gt),
                Head::lin(1, gt),
                zero.clone(),
                Head::zero()
                    .add_prod(1, vec![lt, min_col])
                    .add_prod(1, vec![gt, min_col]),
            ],
        ),
        // (1,0) REP,VAC: FromRep if gnd. var=2gnd,pos=0,att=0,rep=gnd*pd
        (
            (1, 0),
            [
                Head::lin(2, gnd),
                zero.clone(),
                zero.clone(),
                Head::zero().add_prod(1, vec![gnd, pd_col]),
            ],
        ),
        // (0,1) VAC,REP: FromRep if gpd. var=2gpd,pos=gpd,att=0,rep=gpd*nd
        (
            (0, 1),
            [
                Head::lin(2, gpd),
                Head::lin(1, gpd),
                zero.clone(),
                Head::zero().add_prod(1, vec![gpd, nd_col]),
            ],
        ),
        // (2,2) ATT,ATT: TowardAtt if (pd!=nd & min>1). cond=(lt+gt)*gmin. var=cond,pos=lt,att=cond*min,rep=0
        (
            (2, 2),
            [
                Head::zero()
                    .add_prod(1, vec![lt, gmin])
                    .add_prod(1, vec![gt, gmin]),
                // pos = pd<nd MASKED by the fire condition (NONE has pos=false): lt*gmin
                Head::zero().add_prod(1, vec![lt, gmin]),
                Head::zero()
                    .add_prod(1, vec![lt, gmin, min_col])
                    .add_prod(1, vec![gt, gmin, min_col]),
                zero.clone(),
            ],
        ),
        // (2,0) ATT,VAC: TowardAtt if gpd. var=gpd,pos=gpd,att=gpd*pd,rep=0
        (
            (2, 0),
            [
                Head::lin(1, gpd),
                Head::lin(1, gpd),
                Head::zero().add_prod(1, vec![gpd, pd_col]),
                zero.clone(),
            ],
        ),
        // (0,2) VAC,ATT: TowardAtt if gnd. var=gnd,pos=0,att=gnd*nd,rep=0
        (
            (0, 2),
            [
                Head::lin(1, gnd),
                zero.clone(),
                Head::zero().add_prod(1, vec![gnd, nd_col]),
                zero.clone(),
            ],
        ),
        // (0,0) VAC,VAC: None. all 0
        (
            (0, 0),
            [zero.clone(), zero.clone(), zero.clone(), zero.clone()],
        ),
    ];
    let fields = [variant, pos, att, rep];
    for ((i, j), formulas) in &cases {
        let gate = [ipw[*i], inw[*j]];
        for (fc, formula) in fields.iter().zip(formulas.iter()) {
            assert_case(b, &gate, *fc, formula);
        }
    }
    (variant, pos, att, rep)
}

/// THE AUTOMATON GADGET. Emits constraints validating `out_cols == automaton_step(src)`,
/// where `src` is the board held in `board_cols`. Random-access reads (auto pin, the 4
/// raycasts, the step target) are one-hot dot products; the decision derivation is the
/// score-compared `evaluate_axis`/`choose_offset` truth table.
fn automaton_gadget(
    b: &mut Builder,
    n: usize,
    board_cols: &[usize],
    src: &Board,
    out_cols: &[usize],
) {
    let k = n * n;
    let sense = automaton_sense(src);
    let (ax, ay) = src.auto;

    // --- automaton position (ax,ay), pinned so board[n*ay+ax] == AUTO ---
    let ax_col = b.alloc("ax", ColumnKind::Value, ax as i128);
    let ay_col = b.alloc("ay", ColumnKind::Value, ay as i128);
    // Range-pin each coord to 0..=n-1 by bit-decomposition (degree ≤ 2), not the degree-n
    // membership product — the same range, under the constraint-degree cap as the board grows.
    b.decompose_coord_le("ax", ax_col, n as i128 - 1);
    b.decompose_coord_le("ay", ay_col, n as i128 - 1);
    // Row×column √n read (C.2): pin the auto row/column with two n-wide one-hots
    // (`sel_auto_row[ay]`, `sel_auto_col[ax]`) instead of one k-wide one-hot. The cell
    // `(x,y)` is addressed by the product `sel_auto_row[y]·sel_auto_col[x]`.
    let (sel_auto_row, sel_auto_col) = b.one_hot_rowcol(
        "auto",
        n,
        ax as usize,
        &Head::lin(1, ax_col),
        ay as usize,
        &Head::lin(1, ay_col),
    );
    // pin src[auto] == AUTO: AUTO == Σ_y Σ_x sel_row[y]·sel_col[x]·board[y·n+x].
    let mut h = Head::c(-(AUTO as i128));
    for y in 0..n {
        for x in 0..n {
            h = h.add_prod(
                1,
                vec![sel_auto_row[y], sel_auto_col[x], board_cols[y * n + x]],
            );
        }
    }
    b.assert_zero(&h);

    // --- the four rays ---
    // Per ray, materialize M=n steps; validate first-non-vacuum-or-wall termination.
    let mut ray_what = [0usize; 4];
    let mut ray_dist = [0usize; 4];
    let mut what_cols = [0usize; 4];
    let mut dist_cols = [0usize; 4];
    for (d, &(dx, dy)) in DIRS.iter().enumerate() {
        let ray = sense.rays[d];
        ray_what[d] = ray.what as usize;
        ray_dist[d] = ray.dist;
        let dtag = format!("ray{d}");

        // Per-step in-bounds bit + gated read.
        let mut rc_cols: Vec<usize> = Vec::with_capacity(n);
        let mut ib_cols: Vec<usize> = Vec::with_capacity(n);
        for kk in 1..=n {
            let cx = ax + (kk as i32) * dx;
            let cy = ay + (kk as i32) * dy;
            // In-bounds along the varying axis (the other axis is constant & in-range).
            let (d_head, d_val) = if dx == 1 {
                (
                    Head::c(n as i128 - 1 - kk as i128).add_lin(-1, ax_col),
                    n as i128 - 1 - kk as i128 - ax as i128,
                )
            } else if dx == -1 {
                (
                    Head::lin(1, ax_col).add_const(-(kk as i128)),
                    ax as i128 - kk as i128,
                )
            } else if dy == 1 {
                (
                    Head::c(n as i128 - 1 - kk as i128).add_lin(-1, ay_col),
                    n as i128 - 1 - kk as i128 - ay as i128,
                )
            } else {
                (
                    Head::lin(1, ay_col).add_const(-(kk as i128)),
                    ay as i128 - kk as i128,
                )
            };
            let ib = b.forced_ge0(&format!("{dtag}_ib{kk}"), &d_head, d_val, SMALL_RBITS);
            ib_cols.push(ib);
            // Read src[cell] gated by ib (0 when OOB = wall vacuum). The cell sits at a
            // COMPILE-TIME flat offset from the auto pin, so we REUSE `sel_auto` (the proven
            // auto one-hot) shifted by `off` instead of allocating a fresh n² one-hot per step
            // — the ray-scan reduction that collapses the 4n³ selector blowup to n².
            let cell_val = src.cell_at((cx, cy)) as i128; // 0 if OOB
            let rc = b.alloc(format!("{dtag}_rc{kk}"), ColumnKind::Value, cell_val);
            // Reuse the auto row×column one-hots shifted by the cardinal step (sx,sy) =
            // (kk·dx, kk·dy) — no fresh selectors, exactly as the flat ray scan reused
            // `sel_auto`, now over the row×column pair.
            let sx = kk as i128 * dx as i128;
            let sy = kk as i128 * dy as i128;
            b.shifted_read_rowcol_gated(
                &sel_auto_row,
                &sel_auto_col,
                board_cols,
                n,
                ib,
                sx,
                sy,
                rc,
            );
            rc_cols.push(rc);
        }

        // Hit one-hot over steps 1..M selecting dist.
        let hit = {
            let mut sel = Vec::with_capacity(n);
            for kk in 1..=n {
                let v = if kk == ray.dist { 1 } else { 0 };
                let c = b.alloc(format!("{dtag}_hit{kk}"), ColumnKind::Binary, v);
                b.assert_binary(c);
                sel.push(c);
            }
            // Σ hit == 1
            let mut s = Head::c(-1);
            for &c in &sel {
                s = s.add_lin(1, c);
            }
            b.assert_zero(&s);
            sel
        };
        // dist = Σ kk*hit_kk
        let dist_col = b.alloc(format!("{dtag}_dist"), ColumnKind::Value, ray.dist as i128);
        {
            let mut h = Head::lin(-1, dist_col);
            for (i, &c) in hit.iter().enumerate() {
                h = h.add_lin((i + 1) as i128, c);
            }
            b.assert_zero(&h);
        }
        // what = Σ hit_kk*rc_kk
        let what_col = b.alloc(format!("{dtag}_what"), ColumnKind::Value, ray.what as i128);
        b.assert_member(what_col, &[0, 1, 2]);
        {
            let mut h = Head::lin(-1, what_col);
            for kk in 0..n {
                h = h.add_prod(1, vec![hit[kk], rc_cols[kk]]);
            }
            b.assert_zero(&h);
        }
        // before_kk = Σ_{j>kk} hit_j.  before*rc==0 (vacuum before hit) and
        // before*(1-ib)==0 (in-bounds before hit).
        for kk in 0..n {
            // vacuum-before: Σ_{j>kk} hit_j * rc_kk == 0
            let mut hv = Head::zero();
            for j in (kk + 1)..n {
                hv = hv.add_prod(1, vec![hit[j], rc_cols[kk]]);
            }
            b.assert_zero(&hv);
            // in-bounds-before: Σ_{j>kk} hit_j * (1 - ib_kk) == 0
            let mut hi = Head::zero();
            for j in (kk + 1)..n {
                hi = hi
                    .add_lin(1, hit[j])
                    .add_prod(-1, vec![hit[j], ib_cols[kk]]);
            }
            b.assert_zero(&hi);
        }
        // hib = ib at hit; OOB hit => what==0; in-bounds hit => what!=0.
        let hib = {
            let mut hv = 0i128;
            for kk in 0..n {
                hv += (b.value(hit[kk]).0 as i128) * (b.value(ib_cols[kk]).0 as i128);
            }
            let c = b.alloc(format!("{dtag}_hib"), ColumnKind::Binary, hv);
            let mut h = Head::lin(-1, c);
            for kk in 0..n {
                h = h.add_prod(1, vec![hit[kk], ib_cols[kk]]);
            }
            b.assert_zero(&h);
            c
        };
        // (1 - hib) * what == 0
        b.assert_zero(&Head::lin(1, what_col).add_prod(-1, vec![hib, what_col]));
        // hib * (what != 0)
        b.cond_nonzero(&format!("{dtag}_hnz"), hib, what_col, ray.what as i128);

        what_cols[d] = what_col;
        dist_cols[d] = dist_col;
    }

    // --- decisions per axis ---
    let (xv, xp, xa, xr) = decide_axis(
        b,
        "xdec",
        what_cols[0],
        what_cols[1],
        dist_cols[0],
        dist_cols[1],
        ray_what[0],
        ray_what[1],
        ray_dist[0],
        ray_dist[1],
        &sense.x_dec,
    );
    let (yv, yp, ya, yr) = decide_axis(
        b,
        "ydec",
        what_cols[2],
        what_cols[3],
        dist_cols[2],
        dist_cols[3],
        ray_what[2],
        ray_what[3],
        ray_dist[2],
        ray_dist[3],
        &sense.y_dec,
    );

    // --- choose_offset via score comparison ---
    let sx = score_head(xv, xa, xr);
    let sy = score_head(yv, ya, yr);
    let score_x = r::decision_score(&sense.x_dec);
    let score_y = r::decision_score(&sense.y_dec);
    // sgt = [sx>sy], slt=[sx<sy]
    let sgt = b.forced_ge0(
        "sgt",
        &sx.clone().append(&sy.clone().scale(-1)).add_const(-1),
        (score_x - score_y - 1) as i128,
        SCORE_RBITS,
    );
    let slt = b.forced_ge0(
        "slt",
        &sy.clone().append(&sx.clone().scale(-1)).add_const(-1),
        (score_y - score_x - 1) as i128,
        SCORE_RBITS,
    );
    // xmove=[variant_x!=0], ymove=[variant_y!=0]
    let xmove = b.forced_ge0(
        "xmove",
        &Head::lin(1, xv).add_const(-1),
        sense.x_dec.variant as i128 - 1,
        SMALL_RBITS,
    );
    let ymove = b.forced_ge0(
        "ymove",
        &Head::lin(1, yv).add_const(-1),
        sense.y_dec.variant as i128 - 1,
        SMALL_RBITS,
    );
    // column rule (pinned to the board's flag)
    let col = b.alloc("col", ColumnKind::Binary, src.col_rule as i128);
    b.assert_binary(col);
    b.assert_zero(&Head::lin(1, col).add_const(-(src.col_rule as i128)));

    // offset ox,oy in {-1,0,1}
    let (ox, oy) = sense.offset;
    let ox_col = b.alloc("ox", ColumnKind::Value, ox as i128);
    let oy_col = b.alloc("oy", ColumnKind::Value, oy as i128);
    b.assert_member(ox_col, &[-1, 0, 1]);
    b.assert_member(oy_col, &[-1, 0, 1]);
    // ox = sgt*xmove*(2*posx-1)  => ox - 2*sgt*xmove*posx + sgt*xmove == 0
    b.assert_zero(
        &Head::lin(1, ox_col)
            .add_prod(-2, vec![sgt, xmove, xp])
            .add_prod(1, vec![sgt, xmove]),
    );
    // ywins = slt + seq*col, seq = 1 - sgt - slt (tie).  oy = ywins*ymove*(2*posy-1)
    // Expand ywins*ymove*(2posy-1):
    //   ywins = slt + (1 - sgt - slt)*col = slt + col - sgt*col - slt*col
    // oy - [ (2posy-1) * ymove * ywins ] == 0.
    // Let f = (2posy-1)*ymove = 2*ymove*posy - ymove. Then oy - f*ywins == 0.
    //   f*ywins = f*slt + f*col - f*sgt*col - f*slt*col
    // with f = 2*ymove*posy - ymove. Expand each term.
    {
        // helper closure to push f*<gatecols> with sign
        let mut hh = Head::lin(1, oy_col);
        let push_f = |hh: &mut Head, sign: i128, extra: &[usize]| {
            // f = 2*ymove*posy - ymove
            let mut c1 = vec![ymove, yp];
            c1.extend_from_slice(extra);
            *hh = hh.clone().add_prod(-sign * 2, c1);
            let mut c2 = vec![ymove];
            c2.extend_from_slice(extra);
            *hh = hh.clone().add_prod(sign, c2);
        };
        push_f(&mut hh, 1, &[slt]); // + f*slt  => subtract from oy
        push_f(&mut hh, 1, &[col]); // + f*col
        push_f(&mut hh, -1, &[sgt, col]); // - f*sgt*col
        push_f(&mut hh, -1, &[slt, col]); // - f*slt*col
        b.assert_zero(&hh);
    }

    // --- the step: target, in-bounds, vacuum, moved bit, board update ---
    let stepped = automaton_step(src);
    let moved = stepped.auto != src.auto;
    let tx = ax + ox;
    let ty = ay + oy;
    // tib = [target in bounds] = [tx>=0]*[tx<=n-1]*[ty>=0]*[ty<=n-1]
    let bx0 = b.forced_ge0(
        "tx0",
        &Head::lin(1, ax_col).add_lin(1, ox_col),
        tx as i128,
        SMALL_RBITS,
    );
    let bx1 = b.forced_ge0(
        "tx1",
        &Head::c(n as i128 - 1)
            .add_lin(-1, ax_col)
            .add_lin(-1, ox_col),
        n as i128 - 1 - tx as i128,
        SMALL_RBITS,
    );
    let by0 = b.forced_ge0(
        "ty0",
        &Head::lin(1, ay_col).add_lin(1, oy_col),
        ty as i128,
        SMALL_RBITS,
    );
    let by1 = b.forced_ge0(
        "ty1",
        &Head::c(n as i128 - 1)
            .add_lin(-1, ay_col)
            .add_lin(-1, oy_col),
        n as i128 - 1 - ty as i128,
        SMALL_RBITS,
    );
    let tib_val = (b.value(bx0).0 as i128)
        * (b.value(bx1).0 as i128)
        * (b.value(by0).0 as i128)
        * (b.value(by1).0 as i128);
    let tib = b.alloc("tib", ColumnKind::Binary, tib_val);
    b.assert_zero(&Head::lin(1, tib).add_prod(-1, vec![bx0, bx1, by0, by1]));
    // target read (gated by tib): tcell = src[target] (0 if OOB). Row×column √n read:
    // the target row is `ay+oy`, the column `ax+ox`.
    let tcell_val = src.cell_at((tx, ty)) as i128;
    let tcell = b.alloc("tcell", ColumnKind::Value, tcell_val);
    let target_x_head = Head::lin(1, ax_col).add_lin(1, ox_col);
    let target_y_head = Head::lin(1, ay_col).add_lin(1, oy_col);
    let (tx_hot, ty_hot) = if src.in_bounds((tx, ty)) {
        (tx as usize, ty as usize)
    } else {
        (0, 0) // gate off ⇒ the hot index is ignored (all selectors zero)
    };
    b.read_rowcol_gated(
        "targ",
        board_cols,
        n,
        tib,
        tx_hot,
        &target_x_head,
        ty_hot,
        &target_y_head,
        tcell,
    );
    // targ_vac = [tcell==0] = 1 - [tcell>=1]
    let nz = b.forced_ge0(
        "tcnz",
        &Head::lin(1, tcell).add_const(-1),
        tcell_val - 1,
        SMALL_RBITS,
    );
    let targ_vac = b.alloc("tvac", ColumnKind::Binary, 1 - (b.value(nz).0 as i128));
    b.assert_zero(&Head::lin(1, targ_vac).add_lin(1, nz).add_const(-1)); // targ_vac = 1 - nz
    // offnz = ox^2 + oy^2  (0 iff offset zero, else 1)
    let offnz = b.alloc(
        "offnz",
        ColumnKind::Value,
        (ox as i128) * (ox as i128) + (oy as i128) * (oy as i128),
    );
    b.assert_zero(
        &Head::lin(1, offnz)
            .add_prod(-1, vec![ox_col, ox_col])
            .add_prod(-1, vec![oy_col, oy_col]),
    );
    // m = offnz*tib*targ_vac
    let m = b.alloc("moved", ColumnKind::Binary, moved as i128);
    b.assert_zero(&Head::lin(1, m).add_prod(-1, vec![offnz, tib, targ_vac]));
    // sel_target: gated row×column one-hot at target (gate m). The write cell `(x,y)` is
    // addressed by `sel_target_row[y]·sel_target_col[x]`.
    let (sel_target_row, sel_target_col) = b.one_hot_rowcol_gated(
        "targw",
        n,
        m,
        tx_hot,
        &target_x_head,
        ty_hot,
        &target_y_head,
    );

    // --- board update output equalities ---
    // new[c] - old[c] - 3*m*sel_target[c] + m*sel_target[c]*old[c] + m*sel_auto[c]*old[c] == 0,
    // with sel_target[c] = sel_target_row[y]·sel_target_col[x] and likewise for sel_auto.
    for c in 0..k {
        let x = c % n;
        let y = c / n;
        b.assert_zero(
            &Head::lin(1, out_cols[c])
                .add_lin(-1, board_cols[c])
                .add_prod(
                    -(AUTO as i128),
                    vec![m, sel_target_row[y], sel_target_col[x]],
                )
                .add_prod(
                    1,
                    vec![m, sel_target_row[y], sel_target_col[x], board_cols[c]],
                )
                .add_prod(1, vec![m, sel_auto_row[y], sel_auto_col[x], board_cols[c]]),
        );
    }
}

/// **STAGE D1** — the automaton-step-only AIR. `old` has no player moves; the AIR
/// checks `claimed_next == automaton_step(old)`.
///
/// PUBLIC INPUTS (the Custom-VK door's state-binding ABI —
/// `dregg_circuit::effect_vm::custom_state_binding`):
///
/// ```text
///   [ 0.. 8)  old8            the CELL's pre-state root  (the leg's rotated anchor — add_pi'd,
///   [ 8..16)  new8            the CELL's post-state root  fold-connected, opaque to this AIR)
///   [16..24)  board_old_root  CONSTRAINED: cap_node8 Merkle root over the OLD board columns
///   [24..32)  board_new_root  CONSTRAINED: cap_node8 Merkle root over the claimed-next columns
/// ```
///
/// `old8`/`new8` are the SUBSTRATE commitment the deployed state-binding fold
/// (`prove_custom_binding_node_state_segmented`) `connect`s to the turn leg's REAL rotated
/// roots — so a leaf about a DIFFERENT cell transition is UNSAT. They are opaque here (the
/// board AIR does not, and cannot, recompute the cell's v9 chip commit). The two BOARD roots
/// are the game-semantic commitment: `board_root8` binds every board square at ~124 bits via
/// real `MerkleHash8` sites, and the roots ride app PI slots the `custom_proof_commitment`
/// already hashes in full — so "this leaf published board_new_root" is now "the 25-cell board
/// transitioned exactly so, provably", not a free-floating value.
///
/// The bare [`build_d1`] uses [`placeholder_roots`] for the door prefix (the fast self-tests
/// are opaque to it); the FOLD driver calls this `_bound` form with the leg's REAL roots.
pub fn build_d1_bound(
    old: &Board,
    claimed_next: &Board,
    old8: [dregg_circuit::field::BabyBear; 8],
    new8: [dregg_circuit::field::BabyBear; 8],
) -> Builder {
    let n = old.n;
    let mut b = Builder::new(format!("automatafl-d1-n{n}"));
    let old_cols = alloc_board(&mut b, "old", old);
    let new_cols = alloc_board(&mut b, "new", claimed_next);
    // PI[0..16): the door's state-binding prefix (the cell roots; add_pi'd, fold-connected).
    for x in old8.iter().chain(new8.iter()) {
        b.add_pi(x.0 as i128);
    }
    automaton_gadget(&mut b, n, &old_cols, old, &new_cols);
    // PI[16..32): the CONSTRAINED board-state roots (bind_pi'd app PIs).
    bind_board_roots(&mut b, &old_cols, &new_cols);
    b
}

/// Emit + bind the two CONSTRAINED board-state roots (old board, claimed-next board) as the
/// app public inputs `[16..24)` and `[24..32)`. Each is a `cap_node8` Merkle root over the
/// board columns — a genuine ~124-bit commitment the AIR forces (a forged root is UNSAT).
pub(crate) fn bind_board_roots(b: &mut Builder, old_cols: &[usize], new_cols: &[usize]) {
    let old_root = b.board_root8("boardold", old_cols);
    for c in old_root {
        b.bind_pi(c);
    }
    let new_root = b.board_root8("boardnew", new_cols);
    for c in new_root {
        b.bind_pi(c);
    }
}

/// **STAGE D1** with placeholder door roots (the fast battery — the board AIR is opaque to
/// the cell-state prefix). See [`build_d1_bound`] for the fold-driving form.
pub fn build_d1(old: &Board, claimed_next: &Board) -> Builder {
    let (old8, new8) = placeholder_roots();
    build_d1_bound(old, claimed_next, old8, new8)
}

/// The honest D1 program: `claimed_next = automaton_step(old)` (placeholder door roots).
pub fn build_d1_honest(old: &Board) -> Builder {
    let next = automaton_step(old);
    build_d1(old, &next)
}

/// The honest D1 program bound to the leg's REAL cell-state roots (the fold driver).
pub fn build_d1_honest_bound(
    old: &Board,
    old8: [dregg_circuit::field::BabyBear; 8],
    new8: [dregg_circuit::field::BabyBear; 8],
) -> Builder {
    let next = automaton_step(old);
    build_d1_bound(old, &next, old8, new8)
}

// ============================================================================
// D2 / D3 — single move + the n=2 resolution, producing the mid board, then the
// same automaton gadget on mid. (Refinement-tested; see crate::moves.)
// ============================================================================

pub use crate::moves::{
    SealedMove, build_d2, build_d2_bound, build_d2_honest, build_d2_honest_bound, build_d3,
    build_d3_bound, build_d3_honest, build_d3_honest_bound, build_sealed, build_sealed_bound,
    build_sealed_honest, build_sealed_honest_bound,
};

/// Shared entry: validate `claimed_next == apply_turn(old, moves)` given the already
/// move-resolved `mid` columns. Used by D2/D3.
pub(crate) fn automaton_on_mid(
    b: &mut Builder,
    n: usize,
    mid_cols: &[usize],
    mid: &Board,
    new_cols: &[usize],
) {
    automaton_gadget(b, n, mid_cols, mid, new_cols);
}

/// Re-export helpers moves.rs needs.
pub(crate) fn alloc_board_pub(b: &mut Builder, tag: &str, board: &Board) -> Vec<usize> {
    alloc_board(b, tag, board)
}
