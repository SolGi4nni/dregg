//! # `vault_weld` — the IN-AIR VAULT-DEPOSIT (tag 19) no-dilution gates with an OVERFLOW-SAFE
//! MULTI-LIMB PRODUCT COMPARISON (PIECE 2 of the VK epoch for tag 19, STAGED).
//!
//! This is the tag-19 sibling of [`super::satisfaction_weld`] / [`super::discharge_weld`]. The Lean
//! soundness rung is `Dregg2.Deos.CapacitySatisfaction` §9 (`VaultDepositFieldGate`,
//! `vault_satisfaction_witnessed`, and the teeth `vault_inflation_attack_field_rejected` /
//! `vault_dilution_field_rejected` / `vault_no_deposit_field_rejected`); the deployed off-AIR
//! reference is `verify.rs`'s `VAULT_DEPOSIT` arm (which uses `u128` products to avoid wrap).
//!
//! ## The genuinely-hard part: a product inequality that OVERFLOWS the field
//!
//! The share-vault no-dilution gate (the Lean `VaultDepositFieldGate`) is ENTIRELY inequalities:
//!
//!  1. genuine deposit `before[assets] < after[assets]`   (`d = Δassets > 0`)
//!  2. positive mint   `before[shares] < after[shares]`   (`m = Δshares > 0`, the inflation tooth)
//!  3. NO DILUTION     `before[assets]·m ≤ before[shares]·d`   (a PRODUCT inequality)
//!
//! The products `Ta·m` and `Sa·d` can reach `~2^60`, far past the `~2^31` BabyBear field — computing
//! them in-field would WRAP and silently corrupt the comparison (the off-AIR uses `u128`). The in-AIR
//! realization is therefore an OVERFLOW-SAFE MULTI-LIMB scheme:
//!
//!  * **operand decomposition** — `Ta, Sa, m, d` are each split into two 15-bit limbs (range-checked),
//!    bounding the operands to a `[0, 2^30)` window (`~1.07e9`; values past it fail closed — the
//!    documented in-AIR operand window, extensible by adding limbs).
//!  * **schoolbook product with witnessed carries** — `X·Y = X1Y1·2^30 + (X1Y0 + X0Y1)·2^15 + X0Y0`
//!    is accumulated limb-by-limb into four 15-bit output limbs `Z0..Z3` with carry witnesses, where
//!    the troublesome cross term `X1Y0 + X0Y1` (which alone can exceed `p`) is added ONE partial product
//!    at a time through an intermediate `t1`, so EVERY constraint polynomial stays `< p`
//!    (max magnitude `< 2^30 + 2^16 < p`). No in-field value ever wraps.
//!  * **lexicographic borrow comparison** — `Sa·d − Ta·m ≥ 0` is checked by a 4-limb borrow
//!    subtraction `Q − P` with per-limb borrow bits; the absence of a final borrow (`bb3 = 0`) IS
//!    `Ta·m ≤ Sa·d` (no dilution). A diluting deposit (`Ta·m > Sa·d`) produces a final borrow ⟹ the
//!    no-final-borrow gate bites.
//!
//!  The strict-positivity legs `d > 0` / `m > 0` are realized as IS-NONZERO gates (inverse witnesses
//!  `d·d_inv = 1`), so a ZERO-mint (the ERC-4626 first-depositor inflation attack) or a no-deposit
//!  (`d = 0`) is UNSAT; combined with the operand range check (`d, m ∈ [0, 2^30)`, which fails closed on
//!  a field-wrapped NEGATIVE delta) this gives genuine `d, m ∈ [1, 2^30)` strict positivity.
//!
//! ## STAGED — descriptor EMITTED (Lean) + producer EXPORTED; the registry row rides the big-bang
//!
//! The welded descriptor IS now emitted from Lean (`Dregg2.Deos.VaultSatDescriptor.
//! vaultSatVmDescriptor2R24`, v12 offsets through the canonical constants; exercise fixture
//! `circuit/tests/fixtures/vault-sat-v3-staged.json`) and the producer aux-fill is EXPORTED below
//! ([`fill_vault_aux`]); `gentian_discharge_vault_prove.rs` proves real STARKs against it (honest
//! fair-mint deposit proves+verifies; zero-mint inflation / over-mint dilution / no-deposit
//! REFUSED). What still rides the ONE big-bang descriptor regen: the
//! `rotation-v3-staged-registry.tsv` row + the drift-gate FP pin, the declared-tag-19 routing tie,
//! and the welded VK commit + live admission. Until the flip a pure light client does not yet
//! witness vault satisfaction in production.

use super::carrier_floor_weld::caveat_tag_col;
use super::columns::rotation::caveat as cav;
use super::pi::SLOT_CAVEAT_TAG_VAULT_DEPOSIT;
use super::satisfaction_weld::{after_field_col, before_field_col};
use super::trace_rotated::GRAD_ROT_WIDTH;
use crate::descriptor_ir2::{VmConstraint2, WindowExpr, WindowGateSpec};
use crate::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

/// **THE VAULT CAPACITY-SELECTOR COLUMN** — `param2` (`PARAM_BASE + 2`). `1` on the settle row, `0`
/// on padding; the emitted descriptor pins it to PI 46.
pub const VAULT_SEL_COL: usize = super::columns::PARAM_BASE + 2;
/// The PI slot the emitted descriptor pins the selector to.
pub const VAULT_SEL_PI: usize = 46;
/// **THE DECODED VAULT-FLOOR COLUMN** — `param4` (`PARAM_BASE + 4`), the boolean "this cell declares
/// the vault-deposit capacity (some bound caveat type-tag == 19)".
pub const FLOOR_VAULT_COL: usize = super::columns::PARAM_BASE + 4;

/// The vault tag as a signed felt constant (`= 19`).
const TAG_VAULT: i64 = SLOT_CAVEAT_TAG_VAULT_DEPOSIT as i64;

/// Limb width: 15 bits keeps every partial product `< 2^30 < p` and every accumulation `< p`.
pub const LIMB_BITS: usize = 15;
const TWO15: i64 = 1 << LIMB_BITS;
/// The carry width for the cross-term carries (one bit past the limb width — see the header bound).
pub const CARRY_BITS: usize = 16;

// --- decode aux (mirror carrier_floor, tag 19) ---
pub const fn bit_col(k: usize) -> usize {
    GRAD_ROT_WIDTH + k
}
pub const fn inv_col(k: usize) -> usize {
    GRAD_ROT_WIDTH + cav::MAX_CAVEATS + k
}
pub const fn or_col(j: usize) -> usize {
    GRAD_ROT_WIDTH + 2 * cav::MAX_CAVEATS + j
}

// --- product / compare aux block (past the decode aux) ---
const V: usize = GRAD_ROT_WIDTH + 16;
/// `Ta = before[assets]` limbs (lo, hi).
pub const TA0: usize = V;
pub const TA1: usize = V + 1;
/// `Sa = before[shares]` limbs.
pub const SA0: usize = V + 2;
pub const SA1: usize = V + 3;
/// `m = after[shares] − before[shares]` limbs.
pub const M0: usize = V + 4;
pub const M1: usize = V + 5;
/// `d = after[assets] − before[assets]` limbs.
pub const D0: usize = V + 6;
pub const D1: usize = V + 7;
/// Product `P = Ta·m` output limbs (`P3` is the top carry).
pub const P0: usize = V + 8;
pub const P1: usize = V + 9;
pub const P2: usize = V + 10;
pub const P3: usize = V + 11;
/// `P = Ta·m` carry witnesses (`PCA/PCB/PCC`) + the cross-term intermediate `PT1`.
pub const PCA: usize = V + 12;
pub const PCB: usize = V + 13;
pub const PCC: usize = V + 14;
pub const PT1: usize = V + 15;
/// Product `Q = Sa·d` output limbs.
pub const Q0: usize = V + 16;
pub const Q1: usize = V + 17;
pub const Q2: usize = V + 18;
pub const Q3: usize = V + 19;
pub const QCA: usize = V + 20;
pub const QCB: usize = V + 21;
pub const QCC: usize = V + 22;
pub const QT1: usize = V + 23;
/// Borrow-subtraction (`Q − P`) result limbs.
pub const W0: usize = V + 24;
pub const W1: usize = V + 25;
pub const W2: usize = V + 26;
pub const W3: usize = V + 27;
/// Per-limb borrow bits (`BB3` is the final borrow; `0` ⟺ `Q ≥ P` ⟺ no dilution).
pub const BB0: usize = V + 28;
pub const BB1: usize = V + 29;
pub const BB2: usize = V + 30;
pub const BB3: usize = V + 31;
/// is-nonzero inverse witnesses for `d` and `m`.
pub const D_INV: usize = V + 32;
pub const M_INV: usize = V + 33;
/// First bit-decomposition column.
const BIT_BASE: usize = V + 34;

/// The ordered range-checked columns and their bit widths. The producer fill + the gate generator
/// walk this list in lockstep so bit blocks are assigned deterministically.
fn range_specs() -> Vec<(usize, usize)> {
    let l = LIMB_BITS;
    let c = CARRY_BITS;
    vec![
        (TA0, l),
        (TA1, l),
        (SA0, l),
        (SA1, l),
        (M0, l),
        (M1, l),
        (D0, l),
        (D1, l),
        (P0, l),
        (P1, l),
        (P2, l),
        (P3, l),
        (PCA, l),
        (PCB, c),
        (PCC, c),
        (PT1, l),
        (Q0, l),
        (Q1, l),
        (Q2, l),
        (Q3, l),
        (QCA, l),
        (QCB, c),
        (QCC, c),
        (QT1, l),
        (W0, l),
        (W1, l),
        (W2, l),
        (W3, l),
    ]
}

// ---------------------------------------------------------------------------
// gate-body builders
// ---------------------------------------------------------------------------

fn var(c: usize) -> LeanExpr {
    LeanExpr::var(c)
}
fn k(c: i64) -> LeanExpr {
    LeanExpr::constant(c)
}
fn add(a: LeanExpr, b: LeanExpr) -> LeanExpr {
    LeanExpr::add(a, b)
}
fn mul(a: LeanExpr, b: LeanExpr) -> LeanExpr {
    LeanExpr::mul(a, b)
}
fn neg(e: LeanExpr) -> LeanExpr {
    mul(k(-1), e)
}
fn sub(a: LeanExpr, b: LeanExpr) -> LeanExpr {
    add(a, neg(b))
}
fn gate(body: LeanExpr) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(body))
}
fn sel_gate(body: LeanExpr) -> VmConstraint2 {
    gate(mul(var(VAULT_SEL_COL), body))
}

// --- decode (mirror carrier_floor, tag 19) ---
fn is_zero_def_gate(tag_col: usize, b: usize, inv: usize) -> VmConstraint2 {
    gate(add(
        add(var(b), mul(add(var(tag_col), k(-TAG_VAULT)), var(inv))),
        k(-1),
    ))
}
fn is_zero_force_gate(tag_col: usize, b: usize) -> VmConstraint2 {
    gate(mul(add(var(tag_col), k(-TAG_VAULT)), var(b)))
}
fn or_seed_gate(out: usize, b: usize) -> VmConstraint2 {
    gate(sub(var(out), var(b)))
}
fn or_fold_gate(out: usize, in_or: usize, b: usize) -> VmConstraint2 {
    let or = sub(add(var(in_or), var(b)), mul(var(in_or), var(b)));
    gate(sub(var(out), or))
}
fn selector_force_first_gate() -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::First,
        body: mul(var(FLOOR_VAULT_COL), add(var(VAULT_SEL_COL), k(-1))),
    })
}
fn caveat_uniform_gate(tag_col: usize) -> VmConstraint2 {
    VmConstraint2::WindowGate(WindowGateSpec {
        body: WindowExpr::Add(
            Box::new(WindowExpr::Nxt(tag_col)),
            Box::new(WindowExpr::Mul(
                Box::new(WindowExpr::Const(-1)),
                Box::new(WindowExpr::Loc(tag_col)),
            )),
        ),
        on_transition: true,
    })
}

/// **THE VAULT FLOOR DECODE + FIRST-ROW SELECTOR-FORCE + CAVEAT-UNIFORMITY GATES (STAGED).** The
/// tag-19 mirror of `carrier_floor_weld::carrier_floor_gates`.
pub fn vault_floor_gates() -> Vec<VmConstraint2> {
    let mut g = Vec::new();
    for j in 0..cav::MAX_CAVEATS {
        g.push(is_zero_def_gate(caveat_tag_col(j), bit_col(j), inv_col(j)));
        g.push(is_zero_force_gate(caveat_tag_col(j), bit_col(j)));
    }
    g.push(or_seed_gate(or_col(0), bit_col(0)));
    g.push(or_fold_gate(or_col(1), or_col(0), bit_col(1)));
    g.push(or_fold_gate(or_col(2), or_col(1), bit_col(2)));
    g.push(or_fold_gate(FLOOR_VAULT_COL, or_col(2), bit_col(3)));
    g.push(selector_force_first_gate());
    for j in 0..cav::MAX_CAVEATS {
        g.push(caveat_uniform_gate(caveat_tag_col(j)));
    }
    g
}

/// **THE OVERFLOW-SAFE 2×2 → 4-LIMB SCHOOLBOOK PRODUCT GATES (selector-gated).** Forces
/// `Z0 + Z1·2^15 + Z2·2^30 + Z3·2^45 = (x1·2^15 + x0)·(y1·2^15 + y0)` over four 15-bit output limbs,
/// accumulating the cross term ONE partial product at a time through `t1` so every polynomial stays
/// `< p`:
///
///  * A `x0·y0            = Z0 + cA·2^15`
///  * B `x1·y0 + cA       = t1 + cB·2^15`
///  * C `x0·y1 + t1       = Z1 + cC·2^15`
///  * D `x1·y1 + cB + cC  = Z2 + Z3·2^15`   (Z3 is the top carry)
pub fn product_gates(
    x0: usize,
    x1: usize,
    y0: usize,
    y1: usize,
    z0: usize,
    z1: usize,
    z2: usize,
    z3: usize,
    ca: usize,
    cb: usize,
    cc: usize,
    t1: usize,
) -> Vec<VmConstraint2> {
    vec![
        sel_gate(sub(
            sub(mul(var(x0), var(y0)), var(z0)),
            mul(k(TWO15), var(ca)),
        )),
        sel_gate(sub(
            sub(add(mul(var(x1), var(y0)), var(ca)), var(t1)),
            mul(k(TWO15), var(cb)),
        )),
        sel_gate(sub(
            sub(add(mul(var(x0), var(y1)), var(t1)), var(z1)),
            mul(k(TWO15), var(cc)),
        )),
        sel_gate(sub(
            sub(add(add(mul(var(x1), var(y1)), var(cb)), var(cc)), var(z2)),
            mul(k(TWO15), var(z3)),
        )),
    ]
}

/// **THE 4-LIMB BORROW COMPARISON GATES (selector-gated).** A borrow subtraction `Q − P` over the
/// 15-bit limbs: per limb `Q_i − P_i − bb_{i−1} + bb_i·2^15 − w_i = 0` with `bb_{−1} = 0`, each `bb_i`
/// boolean, and a FINAL `bb3 = 0` gate. `bb3 = 0` ⟺ no underflow ⟺ `P ≤ Q` ⟺ `Ta·m ≤ Sa·d`
/// (no dilution); a diluting deposit (`P > Q`) forces a final borrow and the no-borrow gate bites.
pub fn borrow_compare_gates(
    p: [usize; 4],
    q: [usize; 4],
    w: [usize; 4],
    bb: [usize; 4],
) -> Vec<VmConstraint2> {
    let mut g = Vec::new();
    for i in 0..4 {
        let mut body = sub(var(q[i]), var(p[i]));
        if i > 0 {
            body = sub(body, var(bb[i - 1]));
        }
        body = add(body, mul(k(TWO15), var(bb[i])));
        body = sub(body, var(w[i]));
        g.push(sel_gate(body));
        // bb_i boolean.
        g.push(sel_gate(mul(var(bb[i]), add(var(bb[i]), k(-1)))));
    }
    // no final borrow ⟹ P ≤ Q.
    g.push(sel_gate(var(bb[3])));
    g
}

/// The per-list range-check gates: for each `(col, nbits)`, `nbits` selector-gated boolean gates plus
/// a selector-gated assembly `sel · (col − Σ 2^i bit_i) == 0`. Bit blocks are assigned in list order
/// from `BIT_BASE`.
fn range_gates() -> Vec<VmConstraint2> {
    let mut g = Vec::new();
    let mut base = BIT_BASE;
    for (col, nbits) in range_specs() {
        let mut sum = k(0);
        for i in 0..nbits {
            let b = base + i;
            g.push(sel_gate(mul(var(b), add(var(b), k(-1)))));
            sum = add(sum, mul(k(1i64 << i), var(b)));
        }
        g.push(sel_gate(sub(var(col), sum)));
        base += nbits;
    }
    g
}

/// **THE VAULT SATISFACTION GATES (STAGED).** Operand decomposition assemblies + the two is-nonzero
/// (strict-positivity) gates + the two overflow-safe products (`P = Ta·m`, `Q = Sa·d`) + the borrow
/// comparison (`P ≤ Q`) + all limb/carry range checks — all selector-gated. A satisfying proof FORCES
/// `d > 0`, `m > 0`, and `Ta·m ≤ Sa·d` over the committed rotated field columns (the Lean
/// `VaultDepositFieldGate`); an inflation (`m = 0`), no-deposit (`d = 0`), or diluting (`Ta·m > Sa·d`)
/// deposit is UNSAT.
pub fn vault_satisfaction_gates(asset_slot: usize, share_slot: usize) -> Vec<VmConstraint2> {
    let ba = before_field_col(asset_slot);
    let aa = after_field_col(asset_slot);
    let bs = before_field_col(share_slot);
    let as_ = after_field_col(share_slot);
    let d_expr = sub(var(aa), var(ba));
    let m_expr = sub(var(as_), var(bs));

    let mut g = Vec::new();

    // operand decompositions (limb assemblies).
    g.push(sel_gate(sub(
        var(ba),
        add(var(TA0), mul(k(TWO15), var(TA1))),
    ))); // Ta = before[assets]
    g.push(sel_gate(sub(
        var(bs),
        add(var(SA0), mul(k(TWO15), var(SA1))),
    ))); // Sa = before[shares]
    g.push(sel_gate(sub(
        m_expr.clone(),
        add(var(M0), mul(k(TWO15), var(M1))),
    ))); // m = Δshares
    g.push(sel_gate(sub(
        d_expr.clone(),
        add(var(D0), mul(k(TWO15), var(D1))),
    ))); // d = Δassets

    // strict positivity (is-nonzero): d·d_inv = 1, m·m_inv = 1.
    g.push(sel_gate(sub(mul(d_expr, var(D_INV)), k(1))));
    g.push(sel_gate(sub(mul(m_expr, var(M_INV)), k(1))));

    // products: P = Ta·m, Q = Sa·d.
    g.extend(product_gates(
        TA0, TA1, M0, M1, P0, P1, P2, P3, PCA, PCB, PCC, PT1,
    ));
    g.extend(product_gates(
        SA0, SA1, D0, D1, Q0, Q1, Q2, Q3, QCA, QCB, QCC, QT1,
    ));

    // no dilution: Ta·m ≤ Sa·d via borrow compare of P vs Q.
    g.extend(borrow_compare_gates(
        [P0, P1, P2, P3],
        [Q0, Q1, Q2, Q3],
        [W0, W1, W2, W3],
        [BB0, BB1, BB2, BB3],
    ));

    // range checks for all limbs / carries / borrow results.
    g.extend(range_gates());

    g
}

/// **THE FULL IN-AIR VAULT GADGET (STAGED).** Floor decode / selector-force / uniformity followed by
/// the satisfaction gates. The tag-19 face of the sealed-escrow weld — a pure light client witnesses
/// the no-dilution discipline held over the committed state.
pub fn vault_gates(asset_slot: usize, share_slot: usize) -> Vec<VmConstraint2> {
    let mut g = vault_floor_gates();
    g.extend(vault_satisfaction_gates(asset_slot, share_slot));
    g
}

// ---------------------------------------------------------------------------
// THE EXPORTED PRODUCER AUX-FILL (the graduation of the in-test `make_row` witness logic).
// ---------------------------------------------------------------------------

const MASK15: u64 = (1 << LIMB_BITS) - 1;

struct ProductW {
    z0: u64,
    z1: u64,
    z2: u64,
    z3: u64,
    ca: u64,
    cb: u64,
    cc: u64,
    t1: u64,
}

/// The reference schoolbook-with-carries: identical arithmetic to [`product_gates`].
fn mul_witness(x: u64, y: u64) -> ProductW {
    let (x0, x1) = (x & MASK15, x >> LIMB_BITS);
    let (y0, y1) = (y & MASK15, y >> LIMB_BITS);
    let p00 = x0 * y0;
    let z0 = p00 & MASK15;
    let ca = p00 >> LIMB_BITS;
    let tb = x1 * y0 + ca;
    let t1 = tb & MASK15;
    let cb = tb >> LIMB_BITS;
    let tc = x0 * y1 + t1;
    let z1 = tc & MASK15;
    let cc = tc >> LIMB_BITS;
    let td = x1 * y1 + cb + cc;
    let z2 = td & MASK15;
    let z3 = td >> LIMB_BITS;
    debug_assert_eq!(
        z0 + (z1 << LIMB_BITS) + (z2 << (2 * LIMB_BITS)) + (z3 << (3 * LIMB_BITS)),
        x * y,
        "schoolbook reconstruction must equal the integer product"
    );
    ProductW {
        z0,
        z1,
        z2,
        z3,
        ca,
        cb,
        cc,
        t1,
    }
}

#[allow(clippy::too_many_arguments)]
fn fill_product(
    row: &mut [crate::field::BabyBear],
    p: &ProductW,
    z0: usize,
    z1: usize,
    z2: usize,
    z3: usize,
    ca: usize,
    cb: usize,
    cc: usize,
    t1: usize,
) {
    use crate::field::BabyBear;
    row[z0] = BabyBear::new(p.z0 as u32);
    row[z1] = BabyBear::new(p.z1 as u32);
    row[z2] = BabyBear::new(p.z2 as u32);
    row[z3] = BabyBear::new(p.z3 as u32);
    row[ca] = BabyBear::new(p.ca as u32);
    row[cb] = BabyBear::new(p.cb as u32);
    row[cc] = BabyBear::new(p.cc as u32);
    row[t1] = BabyBear::new(p.t1 as u32);
}

/// **THE PRODUCTION VAULT AUX-FILL (one row).** Fill every auxiliary column the vault gadget's
/// gates read, from the row's OWN bound columns — the producer arm the rotated trace generator
/// (and the gentian-style prove exercise) calls after the settle-carrier trace is generated:
///
///  * the floor decode witness (`bit`/`inv`/`or` + `FLOOR_VAULT_COL`), read from the four
///    caveat-commit-bound type-tag columns already on the row;
///  * the operand limbs (`Ta`/`Sa`/`m`/`d`), read from the rotated BEFORE/AFTER field columns;
///  * the is-nonzero inverse witnesses (`D_INV`/`M_INV`, zero when the delta is zero — the
///    inflation / no-deposit refusal witnesses);
///  * both schoolbook products (`P = Ta·m`, `Q = Sa·d`) with their carries, the borrow comparison
///    (`Q − P`), and every range-check bit block (list order, per `range_specs`).
///
/// The row is grown to `width` first. Does NOT touch the capacity selector (`VAULT_SEL_COL`), the
/// field columns, or the PI vector — the trace generator owns those. TOTAL: a non-witnessable row
/// (zero-mint, no-deposit, dilution, or a wrapped negative delta) still fills, producing a REFUSING
/// witness (an is-nonzero / no-final-borrow / limb-range gate cannot vanish) — fail-closed.
pub fn fill_vault_aux_row(
    row: &mut Vec<crate::field::BabyBear>,
    width: usize,
    asset_slot: usize,
    share_slot: usize,
) {
    use crate::field::BabyBear;
    if row.len() < width {
        row.resize(width, BabyBear::ZERO);
    }
    // The floor decode witness over the bound type-tag columns (tag 19).
    let mut running = 0u32;
    for j in 0..cav::MAX_CAVEATS {
        let tag = row[caveat_tag_col(j)].as_u32();
        let is_vault = tag == SLOT_CAVEAT_TAG_VAULT_DEPOSIT;
        let b = u32::from(is_vault);
        row[bit_col(j)] = BabyBear::new(b);
        row[inv_col(j)] = if is_vault {
            BabyBear::ZERO
        } else {
            (BabyBear::new(tag) - BabyBear::new(SLOT_CAVEAT_TAG_VAULT_DEPOSIT))
                .inverse()
                .expect("nonzero tag−19 invertible")
        };
        running |= b;
        if j == 0 {
            row[or_col(0)] = BabyBear::new(running);
        } else if j < cav::MAX_CAVEATS - 1 {
            row[or_col(j)] = BabyBear::new(running);
        } else {
            row[FLOOR_VAULT_COL] = BabyBear::new(running);
        }
    }

    // Operands read from the row's own rotated field columns.
    let ba = row[before_field_col(asset_slot)];
    let aa = row[after_field_col(asset_slot)];
    let bs = row[before_field_col(share_slot)];
    let ash = row[after_field_col(share_slot)];
    let ta = ba.as_u32() as u64;
    let sa = bs.as_u32() as u64;
    let d = (aa - ba).as_u32() as u64;
    let m = (ash - bs).as_u32() as u64;

    // Operand limbs.
    let put = |row: &mut [BabyBear], lo: usize, hi: usize, v: u64| {
        row[lo] = BabyBear::new((v & MASK15) as u32);
        row[hi] = BabyBear::new((v >> LIMB_BITS) as u32);
    };
    put(row, TA0, TA1, ta);
    put(row, SA0, SA1, sa);
    put(row, M0, M1, m);
    put(row, D0, D1, d);

    // is-nonzero inverses (0 when the delta is 0 — the inflation / no-deposit refusal witnesses).
    row[D_INV] = (aa - ba).inverse().unwrap_or(BabyBear::ZERO);
    row[M_INV] = (ash - bs).inverse().unwrap_or(BabyBear::ZERO);

    // Products P = Ta·m, Q = Sa·d (the EXACT schoolbook-with-carries the gates check).
    let p = mul_witness(ta, m);
    let q = mul_witness(sa, d);
    fill_product(row, &p, P0, P1, P2, P3, PCA, PCB, PCC, PT1);
    fill_product(row, &q, Q0, Q1, Q2, Q3, QCA, QCB, QCC, QT1);

    // Borrow compare Q − P.
    let plimb = [p.z0, p.z1, p.z2, p.z3];
    let qlimb = [q.z0, q.z1, q.z2, q.z3];
    let mut borrow: i64 = 0;
    let wcol = [W0, W1, W2, W3];
    let bbcol = [BB0, BB1, BB2, BB3];
    for i in 0..4 {
        let r = qlimb[i] as i64 - plimb[i] as i64 - borrow;
        let (w, bo) = if r < 0 {
            ((r + (1 << LIMB_BITS)) as u64, 1)
        } else {
            (r as u64, 0)
        };
        row[wcol[i]] = BabyBear::new(w as u32);
        row[bbcol[i]] = BabyBear::new(bo);
        borrow = bo as i64;
    }

    // Range-check bit blocks (list order, low bits of each column's canonical value).
    let mut base = BIT_BASE;
    for (col, nbits) in range_specs() {
        let value = row[col].as_u32();
        for i in 0..nbits {
            row[base + i] = BabyBear::new((value >> i) & 1);
        }
        base += nbits;
    }
}

/// **THE PRODUCTION VAULT AUX-FILL (whole trace).** [`fill_vault_aux_row`] on every row — the
/// decode gates are EVERY-ROW (the satisfaction gates are selector-gated, inert on padding), so
/// the aux columns are filled uniformly. The rotated settle-carrier trace + this fill is a complete
/// witness for the staged `vaultSatVmDescriptor2R24` + `vault_floor_gates` weld.
pub fn fill_vault_aux(
    trace: &mut [Vec<crate::field::BabyBear>],
    width: usize,
    asset_slot: usize,
    share_slot: usize,
) {
    for row in trace.iter_mut() {
        fill_vault_aux_row(row, width, asset_slot, share_slot);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_ir2::eval_lean_expr;
    use crate::field::BabyBear;

    const ASSET: usize = 0;
    const SHARE: usize = 1;

    fn violation(
        c: &VmConstraint2,
        local: &[BabyBear],
        next: &[BabyBear],
        is_first: bool,
    ) -> BabyBear {
        match c {
            VmConstraint2::Base(VmConstraint::Gate(body)) => eval_lean_expr(body, local),
            VmConstraint2::Base(VmConstraint::Boundary {
                row: VmRow::First,
                body,
            }) => {
                if is_first {
                    eval_lean_expr(body, local)
                } else {
                    BabyBear::ZERO
                }
            }
            VmConstraint2::WindowGate(g) => eval_window(&g.body, local, next),
            other => panic!("unexpected vault constraint kind: {other:?}"),
        }
    }

    fn eval_window(e: &WindowExpr, local: &[BabyBear], next: &[BabyBear]) -> BabyBear {
        match e {
            WindowExpr::Loc(i) => local[*i],
            WindowExpr::Nxt(i) => next[*i],
            WindowExpr::Const(c) => {
                if *c < 0 {
                    -BabyBear::new((-*c) as u32)
                } else {
                    BabyBear::new(*c as u32)
                }
            }
            WindowExpr::Add(a, b) => eval_window(a, local, next) + eval_window(b, local, next),
            WindowExpr::Mul(a, b) => eval_window(a, local, next) * eval_window(b, local, next),
        }
    }

    /// Build a row by setting the generator-owned columns (tags, selector, field columns), then
    /// running the EXPORTED production aux-fill [`fill_vault_aux_row`] — the tests exercise the
    /// same producer arm the prove exercise / rotated trace generator calls.
    fn make_row(
        tags: [u32; cav::MAX_CAVEATS],
        sel: u32,
        before_assets: u32,
        after_assets: u32,
        before_shares: u32,
        after_shares: u32,
    ) -> Vec<BabyBear> {
        let total_bits: usize = range_specs().iter().map(|(_, n)| *n).sum();
        let width = (BIT_BASE + total_bits)
            .max(after_field_col(7) + 1)
            .max(caveat_tag_col(cav::MAX_CAVEATS - 1) + 1);
        let mut row = vec![BabyBear::ZERO; width];

        for j in 0..cav::MAX_CAVEATS {
            row[caveat_tag_col(j)] = BabyBear::new(tags[j]);
        }
        row[VAULT_SEL_COL] = BabyBear::new(sel);
        row[before_field_col(ASSET)] = BabyBear::new(before_assets);
        row[after_field_col(ASSET)] = BabyBear::new(after_assets);
        row[before_field_col(SHARE)] = BabyBear::new(before_shares);
        row[after_field_col(SHARE)] = BabyBear::new(after_shares);

        fill_vault_aux_row(&mut row, width, ASSET, SHARE);
        row
    }

    fn all_zero_settle(gates: &[VmConstraint2], row: &[BabyBear]) -> bool {
        gates
            .iter()
            .all(|g| violation(g, row, row, /*is_first*/ true) == BabyBear::ZERO)
    }

    #[test]
    fn columns_are_distinct() {
        let mut cols: Vec<usize> = (0..cav::MAX_CAVEATS)
            .flat_map(|j| [caveat_tag_col(j), bit_col(j), inv_col(j)])
            .collect();
        cols.extend([
            or_col(0),
            or_col(1),
            or_col(2),
            FLOOR_VAULT_COL,
            VAULT_SEL_COL,
        ]);
        cols.extend([TA0, TA1, SA0, SA1, M0, M1, D0, D1]);
        cols.extend([P0, P1, P2, P3, PCA, PCB, PCC, PT1]);
        cols.extend([Q0, Q1, Q2, Q3, QCA, QCB, QCC, QT1]);
        cols.extend([W0, W1, W2, W3, BB0, BB1, BB2, BB3, D_INV, M_INV]);
        let total_bits: usize = range_specs().iter().map(|(_, n)| *n).sum();
        cols.extend(BIT_BASE..BIT_BASE + total_bits);
        let n = cols.len();
        cols.sort_unstable();
        cols.dedup();
        assert_eq!(cols.len(), n, "no two vault-gadget columns alias");
    }

    #[test]
    fn honest_deposit_satisfies_every_gate() {
        // The Lean §10 witness: established vault Ta=2, Sa=4; deposit d=10, m=20 → 2·20 ≤ 4·10 (40≤40).
        let gates = vault_gates(ASSET, SHARE);
        let row = make_row([TAG_VAULT as u32, 17, 0, 0], 1, 2, 12, 4, 24);
        assert_eq!(
            row[FLOOR_VAULT_COL],
            BabyBear::ONE,
            "vault declared ⟹ floor 1"
        );
        assert!(
            all_zero_settle(&gates, &row),
            "the honest no-dilution deposit must satisfy every gate"
        );
    }

    #[test]
    fn honest_large_deposit_demonstrates_overflow_safety() {
        // Operands whose products EXCEED the field: Ta = 1_000_000, m = 1_000_000 → Ta·m = 1e12 ≫ p
        // (~2^31). A naive in-field product would WRAP; the multi-limb gates handle it. Fair mint
        // (m/d = Sa/Ta = 1) so 1e12 ≤ 1e12 holds.
        let gates = vault_gates(ASSET, SHARE);
        let ta = 1_000_000u32;
        let sa = 1_000_000u32;
        let d = 1_000_000u32;
        let m = 1_000_000u32;
        let row = make_row([TAG_VAULT as u32, 17, 0, 0], 1, ta, ta + d, sa, sa + m);
        assert!(
            all_zero_settle(&gates, &row),
            "a deposit whose products exceed the field must still satisfy (overflow-safe multi-limb)"
        );
    }

    #[test]
    fn inflation_zero_mint_is_unsat() {
        // The ERC-4626 first-depositor inflation attack: a positive deposit minting ZERO shares
        // (after_shares = before_shares). The is-nonzero(m) gate bites.
        let gates = vault_gates(ASSET, SHARE);
        let row = make_row(
            [TAG_VAULT as u32, 17, 0, 0],
            1,
            2,
            12,
            4,
            /*after_shares*/ 4,
        );
        assert!(
            !all_zero_settle(&gates, &row),
            "a zero-mint deposit must violate the is-nonzero(m) gate"
        );
    }

    #[test]
    fn no_deposit_is_unsat() {
        // A "deposit" that does not advance total_assets (d = 0). The is-nonzero(d) gate bites.
        let gates = vault_gates(ASSET, SHARE);
        let row = make_row(
            [TAG_VAULT as u32, 17, 0, 0],
            1,
            2,
            /*after_assets*/ 2,
            4,
            24,
        );
        assert!(
            !all_zero_settle(&gates, &row),
            "a no-deposit (d = 0) must violate the is-nonzero(d) gate"
        );
    }

    #[test]
    fn dilution_over_mint_is_unsat() {
        // Minting 21 shares for a deposit of 10 (Ta·m = 2·21 = 42 > Sa·d = 4·10 = 40) dilutes the
        // existing holders — the borrow comparison produces a final borrow ⟹ the no-borrow gate bites.
        let gates = vault_gates(ASSET, SHARE);
        let row = make_row(
            [TAG_VAULT as u32, 17, 0, 0],
            1,
            2,
            12,
            4,
            /*after_shares*/ 25,
        );
        assert!(
            !all_zero_settle(&gates, &row),
            "a diluting (over-mint) deposit must violate the no-dilution compare"
        );
    }

    #[test]
    fn boundary_fair_mint_satisfies() {
        // The exact-equality boundary Ta·m = Sa·d (no dilution, no surplus). 2·20 = 4·10 = 40.
        let gates = vault_gates(ASSET, SHARE);
        let row = make_row([TAG_VAULT as u32, 17, 0, 0], 1, 2, 12, 4, 24);
        assert!(
            all_zero_settle(&gates, &row),
            "the fair-mint equality boundary must satisfy (≤ is non-strict)"
        );
    }

    #[test]
    fn declared_vault_with_selector_off_is_unsat() {
        let gates = vault_gates(ASSET, SHARE);
        let row = make_row([TAG_VAULT as u32, 17, 0, 0], /*sel*/ 0, 2, 12, 4, 24);
        assert!(
            !all_zero_settle(&gates, &row),
            "a declared-vault cell cannot dodge the no-dilution discipline by SEL = 0"
        );
    }

    #[test]
    fn first_row_force_inert_on_padding() {
        let gates = vault_gates(ASSET, SHARE);
        let row = make_row([TAG_VAULT as u32, 17, 0, 0], /*sel*/ 0, 2, 12, 4, 24);
        assert_eq!(row[FLOOR_VAULT_COL], BabyBear::ONE);
        let all_inert = gates
            .iter()
            .all(|g| violation(g, &row, &row, /*is_first*/ false) == BabyBear::ZERO);
        assert!(
            all_inert,
            "with sel 0 every vault gate must be inert on a padding row (first-row scoping)"
        );
    }

    #[test]
    fn no_vault_declared_leaves_selector_free() {
        let gates = vault_gates(ASSET, SHARE);
        let row = make_row([6, 17, 0, 0], /*sel*/ 0, 2, 12, 4, 24);
        assert_eq!(row[FLOOR_VAULT_COL], BabyBear::ZERO);
        assert!(
            all_zero_settle(&gates, &row),
            "no vault declared ⟹ no false reject"
        );
    }

    #[test]
    fn caveat_uniformity_bites_on_non_uniform_manifest() {
        let gates = vault_gates(ASSET, SHARE);
        let local = make_row([6, 17, 0, 0], 0, 2, 12, 4, 24);
        let next = make_row([TAG_VAULT as u32, 17, 0, 0], 0, 2, 12, 4, 24);
        let bites = gates
            .iter()
            .any(|g| violation(g, &local, &next, /*is_first*/ true) != BabyBear::ZERO);
        assert!(
            bites,
            "a non-uniform caveat manifest must trip a uniformity gate"
        );
    }
}
