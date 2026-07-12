//! # `bare_floor_refuse_weld` — THE GENTIAN FLAG-DAY Rust shadow: the bare-descriptor dodge, CLOSED.
//!
//! The Rust deployed-column shadow of `Dregg2.Deos.BareCohortFloorRefuse`
//! (`declared_tag_unsat_under_bare`). Where `carrier_floor_weld` decodes the escrow floor and FORCES
//! the satisfaction selector on the WELDED SATISFACTION descriptor, this module welds a
//! `floor == 0`-REFUSE onto every deployed BARE cohort member so a cell that DECLARES a capacity
//! caveat is UNSATISFIABLE under the bare descriptor — forcing the turn onto the satisfaction
//! descriptor and closing the dodge on the DEFAULT path.
//!
//! ## The dodge
//!
//! A `SettleEscrow`/`Discharge`/`VaultDeposit` executes on the wire as a plain zero-amount `Transfer`
//! routed to the BARE `transferVmDescriptor2R24` (no satisfaction gate). A forger settling a half-open
//! escrow on a declared-capacity cell produces an honest-looking transfer STARK that verifies under the
//! bare VK; a pure light client cannot reject it. Nothing FORCES a declared-capacity cell onto the
//! welded satisfaction descriptor. That is the bare-descriptor dodge.
//!
//! ## The fix (the whole-cohort flag-day)
//!
//! Weld onto every deployed bare cohort member, per capacity tag `T ∈ {17 escrow, 18 discharge,
//! 19 vault}`, a decode+refuse block: the per-slot is-zero gadget against `T` over the
//! caveat-commit-bound type-tag columns (cols 291/298/305/312, chained to PI 45), a running-OR fold
//! into a per-tag floor column, then [`floor_zero_refuse_gate`] (`floor == 0`). A cell whose committed
//! manifest declares `T` decodes `floor = 1` (the decode is pinned to the committed manifest by the
//! deployed `caveatCommit` binding — no new hypothesis), so the refuse gate makes it UNSAT. A
//! non-declaring cell decodes `floor = 0` and the refuse is inert (no false reject; the flip is
//! complete). The blocks ride DISJOINT aux column headroom so all three coexist.
//!
//! ## FLIPPED — the refuse is in the DEPLOYED committed VK bytes
//!
//! These gates are the emit-side deployed-column realization of the Lean soundness, and the flag-day
//! regen (`scripts/emit-descriptors.sh` over the welded `v3RegistryCapOpenDep`) has LANDED them into the
//! committed cohort. Every one of the 36 `rotation-v3-staged-registry.tsv` cohort rows carries the
//! `-gentian-deployed-bare-refuse` suffix and the three per-tag `floor == 0`-refuse gates over ITS OWN
//! base (§HETEROGENEOUS GEOMETRY): the 34 standard graduated members base at `GRAD_ROT_WIDTH = 1581`
//! (widen to `trace_width` 1626, floor cols 1593/1609/1625 — the `bit_col`/`floor_col` constants here);
//! the two DISTINCT V1Face members (`setFieldDyn` / `custom`, base 1553) base at 1553 (widen to 1598,
//! floor cols 1565/1581/1597) so the block never strands a 28-column dead gap. The prove-side
//! [`fill_refuse_aux`] recovers each member's aux base from its OWN committed floor gates
//! ([`refuse_aux_base`]), so it lands right regardless of geometry. Witnessed on the DEPLOYED bytes by
//! `deployed_cohort_bytes_carry_the_refuse` below. The apex `Rfix` re-keys over the SAME
//! `v3RegistryCapOpenDep`, so the committed VK and the soundness apex coincide on the refuse. The
//! anti-launder forge tooth still BITES (declared-capacity row UNSAT, non-declared row SAT); the
//! deployed-bytes test proves the flip is REAL, not staged.

use super::carrier_floor_weld::caveat_tag_col;
use super::pi::{
    SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION, SLOT_CAVEAT_TAG_SETTLE_ESCROW,
    SLOT_CAVEAT_TAG_VAULT_DEPOSIT,
};
use super::trace_rotated::GRAD_ROT_WIDTH;
use crate::descriptor_ir2::{VmConstraint2, WindowExpr, WindowGateSpec};
use crate::field::BabyBear;
use crate::lean_descriptor_air::{LeanExpr, VmConstraint};

use super::columns::rotation::caveat as cav;

/// The three deployed capacity tags the flag-day refuses — escrow (17), discharge (18), vault (19).
/// A cell declaring ANY of these is forced onto its satisfaction descriptor. Lean twins
/// `Dregg2.Deos.ConstraintBinding.{tagSettleEscrow, tagDischargeObligation, tagVaultDeposit}`.
pub const CAPACITY_TAGS: [u32; 3] = [
    SLOT_CAVEAT_TAG_SETTLE_ESCROW,
    SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION,
    SLOT_CAVEAT_TAG_VAULT_DEPOSIT,
];

/// The per-tag refuse-block aux stride (bits[0..4), inv[4..8), or[8..11), floor[12]) in free headroom
/// past the graduated rotated lane. Block `b` (0 = escrow, 1 = discharge, 2 = vault) rides
/// `GRAD_ROT_WIDTH + b·STRIDE + …`, DISJOINT so the three blocks coexist on one bare member.
pub const REFUSE_STRIDE: usize = 16;

/// The per-slot is-zero boolean aux column for tag block `b`, caveat slot `k`.
pub const fn bit_col(b: usize, k: usize) -> usize {
    GRAD_ROT_WIDTH + b * REFUSE_STRIDE + k
}
/// The per-slot inverse-witness aux column for tag block `b`, caveat slot `k`.
pub const fn inv_col(b: usize, k: usize) -> usize {
    GRAD_ROT_WIDTH + b * REFUSE_STRIDE + cav::MAX_CAVEATS + k
}
/// The running-OR carrier aux column `j` (`O0..O2`) for tag block `b`.
pub const fn or_col(b: usize, j: usize) -> usize {
    GRAD_ROT_WIDTH + b * REFUSE_STRIDE + 2 * cav::MAX_CAVEATS + j
}
/// **THE PER-TAG FLOOR COLUMN** for block `b` — the running-OR terminus; the refuse gate demands it 0.
pub const fn floor_col(b: usize) -> usize {
    GRAD_ROT_WIDTH + b * REFUSE_STRIDE + 3 * cav::MAX_CAVEATS
}

/// (def_k) is-zero defining gate `b_k + (tag_k − T)·inv_k − 1 == 0`. Lean `isZeroDefGateT`.
fn is_zero_def_gate(tag: i64, tag_c: usize, bool_c: usize, inv_c: usize) -> VmConstraint2 {
    let body = LeanExpr::add(
        LeanExpr::add(
            LeanExpr::var(bool_c),
            LeanExpr::mul(
                LeanExpr::add(LeanExpr::var(tag_c), LeanExpr::constant(-tag)),
                LeanExpr::var(inv_c),
            ),
        ),
        LeanExpr::constant(-1),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// (force_k) is-zero forcing gate `(tag_k − T)·b_k == 0`. Lean `isZeroForceGateT`.
fn is_zero_force_gate(tag: i64, tag_c: usize, bool_c: usize) -> VmConstraint2 {
    let body = LeanExpr::mul(
        LeanExpr::add(LeanExpr::var(tag_c), LeanExpr::constant(-tag)),
        LeanExpr::var(bool_c),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// (seed) OR seed `O0 − b0 == 0`. Lean `CarrierBoundFloorGadget.orSeedGate`.
fn or_seed_gate(out_c: usize, bit_c: usize) -> VmConstraint2 {
    let body = LeanExpr::add(
        LeanExpr::var(out_c),
        LeanExpr::mul(LeanExpr::constant(-1), LeanExpr::var(bit_c)),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// (fold) OR fold `out − (inOr + b − inOr·b) == 0`. Lean `CarrierBoundFloorGadget.orFoldGate`.
fn or_fold_gate(out_c: usize, in_or_c: usize, bit_c: usize) -> VmConstraint2 {
    let or = LeanExpr::add(
        LeanExpr::add(LeanExpr::var(in_or_c), LeanExpr::var(bit_c)),
        LeanExpr::mul(
            LeanExpr::constant(-1),
            LeanExpr::mul(LeanExpr::var(in_or_c), LeanExpr::var(bit_c)),
        ),
    );
    let body = LeanExpr::add(
        LeanExpr::var(out_c),
        LeanExpr::mul(LeanExpr::constant(-1), or),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// **(refuse) THE FLOOR==0-REFUSE GATE** `floor_col == 0`, every (non-last) row. Combined with the
/// decode (which forces `floor_col = 1` when the committed manifest declares the tag), a declared cell
/// has NO satisfying assignment — the bare member REFUSES it. Lean
/// `Dregg2.Deos.BareCohortFloorRefuse.floorZeroRefuseGate`.
pub fn floor_zero_refuse_gate(floor_c: usize) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(LeanExpr::var(floor_c)))
}

/// (caveat-uniformity) `nxt(tag_k) − loc(tag_k) == 0` on the transition — couples the decode row to the
/// last-row PI-45 caveat commit (a forger cannot light a no-declaration manifest on the decode row
/// while committing the real declaration to PI 45). Lean `caveatUniformGate`.
fn caveat_uniform_gate(tag_c: usize) -> VmConstraint2 {
    let body = WindowExpr::Add(
        Box::new(WindowExpr::Nxt(tag_c)),
        Box::new(WindowExpr::Mul(
            Box::new(WindowExpr::Const(-1)),
            Box::new(WindowExpr::Loc(tag_c)),
        )),
    );
    VmConstraint2::WindowGate(WindowGateSpec {
        body,
        on_transition: true,
    })
}

/// The decode+refuse gate block for ONE capacity tag `T` at block index `b`: four per-slot is-zero
/// gadgets against `T` over the caveat-bound type-tag columns, the running-OR fold into `floor_col(b)`,
/// and the `floor == 0` refuse. Lean `refuseGatesT`.
fn tag_refuse_gates(b: usize, tag: u32) -> Vec<VmConstraint2> {
    let t = tag as i64;
    let mut gates = Vec::with_capacity(13);
    for k in 0..cav::MAX_CAVEATS {
        gates.push(is_zero_def_gate(
            t,
            caveat_tag_col(k),
            bit_col(b, k),
            inv_col(b, k),
        ));
        gates.push(is_zero_force_gate(t, caveat_tag_col(k), bit_col(b, k)));
    }
    gates.push(or_seed_gate(or_col(b, 0), bit_col(b, 0)));
    gates.push(or_fold_gate(or_col(b, 1), or_col(b, 0), bit_col(b, 1)));
    gates.push(or_fold_gate(or_col(b, 2), or_col(b, 1), bit_col(b, 2)));
    gates.push(or_fold_gate(floor_col(b), or_col(b, 2), bit_col(b, 3)));
    gates.push(floor_zero_refuse_gate(floor_col(b)));
    gates
}

/// **THE WHOLE-COHORT BARE FLOOR-REFUSE GATES (STAGED).** For every deployed bare cohort member: one
/// decode+refuse block per capacity tag (escrow/discharge/vault) at disjoint aux columns, plus the four
/// shared caveat-uniformity window gates coupling the decode to the PI-45 commit. A cell declaring ANY
/// capacity caveat is UNSAT under the bare member; a non-declaring cell is untouched. The
/// `scripts/emit-descriptors.sh` flag-day welds this onto `v3RegistryBare` (whole-cohort fingerprint
/// move, geometry stable). Lean soundness `BareCohortFloorRefuse.declared_tag_unsat_under_bare`.
pub fn bare_floor_refuse_gates() -> Vec<VmConstraint2> {
    let mut gates = Vec::new();
    for (b, &tag) in CAPACITY_TAGS.iter().enumerate() {
        gates.extend(tag_refuse_gates(b, tag));
    }
    for k in 0..cav::MAX_CAVEATS {
        gates.push(caveat_uniform_gate(caveat_tag_col(k)));
    }
    gates
}

/// The deployed refuse-welded descriptor-name suffix (the gentian flag-day cohort). The weld is
/// applied to exactly the members whose json `name` ends with this; the producer aux-fill below
/// keys on the SAME suffix so it fills iff-welded — width alone would false-positive (a cap-open
/// appendix also anchors at [`GRAD_ROT_WIDTH`]).
pub const REFUSE_WELD_SUFFIX: &str = "-gentian-deployed-bare-refuse";

/// **THE COMPLETENESS LEG of the gentian flag-day.** Fill the bare-floor-refuse decode witnesses —
/// per caveat slot the is-zero `bit`, its inverse witness `inv` (when the slot is NOT the tag), the
/// running-OR carriers, and the folded `floor` — for every capacity-tag block, reading the caveat
/// type-tag columns the row already carries. The prove wrapper calls this once per row, AFTER
/// [`crate::descriptor_ir2::fill_chip_lanes`], for a refuse-welded descriptor.
///
/// The flag-day welded the `floor == 0` refuse gates onto every bare cohort member's committed VK
/// and updated the *transfer* producer, but did NOT propagate the aux fill to the non-transfer
/// producers — so their honest traces left cols `GRAD_ROT_WIDTH..trace_width` (in particular the
/// `inv` witnesses) at zero, violating the is-zero decode gate → `OodEvaluationMismatch` on
/// light-client verify. This restores that leg:
/// - a NON-declaring cell decodes every `floor_col(b) = 0`, the refuse gates are inert, and the
///   honest trace proves + verifies (COMPLETENESS restored — no false reject);
/// - a DECLARING cell has the matching slot decode `bit = 1`, folding `floor = 1`, so the
///   `floor == 0` gate is UNSAT — the cell cannot route through the bare descriptor and is forced
///   onto its satisfaction descriptor (SOUNDNESS preserved: the bare-descriptor dodge stays closed).
/// Recover the refuse-block aux base column for a refuse-welded descriptor DIRECTLY from its own
/// committed floor-refuse gates, so the fill lands on the exact columns the gates read — robust to
/// where the weld placed the block (V3 narrow rides `GRAD_ROT_WIDTH`; a wide member rides
/// `trace_width − 3·REFUSE_STRIDE`; a WIDE+umem member rides the WIDE base with the umem leg appended
/// PAST the refuse block, so `trace_width − …` no longer locates it).
///
/// The three `floor_col(b) == 0` refuse gates are the only bare-`Var` gates the weld emits, at
/// `aux_base + b·REFUSE_STRIDE + 3·MAX_CAVEATS` — a triple `{c, c+REFUSE_STRIDE, c+2·REFUSE_STRIDE}`.
/// We take the HIGHEST such triple (the refuse block sits in the aux headroom, above any base-AIR
/// bare-`Var` gate) and back out `aux_base = c − 3·MAX_CAVEATS`.
fn refuse_aux_base(desc: &crate::descriptor_ir2::EffectVmDescriptor2) -> usize {
    let mut bare_var_gates: Vec<usize> = desc
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Base(VmConstraint::Gate(LeanExpr::Var(col))) => Some(*col),
            _ => None,
        })
        .collect();
    bare_var_gates.sort_unstable();
    bare_var_gates.dedup();
    let has = |c: usize| bare_var_gates.binary_search(&c).is_ok();
    // Descending scan → the first (highest) `floor_col(0)` of a full refuse triple.
    if let Some(floor0) = bare_var_gates
        .iter()
        .rev()
        .copied()
        .find(|&c| has(c + REFUSE_STRIDE) && has(c + 2 * REFUSE_STRIDE))
    {
        return floor0 - 3 * cav::MAX_CAVEATS;
    }
    // Fallback (should be unreachable for a genuinely refuse-welded descriptor): the V3-narrow
    // fixed base, else the trailing-block assumption. Preserves the pre-umem behaviour.
    let v3_refuse_width = floor_col(CAPACITY_TAGS.len() - 1) + 1;
    if desc.trace_width == v3_refuse_width {
        GRAD_ROT_WIDTH
    } else {
        desc.trace_width - 3 * REFUSE_STRIDE
    }
}

/// Recover the four caveat TYPE-TAG columns the refuse decode reads, from the descriptor's OWN
/// committed is-zero DEF gates (`b_k + (tag_k − T)·inv_k − 1 == 0`) of block 0. The tag columns
/// are a function of the member's geometry — the bare cohort reads the fixed
/// `caveat_tag_col(k)` (`CAVEAT_BASE + 1 + k·ENTRY_SIZE`), but a HARDENED `…-v1-avail`
/// transfer/burn member (the GAP #4 availability weld) shifts the whole caveat region by its
/// avail pad, so the fill must land on the columns the committed gates actually constrain, not a
/// fixed base. Falls back to the fixed columns per-slot when a gate is not found.
fn recover_tag_cols(
    desc: &crate::descriptor_ir2::EffectVmDescriptor2,
    aux_base: usize,
) -> [usize; cav::MAX_CAVEATS] {
    let mut cols = [0usize; cav::MAX_CAVEATS];
    for (k, out) in cols.iter_mut().enumerate() {
        let bit = aux_base + k; // block 0, slot k (`bit_col(0, k)` at this member's aux base)
        // Match `Gate(Add(Add(Var(bit), Mul(Add(Var(tag), Const(_)), Var(_))), Const(-1)))`.
        let found = desc.constraints.iter().find_map(|c| {
            let VmConstraint2::Base(VmConstraint::Gate(LeanExpr::Add(outer_l, outer_r))) = c else {
                return None;
            };
            if !matches!(**outer_r, LeanExpr::Const(-1)) {
                return None;
            }
            let LeanExpr::Add(bit_e, mul_e) = &**outer_l else {
                return None;
            };
            if !matches!(**bit_e, LeanExpr::Var(v) if v == bit) {
                return None;
            }
            let LeanExpr::Mul(diff_e, _inv_e) = &**mul_e else {
                return None;
            };
            let LeanExpr::Add(tag_e, _t_e) = &**diff_e else {
                return None;
            };
            match **tag_e {
                LeanExpr::Var(tag_c) => Some(tag_c),
                _ => None,
            }
        });
        *out = found.unwrap_or_else(|| caveat_tag_col(k));
    }
    cols
}

pub fn fill_refuse_aux(desc: &crate::descriptor_ir2::EffectVmDescriptor2, row: &mut [BabyBear]) {
    // Detect the refuse weld by SUBSTRING, not `ends_with`: an additive downstream weld (the WIDE+umem
    // leg, `weld_umem_into_descriptor_with_suffix`) appends its own `-umem-wide-welded-staged` suffix
    // AFTER the `-gentian-deployed-bare-refuse` mark — leaving the refuse suffix in the MIDDLE of the
    // name. The refuse gates are still present (the umem weld preserves every existing constraint), so
    // the decode witnesses still need filling; keying on `ends_with` here silently skipped them and
    // left the `inv` columns zero → the is-zero decode gate is UNSAT on every honest umem-welded turn.
    if !desc.name.contains(REFUSE_WELD_SUFFIX) {
        return;
    }
    let aux_base = refuse_aux_base(desc);
    let tag_cols = recover_tag_cols(desc, aux_base);
    let bit_at = |b: usize, k: usize| aux_base + b * REFUSE_STRIDE + k;
    let inv_at = |b: usize, k: usize| aux_base + b * REFUSE_STRIDE + cav::MAX_CAVEATS + k;
    let or_at = |b: usize, j: usize| aux_base + b * REFUSE_STRIDE + 2 * cav::MAX_CAVEATS + j;
    let floor_at = |b: usize| aux_base + b * REFUSE_STRIDE + 3 * cav::MAX_CAVEATS;
    for (b, &tag) in CAPACITY_TAGS.iter().enumerate() {
        let mut running_or = 0u32;
        for k in 0..cav::MAX_CAVEATS {
            let tag_k = row[tag_cols[k]];
            let is_tag = tag_k == BabyBear::new(tag);
            let bit = u32::from(is_tag);
            row[bit_at(b, k)] = BabyBear::new(bit);
            if !is_tag {
                // The is-zero DEFINING gate `b_k + (tag_k − T)·inv_k − 1 == 0` forces this witness
                // when the slot is not the tag; when it IS the tag `b_k = 1` leaves `inv_k` free.
                row[inv_at(b, k)] = (tag_k - BabyBear::new(tag))
                    .inverse()
                    .expect("a nonzero (tag_k − T) has a field inverse");
            }
            let next_or = running_or | bit;
            if k < cav::MAX_CAVEATS - 1 {
                row[or_at(b, k)] = BabyBear::new(next_or);
            } else {
                row[floor_at(b)] = BabyBear::new(next_or);
            }
            running_or = next_or;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_ir2::eval_lean_expr;
    use crate::field::BabyBear;

    /// Row-aware violation of one constraint against a `(local, next)` window with an `is_first` tag —
    /// replaying the deployed firing domains. Returns `0` iff satisfied.
    fn violation(c: &VmConstraint2, local: &[BabyBear], next: &[BabyBear]) -> BabyBear {
        match c {
            VmConstraint2::Base(VmConstraint::Gate(body)) => eval_lean_expr(body, local),
            VmConstraint2::WindowGate(g) => eval_window_expr(&g.body, local, next),
            other => panic!("unexpected refuse constraint kind: {other:?}"),
        }
    }

    fn eval_window_expr(e: &WindowExpr, local: &[BabyBear], next: &[BabyBear]) -> BabyBear {
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
            WindowExpr::Add(a, b) => {
                eval_window_expr(a, local, next) + eval_window_expr(b, local, next)
            }
            WindowExpr::Mul(a, b) => {
                eval_window_expr(a, local, next) * eval_window_expr(b, local, next)
            }
        }
    }

    /// Build a wide row, fill the four caveat type-tag columns + every tag block's decode witness
    /// (bit = (tag_k == T), inv = 1/(tag_k − T) when nonzero, OR fold into `floor_col`).
    fn make_row(tags: [u32; cav::MAX_CAVEATS]) -> Vec<BabyBear> {
        let width = (0..CAPACITY_TAGS.len())
            .map(|b| floor_col(b) + 1)
            .max()
            .unwrap()
            .max(caveat_tag_col(cav::MAX_CAVEATS - 1) + 1);
        let mut row = vec![BabyBear::ZERO; width];
        for k in 0..cav::MAX_CAVEATS {
            row[caveat_tag_col(k)] = BabyBear::new(tags[k]);
        }
        for (b, &tag) in CAPACITY_TAGS.iter().enumerate() {
            let mut running_or = 0u32;
            for k in 0..cav::MAX_CAVEATS {
                let is_tag = tags[k] == tag;
                let bit = if is_tag { 1 } else { 0 };
                row[bit_col(b, k)] = BabyBear::new(bit);
                if !is_tag {
                    let d = BabyBear::new(tags[k]) - BabyBear::new(tag);
                    row[inv_col(b, k)] = d.inverse().expect("nonzero tag−T has a field inverse");
                }
                let next_or = running_or | bit;
                if k < cav::MAX_CAVEATS - 1 {
                    row[or_col(b, k)] = BabyBear::new(next_or);
                } else {
                    row[floor_col(b)] = BabyBear::new(next_or);
                }
                running_or = next_or;
            }
        }
        row
    }

    fn all_decode_gates_zero(gates: &[VmConstraint2], row: &[BabyBear]) -> bool {
        gates
            .iter()
            .all(|g| violation(g, row, row) == BabyBear::ZERO)
    }

    #[test]
    fn tag_cols_are_the_deployed_bound_columns() {
        // The decode reads the EXACT deployed caveat-manifest type-tag columns the COVERAGE carrier
        // binds via the caveat-commit chain (imported `caveat_tag_col` = `CAVEAT_BASE + 1 + k·ENTRY_SIZE`).
        // Concrete drift pin at the REVOKED-ROOT/178-limb geometry (CAVEAT_BASE = 666; ENTRY_SIZE = 7).
        assert_eq!(caveat_tag_col(0), 667);
        assert_eq!(caveat_tag_col(1), 674);
        assert_eq!(caveat_tag_col(2), 681);
        assert_eq!(caveat_tag_col(3), 688);
    }

    #[test]
    fn decode_and_refuse_columns_are_distinct() {
        let mut cols: Vec<usize> = Vec::new();
        for b in 0..CAPACITY_TAGS.len() {
            for k in 0..cav::MAX_CAVEATS {
                cols.push(bit_col(b, k));
                cols.push(inv_col(b, k));
            }
            cols.push(or_col(b, 0));
            cols.push(or_col(b, 1));
            cols.push(or_col(b, 2));
            cols.push(floor_col(b));
        }
        let n = cols.len();
        cols.sort_unstable();
        cols.dedup();
        assert_eq!(
            cols.len(),
            n,
            "no two refuse-block columns alias across the three tag blocks"
        );
    }

    #[test]
    fn gate_count_matches_lean() {
        // 3 tag blocks × (4×(def+force) + seed + 2 folds + final fold + refuse = 13) + 4 uniformity = 43.
        assert_eq!(tag_refuse_gates(0, SLOT_CAVEAT_TAG_SETTLE_ESCROW).len(), 13);
        assert_eq!(bare_floor_refuse_gates().len(), 3 * 13 + 4);
    }

    /// **THE ANTI-LAUNDER FORGE TOOTH (escrow).** A cell that DECLARES the escrow capacity decodes
    /// `floor = 1`; the `floor == 0`-refuse gate BITES ⟹ UNSAT under the bare member. This is the
    /// forger settling a half-open escrow via a bare Transfer, REFUSED on the default path.
    #[test]
    fn declared_escrow_is_unsat_under_bare() {
        let gates = bare_floor_refuse_gates();
        let row = make_row([SLOT_CAVEAT_TAG_SETTLE_ESCROW, 6, 0, 0]);
        assert_eq!(
            row[floor_col(0)],
            BabyBear::new(1),
            "escrow declared ⟹ block-0 floor decodes 1"
        );
        assert!(
            !all_decode_gates_zero(&gates, &row),
            "a declared-escrow cell MUST be UNSAT under the bare member — the refuse gate must bite"
        );
    }

    /// **THE ANTI-LAUNDER FORGE TOOTH (discharge + vault).** The same for the other two capacity tags —
    /// a discharge- or vault-declared cell is UNSAT under the bare member.
    #[test]
    fn declared_discharge_and_vault_are_unsat_under_bare() {
        let gates = bare_floor_refuse_gates();
        let discharge = make_row([6, SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION, 0, 0]);
        assert_eq!(
            discharge[floor_col(1)],
            BabyBear::new(1),
            "discharge ⟹ block-1 floor 1"
        );
        assert!(
            !all_decode_gates_zero(&gates, &discharge),
            "declared discharge UNSAT under bare"
        );
        let vault = make_row([0, 0, SLOT_CAVEAT_TAG_VAULT_DEPOSIT, 6]);
        assert_eq!(
            vault[floor_col(2)],
            BabyBear::new(1),
            "vault ⟹ block-2 floor 1"
        );
        assert!(
            !all_decode_gates_zero(&gates, &vault),
            "declared vault UNSAT under bare"
        );
    }

    /// **THE COMPLETENESS TOOTH (no false reject).** A cell declaring NO capacity caveat decodes every
    /// block's floor to 0; every refuse gate is inert ⟹ the bare member still ACCEPTS the honest
    /// non-declared turn.
    #[test]
    fn non_declared_cell_is_accepted_by_bare() {
        let gates = bare_floor_refuse_gates();
        let row = make_row([6, 7, 8, 9]); // no capacity tag
        for b in 0..CAPACITY_TAGS.len() {
            assert_eq!(
                row[floor_col(b)],
                BabyBear::ZERO,
                "no capacity tag ⟹ block {b} floor 0"
            );
        }
        assert!(
            all_decode_gates_zero(&gates, &row),
            "a non-declared cell must satisfy every refuse gate (no false reject)"
        );
    }

    /// The uniformity gate bites on a non-uniform manifest (a forger lighting a no-declaration decode
    /// row while committing a declaration to the next/last row).
    #[test]
    fn caveat_uniformity_bites_on_non_uniform_manifest() {
        let gates = bare_floor_refuse_gates();
        let local = make_row([6, 7, 8, 9]); // decode row: no escrow
        let next = make_row([SLOT_CAVEAT_TAG_SETTLE_ESCROW, 7, 8, 9]); // committed: escrow
        assert!(
            gates
                .iter()
                .any(|g| violation(g, &local, &next) != BabyBear::ZERO),
            "a non-uniform manifest must trip a uniformity gate"
        );
    }

    /// **THE ANTI-LAUNDER GATE, ON THE DEPLOYED BYTES (VK-EPOCH §9.3b).** The flip is REAL, not staged:
    /// every one of the 36 deployed cohort rows in the committed `rotation-v3-staged-registry.tsv`
    /// carries the flag-day weld — the `-gentian-deployed-bare-refuse` name suffix, the per-member
    /// widened `trace_width`, and the three pure `floor_col(b) == 0`-refuse gates over ITS OWN base.
    /// §HETEROGENEOUS GEOMETRY: a standard graduated member (base `GRAD_ROT_WIDTH = 1581`) widens to
    /// `1626` with floor cols `1593/1609/1625`; the two DISTINCT V1Face members (setFieldDyn / custom,
    /// base `1553` — four fewer chip sites) widen to `1598` with floor cols `1565/1581/1597` over THEIR
    /// own 1553 base (NOT the fixed 1581 that would strand a 28-column dead gap). Both derive from the
    /// per-member aux base = `trace_width − (3·REFUSE_STRIDE − 3)`; the refuse block spans `base..base+44`.
    /// A light client that verifies any of these deployed descriptors REFUSES a declared-capacity dodge
    /// (Lean `declared_capacity_unsat_deployed`), because the refuse block is in the COMMITTED VK bytes,
    /// not merely the synthetic gates the other tests exercise.
    #[test]
    fn deployed_cohort_bytes_carry_the_refuse() {
        let tsv = crate::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
        // The refuse floor gate the Lean/Rust deployed alignment welds (compact-JSON serialized).
        let refuse_gate =
            |col: usize| format!("{{\"t\":\"gate\",\"body\":{{\"t\":\"var\",\"v\":{col}}}}}");
        // Per-member widening span: the weld widens to `fcDep base 2 + 1 = base + 45`.
        const REFUSE_SPAN: usize = 2 * REFUSE_STRIDE + 13; // = 45
        // The refuse block rides the member's OWN base; floor col b = base + b·REFUSE_STRIDE + 12.
        let member_floor_col =
            |base: usize, b: usize| base + b * REFUSE_STRIDE + 3 * cav::MAX_CAVEATS;

        use crate::effect_vm::trace_rotated::{BURN_AVAIL_PAD, TRANSFER_AVAIL_PAD};
        // The distinct-geometry V1Face members (setFieldDyn / custom) carry four fewer chip
        // sites than the standard graduated member.
        const DISTINCT_BASE: usize = GRAD_ROT_WIDTH - 28; // 1619

        let mut cohort_rows = 0usize;
        let mut standard_rows = 0usize;
        let mut distinct_rows = 0usize;
        let mut avail_rows = 0usize;
        for line in tsv.lines() {
            let cols: Vec<&str> = line.split('\t').collect();
            // v3rot cohort rows are `key \t name \t json`; the welded cohort carries the suffix.
            let name = cols.get(1).copied().unwrap_or("");
            if !name.ends_with("-gentian-deployed-bare-refuse") {
                continue;
            }
            cohort_rows += 1;
            let json = cols.last().copied().unwrap_or("");
            // Derive the member's per-member widened width from its own bytes.
            let tw: usize = json
                .split("\"trace_width\":")
                .nth(1)
                .and_then(|s| s.split(|c: char| !c.is_ascii_digit()).next())
                .and_then(|s| s.parse().ok())
                .unwrap_or_else(|| panic!("cohort row {name} has a trace_width"));
            let base = tw - REFUSE_SPAN;
            // Per-member geometry: the standard graduated base, the distinct V1Face base
            // (setFieldDyn / custom, four fewer chip sites), or a HARDENED `…-v1-avail` member
            // (the GAP #4 availability weld — transfer pad 10 / burn pad 8 over the graduated
            // base, since the avail witness columns widen the v1 face BEFORE the appendix).
            if name.contains("-transfer-v1-avail") {
                assert_eq!(
                    base,
                    GRAD_ROT_WIDTH + TRANSFER_AVAIL_PAD,
                    "hardened transfer member bases at GRAD_ROT_WIDTH + the avail pad"
                );
                avail_rows += 1;
            } else if name.contains("-burn-v1-avail") {
                assert_eq!(
                    base,
                    GRAD_ROT_WIDTH + BURN_AVAIL_PAD,
                    "hardened burn member bases at GRAD_ROT_WIDTH + the avail pad"
                );
                avail_rows += 1;
            } else if base == GRAD_ROT_WIDTH {
                standard_rows += 1;
            } else if base == DISTINCT_BASE {
                distinct_rows += 1;
            } else {
                panic!(
                    "cohort row {name} has unexpected welded width {tw} (base {base}; expected \
                     the standard {GRAD_ROT_WIDTH}, distinct {DISTINCT_BASE}, or avail-padded base)"
                );
            }
            for (b, tag) in [(0, "escrow"), (1, "discharge"), (2, "vault")] {
                let g = refuse_gate(member_floor_col(base, b));
                assert!(
                    json.contains(g.as_str()),
                    "deployed cohort row {name} must carry the {tag} floor-refuse gate at its OWN base \
                     column {} in its committed bytes",
                    member_floor_col(base, b)
                );
            }
        }
        // The whole bare cohort (28 named + 8 setField slots) must be welded — not a subset.
        assert_eq!(
            cohort_rows, 36,
            "all 36 deployed bare cohort rows must carry the flag-day refuse weld"
        );
        // Exactly the two distinct-geometry members (setFieldDyn + custom) ride the reduced base;
        // transfer/burn ride the avail-padded base once the availability flip is INSTALLED (0
        // before the regen, 2 after); the rest are standard graduated members.
        assert_eq!(
            distinct_rows, 2,
            "setFieldDyn + custom are the two distinct-geometry members"
        );
        assert!(
            avail_rows == 0 || avail_rows == 2,
            "the availability flip lands on BOTH transfer and burn or on neither (got {avail_rows})"
        );
        assert_eq!(
            standard_rows + avail_rows,
            34,
            "the 34 non-distinct cohort members are standard or avail-hardened members"
        );
    }
}
