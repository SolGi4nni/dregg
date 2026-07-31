//! **The unforced-PI-pin census, measured on the DEPLOYED bytes through the DEPLOYED decoder.**
//!
//! A `PiBinding { row, col, pi_index }` is `local[col] == pv[pi_index]` on the tagged row
//! (`descriptor_ir2.rs`, the `Ir2Air` eval). That is a BINDING only when something else in the
//! member forces `local[col]`. When no other constraint reads the column, the prover chooses BOTH
//! sides — it picks the column value, publishes it, and the pin is satisfied by construction. The
//! published slot is then host trust wearing an AIR's clothes: a full node compensates by
//! OVERWRITING the slot from its own trusted turn before verifying, and **a light client has no
//! host to do the overwriting.**
//!
//! This file authors no constraint. It parses the three deployed registry TSVs with
//! `parse_vm_descriptor2` — the same decoder the prover feeds — and measures. The AIR-side repair
//! is Lean-authored: `metatheory/Dregg2/Circuit/Emit/UnforcedPiPins.lean` defines `forcedCols` /
//! `unforcedPins` / `dropUnforcedPins`, proves the subtraction a weakening
//! (`satisfied2_dropUnforcedPins`), proves it a FIXPOINT (`unforcedPins_dropUnforcedPins`), proves
//! the dropped column DEAD afterwards (`dropUnforcedPins_col_dead`, so the already-proven E1
//! kill-set removes it), and proves the dropped pin a no-op
//! (`unforced_pin_row_admits_any_value`: overwrite the column and every slot its pins publish with
//! an ARBITRARY value and every constraint still holds — a real binding refuses an inconsistent
//! publication; this one accepts every publication).
//!
//! ## The two reference notions, and why both are here
//!
//! * **row-blind** — `col` appears in NO non-pin constraint anywhere. The Lean subtraction's
//!   condition, and the strongest statement: nothing in the member relates the column to anything.
//! * **row-aware** — `col` appears only in constraints that are INACTIVE on the row the pin fires
//!   on. The live instance is the `.transition { hi, lo }` continuity chain, which is
//!   `is_transition`-gated: it forces row `i+1`'s `state_before[hi]` from row `i`'s
//!   `state_after[lo]` for `i < n-1`. So the FIRST row's `state_before` column has no predecessor
//!   to be forced from, and the LAST row's `state_after` column has no successor. That is exactly
//!   the multiplier vacuity the last-row anchor forge was: a column can look referenced and be
//!   free precisely where the pin reads it.
//!
//! ## Expected counts and the convergence re-emit
//!
//! The constants below are the measurement as of 2026-07-30, BEFORE the convergence re-emit. When
//! that re-emit lands `dropUnforcedPins`, the row-blind counts go to ZERO and this test goes RED —
//! which is the point: whoever lands it must state the new number here.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, VmConstraint2, WindowExpr, parse_vm_descriptor2,
};
use dregg_circuit::effect_vm_descriptors::{
    V3_STAGED_REGISTRY_TSV, WIDE_REGISTRY_STAGED_TSV, WIDE_UMEM_WELD_REGISTRY_TSV,
};
use dregg_circuit::lean_descriptor_air::{HashInput, LeanExpr, VmConstraint, VmRow};

/// The EffectVM state-block bases the offset-encoded `Transition { hi, lo }` reads through
/// (`lean_descriptor_air::EFFECTVM_STATE_{BEFORE,AFTER}_BASE`, re-derived here so a layout move
/// breaks this file rather than silently mis-attributing a reference).
const STATE_BEFORE_BASE: usize = 54;
const STATE_AFTER_BASE: usize = 76;

fn expr_cols(e: &LeanExpr, out: &mut Vec<usize>) {
    match e {
        LeanExpr::Var(v) => out.push(*v),
        LeanExpr::Const(_) => {}
        LeanExpr::Add(a, b) | LeanExpr::Mul(a, b) => {
            expr_cols(a, out);
            expr_cols(b, out);
        }
    }
}

fn wexpr_cols(e: &WindowExpr, loc: &mut Vec<usize>, nxt: &mut Vec<usize>) {
    match e {
        WindowExpr::Loc(c) => loc.push(*c),
        WindowExpr::Nxt(c) => nxt.push(*c),
        WindowExpr::Const(_) => {}
        WindowExpr::Add(a, b) | WindowExpr::Mul(a, b) => {
            wexpr_cols(a, loc, nxt);
            wexpr_cols(b, loc, nxt);
        }
    }
}

/// What a constraint reads, split by which row slice it reads it from. `pi_binding` contributes
/// NOTHING — the whole question is whether anything OTHER than the pin forces the column.
#[derive(Default)]
struct Reads {
    /// current-row reads, active on every row
    loc_all: Vec<usize>,
    /// current-row reads, active only on non-last rows (`is_transition`)
    loc_trans: Vec<usize>,
    /// next-row reads, active on every row (wrap included)
    nxt_all: Vec<usize>,
    /// next-row reads, active only on non-last rows
    nxt_trans: Vec<usize>,
    /// reads guarded to the first row
    first_only: Vec<usize>,
    /// reads guarded to the last row
    last_only: Vec<usize>,
}

fn collect(d: &EffectVmDescriptor2) -> Reads {
    let mut r = Reads::default();
    for c in &d.constraints {
        match c {
            VmConstraint2::Base(VmConstraint::PiBinding { .. }) => {}
            VmConstraint2::Base(VmConstraint::Gate(body)) => expr_cols(body, &mut r.loc_trans),
            VmConstraint2::Base(VmConstraint::Transition { hi, lo }) => {
                // `next[BEFORE + hi] - local[AFTER + lo]`, gated by `is_transition`
                r.nxt_trans.push(STATE_BEFORE_BASE + hi);
                r.loc_trans.push(STATE_AFTER_BASE + lo);
            }
            VmConstraint2::Base(VmConstraint::Boundary { row, body }) => match row {
                VmRow::First => expr_cols(body, &mut r.first_only),
                VmRow::Last => expr_cols(body, &mut r.last_only),
            },
            VmConstraint2::Lookup(l) => {
                for e in &l.tuple {
                    expr_cols(e, &mut r.loc_all);
                }
            }
            VmConstraint2::MemOp(m) => {
                for e in [&m.guard, &m.addr, &m.value, &m.prev_value, &m.prev_serial] {
                    expr_cols(e, &mut r.loc_all);
                }
            }
            VmConstraint2::MapOp(m) => {
                for e in [&m.guard, &m.key, &m.value] {
                    expr_cols(e, &mut r.loc_all);
                }
                for e in m.root.iter().chain(m.new_root.iter()) {
                    expr_cols(e, &mut r.loc_all);
                }
            }
            VmConstraint2::UMemOp(m) => {
                for e in [
                    &m.guard,
                    &m.key,
                    &m.present,
                    &m.value,
                    &m.prev_present,
                    &m.prev_value,
                    &m.prev_serial,
                ] {
                    expr_cols(e, &mut r.loc_all);
                }
            }
            VmConstraint2::ProofBind(p) => {
                for e in [&p.guard, &p.commit, &p.vk] {
                    expr_cols(e, &mut r.loc_all);
                }
            }
            VmConstraint2::WindowGate(w) => {
                if w.on_transition {
                    wexpr_cols(&w.body, &mut r.loc_trans, &mut r.nxt_trans);
                } else {
                    wexpr_cols(&w.body, &mut r.loc_all, &mut r.nxt_all);
                }
            }
        }
    }
    for e in &d.hash_sites {
        r.loc_all.push(e.digest_col);
        for i in &e.inputs {
            if let HashInput::Col(c) = i {
                r.loc_all.push(*c);
            }
        }
    }
    for rg in &d.ranges {
        r.loc_all.push(rg.wire);
    }
    r
}

/// row-BLIND: the column appears in no non-pin reference anywhere.
fn free_row_blind(r: &Reads, col: usize) -> bool {
    ![
        &r.loc_all,
        &r.loc_trans,
        &r.nxt_all,
        &r.nxt_trans,
        &r.first_only,
        &r.last_only,
    ]
    .iter()
    .any(|v| v.contains(&col))
}

/// row-AWARE: nothing active on the pinned row reads the column.
fn free_row_aware(r: &Reads, row: VmRow, col: usize) -> bool {
    if r.loc_all.contains(&col) || r.nxt_all.contains(&col) {
        return false;
    }
    match row {
        // `is_transition` fires on row 0 (any >=2-row trace), so a transition-gated read counts;
        // a `next[..]` read of a transition-gated constraint reaches rows 1.., never row 0.
        VmRow::First => !(r.loc_trans.contains(&col) || r.first_only.contains(&col)),
        // on the last row `is_transition` is 0, so `loc_trans` reads nothing there; but the
        // PREVIOUS row's transition-gated `next[..]` does reach it.
        VmRow::Last => !(r.nxt_trans.contains(&col) || r.last_only.contains(&col)),
    }
}

struct Census {
    members: usize,
    pins: usize,
    free_blind: usize,
    free_aware: usize,
    /// (member key, row, col, pi) for the row-blind free set
    blind_detail: Vec<(String, VmRow, usize, usize)>,
    /// (member key, row, col, pi) for the pins free ONLY on the pinned row
    aware_only_detail: Vec<(String, VmRow, usize, usize)>,
}

fn census(tsv: &str) -> Census {
    let mut out = Census {
        members: 0,
        pins: 0,
        free_blind: 0,
        free_aware: 0,
        blind_detail: Vec::new(),
        aware_only_detail: Vec::new(),
    };
    for line in tsv.lines().filter(|l| !l.is_empty()) {
        let mut it = line.split('\t');
        let key = it.next().expect("registry key").to_string();
        let _name = it.next().expect("member name");
        let json = it.next().expect("member json");
        let d = parse_vm_descriptor2(json).expect("deployed member parses");
        out.members += 1;
        let reads = collect(&d);
        for c in &d.constraints {
            if let VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }) = c {
                out.pins += 1;
                if free_row_blind(&reads, *col) {
                    out.free_blind += 1;
                    out.blind_detail.push((key.clone(), *row, *col, *pi_index));
                }
                if free_row_aware(&reads, *row, *col) {
                    out.free_aware += 1;
                    if !free_row_blind(&reads, *col) {
                        out.aware_only_detail
                            .push((key.clone(), *row, *col, *pi_index));
                    }
                }
            }
        }
    }
    out
}

/// **THE CENSUS.** Measured 2026-07-30 on the deployed bytes. `free_blind` is the set the
/// Lean-side `dropUnforcedPins` removes; when the convergence re-emit lands it, these become 0.
#[test]
fn unforced_pi_pin_census_is_pinned() {
    let v3 = census(V3_STAGED_REGISTRY_TSV);
    let wide = census(WIDE_REGISTRY_STAGED_TSV);
    let welded = census(WIDE_UMEM_WELD_REGISTRY_TSV);

    // ONE comparison, so a drift shows every number at once instead of stopping at the first.
    // `blind` is the set the Lean-side `dropUnforcedPins` removes — PRE-CONVERGENCE it is nonzero;
    // when the convergence re-emit lands the subtraction, all three go to 0 and this goes RED,
    // which is the point: whoever lands it states the new numbers here.
    let measured = format!(
        "v3 {}/{} blind={} aware={} | wide {}/{} blind={} aware={} | welded {}/{} blind={} aware={}",
        v3.members,
        v3.pins,
        v3.free_blind,
        v3.free_aware,
        wide.members,
        wide.pins,
        wide.free_blind,
        wide.free_aware,
        welded.members,
        welded.pins,
        welded.free_blind,
        welded.free_aware,
    );
    assert_eq!(
        measured,
        "v3 60/839 blind=165 aware=216 | wide 57/1639 blind=167 aware=215 \
         | welded 57/1639 blind=167 aware=215",
        "the unforced-PI-pin census moved"
    );

    // The two named candidates the audit called, confirmed here on the emitted bytes.
    let has = |c: &Census, key: &str, col: usize, pi: usize| {
        c.blind_detail
            .iter()
            .any(|(k, _, cc, pp)| k == key && *cc == col && *pp == pi)
    };
    assert!(
        has(&wide, "transferCapOpenTBVmDescriptor2R24", 928, 47),
        "the TB weld's `actor` publishes a prover-chosen felt"
    );
    assert!(
        has(&wide, "transferCapOpenTBVmDescriptor2R24", 929, 48),
        "the TB weld's `dst` publishes a prover-chosen felt"
    );
    assert!(
        has(&wide, "mintVmDescriptor2R24", 68, 46),
        "the mint-hash pin publishes a prover-chosen felt"
    );
    // …and the `src` pin of the same weld is NOT free: `targetBindGate` reads that column.
    assert!(
        !wide
            .blind_detail
            .iter()
            .any(|(k, _, _, pp)| k == "transferCapOpenTBVmDescriptor2R24" && *pp == 46),
        "the TB weld's `src` IS forced (targetBindGate + the depth-16 open read it)"
    );

    // ⚑ **THE ROW-AWARE-ONLY RESIDUE, CLASSIFIED — the part the row-blind subtraction does NOT
    // remove.** Every one of these is a LEGACY 1-felt state-commitment pin: `PI[OLD_COMMIT] =
    // state_before.STATE_COMMIT` on the FIRST row (col 54+12 = 66), or `PI[NEW_COMMIT] =
    // state_after.STATE_COMMIT` on the LAST row (col 76+12 = 88) in the three members whose col 88
    // is not a chip output. The `.transition {12,12}` chain links them to each other and to
    // NOTHING ELSE, and it is `is_transition`-gated, so the first row's before-commit has no
    // predecessor and the last row's after-commit has no successor: the prover picks the chain's
    // endpoints. What makes this a DUPLICATE rather than a hole is that the bound replacement is
    // published in the SAME PI vector — the wide 8-felt BEFORE/AFTER anchors, whose carrier columns
    // ARE poseidon2-chip outputs over the rotated limbs the `weldsAt` welds tie to these very state
    // columns. Deleting the legacy pins is "prefer deleting the old thing to keeping both"; it
    // needs the ROW-AWARE subtraction, whose no-op argument is a single-row trace edit rather than
    // the whole-column one `unforced_pin_row_admits_any_value` proves.
    //
    // This assertion is the DETECTION: if a row-aware-only free pin appears that is NOT one of
    // those two commitment slots, it is a new hole of an unknown kind and this goes red.
    const OLD_COMMIT_COL: usize = STATE_BEFORE_BASE + 12;
    const NEW_COMMIT_COL: usize = STATE_AFTER_BASE + 12;
    for c in [&v3, &wide, &welded] {
        for (key, row, col, pi) in &c.aware_only_detail {
            let known = matches!(
                (row, *col, *pi),
                (VmRow::First, OLD_COMMIT_COL, 0) | (VmRow::Last, NEW_COMMIT_COL, 8)
            );
            assert!(
                known,
                "{key}: an unforced-on-its-row pin that is NOT a legacy state-commitment slot — \
                 row {row:?} col {col} pi {pi}"
            );
        }
    }
    assert_eq!(
        (
            v3.aware_only_detail.len(),
            wide.aware_only_detail.len(),
            welded.aware_only_detail.len()
        ),
        (51, 48, 48),
        "the legacy 1-felt commitment pins whose 8-felt bound replacement rides beside them"
    );
}

/// **How many published slots are pinned AT ALL** — the other half of the light-client answer.
/// A slot no constraint pins is not "trusted", it is IGNORED by the AIR: the verifier supplies it
/// and no equation reads it. The danger is a consumer that believes it attested.
#[test]
fn published_slot_accounting_is_pinned() {
    let mut total_slots = 0usize;
    let mut pinned_slots = 0usize;
    for line in WIDE_REGISTRY_STAGED_TSV.lines().filter(|l| !l.is_empty()) {
        let json = line.split('\t').nth(2).expect("member json");
        let d = parse_vm_descriptor2(json).expect("deployed member parses");
        total_slots += d.public_input_count;
        let mut seen = vec![false; d.public_input_count];
        for c in &d.constraints {
            if let VmConstraint2::Base(VmConstraint::PiBinding { pi_index, .. }) = c {
                if *pi_index < seen.len() {
                    seen[*pi_index] = true;
                }
            }
        }
        pinned_slots += seen.iter().filter(|b| **b).count();
    }
    assert_eq!(total_slots, 3815, "wide registry published PI slots");
    assert_eq!(pinned_slots, 1639, "…of which some constraint pins");
}

/// **The `hsole` side condition of `unforced_pin_row_admits_any_value`, MEASURED.**
///
/// The Lean no-op theorem needs "no OTHER column shares a PI slot with this one" — otherwise
/// overwriting the slot could break a second pin that lands on a different column. That hypothesis
/// is not decorative and it is not assumed: across all three deployed registries the pin relation
/// is a partial INJECTION — no PI slot is pinned by two different columns, and no column is pinned
/// to two different slots. So the theorem applies to every censused pin, and if a future member
/// ever double-pins a slot this goes red before the subtraction is trusted on it.
#[test]
fn pin_relation_is_injective_so_the_no_op_theorem_applies() {
    for (label, tsv) in [
        ("v3", V3_STAGED_REGISTRY_TSV),
        ("wide", WIDE_REGISTRY_STAGED_TSV),
        ("welded", WIDE_UMEM_WELD_REGISTRY_TSV),
    ] {
        for line in tsv.lines().filter(|l| !l.is_empty()) {
            let key = line.split('\t').next().expect("key");
            let json = line.split('\t').nth(2).expect("member json");
            let d = parse_vm_descriptor2(json).expect("deployed member parses");
            let mut pairs: Vec<(usize, usize)> = Vec::new();
            for c in &d.constraints {
                if let VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. }) = c {
                    pairs.push((*pi_index, *col));
                }
            }
            for (i, (pi_a, col_a)) in pairs.iter().enumerate() {
                for (pi_b, col_b) in &pairs[i + 1..] {
                    assert!(
                        !(pi_a == pi_b && col_a != col_b),
                        "{label}/{key}: PI {pi_a} is pinned by two columns ({col_a}, {col_b})"
                    );
                    assert!(
                        !(col_a == col_b && pi_a != pi_b),
                        "{label}/{key}: column {col_a} is pinned to two PI slots ({pi_a}, {pi_b})"
                    );
                }
            }
        }
    }
}

/// **The `APPROVED_HANDOFFS` retired sentinel, measured.**
///
/// `pi::APPROVED_HANDOFFS_BASE..+4` (PI 29..32) is the CapTP federation-scoped approved-handoffs
/// root. `ValidateHandoff` no longer exists as an effect; `pi.rs` says the slot "stays at the
/// empty-tree sentinel", and `pi.rs:864` already admits it is "bound only by the executor's PI
/// matching loop". This makes that admission a MEASUREMENT: no member of any deployed registry
/// pins those four slots to any column, so what the AIR says about them is nothing at all. They
/// are verifier-supplied inputs that no equation reads — the same class as the other 2,172
/// unpinned slots, not a binding that a light client could rely on.
///
/// Deleting the slots is a PI-layout flag day (every offset above 32 shifts, in `pi.rs`, every
/// producer's PI vector, `proof_verify.rs`, the fold and the Mina-side verifier, in one commit).
/// This test is the standing statement that nothing in-circuit is lost by doing it.
#[test]
fn approved_handoffs_sentinel_is_pinned_by_no_member() {
    use dregg_circuit::effect_vm::pi::{APPROVED_HANDOFFS_BASE, APPROVED_HANDOFFS_LEN};
    for (label, tsv) in [
        ("v3", V3_STAGED_REGISTRY_TSV),
        ("wide", WIDE_REGISTRY_STAGED_TSV),
        ("welded", WIDE_UMEM_WELD_REGISTRY_TSV),
    ] {
        for line in tsv.lines().filter(|l| !l.is_empty()) {
            let key = line.split('\t').next().expect("key");
            let json = line.split('\t').nth(2).expect("member json");
            let d = parse_vm_descriptor2(json).expect("deployed member parses");
            for c in &d.constraints {
                if let VmConstraint2::Base(VmConstraint::PiBinding { pi_index, .. }) = c {
                    assert!(
                        !(APPROVED_HANDOFFS_BASE..APPROVED_HANDOFFS_BASE + APPROVED_HANDOFFS_LEN)
                            .contains(pi_index),
                        "{label}/{key}: PI {pi_index} is in the retired APPROVED_HANDOFFS window \
                         and IS pinned — the sentinel became load-bearing"
                    );
                }
            }
        }
    }
}

/// **The `RETIRED_SELECTORS` claim, corrected into a measurement.**
///
/// `circuit/src/effect_vm/columns.rs` used to state that "the AIR pins every retired selector to
/// ZERO on every row, so no valid trace can carry a doomed effect (the refusal is in-circuit)".
/// That was FALSE: measured here, across all 117 emitted members of the two registries, the 24
/// retired selector columns are referenced by **zero** constraints — no pin-to-zero, no gate, no
/// lookup. What makes them harmless is not a refusal but INERTNESS: nothing reads them, so their
/// value cannot reach any published slot. This test is that fact, and it goes red the day one of
/// them becomes load-bearing.
#[test]
fn retired_selector_columns_are_referenced_by_nothing() {
    use dregg_circuit::effect_vm::columns::sel::RETIRED_SELECTORS;
    for (label, tsv) in [
        ("v3", V3_STAGED_REGISTRY_TSV),
        ("wide", WIDE_REGISTRY_STAGED_TSV),
    ] {
        for line in tsv.lines().filter(|l| !l.is_empty()) {
            let key = line.split('\t').next().expect("key");
            let json = line.split('\t').nth(2).expect("member json");
            let d = parse_vm_descriptor2(json).expect("deployed member parses");
            let r = collect(&d);
            let pinned: Vec<usize> = d
                .constraints
                .iter()
                .filter_map(|c| match c {
                    VmConstraint2::Base(VmConstraint::PiBinding { col, .. }) => Some(*col),
                    _ => None,
                })
                .collect();
            for s in RETIRED_SELECTORS {
                assert!(
                    free_row_blind(&r, s) && !pinned.contains(&s),
                    "{label}/{key}: retired selector column {s} is referenced — the layout note \
                     claims these are inert, and a reference makes that claim false"
                );
            }
        }
    }
}
