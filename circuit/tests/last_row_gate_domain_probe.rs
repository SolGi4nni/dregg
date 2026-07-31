//! Do the deployed row-local bodies HOLD on the honest last row, and do they CATCH the forge?
//!
//! Read-only. Evaluates every row-local constraint body of the deployed wide transfer member on
//! every row of an HONEST trace, and separately on the FORGED last row, and reports which rows /
//! which bodies are non-zero.
//!
//! This is the measurement that CHOSE the repair. Before the flag day it showed: the honest trace
//! violates ZERO bodies on all 64 rows (so lifting the gates off the transition domain costs the
//! honest prover nothing), the honest last row is BYTE-IDENTICAL to the row before it, and the
//! forge's residue on the last row is the SAME `{0, 46, 47}` as on the transition-covered row — so
//! the vacuity was the `is_transition()` MULTIPLIER, not missing algebra. It also refuted candidate
//! 3 (force a trailing inert row): the trace already has 63 of them.
//!
//! ⚑ Bodies are read through `descriptor_ir2::row_local_body`, NOT by matching
//! `VmConstraint::Gate`. After the hardening the deployed members carry ZERO transition-domain
//! `Gate`s — a kind-matching probe would have gone silently vacuous at exactly the moment the
//! repair it justified landed, and reported green. Every count here is asserted non-zero for the
//! same reason.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2, WindowExpr,
    chip_absorb_all_lanes, eval_lean_expr, parse_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, generate_rotated_effect_vm_descriptor_and_trace_wide,
    transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::{
    V3_STAGED_REGISTRY_TSV, WIDE_REGISTRY_STAGED_TSV, WIDE_UMEM_WELD_REGISTRY_TSV,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint};
use dregg_turn::rotation_witness as rw;

const V1_AFTER_BAL_LO: usize = dregg_circuit::effect_vm::columns::STATE_AFTER_BASE
    + dregg_circuit::effect_vm::columns::state::BALANCE_LO;
const FORGED_BALANCE: u32 = 999_999_999;

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

#[allow(clippy::type_complexity)]
fn honest_wide_transfer() -> (
    EffectVmDescriptor2,
    Vec<Vec<BabyBear>>,
    Vec<BabyBear>,
    Vec<Vec<HeapLeaf>>,
    MemBoundaryWitness,
) {
    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64, 1);
    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nr = dregg_circuit::heap_root::empty_heap_root_8();
    let cr = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[5u8; 32], [6u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nr,
        &cr,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nr,
        &cr,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let membership_teeth = (BabyBear::new(0xA11CE), BabyBear::new(0xF00D));
    generate_rotated_effect_vm_descriptor_and_trace_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &transfer_caveat_manifest(),
        None,
        None,
        None,
        Some(membership_teeth),
    )
    .expect("honest wide transfer")
}

struct ChipSite {
    arity: usize,
    inputs: Vec<LeanExpr>,
    outputs: Vec<usize>,
}

fn chip_sites(desc: &EffectVmDescriptor2) -> Vec<ChipSite> {
    let tid = desc
        .tables
        .iter()
        .find(|t| t.sem == TableSem::Poseidon2Chip)
        .map(|t| t.id)
        .expect("chip table");
    let mut out = Vec::new();
    for k in &desc.constraints {
        let VmConstraint2::Lookup(l) = k else {
            continue;
        };
        if l.table != tid || l.tuple.len() != 25 {
            continue;
        }
        let LeanExpr::Const(arity) = l.tuple[0] else {
            continue;
        };
        out.push(ChipSite {
            arity: arity as usize,
            inputs: l.tuple[1..17].to_vec(),
            outputs: l.tuple[17..25]
                .iter()
                .map(|e| match e {
                    LeanExpr::Var(c) => *c,
                    _ => usize::MAX,
                })
                .collect(),
        });
    }
    out
}

fn rehash_row(sites: &[ChipSite], row: &mut [BabyBear]) {
    for _ in 0..64 {
        let mut changed = false;
        for s in sites {
            let ins: Vec<BabyBear> = s.inputs[..s.arity]
                .iter()
                .map(|e| eval_lean_expr(e, row))
                .collect();
            let lanes = chip_absorb_all_lanes(s.arity, &ins);
            for (j, &c) in s.outputs.iter().enumerate() {
                if c != usize::MAX && row[c] != lanes[j] {
                    row[c] = lanes[j];
                    changed = true;
                }
            }
        }
        if !changed {
            return;
        }
    }
    panic!("no fixpoint");
}

/// The trace the AIR actually sees: rows grown to the descriptor width, chip lanes derived, and
/// the gentian refuse-aux block filled — exactly `descriptor_ir2::trace_with_chip_lanes`.
fn air_trace(desc: &EffectVmDescriptor2, base: &[Vec<BabyBear>]) -> Vec<Vec<BabyBear>> {
    let mut t = base.to_vec();
    for row in &mut t {
        if row.len() < desc.trace_width {
            row.resize(desc.trace_width, BabyBear::ZERO);
        }
        dregg_circuit::descriptor_ir2::fill_chip_lanes(desc, row);
        dregg_circuit::effect_vm::bare_floor_refuse_weld::fill_refuse_aux(desc, row);
    }
    t
}

/// Indices (into `desc.constraints`) of every ROW-LOCAL body that is non-zero on `row`.
///
/// Reads the body through `descriptor_ir2::row_local_body`, so it finds the body whether the
/// emitter carries it as a transition-domain `Gate` or (after the last-row hardening flag day) as a
/// whole-domain `windowGate`. Matching the KIND here would have made this probe go silently
/// vacuous the moment the repair it was written to justify actually landed.
fn violated_gates(desc: &EffectVmDescriptor2, row: &[BabyBear]) -> Vec<usize> {
    desc.constraints
        .iter()
        .enumerate()
        .filter_map(|(i, k)| {
            let b = dregg_circuit::descriptor_ir2::row_local_body(k)?;
            (eval_lean_expr(&b, row) != BabyBear::ZERO).then_some(i)
        })
        .collect()
}

/// How many row-local bodies the member carries at all — asserted non-zero everywhere below so a
/// "nothing was violated" reading can never be a "nothing was looked at" reading.
fn row_local_body_count(desc: &EffectVmDescriptor2) -> usize {
    desc.constraints
        .iter()
        .filter(|k| dregg_circuit::descriptor_ir2::row_local_body(k).is_some())
        .count()
}

#[test]
fn honest_last_row_already_satisfies_every_gate_body() {
    let (desc, base, _pis, _heaps, _mb) = honest_wide_transfer();
    let trace = air_trace(&desc, &base);
    let n = trace.len();
    let n_gates = row_local_body_count(&desc);
    assert!(
        n_gates > 0,
        "this probe measures ROW-LOCAL BODIES; a member with none would make every assertion below \
         vacuous"
    );
    eprintln!(
        "member {} — width {}, rows {n}, gates {n_gates}",
        desc.name, desc.trace_width
    );

    let mut bad_rows: Vec<(usize, Vec<usize>)> = Vec::new();
    for (r, row) in trace.iter().enumerate() {
        let v = violated_gates(&desc, row);
        if !v.is_empty() {
            bad_rows.push((r, v));
        }
    }
    eprintln!("HONEST trace: rows with a non-zero gate body: {bad_rows:?}");

    // Is the last row byte-identical to the previous pad row?
    let same = trace[n - 1] == trace[n - 2];
    eprintln!("HONEST trace: row[n-1] == row[n-2]: {same}");
    if !same {
        let diffs: Vec<usize> = (0..desc.trace_width)
            .filter(|&c| trace[n - 1][c] != trace[n - 2][c])
            .collect();
        eprintln!("  differing columns ({}): {:?}", diffs.len(), diffs);
    }

    assert!(
        bad_rows.is_empty(),
        "the honest trace must satisfy every gate body on EVERY row (including the last) for the \
         whole-domain repair to cost the honest prover nothing"
    );
}

#[test]
fn the_forged_last_row_violates_gate_bodies() {
    let (desc, base, _pis, _heaps, _mb) = honest_wide_transfer();
    let trace = air_trace(&desc, &base);
    let n = trace.len();
    let sites = chip_sites(&desc);

    // The same mutation the forge makes, on the last row.
    let mut t = trace.clone();
    t[n - 1][V1_AFTER_BAL_LO] = BabyBear::new(FORGED_BALANCE);
    // and the rotated limb, found by scanning for cells that held the honest balance
    let honest = trace[n - 1][V1_AFTER_BAL_LO];
    let mirrors: Vec<usize> = (0..desc.trace_width)
        .filter(|&c| c != V1_AFTER_BAL_LO && trace[n - 1][c] == honest)
        .collect();
    eprintln!("columns mirroring the honest AFTER balance on the last row: {mirrors:?}");
    for &c in &mirrors {
        t[n - 1][c] = BabyBear::new(FORGED_BALANCE);
    }
    rehash_row(&sites, &mut t[n - 1]);

    assert!(row_local_body_count(&desc) > 0, "non-vacuity");
    let v = violated_gates(&desc, &t[n - 1]);
    eprintln!(
        "FORGED last row: {} row-local bodies are non-zero: {:?}",
        v.len(),
        &v[..v.len().min(20)]
    );
    for &i in v.iter().take(6) {
        eprintln!("   gate #{i}: {:?}", &desc.constraints[i]);
    }
    assert!(
        !v.is_empty(),
        "if the forged last row satisfies every gate body too, the whole-domain repair does NOT \
         close the forge and a different repair is needed"
    );
}

/// Which gate bodies MENTION the AFTER-balance column, and do any of them also mention the
/// BEFORE-balance column? A recomposition gate alone would only force the limb witness to track
/// the forged value; an economic gate is what forces the value itself.
#[test]
fn which_gates_reference_the_after_balance_column() {
    use dregg_circuit::effect_vm::columns::{STATE_AFTER_BASE, STATE_BEFORE_BASE, state};
    let (desc, _base, _pis, _heaps, _mb) = honest_wide_transfer();
    let before_bal = STATE_BEFORE_BASE + state::BALANCE_LO;
    let after_bal = STATE_AFTER_BASE + state::BALANCE_LO;
    eprintln!("before_bal col {before_bal}, after_bal col {after_bal}");

    fn vars(e: &LeanExpr, acc: &mut Vec<usize>) {
        match e {
            LeanExpr::Var(c) => acc.push(*c),
            LeanExpr::Const(_) => {}
            LeanExpr::Add(a, b) | LeanExpr::Mul(a, b) => {
                vars(a, acc);
                vars(b, acc);
            }
        }
    }
    for (i, k) in desc.constraints.iter().enumerate() {
        let Some(b) = dregg_circuit::descriptor_ir2::row_local_body(k) else {
            continue;
        };
        let mut v = Vec::new();
        vars(&b, &mut v);
        if v.contains(&after_bal) {
            eprintln!(
                "gate #{i} touches AFTER balance; also BEFORE balance: {}\n   {b:?}",
                v.contains(&before_bal)
            );
        }
    }
    // And the transitions, for contrast.
    for (i, k) in desc.constraints.iter().enumerate() {
        if let VmConstraint2::Base(VmConstraint::Transition { hi, lo }) = k {
            if STATE_AFTER_BASE + lo == after_bal {
                eprintln!("transition #{i}: next[before+{hi}] == local[after+{lo}]");
            }
        }
    }
}

/// **THE SMART FORGE, evaluated against the gate bodies only.** Mutate the AFTER balance AND
/// repair its 15-bit limb witness (so gates #36/#37 recompose), then re-derive the chip chain.
/// Report every gate body still non-zero — on the last row and on the transition-covered row.
#[test]
fn smart_forge_gate_residue() {
    let (desc, base, _pis, _heaps, _mb) = honest_wide_transfer();
    let trace = air_trace(&desc, &base);
    let n = trace.len();
    let sites = chip_sites(&desc);
    // ONLY the AFTER side: col 76 (v1 AFTER balance), col 284 (its rotated-block mirror), and the
    // AFTER limb witness (96/97). The BEFORE block (54, 94/95) is left honest — mutating it would
    // break the INCOMING transition from row n-2, which is enforced on both rows and would make
    // the measurement inattributable.
    let forged = BabyBear::new(FORGED_BALANCE);
    let (lo, hi) = (FORGED_BALANCE & 0x7fff, FORGED_BALANCE >> 15);

    for row in [n - 1, n - 2] {
        let mut t = trace.clone();
        for c in [V1_AFTER_BAL_LO, 284usize] {
            t[row][c] = forged;
        }
        for (a, b) in [(96usize, 97usize)] {
            t[row][a] = BabyBear::new(lo);
            t[row][b] = BabyBear::new(hi);
        }
        rehash_row(&sites, &mut t[row]);
        let v = violated_gates(&desc, &t[row]);
        eprintln!(
            "SMART forge at row {row}: {} gate bodies non-zero: {v:?}",
            v.len()
        );
        for &i in v.iter().take(8) {
            eprintln!("   gate #{i}: {:?}", &desc.constraints[i]);
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// ⚑ HOUSE LAW #1: is `row_local_body` TRANSLATION, or is it authoring?
// ─────────────────────────────────────────────────────────────────────────────

/// Do a `WindowExpr` and a `LeanExpr` have the SAME SHAPE and the SAME LEAVES, node for node?
///
/// `false` on any structural disagreement, and on any `Nxt` leaf (which has no one-row reading at
/// all). Nothing here is tolerant: a translation that invented a node, dropped a node, changed a
/// column index or changed a constant would fail.
fn mirrors(w: &WindowExpr, l: &LeanExpr) -> bool {
    match (w, l) {
        (WindowExpr::Loc(a), LeanExpr::Var(b)) => a == b,
        (WindowExpr::Const(a), LeanExpr::Const(b)) => a == b,
        (WindowExpr::Add(a1, a2), LeanExpr::Add(b1, b2))
        | (WindowExpr::Mul(a1, a2), LeanExpr::Mul(b1, b2)) => mirrors(a1, b1) && mirrors(a2, b2),
        _ => false,
    }
}

/// **THE LAW-1 QUESTION, MEASURED over all 174 deployed members.**
///
/// `descriptor_ir2::row_local_body` reads a whole-domain `windowGate`'s body back as a `LeanExpr`,
/// and its private helper `window_body_as_local` constructs `LeanExpr::{Var, Const, Add, Mul}` to
/// do it. A doctrine gate counts those four constructions as authored sites, and it is right to:
/// constructing a `LeanExpr` in Rust is EXACTLY the shape of the drift House Law #1 forbids, and
/// "it is only plumbing" is what every instance of that drift says about itself.
///
/// So it is measured rather than asserted. Over every whole-domain `windowGate` in all three
/// deployed registries, the returned `LeanExpr` must be the node-for-node MIRROR of the
/// `WindowExpr` the Lean emitter committed — same shape, same column indices, same constants,
/// nothing added, nothing dropped. A function that is a total structural isomorphism onto its own
/// input cannot express a constraint the input did not already contain: every leaf it emits came
/// from the descriptor, which came from Lean.
///
/// That is the difference between translation and authoring, and this is the instrument that keeps
/// it honest. If someone later gives `window_body_as_local` a case that synthesizes a node — a
/// normalisation, a folded constant, a rewritten selector — this goes RED, because the mirror
/// stops holding. It is not a comment promising good behaviour; it is a check that fails.
///
/// ⚑ It measures translation. It does NOT license authoring anywhere else in the file, and it says
/// nothing about the 283 sites the gate already ledgers there.
#[test]
fn row_local_body_is_a_structural_mirror_and_authors_nothing() {
    let mut whole_domain = 0usize;
    let mut two_row = 0usize;
    let mut gates = 0usize;
    for (label, tsv) in [
        ("V3_STAGED_REGISTRY_TSV", V3_STAGED_REGISTRY_TSV),
        ("WIDE_REGISTRY_STAGED_TSV", WIDE_REGISTRY_STAGED_TSV),
        ("WIDE_UMEM_WELD_REGISTRY_TSV", WIDE_UMEM_WELD_REGISTRY_TSV),
    ] {
        for line in tsv.lines() {
            let mut it = line.splitn(3, '\t');
            let (Some(key), Some(_), Some(json)) = (it.next(), it.next(), it.next()) else {
                continue;
            };
            let d = parse_vm_descriptor2(json).unwrap_or_else(|e| panic!("{key}: {e}"));
            for (i, k) in d.constraints.iter().enumerate() {
                let got = dregg_circuit::descriptor_ir2::row_local_body(k);
                match k {
                    VmConstraint2::WindowGate(w) if !w.on_transition => {
                        match got {
                            Some(l) => {
                                assert!(
                                    mirrors(&w.body, &l),
                                    "{label}/{key} constraint {i}: `row_local_body` returned a \
                                     body that is NOT the node-for-node mirror of the committed \
                                     `WindowExpr`. That is AUTHORING, not translation, and it \
                                     belongs in the Lean emitter.\n  window: {:?}\n  lean:   {l:?}",
                                    w.body
                                );
                                whole_domain += 1;
                            }
                            // The only legitimate `None` on a whole-domain gate: a genuine
                            // two-row body, which has no one-row reading to translate.
                            None => two_row += 1,
                        }
                    }
                    // A transition-domain `Gate` is returned BORROWED — nothing is constructed.
                    VmConstraint2::Base(VmConstraint::Gate(b)) => {
                        assert_eq!(got.as_deref(), Some(b));
                        gates += 1;
                    }
                    // Everything else carries no row-local body at all.
                    _ => assert!(got.is_none(), "{label}/{key} constraint {i}"),
                }
            }
        }
    }
    eprintln!(
        "LAW-1 MIRROR: {whole_domain} whole-domain bodies translated node-for-node, \
         {two_row} genuinely two-row (correctly refused), {gates} residual transition-domain gates"
    );
    assert!(
        whole_domain > 10_000,
        "the mirror must be measured over the WHOLE deployed surface, not a handful — saw only \
         {whole_domain}"
    );
    assert_eq!(
        gates, 0,
        "no transition-domain `Gate` should survive in a deployed member after the hardening"
    );
}
