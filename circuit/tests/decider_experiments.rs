//! # DECIDER EXPERIMENTS D1/D2/D3/D6/D7 — measurement only
//!
//! Companion doc: `docs/DECIDERS-rotated-arch-D1-D7.md`. Charter:
//! `docs/ARCH-REVIEW-rotated-commitment-chip.md` (commit 1b6ef98ef), §Stage-0 decider table.
//!
//! SUBSTRATE NOTE (say it out loud): this file AUTHORS NO AIR. Every constraint it reads was
//! emitted by the Lean emitters and parsed back out of the deployed staged registry TSV. The
//! only "AIR-shaped" objects here are the two D7 spike AIRs, which are THROWAWAY p3 toys that
//! never touch a registry, an FP, or a VK — they exist to answer "does the pinned plonky3
//! batch STARK carry preprocessed columns end-to-end", nothing else. A real preprocessed
//! surface is a Lean-emitted object; building it is Stage-2/3 work gated on this measurement.
//!
//! What each test measures:
//!
//! * `d1_d2_chip_census_and_logup_aux_provenance` — D1: the UNIQUE-permutation count the chip
//!   table actually holds for the deployed wide transfer (the `chip_hist` dedup), the post-S2
//!   projection, and a simulated rate-8 schedule; D2: the exact LogUp aux provenance read off
//!   a real proof (`global_lookup_data` bus names + `permutation_local` widths).
//! * `d3_declared_main_arity_is_inert_in_the_rust_realization` — D3: the 2617 ≠ 2664 audit,
//!   by mutating the declared main-table arity and byte-comparing the proofs.
//! * `d6_per_member_chip_cliff_census` — D6: the static per-member chip-query census over all
//!   57 wide members, with post-S2 / post-rate-8 projections against the 64/128/256 cliffs.
//! * `d7_preprocessed_column_spike` — D7: one constant column carried as a preprocessed
//!   (committed-once, VK-side) matrix through the pinned `p3-batch-stark` prove/verify path,
//!   plus the two adoption probes: tamper rejection and a LogUp interaction whose field READS
//!   a preprocessed column.
//! * `e3_mutable_last_limb_schedule_rate8_sim` — E3 (backlog rank 3, PRE-FREEZE): the D1
//!   rate-8 simulator re-run under the two mutable-LAST candidate v10 absorption schedules,
//!   measuring the BEFORE/AFTER cross-chain chip dedup the deployed mutable-FIRST order
//!   (`cell/src/commitment.rs:1075-1083`) forfeits, and the resulting Epoch-2 chip heights.
//!
//! Run (release; debug prove times and heights are still valid but slow):
//! ```text
//! CARGO_TARGET_DIR=/tmp/decider-check cargo test -p dregg-circuit --release \
//!   --test decider_experiments -- --nocapture
//! ```

use std::collections::{BTreeMap, BTreeSet, HashSet};

use dregg_circuit::CellState;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, WindowExpr, chip_absorb_all_lanes,
    fill_chip_lanes, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::Effect;
use dregg_circuit::effect_vm::bare_floor_refuse_weld as refuse;
use dregg_circuit::effect_vm::trace_rotated::{
    GRAD_ROT_WIDTH, RotatedBlockWitness, TRANSFER_AVAIL_PAD, WIDE_CARRIER_APPENDIX,
    generate_rotated_effect_vm_descriptor_and_trace_wide, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint};
use dregg_turn::rotation_witness as rw;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};

const KEY: &str = "transferVmDescriptor2R24";
/// The poseidon2-chip table wire id in the wide rotated descriptors.
const TID_P2: usize = 1;
/// `[arity, in0..in15, out0..out7]`.
const CHIP_TUPLE_LEN: usize = 25;
const CHIP_IN0: usize = 1;
const CHIP_OUT0: usize = 17;

// ---------------------------------------------------------------------------
// shared plumbing (the same honest witness the drop measurement uses)
// ---------------------------------------------------------------------------

fn member_json(key: &str) -> &'static str {
    WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(key) {
                it.nth(1)
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{key} not in WIDE_REGISTRY_STAGED_TSV"))
}

/// Evaluate a descriptor expression over one row (the same semantics as the crate-private
/// `eval_c`; four arms, no interpretation freedom).
fn ev(e: &LeanExpr, row: &[BabyBear]) -> BabyBear {
    match e {
        LeanExpr::Var(v) => row[*v],
        LeanExpr::Const(c) => {
            // Signed constant reduced into the field.
            let m = 2013265921i64;
            BabyBear::new(c.rem_euclid(m) as u32)
        }
        LeanExpr::Add(a, b) => ev(a, row) + ev(b, row),
        LeanExpr::Mul(a, b) => ev(a, row) * ev(b, row),
    }
}

fn expr_vars(e: &LeanExpr, acc: &mut HashSet<usize>) {
    match e {
        LeanExpr::Var(v) => {
            acc.insert(*v);
        }
        LeanExpr::Const(_) => {}
        LeanExpr::Add(a, b) | LeanExpr::Mul(a, b) => {
            expr_vars(a, acc);
            expr_vars(b, acc);
        }
    }
}

/// One parsed chip site: tag (the arity constant in tuple slot 0), the 16 input exprs, the
/// 8 output exprs, and the Var sets on each side.
struct ChipSite {
    /// Index into the member's chip-site list (constraint order).
    idx: usize,
    /// The arity TAG (tuple[0]); `None` when the tag is not a bare constant.
    tag: Option<i64>,
    /// Number of genuine `Var`s among the 16 input slots (the drop test's "input arity").
    var_arity: usize,
    ins: Vec<LeanExpr>,
    outs: Vec<LeanExpr>,
    in_vars: HashSet<usize>,
    out_vars: HashSet<usize>,
}

fn chip_sites(desc: &EffectVmDescriptor2) -> Vec<ChipSite> {
    let mut sites = Vec::new();
    for k in &desc.constraints {
        let VmConstraint2::Lookup(l) = k else {
            continue;
        };
        if l.table != TID_P2 || l.tuple.len() != CHIP_TUPLE_LEN {
            continue;
        }
        let tag = match &l.tuple[0] {
            LeanExpr::Const(c) => Some(*c),
            _ => None,
        };
        let ins: Vec<LeanExpr> = l.tuple[CHIP_IN0..CHIP_OUT0].to_vec();
        let outs: Vec<LeanExpr> = l.tuple[CHIP_OUT0..].to_vec();
        let mut in_vars = HashSet::new();
        let mut out_vars = HashSet::new();
        for e in &ins {
            expr_vars(e, &mut in_vars);
        }
        for e in &outs {
            expr_vars(e, &mut out_vars);
        }
        let var_arity = ins.iter().filter(|e| matches!(e, LeanExpr::Var(_))).count();
        sites.push(ChipSite {
            idx: sites.len(),
            tag,
            var_arity,
            ins,
            outs,
            in_vars,
            out_vars,
        });
    }
    sites
}

fn window_vars(e: &WindowExpr, acc: &mut HashSet<usize>) {
    match e {
        WindowExpr::Loc(c) | WindowExpr::Nxt(c) => {
            acc.insert(*c);
        }
        WindowExpr::Const(_) => {}
        WindowExpr::Add(a, b) | WindowExpr::Mul(a, b) => {
            window_vars(a, acc);
            window_vars(b, acc);
        }
    }
}

/// Every column read by any NON-chip constraint or bound to a PI (the "external sinks" of the
/// chip-site graph). Every constraint form is covered so a site feeding a mem/map/umem op, a
/// proof-bind, or a windowed gate is never misclassified as dead.
fn non_chip_sinks(desc: &EffectVmDescriptor2) -> HashSet<usize> {
    let mut sinks = HashSet::new();
    for k in &desc.constraints {
        match k {
            VmConstraint2::Lookup(l) if l.table == TID_P2 && l.tuple.len() == CHIP_TUPLE_LEN => {}
            VmConstraint2::Lookup(l) => {
                for e in &l.tuple {
                    expr_vars(e, &mut sinks);
                }
            }
            VmConstraint2::Base(b) => match b {
                VmConstraint::Gate(e) => expr_vars(e, &mut sinks),
                VmConstraint::Boundary { body, .. } => expr_vars(body, &mut sinks),
                VmConstraint::Transition { hi, lo } => {
                    sinks.insert(*hi);
                    sinks.insert(*lo);
                }
                VmConstraint::PiBinding { col, .. } => {
                    sinks.insert(*col);
                }
            },
            VmConstraint2::MemOp(m) => {
                for e in [&m.guard, &m.addr, &m.value, &m.prev_value, &m.prev_serial] {
                    expr_vars(e, &mut sinks);
                }
            }
            VmConstraint2::MapOp(m) => {
                for e in [&m.guard, &m.key, &m.value] {
                    expr_vars(e, &mut sinks);
                }
                for e in m.root.iter().chain(m.new_root.iter()) {
                    expr_vars(e, &mut sinks);
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
                    expr_vars(e, &mut sinks);
                }
            }
            VmConstraint2::ProofBind(m) => {
                for e in [&m.guard, &m.commit, &m.vk] {
                    expr_vars(e, &mut sinks);
                }
            }
            VmConstraint2::WindowGate(w) => window_vars(&w.body, &mut sinks),
        }
    }
    sinks
}

/// The transitively-DEAD chip-site set: sites none of whose outputs reach a non-chip sink,
/// even through other chip sites. This is the constraint-level S2 classifier — the review's
/// negative check ("nothing outside the 1-felt lookups reads the legacy carriers/digests/
/// lanes") is exactly "the S2 sites are transitively dead".
fn dead_sites(desc: &EffectVmDescriptor2, sites: &[ChipSite]) -> HashSet<usize> {
    let sinks = non_chip_sinks(desc);
    let mut live: Vec<bool> = sites
        .iter()
        .map(|s| s.out_vars.iter().any(|v| sinks.contains(v)))
        .collect();
    loop {
        let mut changed = false;
        // A site is live if any live site READS one of its outputs.
        let live_in_vars: HashSet<usize> = sites
            .iter()
            .filter(|s| live[s.idx])
            .flat_map(|s| s.in_vars.iter().copied())
            .collect();
        for s in sites {
            if !live[s.idx] && s.out_vars.iter().any(|v| live_in_vars.contains(v)) {
                live[s.idx] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    sites
        .iter()
        .filter(|s| !live[s.idx])
        .map(|s| s.idx)
        .collect()
}

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

fn producer_cell(balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// The honest wide transfer, minted through the PRODUCTION dispatcher — identical witness
/// shape to `legacy_chain_drop_measurement.rs` so the numbers line up with the [M] baseline.
fn honest_wide_transfer() -> (
    EffectVmDescriptor2,
    Vec<Vec<BabyBear>>,
    Vec<BabyBear>,
    Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>,
    MemBoundaryWitness,
) {
    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance);
    let after_cell = producer_cell(before_balance - amount as i64);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let produce = |cell: &Cell| {
        rw::produce(
            cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        )
    };
    let bridge =
        |w: &rw::RotationWitness| RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).unwrap();
    let before_w = produce(&before_cell);
    let after_w = produce(&after_cell);
    let membership_teeth = (BabyBear::new(0xA11CE), BabyBear::new(0xF00D));
    let (desc, trace, dpis, map_heaps, mb) = generate_rotated_effect_vm_descriptor_and_trace_wide(
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
    .expect("the deployed wide transfer leg mints");
    (desc, trace, dpis, map_heaps, mb)
}

fn next_pow2(n: usize) -> usize {
    n.next_power_of_two().max(1)
}

/// Total columns this member's OWN E1 kill-set (the Epoch-1 SECOND flag-day) deletes, summed from
/// the Lean-emitted single source `E1_COMPACT_TABLE` — exactly what `compact_e1_columns` drains.
fn e1_deleted_cols(key: &str) -> usize {
    dregg_circuit::effect_vm::e1_compact_generated::E1_COMPACT_TABLE
        .iter()
        .find(|(k, _)| *k == key)
        .map(|(_, runs)| runs.iter().map(|(a, b)| b - a).sum())
        .unwrap_or_else(|| panic!("{key} not in E1_COMPACT_TABLE"))
}

/// **THE COMPACTED PRODUCER ROW of the deployed wide transfer, DERIVED** — the AVAIL-hardened
/// graduated rotated host PLUS the wide-carrier appendix, MINUS the S2 stratum (Epoch 1) and MINUS
/// this member's own E1 kill-set, both read from the Lean-emitted tables the deployed producer
/// drains. This is what the descriptor DECLARES as its main-table arity; the committed
/// `trace_width` rides higher by the spliced teeth and the prover-filled refuse block.
fn compacted_producer_width() -> usize {
    GRAD_ROT_WIDTH + TRANSFER_AVAIL_PAD + WIDE_CARRIER_APPENDIX
        - dregg_circuit::effect_vm::s2_compact_generated::S2_DELETED_COLS
        - e1_deleted_cols(KEY)
}

/// The COMMITTED `trace_width` of the deployed wide transfer: the compacted producer row + the 2
/// spliced membership-claim teeth + the top-of-trace refuse-weld footprint (this member's refuse
/// block sits at the very top, so it carries no dead stride-tail).
fn committed_wide_transfer_width() -> usize {
    compacted_producer_width() + 2 + refuse::REFUSE_WELD_WIDEN
}

// ===========================================================================
// D1 + D2
// ===========================================================================

#[test]
fn d1_d2_chip_census_and_logup_aux_provenance() {
    let (desc, mut trace, pis, heaps, mem) = honest_wide_transfer();
    assert_eq!(
        desc.trace_width,
        committed_wide_transfer_width(),
        "deployed wide transfer width"
    );
    assert_eq!(desc.public_input_count, 68);

    // Grow producer rows to trace_width and run the DEPLOYED lane weld (pub API), so every
    // chip tuple (including wide-chain state lanes) evaluates to its genuine value.
    for row in &mut trace {
        row.resize(desc.trace_width, BabyBear::ZERO);
    }
    for row in &mut trace {
        fill_chip_lanes(&desc, row);
    }

    let sites = chip_sites(&desc);
    // A MEASURED census, deliberately kept a literal: unlike a width it is not a function of the
    // Lean-emitted deletion tables, and a change in it SHOULD be a flag-day someone reads — not a
    // number that silently follows a regen. It moved 254 → 134 when the S2 flag-day deleted the
    // graduated chip-lane stratum, then 134 → 138 / 254 → 262 at the NINE-LANE epoch (each rotated
    // block gained two absorption sites with the six new limbs: 60 → 62 per block). The relation
    // below anchors both literals to the Lean-emitted deletion table so an S2 span change fails
    // loudly here instead of leaving a floating count. ⚑ 138 → 140 / 262 → 264 at the rc FOLD: the
    // caveat region gained the TWO chip sites that absorb the DFA route-commitment carrier into the
    // published caveat commitment (the S2 stratum is per-BLOCK and does not move with them).
    assert_eq!(sites.len(), 140, "chip lookups at HEAD (was 264 pre-S2)");
    assert_eq!(
        sites.len() + dregg_circuit::effect_vm::s2_compact_generated::S2_LANE_SPAN / 7,
        264,
        "the S2 flag-day deleted exactly the graduated chip-lane sites (S2_LANE_SPAN spans 7 lanes \
         per site), taking the deployed census 264 → 140"
    );

    // -- tag / var-arity histograms --
    let mut tag_hist: BTreeMap<i64, usize> = BTreeMap::new();
    let mut var_hist: BTreeMap<usize, usize> = BTreeMap::new();
    for s in &sites {
        *tag_hist
            .entry(s.tag.expect("tag is a constant"))
            .or_default() += 1;
        *var_hist.entry(s.var_arity).or_default() += 1;
    }
    println!("D1: site tag histogram      = {tag_hist:?}");
    println!("D1: site var-arity histogram = {var_hist:?}");

    // -- evaluate every site's tuple on EVERY row (exactly the key set build_traces feeds
    //    chip_hist), check fill-faithfulness, and keep the row-0 tuple per site for the
    //    site-level classification below --
    let mut per_site_tuples: Vec<Vec<u32>> = Vec::with_capacity(sites.len());
    let mut chip_hist_keys: BTreeSet<Vec<u32>> = BTreeSet::new();
    let mut per_site_distinct: Vec<usize> = Vec::with_capacity(sites.len());
    for s in &sites {
        let mut site_set: BTreeSet<Vec<u32>> = BTreeSet::new();
        let mut tup0: Option<Vec<u32>> = None;
        for (ri, row) in trace.iter().enumerate() {
            let mut t = Vec::with_capacity(CHIP_TUPLE_LEN);
            t.push(s.tag.unwrap() as u32);
            for e in &s.ins {
                t.push(ev(e, row).as_u32());
            }
            for e in &s.outs {
                t.push(ev(e, row).as_u32());
            }
            if ri == 0 {
                tup0 = Some(t.clone());
            }
            site_set.insert(t.clone());
            chip_hist_keys.insert(t);
        }
        let tup0 = tup0.unwrap();
        // Fill-faithfulness: the 8 evaluated out lanes must equal the genuine permutation of
        // the evaluated inputs under the chip's own seeding (the pub absorb helper).
        let ins_v: Vec<BabyBear> = s.ins.iter().map(|e| ev(e, &trace[0])).collect();
        let lanes = chip_absorb_all_lanes(s.tag.unwrap() as usize, &ins_v);
        for (j, lane) in lanes.iter().enumerate() {
            assert_eq!(
                tup0[CHIP_OUT0 + j],
                lane.as_u32(),
                "site {} lane {j}: evaluated out != genuine permutation",
                s.idx
            );
        }
        per_site_distinct.push(site_set.len());
        per_site_tuples.push(tup0);
    }
    let row_varying_sites = per_site_distinct.iter().filter(|&&n| n > 1).count();
    let mut varying_hist: BTreeMap<usize, usize> = BTreeMap::new();
    for &n in &per_site_distinct {
        *varying_hist.entry(n).or_default() += 1;
    }
    println!(
        "D1: row-varying sites = {row_varying_sites} (distinct-tuples-per-site histogram \
         {varying_hist:?})"
    );

    // -- D1 headline: the chip_hist dedup, over ALL rows (the table's real unique count) --
    println!(
        "D1: DEPLOYED chip_hist unique permutations = {} ({} sites x {} rows = {} queries) \
         -> chip height {}",
        chip_hist_keys.len(),
        sites.len(),
        trace.len(),
        sites.len() * trace.len(),
        next_pow2(chip_hist_keys.len())
    );
    let unique_all = &chip_hist_keys;
    let mut unique_by_tag: BTreeMap<u32, usize> = BTreeMap::new();
    for t in unique_all {
        *unique_by_tag.entry(t[0]).or_default() += 1;
    }
    println!("D1: unique-by-tag = {unique_by_tag:?}");
    // Row-0 site-level dedup (how many of the 254 site tuples coincide on the fill row).
    let row0_unique: BTreeSet<&Vec<u32>> = per_site_tuples.iter().collect();
    println!(
        "D1: row-0 site-tuple dedup = {} of {}",
        row0_unique.len(),
        sites.len()
    );

    // -- S2 classification (transitively-dead sites) + post-S2 dedup --
    let dead = dead_sites(&desc, &sites);
    let mut dead_by_tag: BTreeMap<i64, usize> = BTreeMap::new();
    for s in &sites {
        if dead.contains(&s.idx) {
            *dead_by_tag.entry(s.tag.unwrap()).or_default() += 1;
        }
    }
    println!(
        "D1: transitively-dead (S2) sites = {} by tag {dead_by_tag:?}",
        dead.len()
    );
    let surviving_varying: Vec<&ChipSite> = sites
        .iter()
        .filter(|s| !dead.contains(&s.idx) && per_site_distinct[s.idx] > 1)
        .collect();
    println!(
        "D1: surviving sites that vary by row = {} (tags {:?})",
        surviving_varying.len(),
        surviving_varying
            .iter()
            .fold(BTreeMap::<i64, usize>::new(), |mut m, s| {
                *m.entry(s.tag.unwrap()).or_default() += 1;
                m
            })
    );
    // Which rows deviate from the row-0 tuple? (per varying site: the set of deviating rows)
    let mut deviating_rows: BTreeSet<usize> = BTreeSet::new();
    for s in sites.iter().filter(|s| per_site_distinct[s.idx] > 1) {
        for (ri, row) in trace.iter().enumerate() {
            let mut t = Vec::with_capacity(CHIP_TUPLE_LEN);
            t.push(s.tag.unwrap() as u32);
            for e in &s.ins {
                t.push(ev(e, row).as_u32());
            }
            for e in &s.outs {
                t.push(ev(e, row).as_u32());
            }
            if t != per_site_tuples[s.idx] {
                deviating_rows.insert(ri);
            }
        }
    }
    println!("D1: rows where any varying site deviates from its row-0 tuple = {deviating_rows:?}");

    // POST-S2 unique, over ALL rows of the SURVIVING sites (the exact post-deletion table).
    let mut unique_post_s2: BTreeSet<Vec<u32>> = BTreeSet::new();
    for s in sites.iter().filter(|s| !dead.contains(&s.idx)) {
        for row in trace.iter() {
            let mut t = Vec::with_capacity(CHIP_TUPLE_LEN);
            t.push(s.tag.unwrap() as u32);
            for e in &s.ins {
                t.push(ev(e, row).as_u32());
            }
            for e in &s.outs {
                t.push(ev(e, row).as_u32());
            }
            unique_post_s2.insert(t);
        }
    }
    println!(
        "D1: POST-S2 unique permutations (all rows) = {} (of {} surviving sites; row-0-only \
         dedup = {}) -> chip height {}",
        unique_post_s2.len(),
        sites.len() - dead.len(),
        {
            let r0: BTreeSet<&Vec<u32>> = per_site_tuples
                .iter()
                .enumerate()
                .filter(|(i, _)| !dead.contains(i))
                .map(|(_, t)| t)
                .collect();
            r0.len()
        },
        next_pow2(unique_post_s2.len())
    );

    // -- classify the surviving sites for the rate-8 simulation --
    // wide chain steps: tag 11 (the two terminators are ALSO tag 11 with 9 genuine vars).
    let live_sites: Vec<&ChipSite> = sites.iter().filter(|s| !dead.contains(&s.idx)).collect();
    let wide_out_vars: HashSet<usize> = live_sites
        .iter()
        .filter(|s| s.tag == Some(11))
        .flat_map(|s| s.out_vars.iter().copied())
        .collect();
    let wide_in_vars: HashSet<usize> = live_sites
        .iter()
        .filter(|s| s.tag == Some(11))
        .flat_map(|s| s.in_vars.iter().copied())
        .collect();
    // heads: live tag-4 sites whose outputs feed a tag-11 site.
    let heads: Vec<&&ChipSite> = live_sites
        .iter()
        .filter(|s| s.tag == Some(4) && s.out_vars.iter().any(|v| wide_in_vars.contains(v)))
        .collect();
    println!("D1: wide heads (tag-4 feeding tag-11) = {}", heads.len());

    // Walk each wide chain in order, harvesting the FRESH absorbed values (inputs that are
    // Vars not produced by another tag-11 site or head — i.e. limbs, incl. the iroot).
    let head_out: HashSet<usize> = heads
        .iter()
        .flat_map(|s| s.out_vars.iter().copied())
        .collect();
    let mut chains: Vec<Vec<BabyBear>> = Vec::new(); // fresh streams incl. 4 head limbs
    for head in &heads {
        let mut stream: Vec<BabyBear> = head.ins.iter().take(4).map(|e| ev(e, &trace[0])).collect();
        // follow: the chain step whose state inputs read THIS site's outputs.
        let mut cur: &ChipSite = head;
        loop {
            let next = live_sites.iter().find(|s| {
                s.tag == Some(11)
                    && s.idx != cur.idx
                    && s.in_vars.iter().any(|v| cur.out_vars.contains(v))
            });
            let Some(next) = next else { break };
            for (k, e) in next.ins.iter().enumerate() {
                if k < 8 {
                    continue; // state lanes
                }
                if let LeanExpr::Var(v) = e {
                    if !wide_out_vars.contains(v) && !head_out.contains(v) {
                        stream.push(ev(e, &trace[0]));
                    }
                }
            }
            cur = next;
        }
        chains.push(stream);
    }
    for (i, c) in chains.iter().enumerate() {
        println!(
            "D1: wide chain {i} fresh stream = {} felts (incl. 4 head limbs)",
            c.len()
        );
    }

    // -- the simulated rate-8 schedule --
    // Absorb step = one arity-16 compression [state8 || block8] (the R8 shape modulo the tag
    // retype the review mandates). Two seed disciplines:
    //   (a) shared domain seed for both chains  (b) per-object domain seeds
    let simulate = |seed_tag: u32, stream: &[BabyBear]| -> Vec<Vec<u32>> {
        let mut tuples = Vec::new();
        let mut state: [BabyBear; 8] =
            chip_absorb_all_lanes(4, &[BabyBear::new(0xD05EED), BabyBear::new(seed_tag)]);
        for block in stream.chunks(8) {
            let mut ins: Vec<BabyBear> = state.to_vec();
            ins.extend_from_slice(block);
            ins.resize(16, BabyBear::ZERO);
            let outs = chip_absorb_all_lanes(16, &ins);
            let mut t = Vec::with_capacity(CHIP_TUPLE_LEN);
            t.push(16u32);
            for v in &ins {
                t.push(v.as_u32());
            }
            for v in &outs {
                t.push(v.as_u32());
            }
            tuples.push(t);
            state = outs;
        }
        tuples
    };
    let sim_shared: Vec<Vec<u32>> = chains.iter().flat_map(|c| simulate(0, c)).collect();
    let sim_perobj: Vec<Vec<u32>> = chains
        .iter()
        .enumerate()
        .flat_map(|(i, c)| simulate(i as u32 + 1, c))
        .collect();
    let sim_shared_unique: BTreeSet<&Vec<u32>> = sim_shared.iter().collect();
    let sim_perobj_unique: BTreeSet<&Vec<u32>> = sim_perobj.iter().collect();
    println!(
        "D1: rate-8 sim steps = {} total; unique(shared-seed) = {}, unique(per-object-seed) = {}",
        sim_shared.len(),
        sim_shared_unique.len(),
        sim_perobj_unique.len()
    );

    // Survivors of Epoch-2-A: everything live except the wide chain steps and the heads.
    let survivors: BTreeSet<&Vec<u32>> = live_sites
        .iter()
        .filter(|s| s.tag != Some(11) && !heads.iter().any(|h| h.idx == s.idx))
        .map(|s| &per_site_tuples[s.idx])
        .collect();
    println!(
        "D1: non-wide survivors (post-S2, minus wide chains+heads) unique = {}",
        survivors.len()
    );
    let v_a: usize = survivors.len() + sim_perobj_unique.len();
    println!(
        "D1: EPOCH-2-A (rate-8 blocks, caveat kept, H4 kept) unique ~= {} -> chip height {}",
        v_a,
        next_pow2(v_a)
    );

    // Caveat chain + H4 variants (identified structurally among the survivors).
    // H4 root: the tag-4 site whose out0 lands on the PI-8-bound column.
    let pi8_col: Option<usize> = desc.constraints.iter().find_map(|k| match k {
        VmConstraint2::Base(VmConstraint::PiBinding {
            col, pi_index: 8, ..
        }) => Some(*col),
        _ => None,
    });
    let h4_root: Option<&&ChipSite> = live_sites.iter().find(|s| {
        s.tag == Some(4) && matches!(&s.outs[0], LeanExpr::Var(v) if Some(*v) == pi8_col)
    });
    let h4_sites: HashSet<usize> = match h4_root {
        Some(root) => {
            let mut set: HashSet<usize> = live_sites
                .iter()
                .filter(|s| s.out_vars.iter().any(|v| root.in_vars.contains(v)))
                .map(|s| s.idx)
                .collect();
            set.insert(root.idx);
            set
        }
        None => HashSet::new(),
    };
    println!("D1: H4 stratum sites (root + feeders) = {}", h4_sites.len());
    // Caveat chain: the remaining live tag-4 sites (not heads, not H4) + tag-2 joins.
    let caveat_sites: Vec<&&ChipSite> = live_sites
        .iter()
        .filter(|s| {
            (s.tag == Some(4) || s.tag == Some(2))
                && !heads.iter().any(|h| h.idx == s.idx)
                && !h4_sites.contains(&s.idx)
        })
        .collect();
    // Fresh caveat felts: Var inputs not produced by any chip site.
    let all_chip_out: HashSet<usize> = sites
        .iter()
        .flat_map(|s| s.out_vars.iter().copied())
        .collect();
    let caveat_fresh: usize = caveat_sites
        .iter()
        .flat_map(|s| s.ins.iter())
        .filter(|e| matches!(e, LeanExpr::Var(v) if !all_chip_out.contains(v)))
        .count();
    println!(
        "D1: caveat-stratum sites = {} (fresh felts {}) -> rate-8 steps {}",
        caveat_sites.len(),
        caveat_fresh,
        caveat_fresh.div_ceil(8)
    );
    let v_b = v_a - caveat_sites.len() + caveat_fresh.div_ceil(8);
    let v_c = v_b.saturating_sub(h4_sites.len());
    println!(
        "D1: EPOCH-2-B (+caveat rate-8) unique ~= {v_b} -> chip height {}",
        next_pow2(v_b)
    );
    println!(
        "D1: EPOCH-2-C (+H4 retired) unique ~= {v_c} -> chip height {}",
        next_pow2(v_c)
    );

    // -- prove once: cross-check the dedup against the REAL chip instance height, and harvest
    //    the D2 aux geometry off the proof object --
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &mem, &heaps).expect("must prove");
    verify_vm_descriptor2(&desc, &proof, &pis).expect("must verify");

    println!("D2: degree_bits = {:?}", proof.degree_bits);
    let chip_h = 1usize << proof.degree_bits[1];
    assert_eq!(
        chip_h,
        next_pow2(unique_all.len()),
        "the chip table height must be next_pow2(unique permutations) — the D1 dedup census \
         and the deployed build_traces disagree"
    );

    for (i, inst) in proof.opened_values.instances.iter().enumerate() {
        println!(
            "D2: instance {i}: h=2^{} main_cols={} perm_opened(base cols)={} quotient_chunks={}",
            proof.degree_bits.get(i).copied().unwrap_or(0),
            inst.base_opened_values.trace_local.len(),
            inst.permutation_local.len(),
            inst.base_opened_values.quotient_chunks.len(),
        );
    }
    // Bus-name census straight off the proof: one LookupData per GLOBAL interaction.
    for (i, ld) in proof.global_lookup_data.iter().enumerate() {
        let mut by_bus: BTreeMap<&str, usize> = BTreeMap::new();
        for d in ld {
            *by_bus.entry(d.name.as_str()).or_default() += 1;
        }
        println!(
            "D2: instance {i}: {} global interactions by bus = {by_bus:?}",
            ld.len()
        );
        // THE FLATTEN FACTOR: the committed aux matrix is the ext-valued running-sum matrix
        // flattened to base (prover.rs:269 at the pin), so opened perm cols = EXT_DEGREE x
        // interactions. This is the "4 base cols per interaction" accounting, confirmed.
        let perm_opened = proof.opened_values.instances[i].permutation_local.len();
        assert_eq!(
            perm_opened,
            dregg_circuit::descriptor_ir2::IR2_EXT_DEGREE * ld.len(),
            "instance {i}: perm opened cols != ext_degree x interactions"
        );
    }
    let total = postcard::to_allocvec(&proof).unwrap().len();
    let lookups_b = postcard::to_allocvec(&proof.global_lookup_data)
        .unwrap()
        .len();
    println!("D2: proof bytes = {total} (global_lookup_data {lookups_b} B)");
}

// ===========================================================================
// D3
// ===========================================================================

#[test]
fn d3_declared_main_arity_is_inert_in_the_rust_realization() {
    let (desc, mut trace, pis, heaps, mem) = honest_wide_transfer();
    for row in &mut trace {
        row.resize(desc.trace_width, BabyBear::ZERO);
    }
    let deployed = parse_vm_descriptor2(member_json(KEY)).unwrap();
    assert_eq!(desc.name, deployed.name);
    assert_eq!(
        deployed.tables[0].arity,
        compacted_producer_width(),
        "declared main arity at HEAD == the COMPACTED PRODUCER row (the teeth + the prover-filled \
         refuse block ride ABOVE it, which is exactly why the declared arity != trace_width)"
    );
    assert_eq!(
        deployed.trace_width,
        committed_wide_transfer_width(),
        "trace_width at HEAD"
    );
    assert_eq!(
        deployed.trace_width - deployed.tables[0].arity,
        2 + refuse::REFUSE_WELD_WIDEN,
        "the gap between the declared main arity and trace_width is exactly the 2 spliced \
         membership teeth + the refuse-weld footprint"
    );

    let proof_a = prove_vm_descriptor2(&desc, &trace, &pis, &mem, &heaps).expect("baseline proves");
    // Committed main width = trace_width + range-decomposition appendage (the third width).
    println!(
        "D3: widths: declared main arity {} != trace_width {} != committed main cols {}",
        desc.tables[0].arity,
        desc.trace_width,
        proof_a.opened_values.instances[0]
            .base_opened_values
            .trace_local
            .len()
    );

    // Mutate the declared main arity to an absurd value; if any prover/verifier arm read it,
    // this would shift a layout or a transcript observation somewhere.
    let mut mutant = desc.clone();
    for t in mutant.tables.iter_mut() {
        if t.id == 0 {
            t.arity = 99_999;
        }
    }
    let proof_b = prove_vm_descriptor2(&mutant, &trace, &pis, &mem, &heaps).expect("mutant proves");
    verify_vm_descriptor2(&mutant, &proof_b, &pis).expect("mutant verifies");
    // Cross-acceptance both ways: the proofs are interchangeable across the mutation.
    verify_vm_descriptor2(&desc, &proof_b, &pis).expect("mutant proof under deployed desc");
    verify_vm_descriptor2(&mutant, &proof_a, &pis).expect("deployed proof under mutant desc");

    let a = postcard::to_allocvec(&proof_a).unwrap();
    let b = postcard::to_allocvec(&proof_b).unwrap();
    assert_eq!(
        a, b,
        "D3: the declared main-table arity CHANGED the proof bytes — it is load-bearing \
         somewhere in the Rust realization after all"
    );
    println!(
        "D3: proofs byte-identical under arity mutation ({} B) — the declared main arity is \
         INERT in the Rust prove/verify realization (only trace_width + the derived layout \
         matter); its only binding is the registry JSON fingerprint",
        a.len()
    );
}

// ===========================================================================
// D6
// ===========================================================================

#[test]
fn d6_per_member_chip_cliff_census() {
    let mut n_members = 0usize;
    println!(
        "D6: key\tsites\ts2_dead\tlive\tpostS2_h\twide_sites\theads\tfreshA\tfreshB\tcaveat_sites\t\
         caveat_fresh\th4_sites\tmap_ops\trate8_A\th_A\trate8_B\th_B\trate8_C\th_C"
    );
    for line in WIDE_REGISTRY_STAGED_TSV.lines() {
        let mut it = line.splitn(3, '\t');
        let (Some(key), Some(_fp), Some(json)) = (it.next(), it.next(), it.next()) else {
            continue;
        };
        if json.is_empty() {
            continue;
        }
        let Ok(desc) = parse_vm_descriptor2(json) else {
            println!("D6: {key}\tPARSE-FAIL");
            continue;
        };
        n_members += 1;
        let sites = chip_sites(&desc);
        let dead = dead_sites(&desc, &sites);
        let live: Vec<&ChipSite> = sites.iter().filter(|s| !dead.contains(&s.idx)).collect();

        let wide_in: HashSet<usize> = live
            .iter()
            .filter(|s| s.tag == Some(11))
            .flat_map(|s| s.in_vars.iter().copied())
            .collect();
        let heads: Vec<&&ChipSite> = live
            .iter()
            .filter(|s| s.tag == Some(4) && s.out_vars.iter().any(|v| wide_in.contains(v)))
            .collect();
        let head_idx: HashSet<usize> = heads.iter().map(|s| s.idx).collect();
        let wide_sites: Vec<&&ChipSite> = live.iter().filter(|s| s.tag == Some(11)).collect();
        let all_chip_out: HashSet<usize> = sites
            .iter()
            .flat_map(|s| s.out_vars.iter().copied())
            .collect();

        // Fresh felts absorbed by the wide chains: Var inputs of tag-11 sites beyond the 8
        // state lanes that no chip site produces (limbs + iroot), plus the heads' 4 limbs each.
        let fresh_body: usize = wide_sites
            .iter()
            .flat_map(|s| s.ins.iter().skip(8))
            .filter(|e| matches!(e, LeanExpr::Var(v) if !all_chip_out.contains(v)))
            .count();
        let fresh_a = fresh_body; // heads kept as-is (2 seed sites survive)
        let fresh_b = fresh_body + 4 * heads.len(); // heads folded into the rate-8 stream

        // H4 stratum: root = tag-4 site whose out0 is the PI-8-bound column, + its feeders.
        let pi8_col: Option<usize> = desc.constraints.iter().find_map(|k| match k {
            VmConstraint2::Base(VmConstraint::PiBinding {
                col, pi_index: 8, ..
            }) => Some(*col),
            _ => None,
        });
        let h4_root = live.iter().find(|s| {
            s.tag == Some(4) && matches!(&s.outs[0], LeanExpr::Var(v) if Some(*v) == pi8_col)
        });
        let h4_sites: HashSet<usize> = match h4_root {
            Some(root) => {
                let mut set: HashSet<usize> = live
                    .iter()
                    .filter(|s| s.out_vars.iter().any(|v| root.in_vars.contains(v)))
                    .map(|s| s.idx)
                    .collect();
                set.insert(root.idx);
                set
            }
            None => HashSet::new(),
        };

        // Caveat stratum: remaining live tag-4 / tag-2 sites (not heads, not H4).
        let caveat: Vec<&&ChipSite> = live
            .iter()
            .filter(|s| {
                (s.tag == Some(4) || s.tag == Some(2))
                    && !head_idx.contains(&s.idx)
                    && !h4_sites.contains(&s.idx)
            })
            .collect();
        let caveat_fresh: usize = caveat
            .iter()
            .flat_map(|s| s.ins.iter())
            .filter(|e| matches!(e, LeanExpr::Var(v) if !all_chip_out.contains(v)))
            .count();

        let map_ops = desc
            .constraints
            .iter()
            .filter(|k| matches!(k, VmConstraint2::MapOp(_)))
            .count();

        // Projections (static NO-DEDUP upper bounds; D1 measures dedup on the transfer):
        //   A: S2 gone, wide chains at rate 8 (heads kept), caveat + H4 as-is.
        //   B: A + heads folded + caveat at rate 8.
        //   C: B + H4 retired.
        let post_s2 = live.len();
        let rate8_a = post_s2 - wide_sites.len() + fresh_a.div_ceil(8);
        let rate8_b = post_s2 - wide_sites.len() - heads.len() - caveat.len()
            + fresh_b.div_ceil(8)
            + caveat_fresh.div_ceil(8);
        let rate8_c = rate8_b.saturating_sub(h4_sites.len());

        println!(
            "D6: {key}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            sites.len(),
            dead.len(),
            post_s2,
            next_pow2(post_s2),
            wide_sites.len(),
            heads.len(),
            fresh_a,
            fresh_b,
            caveat.len(),
            caveat_fresh,
            h4_sites.len(),
            map_ops,
            rate8_a,
            next_pow2(rate8_a),
            rate8_b,
            next_pow2(rate8_b),
            rate8_c,
            next_pow2(rate8_c),
        );
    }
    println!("D6: members = {n_members}");
    assert_eq!(n_members, 57, "the wide staged registry carries 57 members");
}

// ===========================================================================
// E3 — mutable-last limb schedule: the rate-8 sim re-run (pre-freeze decision)
// ===========================================================================

/// E3 (`docs/EFFICIENCY-BACKLOG-circuit-minimality.md` rank 3) — MEASUREMENT ONLY; no
/// emitted/deployed descriptor byte is touched. The v10 absorption order is being frozen in
/// the Epoch-2 bundle. The deployed (v9) schedule absorbs the transfer-mutated scalars FIRST
/// (`pre[1]=balance_lo, pre[2]=nonce, pre[3]=balance_hi`, `cell/src/commitment.rs:1075-1083`),
/// so D1's rate-8 simulation measured ZERO cross-chain dedup: the BEFORE/AFTER 179-felt
/// streams diverge in the head step and every subsequent chained step differs (46/46 unique
/// -> chip height 64). This test re-runs the SAME simulator under the two mutable-LAST
/// candidate schedules — a schedule is a static position permutation applied identically to
/// both chains — and reports the shared-step count, the unique-tuple count, and the Epoch-2
/// A/B/C chip heights. Because 179 = 22*8 + 3, the two candidates differ by ONE shared step:
///
///   M1: mutable scalars last among the PRE-limbs, iroot kept absolutely last (preserves the
///       v9 "iroot absorbed last" invariant) — balance_lo lands in step 21 of 23.
///   M2: mutable scalars absolutely last (after the iroot) — all divergence in step 22 of 23.
#[test]
fn e3_mutable_last_limb_schedule_rate8_sim() {
    let (desc, mut trace, _pis, _heaps, _mem) = honest_wide_transfer();
    for row in &mut trace {
        row.resize(desc.trace_width, BabyBear::ZERO);
    }
    for row in &mut trace {
        fill_chip_lanes(&desc, row);
    }
    let sites = chip_sites(&desc);
    let dead = dead_sites(&desc, &sites);
    let live_sites: Vec<&ChipSite> = sites.iter().filter(|s| !dead.contains(&s.idx)).collect();

    // -- harvest the two wide fresh streams (the identical walk to D1's) --
    let wide_out_vars: HashSet<usize> = live_sites
        .iter()
        .filter(|s| s.tag == Some(11))
        .flat_map(|s| s.out_vars.iter().copied())
        .collect();
    let wide_in_vars: HashSet<usize> = live_sites
        .iter()
        .filter(|s| s.tag == Some(11))
        .flat_map(|s| s.in_vars.iter().copied())
        .collect();
    let heads: Vec<&&ChipSite> = live_sites
        .iter()
        .filter(|s| s.tag == Some(4) && s.out_vars.iter().any(|v| wide_in_vars.contains(v)))
        .collect();
    assert_eq!(heads.len(), 2, "one BEFORE and one AFTER wide head");
    let head_out: HashSet<usize> = heads
        .iter()
        .flat_map(|s| s.out_vars.iter().copied())
        .collect();
    let mut chains: Vec<Vec<BabyBear>> = Vec::new();
    for head in &heads {
        let mut stream: Vec<BabyBear> = head.ins.iter().take(4).map(|e| ev(e, &trace[0])).collect();
        let mut cur: &ChipSite = head;
        loop {
            let next = live_sites.iter().find(|s| {
                s.tag == Some(11)
                    && s.idx != cur.idx
                    && s.in_vars.iter().any(|v| cur.out_vars.contains(v))
            });
            let Some(next) = next else { break };
            for (k, e) in next.ins.iter().enumerate() {
                if k < 8 {
                    continue; // state lanes
                }
                if let LeanExpr::Var(v) = e {
                    if !wide_out_vars.contains(v) && !head_out.contains(v) {
                        stream.push(ev(e, &trace[0]));
                    }
                }
            }
            cur = next;
        }
        chains.push(stream);
    }
    assert_eq!(chains.len(), 2);
    for (i, c) in chains.iter().enumerate() {
        assert_eq!(c.len(), 185, "chain {i}: 184 pre-limbs + iroot");
    }

    // -- the empirical divergence set: WHERE do the two streams actually differ? --
    // The E3 premise is that a transfer's divergence is confined to the three mutable
    // scalars r0/r1/r2 (stream positions 1..=3); cells_root (0) and the iroot (178) are
    // turn-level, everything else (fields, authority digest, roots) is untouched by a
    // transfer. If this assert ever fires, the reorder win is smaller than projected.
    let divergent: Vec<usize> = (0..179)
        .filter(|&i| chains[0][i].as_u32() != chains[1][i].as_u32())
        .collect();
    println!("E3: BEFORE/AFTER divergent stream positions = {divergent:?} (of 179)");
    assert!(!divergent.is_empty(), "a transfer must move the balance");
    assert!(
        divergent.iter().all(|&i| (1..=3).contains(&i)),
        "transfer divergence must be confined to the mutable scalars at stream positions \
         1..=3 (balance_lo/nonce/balance_hi, cell/src/commitment.rs:1075-1083); got \
         {divergent:?}"
    );

    // -- the same rate-8 simulator as D1 (state8 ‖ 8 fresh felts, arity-16, domain-seeded) --
    let simulate = |seed_tag: u32, stream: &[BabyBear]| -> Vec<Vec<u32>> {
        let mut tuples = Vec::new();
        let mut state: [BabyBear; 8] =
            chip_absorb_all_lanes(4, &[BabyBear::new(0xD05EED), BabyBear::new(seed_tag)]);
        for block in stream.chunks(8) {
            let mut ins: Vec<BabyBear> = state.to_vec();
            ins.extend_from_slice(block);
            ins.resize(16, BabyBear::ZERO);
            let outs = chip_absorb_all_lanes(16, &ins);
            let mut t = Vec::with_capacity(CHIP_TUPLE_LEN);
            t.push(16u32);
            for v in &ins {
                t.push(v.as_u32());
            }
            for v in &outs {
                t.push(v.as_u32());
            }
            tuples.push(t);
            state = outs;
        }
        tuples
    };

    // -- the candidate schedules: static position permutations, applied to BOTH chains --
    let identity: Vec<usize> = (0..179).collect();
    let mut m1: Vec<usize> = vec![0];
    m1.extend(4..178);
    m1.extend([1, 2, 3]);
    m1.push(178);
    let mut m2: Vec<usize> = vec![0];
    m2.extend(4..178);
    m2.push(178);
    m2.extend([1, 2, 3]);
    for (name, p) in [("M1", &m1), ("M2", &m2)] {
        assert_eq!(p.len(), 179, "{name}: schedule length");
        let mut seen = vec![false; 179];
        for &i in p.iter() {
            assert!(!seen[i], "{name}: position {i} scheduled twice");
            seen[i] = true;
        }
    }

    // Run one schedule under the SHARED-seed discipline; returns (unique, shared steps).
    let run = |perm: &[usize]| -> (usize, usize) {
        let per_chain: Vec<Vec<Vec<u32>>> = chains
            .iter()
            .map(|c| {
                let reordered: Vec<BabyBear> = perm.iter().map(|&i| c[i]).collect();
                simulate(0, &reordered)
            })
            .collect();
        assert_eq!(per_chain[0].len(), 23, "179 felts -> 23 rate-8 steps");
        assert_eq!(per_chain[1].len(), 23);
        let shared = per_chain[0]
            .iter()
            .zip(per_chain[1].iter())
            .filter(|(a, b)| a == b)
            .count();
        let uniq: BTreeSet<&Vec<u32>> = per_chain.iter().flatten().collect();
        (uniq.len(), shared)
    };

    let (base_uniq, base_shared) = run(&identity);
    println!(
        "E3: DEPLOYED order (mutable-FIRST): shared steps = {base_shared}/23, unique = \
         {base_uniq}/46"
    );
    assert_eq!(
        (base_uniq, base_shared),
        (46, 0),
        "D1 calibration: the deployed order has ZERO cross-chain dedup"
    );

    let (m1_uniq, m1_shared) = run(&m1);
    let (m2_uniq, m2_shared) = run(&m2);
    println!(
        "E3: M1 (mutable-last, iroot last): shared steps = {m1_shared}/23, unique = {m1_uniq}/46"
    );
    println!(
        "E3: M2 (mutable absolute-last):    shared steps = {m2_shared}/23, unique = {m2_uniq}/46"
    );
    // Divergence is chained: once a step differs, every later step differs. balance_lo sits
    // at reordered position 175 under M1 (step 21: two divergent steps) and 176 under M2
    // (step 22: one divergent step). The counts are pinned so any drift SPEAKS.
    assert_eq!(
        (m1_shared, m1_uniq),
        (21, 25),
        "M1: 21/23 shared -> 23 + 2 unique"
    );
    assert_eq!(
        (m2_shared, m2_uniq),
        (22, 24),
        "M2: 22/23 shared -> 23 + 1 unique"
    );

    // -- the seed coupling: a per-object domain seed kills the entire win --
    let perobj: Vec<Vec<u32>> = chains
        .iter()
        .enumerate()
        .flat_map(|(i, c)| {
            let reordered: Vec<BabyBear> = m1.iter().map(|&j| c[j]).collect();
            simulate(i as u32 + 1, &reordered)
        })
        .collect();
    let perobj_uniq: BTreeSet<&Vec<u32>> = perobj.iter().collect();
    println!(
        "E3: M1 under PER-OBJECT seeds: unique = {}/46 — the dedup exists ONLY under the \
         shared-seed discipline; the design-B per-object seed choice forfeits it",
        perobj_uniq.len()
    );
    assert_eq!(perobj_uniq.len(), 46);

    // -- Epoch-2 A/B/C projections (the same bundle arithmetic as D1) --
    let head_idx: HashSet<usize> = heads.iter().map(|s| s.idx).collect();
    let mut survivor_tuples: BTreeSet<Vec<u32>> = BTreeSet::new();
    for s in live_sites
        .iter()
        .filter(|s| s.tag != Some(11) && !head_idx.contains(&s.idx))
    {
        let mut t = Vec::with_capacity(CHIP_TUPLE_LEN);
        t.push(s.tag.unwrap() as u32);
        for e in &s.ins {
            t.push(ev(e, &trace[0]).as_u32());
        }
        for e in &s.outs {
            t.push(ev(e, &trace[0]).as_u32());
        }
        survivor_tuples.insert(t);
    }
    let survivors = survivor_tuples.len();
    // ⚑ 14 → 16 at the rc FOLD: the caveat region gained the two chip sites that absorb the DFA
    // route-commitment carrier into the published caveat commitment, and neither is a chain HEAD
    // nor a tag-11 wide site, so both land in the non-wide survivor set.
    assert_eq!(survivors, 16, "D1's non-wide survivor count");

    let pi8_col: Option<usize> = desc.constraints.iter().find_map(|k| match k {
        VmConstraint2::Base(VmConstraint::PiBinding {
            col, pi_index: 8, ..
        }) => Some(*col),
        _ => None,
    });
    let h4_root: Option<&&ChipSite> = live_sites.iter().find(|s| {
        s.tag == Some(4) && matches!(&s.outs[0], LeanExpr::Var(v) if Some(*v) == pi8_col)
    });
    let h4_sites: HashSet<usize> = match h4_root {
        Some(root) => {
            let mut set: HashSet<usize> = live_sites
                .iter()
                .filter(|s| s.out_vars.iter().any(|v| root.in_vars.contains(v)))
                .map(|s| s.idx)
                .collect();
            set.insert(root.idx);
            set
        }
        None => HashSet::new(),
    };
    let caveat_sites: Vec<&&ChipSite> = live_sites
        .iter()
        .filter(|s| {
            (s.tag == Some(4) || s.tag == Some(2))
                && !head_idx.contains(&s.idx)
                && !h4_sites.contains(&s.idx)
        })
        .collect();
    let all_chip_out: HashSet<usize> = sites
        .iter()
        .flat_map(|s| s.out_vars.iter().copied())
        .collect();
    let caveat_fresh: usize = caveat_sites
        .iter()
        .flat_map(|s| s.ins.iter())
        .filter(|e| matches!(e, LeanExpr::Var(v) if !all_chip_out.contains(v)))
        .count();
    // ⚑ (10, 29, 4) → (12, 33, 4) at the rc FOLD. The caveat stratum gained the TWO sites that
    // absorb the DFA route-commitment carrier into the published caveat commitment (one arity-4,
    // one arity-2), and with them FOUR fresh inputs — the four rc lanes, which are exactly the
    // columns that were read by nothing before. The H4 stratum is untouched.
    assert_eq!(
        (caveat_sites.len(), caveat_fresh, h4_sites.len()),
        (12, 33, 4),
        "D1's caveat/H4 strata"
    );

    let project = |name: &str, wide_uniq: usize| -> (usize, usize, usize) {
        let v_a = survivors + wide_uniq;
        let v_b = v_a - caveat_sites.len() + caveat_fresh.div_ceil(8);
        let v_c = v_b - h4_sites.len();
        println!(
            "E3: {name}: EPOCH-2-A ~= {v_a} -> h {} | EPOCH-2-B ~= {v_b} -> h {} | \
             EPOCH-2-C ~= {v_c} -> h {}",
            next_pow2(v_a),
            next_pow2(v_b),
            next_pow2(v_c)
        );
        (v_a, v_b, v_c)
    };
    let (_, b0, c0) = project("DEPLOYED order", base_uniq);
    let (_, b1, c1) = project("M1            ", m1_uniq);
    let (_, b2, c2) = project("M2            ", m2_uniq);
    assert_eq!(
        next_pow2(c0),
        64,
        "mutable-first: the bundle is stuck at 64"
    );
    assert_eq!(next_pow2(b0), 64);
    assert_eq!(
        next_pow2(c1),
        32,
        "M1 lands the full Epoch-2 bundle (C) at chip height 32"
    );
    assert_eq!(next_pow2(c2), 32);
    assert_eq!(
        next_pow2(b1),
        64,
        "M1 leaves EPOCH-2-B at 64 (one step of dedup short: 33 > 32)"
    );
    // ⚑ 32 → 64 at the rc FOLD, and this is a MEASURED COST, not a re-pin. The caveat fold's two
    // new absorption sites move the projection by +1 (`survivors` +2, `caveat_sites` +2 cancelling
    // it, `caveat_fresh` 29 → 33 crossing a rate-8 bucket: ⌈33/8⌉ = 5 where ⌈29/8⌉ = 4), which puts
    // EPOCH-2-B at 33 — one over the cliff. EPOCH-2-C is unaffected (`c2` = 29, still ≤ 32), so the
    // full Epoch-2 bundle still lands at chip height 32 under M2; only the B projection loses it.
    // Recorded here rather than smoothed away: the route-commitment binding cost one rate-8 step of
    // headroom in the B stratum, and a future scheduling change should know it is spending against
    // 33, not 32.
    assert_eq!(
        next_pow2(b2),
        64,
        "M2's EPOCH-2-B is one step over the 32 cliff since the rc fold (33 unique)"
    );

    // -- registry-wide projection: the wide skeleton (118 tag-11 sites + 2 heads, 179 fresh
    //    felts/chain) is IDENTICAL on all 57 members (D6), so the wide-step dedup transposes
    //    as rate8_C' = rate8_C - 46 + unique. HONEST SCOPE: the FULL dedup applies to verbs
    //    whose BEFORE/AFTER mutation set rides the reordered tail (balance/nonce verbs:
    //    transfer/burn/mint/fee/supplyMint/...). Verbs mutating mid-schedule limb groups
    //    (setField -> field lanes, setPerms/setVK -> their groups, capOpen writes ->
    //    cap_root at pre-limb 25) diverge from that group's step onward, and map-op members
    //    additionally carry unmeasured witness node8 rows. --
    println!("E3: registry projection at M1 (rate8_C' = rate8_C - 46 + {m1_uniq}):");
    for (class, n, rate8_c) in [
        ("transfer-core verbs", 33usize, 49usize),
        ("makeSovereign", 1, 51),
        ("noteSpend/noteCreate/createCell", 3, 65),
        ("capOpen family", 16, 66),
        ("refusal/heapWrite", 2, 82),
        ("attenuateCapOpenEff/refreshDelegationWCO", 2, 83),
    ] {
        let v = rate8_c - 46 + m1_uniq;
        println!(
            "E3:   {class} ({n} members): rate8_C {rate8_c} -> {v} -> chip height {}",
            next_pow2(v)
        );
    }
    // The closed form for the freeze decision (transfer-family constants at the rc-fold geometry:
    // survivors 16 - caveat 12 + caveat-steps 5 - H4 4 = +5): v_C = wide_unique + 5, so chip-32
    // needs wide_unique <= 27, i.e. at most 5 divergent after-chain steps, i.e. the verb's whole
    // mutation set confined to the LAST 5 rate-8 steps = the last 35 schedule positions. (The
    // window is unchanged; the slack inside it shrank by one unique tuple.)
    println!(
        "E3: tail window — chip-32 holds for any verb whose BEFORE/AFTER mutation set fits \
         the last 35 schedule positions (divergence confined to the final 5 of 23 steps)"
    );
    println!(
        "E3: cell arithmetic at the D2-corrected chip shape (398 base cols): h=64 = {} \
         cells, h=32 = {} cells; the 64->32 halving saves {} committed cells (~{:.1}% of \
         the 82,720-cell floor)",
        398 * 64,
        398 * 32,
        398 * 32,
        100.0 * (398.0 * 32.0) / 82_720.0
    );
}

// ===========================================================================
// D7 — the preprocessed-column spike (p3 toys; NOT deployment candidates)
// ===========================================================================

mod d7 {
    use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
    use p3_batch_stark::{ProverData, StarkInstance, prove_batch, verify_batch};
    use p3_field::Field;
    use p3_field::PrimeCharacteristicRing;
    use p3_field::PrimeField32;
    use p3_lookup::InteractionBuilder;
    use p3_lookup::bus::PermutationCheckBus;
    use p3_matrix::dense::RowMajorMatrix;

    type Val = p3_baby_bear::BabyBear;

    /// One ROW-CONSTANT column carried as preprocessed: `main[0] == prep[0]` on every row.
    #[derive(Clone, Copy)]
    pub struct PrepConstAir {
        pub height: usize,
        pub value: u64,
        pub tamper: bool,
        /// Also push a self-balancing LogUp interaction whose FIELD reads the preprocessed
        /// column (the design-B "masked multiset" adoption probe).
        pub with_lookup: bool,
    }

    impl<F: Field> BaseAir<F> for PrepConstAir {
        fn width(&self) -> usize {
            1
        }
        fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
            let mut v = vec![F::from_u64(self.value); self.height];
            if self.tamper {
                v[1] += F::ONE;
            }
            Some(RowMajorMatrix::new_col(v))
        }
        fn preprocessed_width(&self) -> usize {
            1
        }
    }

    impl<AB> Air<AB> for PrepConstAir
    where
        AB: AirBuilder + InteractionBuilder,
        AB::F: PrimeField32,
    {
        fn eval(&self, builder: &mut AB) {
            let local0: AB::Expr = {
                let main = builder.main();
                let v: AB::Var = main.current(0).unwrap();
                v.into()
            };
            let prep0: AB::Expr = {
                let prep = builder.preprocessed();
                let v = prep.current(0).unwrap();
                v.into()
            };
            builder.assert_zero(local0.clone() - prep0.clone());
            if self.with_lookup {
                // Send + receive the SAME preprocessed-valued tuple: balances to zero, but
                // forces the LogUp field-evaluation path to read the preprocessed matrix.
                let bus = PermutationCheckBus::new("d7_prep_probe");
                bus.send(builder, [prep0.clone()], AB::Expr::ONE);
                bus.receive(builder, [prep0], AB::Expr::ONE);
            }
        }
    }

    /// The same statement WITHOUT preprocessed columns (baseline for the byte delta).
    #[derive(Clone, Copy)]
    pub struct PlainConstAir {
        pub value: u64,
    }
    impl<F: Field> BaseAir<F> for PlainConstAir {
        fn width(&self) -> usize {
            1
        }
    }
    impl<AB> Air<AB> for PlainConstAir
    where
        AB: AirBuilder + InteractionBuilder,
        AB::F: PrimeField32,
    {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let v: AB::Var = main.current(0).unwrap();
            let c = AB::Expr::from_u64(self.value);
            let e: AB::Expr = v.into();
            builder.assert_zero(e - c);
        }
    }

    #[test]
    fn d7_preprocessed_column_spike() {
        // The PRODUCTION IR-v2 FRI knobs, so the answer is about the deployed configuration,
        // not a toy one.
        let config = dregg_circuit::plonky3_prover::create_config_with_fri(
            dregg_circuit::descriptor_ir2::IR2_FRI_LOG_BLOWUP,
            dregg_circuit::descriptor_ir2::IR2_FRI_LOG_FINAL_POLY_LEN,
            dregg_circuit::descriptor_ir2::IR2_FRI_MAX_LOG_ARITY,
            dregg_circuit::descriptor_ir2::IR2_FRI_NUM_QUERIES,
            dregg_circuit::descriptor_ir2::IR2_FRI_QUERY_POW_BITS,
        );
        let height = 64usize;
        let value = 0xC0FFEEu64;
        let trace = RowMajorMatrix::new_col(vec![Val::from_u64(value); height]);

        // (1) The basic carry: one preprocessed constant column, committed ONCE into
        //     CommonData (the VK side), opened per proof.
        let air = PrepConstAir {
            height,
            value,
            tamper: false,
            with_lookup: false,
        };
        let instances = vec![StarkInstance {
            air: &air,
            trace: &trace,
            public_values: vec![],
        }];
        let prover_data = ProverData::from_instances(&config, &instances);
        assert!(
            prover_data.common.preprocessed.is_some(),
            "D7: the pinned batch-stark must commit the preprocessed matrix into CommonData"
        );
        let proof = prove_batch(&config, &instances, &prover_data);
        verify_batch(&config, &[air], &proof, &[vec![]], &prover_data.common)
            .expect("D7: preprocessed constant column must prove + verify");
        let prep_bytes = postcard::to_allocvec(&proof).unwrap().len();

        // (2) Tamper rejection: a verifier pinned to a DIFFERENT preprocessed commitment must
        //     refuse this proof (the committed-once column is sound, not advisory).
        let tampered = PrepConstAir {
            height,
            value,
            tamper: true,
            with_lookup: false,
        };
        let t_instances = vec![StarkInstance {
            air: &tampered,
            trace: &trace,
            public_values: vec![],
        }];
        let t_data = ProverData::from_instances(&config, &t_instances);
        assert!(
            verify_batch(&config, &[tampered], &proof, &[vec![]], &t_data.common).is_err(),
            "D7: a proof against commitment A must NOT verify under commitment B"
        );

        // (3) The interaction probe: a LogUp field reading the preprocessed column.
        let lk_air = PrepConstAir {
            height,
            value,
            tamper: false,
            with_lookup: true,
        };
        let lk_instances = vec![StarkInstance {
            air: &lk_air,
            trace: &trace,
            public_values: vec![],
        }];
        let lk_data = ProverData::from_instances(&config, &lk_instances);
        let lk_proof = prove_batch(&config, &lk_instances, &lk_data);
        verify_batch(&config, &[lk_air], &lk_proof, &[vec![]], &lk_data.common)
            .expect("D7: a LogUp interaction with a preprocessed-valued field must verify");

        // (4) Baseline without preprocessed, same statement, for the wire delta.
        let plain = PlainConstAir { value };
        let p_instances = vec![StarkInstance {
            air: &plain,
            trace: &trace,
            public_values: vec![],
        }];
        let p_data = ProverData::from_instances(&config, &p_instances);
        let p_proof = prove_batch(&config, &p_instances, &p_data);
        verify_batch(&config, &[plain], &p_proof, &[vec![]], &p_data.common)
            .expect("baseline verifies");
        let plain_bytes = postcard::to_allocvec(&p_proof).unwrap().len();

        println!(
            "D7: GREEN at the pin — preprocessed column proves+verifies under the PRODUCTION \
             IR-v2 FRI config; commitment lives in CommonData (VK-side, committed once); \
             tamper REJECTED; LogUp-field-over-preprocessed GREEN. proof bytes: with prep {} \
             vs plain {} (delta {:+} B/column at h=64)",
            prep_bytes,
            plain_bytes,
            prep_bytes as i64 - plain_bytes as i64
        );
    }
}
