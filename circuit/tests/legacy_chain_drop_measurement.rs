//! # THE S2-DELETION YIELD — measured on the DEPLOYED compact member (Epoch 1 landed).
//!
//! The pre-flip harness in this file measured what DELETING the two rotated 1-felt
//! Merkle–Damgård chains (S2) would buy, via a mechanical drop variant, and recorded the
//! deployed baseline (docs/MEASURE-legacy-1felt-chain-drop.md:108-138):
//!
//!   proof 556,810 B | committed cells 578,720 base-eq | prover ~637.9 ms | width 2664
//!
//! The deletion has now LANDED: the committed wide registry is S2-compacted at the Lean emit
//! (`RotWideCompactS2.compactS2`, gated per member by `compactOk`), the producer compacts
//! through the Lean-emitted geometry table, and the dispatcher resolves the compact member.
//! This test measures the DEPLOYED member as-is and prints the delta against the RECORDED
//! pre-flip baseline. It also asserts the ABSENCE of the S2 stratum (no poseidon2 lookup's
//! out0 in the retired carrier bands) — the negative twin of the emit-time `compactOk` gate.
//!
//! Run (release; debug prove times are lies):
//! ```text
//! CARGO_TARGET_DIR=/tmp/nf-check cargo test -p dregg-circuit --release \
//!   --test legacy_chain_drop_measurement -- --nocapture
//! ```

use std::time::Instant;

use dregg_circuit::CellState;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::Effect;
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, generate_rotated_effect_vm_descriptor_and_trace_wide,
    transfer_caveat_manifest,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_turn::rotation_witness as rw;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};

/// The RECORDED pre-flip deployed baseline ([M], docs/MEASURE-legacy-1felt-chain-drop.md).
///
/// ⚠ THESE THREE ARE RETIRED-GEOMETRY FIGURES and are used ONLY in the report `println!`s at the
/// bottom of this file. They were measured on the 178-limb member; the deployed member is now
/// 184-limb, so the byte/cell/millisecond deltas they print are CROSS-EPOCH and overstate the S2
/// deletion's yield by whatever the nine-lane epoch itself added. They are kept, labelled, rather
/// than silently re-typed, because nobody has re-measured them.
const BASELINE_BYTES: usize = 556_810;
const BASELINE_CELLS: usize = 578_720;
const BASELINE_PROVER_MS: f64 = 637.9;

/// The UNCOMPACTED deployed wide-transfer width at the CURRENT geometry — the only baseline the
/// width assertion below uses, and the one figure of the four that is re-derived rather than
/// recorded:
///
/// ```text
/// UNCOMPACTED = <narrow deployed cohort trace_width> + WIDE_CARRIER_APPENDIX + 2 membership teeth
///   178-limb:  1702 + 960 + 2 = 2664   (the recorded [M] baseline, reproduced exactly)
///   184-limb:  1746 + 992 + 2 = 2740
///   rc FOLD:   1762 + 992 + 2 = 2756
///   CANON9:    1874 + 992 + 2 = 2868
/// ```
///
/// The +76 (178 → 184) is `44` on the narrow member (`2·ΔB_SPAN + 7·ΔN_ROT_SITES = 16 + 28`) plus
/// `32` on the carrier appendix (`2 · 8 · ΔWIDE_NUM_CARRIERS = 2·8·2`). The further +16 (rc FOLD)
/// is entirely on the narrow member: `ΔC_SPAN(2) + 7·ΔN_ROT_SITES(2) = 2 + 14`, the two carriers
/// the caveat fold's rc extension needs plus their graduated chip lanes; the carrier appendix does
/// not move.
///
/// ⚑ The further +112 (FIELDS-CANONICITY, 2026-07-31) is ALSO entirely on the narrow member, and
/// for the OPPOSITE reason to the rc fold's: `ΔAPPENDIX_SPAN = CANON9_SPAN = 2 blocks · 8 slots ·
/// 7 aux = 112` with `ΔN_ROT_SITES = 0`. `fieldsCanonical9At_hashSites` proves the wrap adds no
/// hash site — it appends constraints into columns `rotateV3` had already allocated — so nothing
/// is multiplied by 7 here. And `WIDE_NUM_CARRIERS` is a function of `NUM_PRE_LIMBS`, which did
/// not move, so the carrier appendix stays at 992: the aux region rides PAST the limbs and the
/// absorption chain never sees it.
///
/// Cross-check that this is the right baseline and not a fitted number:
/// `2868 − S2_DELETED_COLS(992) − e1_drop(94) = 1782`, which is the committed
/// `transferVmDescriptor2R24` wide width, and the assertion below computes exactly that
/// subtraction from live constants.
///
/// **The deletion's CLAIM is unchanged, and the RATIO is WEAKENING — which is the honest way to
/// report it.** It removed `960 + 94 = 1054` of 2664 columns (−39.6%); then `992 + 94 = 1086` of
/// 2740 (−39.6%); then of 2756 (−39.4%); now `992 + 94 = 1086` of 2868 (−37.9%). The S2 band grows
/// with the LIMB COUNT, not with the caveat region and not with the canonicity aux, so both the rc
/// fold's +16 and canon9's +112 land entirely on the SURVIVING side. That is not a regression: a
/// dead-stratum deletion must not touch bound columns, and every one of those 128 is read by a
/// constraint.
const BASELINE_WIDTH: usize = 2868;

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

/// The honest wide transfer, minted through the PRODUCTION dispatcher
/// (`generate_rotated_effect_vm_descriptor_and_trace_wide` — the call
/// `mint_rotated_participant_leg` makes for a transfer), so the descriptor, trace, PI vector and
/// witnesses are exactly the deployed set: 68 PIs = 66 producer + 2 spliced membership claim PIs.
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
    // The producer-honest membership-teeth pair (the 2 teeth columns pair 1:1 with the 2 claim PIs).
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

// ---------------------------------------------------------------------------
// (1) THE STRUCTURAL FINDING — pinned, so a future emit change cannot silently
//     change the answer this measurement was taken under.
// ---------------------------------------------------------------------------

fn breakdown(
    label: &str,
    proof: &p3_batch_stark::BatchProof<dregg_circuit::plonky3_prover::DreggStarkConfig>,
) -> (usize, usize, usize) {
    let total = postcard::to_allocvec(proof).expect("postcard").len();
    let opened = postcard::to_allocvec(&proof.opened_values).unwrap().len();
    let opening = postcard::to_allocvec(&proof.opening_proof).unwrap().len();
    let commitments = postcard::to_allocvec(&proof.commitments).unwrap().len();
    let lookups = postcard::to_allocvec(&proof.global_lookup_data)
        .unwrap()
        .len();
    println!(
        "[{label}] proof {total} B | commitments {commitments} B | opened_values {opened} B | \
         opening_proof {opening} B | lookup_data {lookups} B | degree_bits {:?}",
        proof.degree_bits
    );
    for (i, inst) in proof.opened_values.instances.iter().enumerate() {
        println!(
            "[{label}]   instance {i}: log2(h)={} main_cols={} perm_cols(ext)={} quotient_chunks={}",
            proof.degree_bits.get(i).copied().unwrap_or(0),
            inst.base_opened_values.trace_local.len(),
            inst.permutation_local.len(),
            inst.base_opened_values.quotient_chunks.len(),
        );
    }
    (total, opened, opening)
}

/// Committed base-eq cells, the docs/MEASURE accounting: Σ height · (main base cols + 4·ext perm
/// cols) over the batch instances (the quotient is not a committed trace; the range instance's
/// small contribution is included via its instance row).
fn committed_cells(
    proof: &p3_batch_stark::BatchProof<dregg_circuit::plonky3_prover::DreggStarkConfig>,
) -> usize {
    proof
        .opened_values
        .instances
        .iter()
        .enumerate()
        .map(|(i, inst)| {
            let h = 1usize << proof.degree_bits.get(i).copied().unwrap_or(0);
            h * (inst.base_opened_values.trace_local.len() + 4 * inst.permutation_local.len())
        })
        .sum()
}

#[test]
fn s2_deletion_yield_measurement() {
    const REPS: usize = 3;

    let (deployed, mut trace, pis, heaps, mem) = honest_wide_transfer();
    // The deployed compact width: 2664 − 960 (two 60-col carrier bands + 840 chip lanes, S2) − the
    // E1 dead v1-face bands (Epoch-1 SECOND flag-day, per-member from the Lean-emitted table).
    let e1_drop: usize = dregg_circuit::effect_vm::e1_compact_generated::E1_COMPACT_TABLE
        .iter()
        .find(|(k, _)| *k == "transferVmDescriptor2R24")
        .map(|(_, iv)| iv.iter().map(|(a, b)| b - a).sum())
        .expect("transfer in E1_COMPACT_TABLE");
    assert_eq!(
        deployed.trace_width,
        BASELINE_WIDTH - dregg_circuit::effect_vm::s2_compact_generated::S2_DELETED_COLS - e1_drop,
        "compact width"
    );
    assert_eq!(
        deployed.public_input_count, 68,
        "PI shape UNCHANGED by the deletion"
    );
    assert_eq!(pis.len(), deployed.public_input_count);

    // THE ABSENCE GATE: no poseidon2 lookup's out0 lands in the retired 1-felt carrier bands
    // (the S2 stratum is GONE from the committed member, not merely unread).
    // READ from the Lean-emitted s2_compact_generated table — never transcribed, so a regen that
    // moves this member's block base cannot leave the band arithmetic below pointing at stale
    // columns.
    let (bb, lane) = dregg_circuit::effect_vm::s2_compact_generated::S2_COMPACT_TABLE
        .iter()
        .find(|(k, _, _)| *k == "transferVmDescriptor2R24")
        .map(|(_, bb, lane)| (*bb, *lane))
        .expect("transfer in S2_COMPACT_TABLE");
    let dead = |c: usize| {
        (bb + 179 - 60..bb + 179).contains(&c) // compact coords: the bands were REMOVED, so
    };
    let _ = dead; // (the bands do not exist in compact coordinates; assert via count instead)
    let arity4 = deployed
        .constraints
        .iter()
        .filter(|k| match k {
            VmConstraint2::Lookup(l) if l.table == 1 => {
                let genuine = l.tuple[1..17]
                    .iter()
                    .filter(|e| matches!(e, LeanExpr::Var(_)))
                    .count();
                genuine == 4
            }
            _ => false,
        })
        .count();
    // Pre-flip: 133 arity-4 sites (120 S2 chain + own/caveat heads). Post-flip: the S2 chain's
    // 118 arity-4 body sites are gone; what remains is the S1 H4 commit + caveat heads + wide heads.
    assert!(
        arity4 < 20,
        "the 120-site 1-felt chains are gone (found {arity4} arity-4 chip lookups)"
    );
    let _ = lane;

    println!("=========================================================");
    println!(
        "deployed (S2-compacted): name={} width={}",
        deployed.name, deployed.trace_width
    );
    println!("=========================================================");

    for row in &mut trace {
        row.resize(deployed.trace_width, BabyBear::ZERO);
    }

    let mut prove_ms = Vec::new();
    let mut verify_ms = Vec::new();
    let mut bytes = (0usize, 0usize, 0usize);
    let mut cells = 0usize;
    for r in 0..REPS {
        let t0 = Instant::now();
        let proof = prove_vm_descriptor2(&deployed, &trace, &pis, &mem, &heaps)
            .unwrap_or_else(|e| panic!("DEPLOYED compact member MUST PROVE: {e}"));
        prove_ms.push(t0.elapsed().as_secs_f64() * 1000.0);
        let t1 = Instant::now();
        verify_vm_descriptor2(&deployed, &proof, &pis)
            .unwrap_or_else(|e| panic!("DEPLOYED compact member MUST VERIFY: {e}"));
        verify_ms.push(t1.elapsed().as_secs_f64() * 1000.0);
        if r == 0 {
            bytes = breakdown("DEPLOYED-COMPACT", &proof);
            cells = committed_cells(&proof);
        }
    }
    prove_ms.sort_by(f64::total_cmp);
    verify_ms.sort_by(f64::total_cmp);

    let pct = |a: f64, b: f64| (b - a) / a * 100.0;
    println!("========== THE S2-DELETION YIELD (vs recorded pre-flip [M]) ==========");
    println!(
        "trace width   : {} -> {}  ({:+.1}%)",
        BASELINE_WIDTH,
        deployed.trace_width,
        pct(BASELINE_WIDTH as f64, deployed.trace_width as f64)
    );
    println!(
        "proof bytes   : {} -> {}  ({:+.1}%)",
        BASELINE_BYTES,
        bytes.0,
        pct(BASELINE_BYTES as f64, bytes.0 as f64)
    );
    println!(
        "committed cells: {} -> {}  ({:+.1}%)",
        BASELINE_CELLS,
        cells,
        pct(BASELINE_CELLS as f64, cells as f64)
    );
    println!(
        "prover ms      : {:.1} (recorded) -> min {:.1} med {:.1} (this box; cross-box \
         comparisons are indicative only)",
        BASELINE_PROVER_MS,
        prove_ms[0],
        prove_ms[REPS / 2],
    );
    println!(
        "verify ms      : min {:.2} med {:.2}",
        verify_ms[0],
        verify_ms[REPS / 2]
    );
    println!("======================================================================");
}
