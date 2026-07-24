//! # HEAP-WRITE producer≡descriptor ROUNDTRIP + AFTER-root 8-felt binding forge.
//!
//! ## The gap under attack (R3, v13-class)
//!
//! `heapWriteVmDescriptor2R24` is the write-bearing Class-A member. Unlike the effect-dispatched
//! cohort it has NO live selector — it is reached only through the dedicated per-family producer
//! [`generate_rotated_heap_write_wide`]. R3 flagged it as the sharpest surviving v13-class gap: a
//! DISTINCT heap-splice producer, structurally pinned only, with no end-to-end prove+verify roundtrip
//! that would catch the producer silently diverging from the committed descriptor while the drift gate
//! stays green (the v13 stale-descriptor scare class).
//!
//! The staleness risk is REAL and visible: the source carries drifted geometry comments whose ACTUAL
//! runtime values moved under them, and a sibling structural test
//! (`heap_write_deployed_root_forced.rs`) hard-codes a STALE `new_root` lane-0 column that no longer
//! matches the committed descriptor. So the only trustworthy check is an EXECUTED roundtrip that
//! binds the producer's laid columns to the committed descriptor's map-op columns through an actual
//! proof — and every geometry here is DERIVED (host + carriers − S2 − E1; columns pushed through the
//! deployed compaction) rather than transcribed, so the next flag-day moves the pins with the bytes.
//!
//! ## What this file pins
//!
//!  (a) ROUNDTRIP — the wide producer's trace PROVES + light-client VERIFIES against the COMMITTED
//!      bare-wide `heapWriteVmDescriptor2R24`, AND the producer's written after-root columns are
//!      byte-identical to the descriptor's `.write` map-op `new_root` columns — asserted as the S2+E1
//!      IMAGE of `AFTER_BASE + HEAP_ROOT_GROUP`, so the BANDS are pinned and not merely the count
//!      (the anti-drift catcher). Also pins that the UNCOMPACTED v3-live committed descriptor carries
//!      those columns at their raw coordinates and the truncated producer trace proves against it —
//!      closing R3's "partial on both paths".
//!  (b) AFTER-ROOT 8-FELT FORGE — forge the `.write` `new_root` completion lanes 1..7 to garbage
//!      while keeping lane 0 honest, recompute the after block-commit + wide carriers so the trace is
//!      fully self-consistent, and run the pure LC verify. If UNSAT, the deployed `.write` map-op
//!      binds ALL EIGHT after-root felts to the genuine sorted-Merkle splice (~124-bit), not lane-0
//!      (~31-bit).

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MapKind, MemBoundaryWitness, VmConstraint2, chip_absorb_all_lanes,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::layout_generated::HEAP_ROOT_GROUP;
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_STATE_COMMIT, BEFORE_BASE, HEAP_WRITE_HOST_WIDTH, HEAP_WRITE_READ_BASE,
    RotatedBlockWitness, WIDE_CARRIER_APPENDIX, append_wide_carriers, compact_e1_columns,
    compact_s2_columns, empty_caveat_manifest, generate_rotated_heap_write_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::{V3_STAGED_REGISTRY_TSV, WIDE_REGISTRY_STAGED_TSV};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal::{Outcome, classify};
use dregg_turn::rotation_witness as rw;

const KEY: &str = "heapWriteVmDescriptor2R24";

fn registry_json(tsv: &'static str, name: &str) -> &'static str {
    tsv.lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in registry"))
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

/// Total columns this member's OWN E1 kill-set (the Epoch-1 SECOND flag-day) deletes, summed from
/// the Lean-emitted single source `E1_COMPACT_TABLE` — exactly what `compact_e1_columns` drains.
fn e1_deleted_cols(key: &str) -> usize {
    dregg_circuit::effect_vm::e1_compact_generated::E1_COMPACT_TABLE
        .iter()
        .find(|(k, _)| *k == key)
        .map(|(_, runs)| runs.iter().map(|(a, b)| b - a).sum())
        .unwrap_or_else(|| panic!("{key} not in E1_COMPACT_TABLE"))
}

/// The RAW (pre-compaction) wide row width the producer assembles before it compacts: the OPTION-I
/// after-spine host + the wide-carrier appendix.
fn raw_wide_width() -> usize {
    HEAP_WRITE_HOST_WIDTH + WIDE_CARRIER_APPENDIX
}

/// **THE COMMITTED BARE-WIDE WIDTH, DERIVED** — the raw wide row MINUS the S2 stratum (Epoch 1: the
/// two rotated 1-felt chain carrier bands + their 840 graduated chip-lane columns) MINUS this
/// member's own E1 kill-set. Both deletions come from the Lean-emitted tables the producer itself
/// drains, so this pin follows the next compaction instead of rotting into a dead gate.
fn committed_wide_width() -> usize {
    raw_wide_width()
        - dregg_circuit::effect_vm::s2_compact_generated::S2_DELETED_COLS
        - e1_deleted_cols(KEY)
}

/// The RAW (pre-compaction) columns of the AFTER rotated block's heap-root 8-felt group — lane 0 the
/// scalar heap-root limb, lanes 1..7 the completion limbs — read from the Lean-emitted layout row
/// `HEAP_ROOT_GROUP` rather than transcribed. These are the columns the producer writes the faithful
/// 8-felt splice root into, and the columns the `.write` map-op's `new_root` binds.
fn raw_after_heap_root_cols() -> Vec<usize> {
    HEAP_ROOT_GROUP
        .iter()
        .map(|&off| AFTER_BASE + off)
        .collect()
}

/// **THE COMPACTION IMAGE of raw producer columns — the BAND pin.** Where each pre-compaction column
/// lands in the S2+E1-compacted member, computed by running the DEPLOYED compaction
/// (`compact_s2_columns` then `compact_e1_columns` — the very calls the wide producer makes) over a
/// row of column IDENTITIES. A column COUNT is not enough: a table regen that deletes a DIFFERENT
/// band of the SAME size renumbers these columns, and the honest proof would go UNSAT with no
/// explanation. Deriving the image makes that regen fail HERE, naming the moved column.
fn compacted_cols(key: &str, raw_width: usize, raw_cols: &[usize]) -> Vec<usize> {
    let mut identity: Vec<Vec<BabyBear>> =
        vec![(0..raw_width).map(|c| BabyBear::new(c as u32)).collect()];
    compact_s2_columns(&mut identity, key).expect("S2 compaction of the identity row");
    compact_e1_columns(&mut identity, key).expect("E1 compaction of the identity row");
    raw_cols
        .iter()
        .map(|&raw| {
            identity[0]
                .iter()
                .position(|&v| v == BabyBear::new(raw as u32))
                .unwrap_or_else(|| {
                    panic!(
                        "raw column {raw} was DELETED by the {key} kill-set — it cannot be a \
                            surviving binding column"
                    )
                })
        })
        .collect()
}

/// The `.write` map-op's `new_root` 8-felt group COLUMNS, straight off the parsed descriptor.
fn write_new_root_cols(desc: &EffectVmDescriptor2) -> Vec<usize> {
    for c in &desc.constraints {
        if let VmConstraint2::MapOp(m) = c {
            if m.op == MapKind::Write {
                return m
                    .new_root
                    .iter()
                    .map(|e| match e {
                        LeanExpr::Var(i) => *i,
                        other => panic!("new_root lane is not a Var column: {other:?}"),
                    })
                    .collect();
            }
        }
    }
    panic!("descriptor {} has no WRITE map-op", desc.name);
}

/// `true` iff prove/verify REFUSES (Err or panic) on the given trace + PIs — the LC verdict.
fn refused(
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<HeapLeaf>],
) -> bool {
    match classify("refused", || {
        let proof = prove_vm_descriptor2(desc, trace, dpis, mem_boundary, map_heaps)?;
        verify_vm_descriptor2(desc, &proof, dpis)
    }) {
        // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
        // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
        // debug_assert), which used to land here and read as "rejected".
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

/// Build the honest wide heap-write turn (the exact fixture `wide_new_members_cover` uses), returning
/// the producer's `(trace, dpis, map_heaps)` and the recomputed heap-address the splice opens.
fn honest_heap_write() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, Vec<Vec<HeapLeaf>>) {
    let st = CellState::new(100, 5);
    let value_full: u64 = 30;
    let effects = vec![Effect::Mint {
        value_lo: BabyBear::new(value_full as u32),
        mint_hash: BabyBear::new(0),
        value_full,
    }];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(100, 5);
    let after_cell = producer_cell(100 + value_full as i64, 6);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[11u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );

    let coll = BabyBear::new(42);
    let key = BabyBear::new(7);
    let value = BabyBear::new(123);
    let mut absorb_in = [BabyBear::new(0); 11];
    absorb_in[0] = coll;
    absorb_in[1] = key;
    let addr = chip_absorb_all_lanes(2, &absorb_in)[0];
    let heap = vec![
        HeapLeaf::entry(addr, BabyBear::new(9)),
        HeapLeaf::entry(BabyBear::new(999_983), BabyBear::new(1)),
    ];

    let (trace, dpis, map_heaps) = generate_rotated_heap_write_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
        coll,
        key,
        value,
        &heap,
    )
    .expect("wide heap-write generation");
    (trace, dpis, map_heaps)
}

/// **(a) ROUNDTRIP + ANTI-DRIFT.** The wide producer PROVES + light-client VERIFIES against the
/// COMMITTED `heapWriteVmDescriptor2R24`, and the columns the producer laid the after heap-root group
/// into are byte-identical to the committed descriptor's `.write` map-op `new_root` columns. This is
/// the executed check the structural teeth cannot give: a producer that laid the group at the STALE
/// (188/237-based) columns while the committed descriptor moved to 188/415 would be UNSAT here.
#[test]
fn roundtrip_wide_producer_matches_committed_descriptor() {
    let wide_desc = parse_vm_descriptor2(registry_json(WIDE_REGISTRY_STAGED_TSV, KEY))
        .expect("committed bare-wide heapWriteVmDescriptor2R24 parses");
    assert_eq!(
        wide_desc.trace_width,
        committed_wide_width(),
        "committed bare-wide width"
    );
    assert_eq!(wide_desc.public_input_count, 20, "committed bare-wide PIs");

    let new_root_cols = write_new_root_cols(&wide_desc);
    assert_eq!(new_root_cols.len(), 8, "after-root is an 8-felt group");
    // THE ANTI-DRIFT PIN, DERIVED THROUGH THE BANDS. The producer writes the after heap-root group
    // at the RAW columns `AFTER_BASE + HEAP_ROOT_GROUP[lane]`, then compacts; the committed
    // descriptor's `new_root` must be exactly the image of those raw columns under the DEPLOYED S2
    // + E1 kill-sets. This binds the producer and the frozen descriptor to the same felts through
    // the same bands — a compaction that drops different bands of the same size REDs here rather
    // than leaving the honest proof mysteriously UNSAT.
    assert_eq!(
        new_root_cols,
        compacted_cols(KEY, raw_wide_width(), &raw_after_heap_root_cols()),
        "committed .write new_root columns == the S2+E1 image of AFTER_BASE + HEAP_ROOT_GROUP — the \
         anti-drift pin"
    );

    let (trace, dpis, map_heaps) = honest_heap_write();
    assert_eq!(
        trace[0].len(),
        wide_desc.trace_width,
        "producer width == descriptor width"
    );
    assert_eq!(
        dpis.len(),
        wide_desc.public_input_count,
        "producer PI count == descriptor PI count"
    );

    // Non-vacuity: the producer actually laid the genuine 8-felt splice root into those columns, with
    // ≥1 nonzero completion lane (so the forge below moves a genuinely bound felt).
    let honest_root: Vec<BabyBear> = new_root_cols.iter().map(|&c| trace[0][c]).collect();
    assert!(
        (1..8).any(|l| honest_root[l] != BabyBear::ZERO),
        "the genuine 8-felt after-root has ≥1 nonzero completion lane"
    );

    let mb = MemBoundaryWitness::default();
    let proof = prove_vm_descriptor2(&wide_desc, &trace, &dpis, &mb, &map_heaps)
        .expect("ROUNDTRIP: wide heap-write producer must PROVE against the committed descriptor");
    verify_vm_descriptor2(&wide_desc, &proof, &dpis)
        .expect("ROUNDTRIP: light client must VERIFY the wide heap-write proof");
    eprintln!(
        "HEAP-WRITE ROUNDTRIP (bare-wide {}/{}): producer≡descriptor — PROVED + VERIFIED, after-root \
         group laid at the committed new_root columns {new_root_cols:?}. Coverage gap CLOSED, benign.",
        wide_desc.trace_width, wide_desc.public_input_count
    );
}

/// **(a′) v3-live path.** The committed v3-live `heapWriteVmDescriptor2R24` carries the `.write`
/// map-op at the RAW (pre-compaction) rotated coordinates — `root` at `BEFORE_BASE +
/// HEAP_ROOT_GROUP`, `new_root` at `AFTER_BASE + HEAP_ROOT_GROUP` — because the narrow V3 registry
/// never took the S2 / E1 flag-days: its width is still the raw graduated Class-A heap base
/// ([`HEAP_WRITE_READ_BASE`]), where the WIDE twin is that base + read appendix + after spine + wide
/// carriers MINUS both kill-sets. Truncating the wide producer's trace to the v3-live width and
/// proving against the committed v3-live descriptor with the honest heap witness closes R3's
/// "partial on v3-live" leg. Reports PASS or a genuine shape MISMATCH.
#[test]
fn roundtrip_v3_live_descriptor() {
    let v3 = parse_vm_descriptor2(registry_json(V3_STAGED_REGISTRY_TSV, KEY))
        .expect("committed v3-live heapWriteVmDescriptor2R24 parses");
    // The narrow V3 member is UNCOMPACTED — the raw graduated Class-A heap base, 14 columns
    // narrower than the rotated cohort base. Derived, so a graduation change moves it here.
    assert_eq!(
        v3.trace_width, HEAP_WRITE_READ_BASE,
        "committed v3-live width"
    );
    assert_eq!(v3.public_input_count, 4, "committed v3-live PIs");
    assert_eq!(
        write_new_root_cols(&v3),
        raw_after_heap_root_cols(),
        "the uncompacted v3-live .write new_root columns are the RAW AFTER heap-root group"
    );

    let (wide_trace, wide_dpis, map_heaps) = honest_heap_write();
    // Truncate the wide producer trace to the v3-live width; use the first 4 (base) PIs.
    let trace: Vec<Vec<BabyBear>> = wide_trace
        .iter()
        .map(|r| r[..v3.trace_width].to_vec())
        .collect();
    let dpis: Vec<BabyBear> = wide_dpis[..v3.public_input_count].to_vec();
    assert_eq!(trace[0].len(), HEAP_WRITE_READ_BASE);
    assert_eq!(dpis.len(), 4);

    let mb = MemBoundaryWitness::default();
    let refused_v3 = refused(&v3, &trace, &dpis, &mb, &map_heaps);
    if refused_v3 {
        eprintln!(
            "HEAP-WRITE v3-live ({}/{}): the truncated producer trace does NOT prove against the \
             committed v3-live descriptor — a producer≡descriptor SHAPE MISMATCH on the v3-live leg.",
            v3.trace_width, v3.public_input_count
        );
    } else {
        eprintln!(
            "HEAP-WRITE v3-live ({}/{}): truncated producer trace PROVED + VERIFIED against the \
             committed v3-live descriptor. v3-live coverage CLOSED (shares the wide 8-felt splice).",
            v3.trace_width, v3.public_input_count
        );
    }
    assert!(
        !refused_v3,
        "MISMATCH: the wide producer's HEAP_WRITE_READ_BASE-col prefix must satisfy the committed v3-live descriptor \
         (they share the .write map-op) — a refusal is a live v3-live producer≡descriptor divergence"
    );
}

const FORGED_LANES: [u32; 7] = [0xDEAD, 0xBEEF, 0x1234, 0x5678, 0x9ABC, 0xCAFE, 0xF00D];

/// **(b-ADV) THE ADVERSARIAL R1-TRAP CHECK — the after-root forge run against the DEPLOYED registry.**
///
/// The finder's forge `after_root_completion_lane_forge_is_unsat` runs against `WIDE_REGISTRY_STAGED_TSV`,
/// which its own doc (`effect_vm_descriptors.rs:1204`) calls "the parallel wide path BESIDE" the live
/// registry, "the live 1-felt `V3_STAGED_REGISTRY_TSV` / FP / VK are UNTOUCHED." The light client the
/// wire runs verifies against the DEPLOYED registry — `V3_STAGED_REGISTRY_TSV` (`:821`, "the live
/// 1-felt" registry). If the deployed member bound only after-root lane 0 while WIDE bound all 8, the
/// finder's UNSAT would be an R1-trap (proving 8-felt binding on an undeployed descriptor). This test
/// re-runs the identical forge against the DEPLOYED v3-live descriptor. UNSAT here ⟹ the
/// DEPLOYED heapWrite `.write` map-op binds all 8 after-root felts — the finder's refutation holds on
/// the real light-client path, not just the staged wide twin.
#[test]
#[allow(non_snake_case)]
fn after_root_forge_is_unsat_against_DEPLOYED_v3_registry() {
    let v3 = parse_vm_descriptor2(registry_json(V3_STAGED_REGISTRY_TSV, KEY))
        .expect("committed DEPLOYED v3-live heapWriteVmDescriptor2R24 parses");
    assert_eq!(
        v3.trace_width, HEAP_WRITE_READ_BASE,
        "deployed v3-live width"
    );
    assert_eq!(v3.public_input_count, 4, "deployed v3-live PIs");
    let new_root_cols = write_new_root_cols(&v3);
    assert_eq!(
        new_root_cols,
        raw_after_heap_root_cols(),
        "deployed v3-live .write new_root columns — the RAW AFTER heap-root group, all 8 lanes \
         within the width"
    );

    let (trace, dpis, map_heaps) = honest_heap_write();
    let mb = MemBoundaryWitness::default();

    // NO DOWNGRADE: the honest truncated producer proves + verifies against the deployed descriptor.
    let htrace: Vec<Vec<BabyBear>> = trace.iter().map(|r| r[..v3.trace_width].to_vec()).collect();
    let hdpis: Vec<BabyBear> = dpis[..4].to_vec();
    assert!(
        !refused(&v3, &htrace, &hdpis, &mb, &map_heaps),
        "NO DOWNGRADE: honest heap-write must prove+verify against the deployed v3 descriptor"
    );

    let honest_root: Vec<BabyBear> = new_root_cols.iter().map(|&c| trace[0][c]).collect();

    // THE FORGE (identical to the finder's, but bound for the DEPLOYED descriptor): garble after-root
    // completion lanes 1..7 on every row, keep lane 0 honest, recompute the after block-commit so only
    // the deployed .write map-op grow-gate can bite, then truncate to the deployed v3-live width + build
    // the deployed 4-PI vector (pi0 = before state-commit, pi1 = recomputed after state-commit).
    let mut ftrace = trace.clone();
    for row in ftrace.iter_mut() {
        for lane in 1..8 {
            row[new_root_cols[lane]] = BabyBear::new(FORGED_LANES[lane - 1]);
        }
    }
    assert!(
        (1..8).any(|l| ftrace[0][new_root_cols[l]] != honest_root[l]),
        "the forged high lanes differ from the genuine splice root"
    );
    dregg_circuit::effect_vm::trace_rotated::recompute_after_blocks_for_test(&mut ftrace);
    let last = ftrace.len() - 1;
    let before_sc = ftrace[0][BEFORE_BASE + B_STATE_COMMIT];
    let after_sc = ftrace[last][AFTER_BASE + B_STATE_COMMIT];
    let ftrace_v3: Vec<Vec<BabyBear>> = ftrace
        .iter()
        .map(|r| r[..v3.trace_width].to_vec())
        .collect();
    let mut fdpis = dpis[..4].to_vec();
    fdpis[0] = before_sc;
    fdpis[1] = after_sc;

    let unsat = refused(&v3, &ftrace_v3, &fdpis, &mb, &map_heaps);
    if unsat {
        eprintln!(
            "HEAP-WRITE DEPLOYED-REGISTRY VERDICT: the after-root completion-lane forge is UNSAT against \
             the DEPLOYED v3-live descriptor — the light client the wire runs binds ALL EIGHT \
             after-root felts. NOT an R1-trap; the finder's refutation holds on the deployed path."
        );
    } else {
        eprintln!(
            "HEAP-WRITE DEPLOYED-REGISTRY VERDICT: the forge PROVES+VERIFIES against the DEPLOYED v3-live \
             descriptor — the light client binds only after-root lane 0 (~31-bit). The finder's UNSAT \
             was an R1-TRAP (staged-wide only). LIVE 8-felt gap on the deployed heapWrite path."
        );
    }
    assert!(
        unsat,
        "R1-TRAP: the after-root forge proves+verifies against the DEPLOYED v3 registry member — the \
         deployed light-client heapWrite binds only lane-0, not the 8-felt splice. The finder tested \
         the undeployed WIDE twin."
    );
}

/// **(b) AFTER-ROOT 8-FELT BINDING FORGE.** Forge the `.write` `new_root` completion lanes 1..7 to
/// garbage on every row while keeping lane 0 honest, recompute the after block-commit chain + wide
/// carriers so the ONLY thing that can bite is the map-op grow-gate on the completion lanes, then run
/// the pure LC verify. UNSAT ⟹ the deployed `.write` map-op binds all 8 after-root felts to the
/// genuine sorted-Merkle splice (~124-bit), not lane-0.
#[test]
fn after_root_completion_lane_forge_is_unsat() {
    let wide_desc = parse_vm_descriptor2(registry_json(WIDE_REGISTRY_STAGED_TSV, KEY)).unwrap();
    let new_root_cols = write_new_root_cols(&wide_desc);

    let (trace, dpis, map_heaps) = honest_heap_write();
    let mb = MemBoundaryWitness::default();

    // POSITIVE (no downgrade): the honest turn proves + verifies.
    let honest_proof = prove_vm_descriptor2(&wide_desc, &trace, &dpis, &mb, &map_heaps)
        .expect("NO DOWNGRADE: honest wide heap-write proves");
    verify_vm_descriptor2(&wide_desc, &honest_proof, &dpis)
        .expect("NO DOWNGRADE: honest wide heap-write verifies");

    // Non-vacuity: ≥1 forged completion lane genuinely differs from the honest after-root felt.
    let honest_root: Vec<BabyBear> = new_root_cols.iter().map(|&c| trace[0][c]).collect();

    // THE FORGE: garble lanes 1..7 on every row; keep lane 0 honest. These completion lanes are the
    // after rotated block's heap-root completion limbs (58..64), so they feed the after STATE_COMMIT —
    // recompute the after block-commit + re-derive the wide carriers/PIs so the trace is fully
    // self-consistent and the map-op grow-gate is the sole possible binder.
    let mut ftrace = trace.clone();
    for row in ftrace.iter_mut() {
        for lane in 1..8 {
            row[new_root_cols[lane]] = BabyBear::new(FORGED_LANES[lane - 1]);
        }
    }
    assert_eq!(
        ftrace[0][new_root_cols[0]], trace[0][new_root_cols[0]],
        "lane 0 (the scalar heap-root limb) stays honest — only the high seven lanes are forged"
    );
    assert!(
        (1..8).any(|l| ftrace[0][new_root_cols[l]] != honest_root[l]),
        "the forged high lanes differ from the genuine splice root (the grow-gate's UNSAT precondition)"
    );

    dregg_circuit::effect_vm::trace_rotated::recompute_after_blocks_for_test(&mut ftrace);
    // Rebuild the base 4 PIs (pi1 = the recomputed after state-commit on the last row) + wide carriers.
    let last = ftrace.len() - 1;
    let mut base4 = dpis[..4].to_vec();
    base4[0] = ftrace[0][BEFORE_BASE + B_STATE_COMMIT];
    base4[1] = ftrace[last][AFTER_BASE + B_STATE_COMMIT];
    let fdpis = append_wide_carriers(&mut ftrace, base4, HEAP_WRITE_HOST_WIDTH);
    assert_eq!(fdpis.len(), 20);

    let unsat = refused(&wide_desc, &ftrace, &fdpis, &mb, &map_heaps);
    if unsat {
        eprintln!(
            "HEAP-WRITE AFTER-ROOT VERDICT: the completion-lane forge is UNSAT — the deployed .write \
             map-op binds ALL EIGHT after-root felts to the genuine sorted-Merkle splice (~124-bit). \
             The 8-felt AFTER-root binding is faithfully enforced, not lane-0."
        );
    } else {
        eprintln!(
            "HEAP-WRITE AFTER-ROOT VERDICT: the completion-lane forge PROVES+VERIFIES — the deployed \
             descriptor binds only after-root lane 0 (~31-bit). A LIVE 8-felt gap."
        );
    }
    assert!(
        unsat,
        "AFTER-ROOT FORGE: a heap-write forged to differ ONLY in the after-root's high seven \
         completion lanes proves+verifies through the deployed descriptor — the 8-felt AFTER-root is \
         NOT bound (lane-0 only). This is a live light-client soundness gap."
    );
}
