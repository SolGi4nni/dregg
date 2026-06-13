//! # THE EPOCH PAYOFF MEASUREMENT — does IR-v2 actually make the per-turn proof SMALLER?
//!
//! `docs/EPOCH-DESIGN.md` predicts that moving Poseidon2 out of row-width (the 4 hash-site aux
//! blocks = 1,408 of the 1,654 extended columns, 85%) into a chip-table lookup shrinks the
//! 451.7 KiB per-turn proof toward ~100-200 KiB. This test MEASURES that claim before the VK
//! bump rides on it: the SAME real transfer effect (the validated reference of
//! `effect_vm_ir2_validate.rs`) is proven through BOTH provers and the postcard-serialized
//! wire sizes are compared.
//!
//!   * **v1** — the LIVE path: `lean_descriptor_air::prove_vm_descriptor` over the graduated
//!     transfer descriptor (the single-table extended-row AIR; the wire `EffectVmP3Proof` the
//!     SDK cutover emits today — `docs/PROOF-ECONOMICS.md` §1's 451.7 KiB baseline).
//!   * **IR-v2** — `descriptor_ir2::prove_vm_descriptor2` over the graduated
//!     `transferVmDescriptor2` (the five-table EPOCH batch STARK: main + poseidon2-chip +
//!     range + memory + map-ops).
//!
//! Both proofs verify through their INDEPENDENT verifiers before being measured, so the sizes
//! compared are sizes of REAL proofs. The test asserts nothing about WHICH is smaller — it is
//! a measurement, and a negative result (multi-table overhead exceeding the inline-aux saving
//! at this trace size) is exactly what it exists to surface. The numbers land in
//! `docs/PROOF-ECONOMICS.md`.
//!
//! Gated on `recursion` (the feature that compiles `descriptor_ir2`). Run ONCE, release
//! (debug prove times would be lies):
//!   cargo test -p dregg-circuit --release --features recursion --test effect_vm_ir2_size_measure -- --nocapture

#![cfg(feature = "recursion")]

use std::time::Instant;

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    prove_vm_descriptor2_with_config, verify_vm_descriptor2, verify_vm_descriptor2_with_config,
};
use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace, sel};
use dregg_circuit::effect_vm_descriptors::{descriptor_for_selector, descriptor2_for_key};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{
    descriptor_recursion_matrix, parse_vm_descriptor, prove_vm_descriptor, verify_vm_descriptor,
};

fn kib(bytes: usize) -> f64 {
    bytes as f64 / 1024.0
}

/// Postcard component breakdown shared by both wire proofs (`BatchProof<DreggStarkConfig>`).
fn breakdown(
    label: &str,
    proof: &p3_batch_stark::BatchProof<dregg_circuit::plonky3_prover::DreggStarkConfig>,
) -> usize {
    let total = postcard::to_allocvec(proof).expect("postcard").len();
    let commitments = postcard::to_allocvec(&proof.commitments).unwrap().len();
    let opened = postcard::to_allocvec(&proof.opened_values).unwrap().len();
    let opening = postcard::to_allocvec(&proof.opening_proof).unwrap().len();
    let lookups = postcard::to_allocvec(&proof.global_lookup_data)
        .unwrap()
        .len();
    println!(
        "[{label}] total: {total} B ({:.1} KiB) | commitments: {commitments} B | \
         opened_values: {opened} B ({:.1} KiB) | opening_proof: {opening} B ({:.1} KiB) | \
         lookups: {lookups} B | degree_bits: {:?}",
        kib(total),
        kib(opened),
        kib(opening),
        proof.degree_bits,
    );
    total
}

/// THE MEASUREMENT: one real transfer, proven through the live v1 descriptor path AND the
/// EPOCH IR-v2 multi-table path; wire sizes + prove/verify times reported side by side.
#[test]
fn ir2_vs_v1_transfer_proof_size() {
    // The same real transfer witness both provers consume (the validated reference).
    let state = CellState::new(100_000, 0);
    let effects = vec![Effect::Transfer {
        amount: 50,
        direction: 1,
    }];
    let (base_trace, pis) = generate_effect_vm_trace(&state, &effects);
    assert_eq!(
        base_trace[0].len(),
        186,
        "canonical 186-col EffectVM layout"
    );

    // ---- v1: the LIVE single-table descriptor-interpreter path (the SDK cutover prover). ----
    let v1_json = descriptor_for_selector(sel::TRANSFER).expect("v1 transfer descriptor");
    let v1_desc = parse_vm_descriptor(v1_json).expect("v1 transfer descriptor parses");
    let v1_dpis: Vec<BabyBear> = pis[..v1_desc.public_input_count].to_vec();
    let extended_width = descriptor_recursion_matrix(&v1_desc, &base_trace)
        .expect("v1 extended matrix")
        .width;

    let t0 = Instant::now();
    let v1_proof =
        prove_vm_descriptor(&v1_desc, &base_trace, &v1_dpis).expect("v1 transfer proves");
    let v1_prove_ms = t0.elapsed().as_millis();
    let t1 = Instant::now();
    verify_vm_descriptor(&v1_desc, &v1_proof, &v1_dpis).expect("v1 transfer verifies");
    let v1_verify_ms = t1.elapsed().as_micros() as f64 / 1000.0;

    println!("== v1 (live single-table descriptor AIR; extended row = {extended_width} cols) ==");
    let v1_bytes = breakdown("v1", &v1_proof);
    println!("[v1] prove+selfverify: {v1_prove_ms} ms | verify: {v1_verify_ms:.1} ms");

    // ---- IR-v2: the EPOCH five-table batch STARK. ----
    let v2_json = descriptor2_for_key("transferVmDescriptor2").expect("v2 transfer descriptor");
    let v2_desc = parse_vm_descriptor2(v2_json).expect("v2 transfer descriptor parses");
    assert_eq!(
        v2_desc.trace_width, 186,
        "graduated transfer keeps the 186 base width"
    );
    assert_eq!(v2_desc.tables.len(), 5, "the five EPOCH tables");
    let v2_dpis: Vec<BabyBear> = pis[..v2_desc.public_input_count].to_vec();
    // Transfer declares no memory ops and no map ops → empty boundary + no witness heaps.
    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    let t2 = Instant::now();
    let v2_proof = prove_vm_descriptor2(&v2_desc, &base_trace, &v2_dpis, &mem_boundary, &map_heaps)
        .expect("IR-v2 transfer proves");
    let v2_prove_ms = t2.elapsed().as_millis();
    let t3 = Instant::now();
    verify_vm_descriptor2(&v2_desc, &v2_proof, &v2_dpis).expect("IR-v2 transfer verifies");
    let v2_verify_ms = t3.elapsed().as_micros() as f64 / 1000.0;

    println!("== IR-v2 (EPOCH multi-table batch STARK: main + chip + range + memory + map-ops) ==");
    let v2_bytes = breakdown("ir2", &v2_proof);
    println!("[ir2] prove+selfverify: {v2_prove_ms} ms | verify: {v2_verify_ms:.1} ms");

    // ---- The verdict line. ----
    let delta = v1_bytes as i64 - v2_bytes as i64;
    let ratio = v2_bytes as f64 / v1_bytes as f64;
    println!("== VERDICT (same real transfer, both proofs independently verified) ==");
    println!(
        "v1: {v1_bytes} B ({:.1} KiB) | IR-v2: {v2_bytes} B ({:.1} KiB) | delta: {delta} B \
         ({:.1} KiB) | IR-v2/v1 ratio: {ratio:.3} ({:+.1}%)",
        kib(v1_bytes),
        kib(v2_bytes),
        kib(delta.unsigned_abs() as usize) * delta.signum() as f64,
        (ratio - 1.0) * 100.0,
    );
    println!(
        "prove: v1 {v1_prove_ms} ms vs IR-v2 {v2_prove_ms} ms | verify: v1 {v1_verify_ms:.1} ms \
         vs IR-v2 {v2_verify_ms:.1} ms"
    );
}

/// THE UNIVERSAL-MEMORY SIZE PROBE: one state write + read-back expressed BOTH ways —
/// as boundary map ops (sorted-Poseidon2 openings riding the chip bus) and as universal
/// memory ops (the ONE Blum multiset, `docs/UNIVERSAL-MEMORY.md`) — plus the `absent`
/// non-membership shape, all proven through the production `ir2_config` and measured.
/// The umem proof commits NO chip table (zero intra-proof hashing); the map/absent proofs
/// pay the chip. Numbers, not vibes: this is the intra-proof half of the universal-memory
/// economics (boundary reconciliation stays map-op-shaped, once per touched key per proof).
#[test]
fn ir2_umem_vs_map_size_probe() {
    use dregg_circuit::descriptor_ir2::{
        EffectVmDescriptor2, MapKind, MapOpSpec, MemKind, NULLIFIER_DOMAIN, UMemBoundaryWitness,
        UMemOpSpec, VmConstraint2, prove_vm_descriptor2_umem,
    };
    use dregg_circuit::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf};
    use dregg_circuit::lean_descriptor_air::LeanExpr;

    let heap = vec![
        HeapLeaf {
            addr: BabyBear::new(100),
            value: BabyBear::new(77),
        },
        HeapLeaf {
            addr: BabyBear::new(200),
            value: BabyBear::new(88),
        },
    ];
    let tree = CanonicalHeapTree::new(heap.clone(), HEAP_TREE_DEPTH);
    let root = tree.root();

    // ---- (a) the map-write shape: one in-place sorted write. ----
    let w = tree
        .update_witness(HeapLeaf {
            addr: BabyBear::new(100),
            value: BabyBear::new(99),
        })
        .expect("key present");
    let map_desc = EffectVmDescriptor2 {
        name: "probe-map-write".to_string(),
        trace_width: 6,
        public_input_count: 0,
        tables: vec![],
        constraints: vec![VmConstraint2::MapOp(MapOpSpec {
            guard: LeanExpr::Var(5),
            root: LeanExpr::Var(0),
            key: LeanExpr::Var(1),
            value: LeanExpr::Var(2),
            new_root: LeanExpr::Var(3),
            op: MapKind::Write,
        })],
        hash_sites: vec![],
        ranges: vec![],
    };
    let mut map_rows = vec![
        vec![
            root,
            BabyBear::new(100),
            BabyBear::new(99),
            w.new_root,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        4
    ];
    map_rows[0][5] = BabyBear::ONE;
    let t0 = Instant::now();
    let map_proof = prove_vm_descriptor2(
        &map_desc,
        &map_rows,
        &[],
        &MemBoundaryWitness::default(),
        &[heap.clone()],
    )
    .expect("map write proves");
    let map_ms = t0.elapsed().as_millis();
    verify_vm_descriptor2(&map_desc, &map_proof, &[]).expect("map write verifies");
    let map_bytes = breakdown("map-write", &map_proof);

    // ---- (b) the SAME state intent as universal memory ops: write + read-back. ----
    let umem_desc = EffectVmDescriptor2 {
        name: "probe-umem-write".to_string(),
        trace_width: 4,
        public_input_count: 0,
        tables: vec![],
        constraints: vec![
            VmConstraint2::UMemOp(UMemOpSpec {
                guard: LeanExpr::Var(3),
                domain: 1, // heap
                key: LeanExpr::Var(0),
                present: LeanExpr::Const(1),
                value: LeanExpr::Var(1),
                prev_present: LeanExpr::Const(1),
                prev_value: LeanExpr::Const(77),
                prev_serial: LeanExpr::Const(0),
                kind: MemKind::Write,
            }),
            VmConstraint2::UMemOp(UMemOpSpec {
                guard: LeanExpr::Var(3),
                domain: 1,
                key: LeanExpr::Var(0),
                present: LeanExpr::Const(1),
                value: LeanExpr::Var(1),
                prev_present: LeanExpr::Const(1),
                prev_value: LeanExpr::Var(1),
                prev_serial: LeanExpr::Const(1),
                kind: MemKind::Read,
            }),
        ],
        hash_sites: vec![],
        ranges: vec![],
    };
    let mut um_rows = vec![
        vec![
            BabyBear::new(100),
            BabyBear::new(99),
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        4
    ];
    um_rows[0][3] = BabyBear::ONE;
    let boundary = UMemBoundaryWitness {
        addrs: vec![(1, BabyBear::new(100))],
        init_vals: vec![Some(BabyBear::new(77))],
    };
    let t1 = Instant::now();
    let um_proof = prove_vm_descriptor2_umem(
        &umem_desc,
        &um_rows,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &boundary,
    )
    .expect("umem write+read proves");
    let um_ms = t1.elapsed().as_millis();
    verify_vm_descriptor2(&umem_desc, &um_proof, &[]).expect("umem proof verifies");
    let um_bytes = breakdown("umem-write+read", &um_proof);

    // ---- (c) the `absent` non-membership shape (the boundary gap leg). ----
    let absent_desc = EffectVmDescriptor2 {
        name: "probe-absent".to_string(),
        trace_width: 4,
        public_input_count: 0,
        tables: vec![],
        constraints: vec![VmConstraint2::MapOp(MapOpSpec {
            guard: LeanExpr::Var(3),
            root: LeanExpr::Var(0),
            key: LeanExpr::Var(1),
            value: LeanExpr::Const(0),
            new_root: LeanExpr::Var(2),
            op: MapKind::Absent,
        })],
        hash_sites: vec![],
        ranges: vec![],
    };
    let mut ab_rows = vec![vec![root, BabyBear::new(150), root, BabyBear::ZERO]; 4];
    ab_rows[0][3] = BabyBear::ONE;
    let t2 = Instant::now();
    let ab_proof = prove_vm_descriptor2(
        &absent_desc,
        &ab_rows,
        &[],
        &MemBoundaryWitness::default(),
        &[heap],
    )
    .expect("absent proves");
    let ab_ms = t2.elapsed().as_millis();
    verify_vm_descriptor2(&absent_desc, &ab_proof, &[]).expect("absent verifies");
    let ab_bytes = breakdown("absent", &ab_proof);

    println!("== UNIVERSAL-MEMORY PROBE VERDICT (production ir2_config, all verified) ==");
    println!(
        "map-write: {map_bytes} B ({:.1} KiB, {map_ms} ms) | umem write+read: {um_bytes} B \
         ({:.1} KiB, {um_ms} ms) | absent: {ab_bytes} B ({:.1} KiB, {ab_ms} ms) | NULLIFIER_DOMAIN={NULLIFIER_DOMAIN}",
        kib(map_bytes),
        kib(um_bytes),
        kib(ab_bytes),
    );
    assert!(
        um_proof.degree_bits.len() == 4,
        "umem probe must commit main + byte + umemory + umem-boundary (NO chip)"
    );
}

/// THE FRI GRID: the same real transfer proven through the IR-v2 batch at every
/// security-parity `(log_blowup, num_queries)` point the degree-7 chip admits
/// (`q × lb + 16 PoW ≥ 130 bits` conjectured throughout — v1-`create_config` parity
/// on both the conjectured AND proven ledgers). This is the measurement `ir2_config`'s
/// `(6, 19)` pin stands on; re-run it before moving the pin. Queries dominate IR-v2
/// proof size (tables are 2³–2⁸ rows, so high-blowup LDE costs the prover only
/// milliseconds): size falls monotonically with blowup, prove time roughly doubles
/// per step. Points below lb=3 are unprovable with the inline x⁷ S-box (quotient
/// needs 8 chunks); they were measured with a degree-3 registered-S-box chip variant
/// and LOST at parity anyway (+89/+356 KiB at lb=2/lb=1) — docs/PROOF-ECONOMICS.md §2c.
#[test]
fn ir2_fri_grid() {
    use dregg_circuit::plonky3_prover::create_config_with_fri;

    let state = CellState::new(100_000, 0);
    let effects = vec![Effect::Transfer {
        amount: 50,
        direction: 1,
    }];
    let (base_trace, pis) = generate_effect_vm_trace(&state, &effects);
    let v2_json = descriptor2_for_key("transferVmDescriptor2").expect("v2 transfer descriptor");
    let v2_desc = parse_vm_descriptor2(v2_json).expect("v2 transfer descriptor parses");
    let v2_dpis: Vec<BabyBear> = pis[..v2_desc.public_input_count].to_vec();
    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    for (lb, q) in [
        (3usize, 38usize),
        (4, 29),
        (5, 23),
        (6, 19),
        (7, 17),
        (8, 15),
    ] {
        let config = create_config_with_fri(lb, 0, 3, q, 16);
        let t0 = Instant::now();
        let proof = prove_vm_descriptor2_with_config(
            &v2_desc,
            &base_trace,
            &v2_dpis,
            &mem_boundary,
            &map_heaps,
            &config,
        )
        .expect("IR-v2 transfer proves at this grid point");
        let prove_ms = t0.elapsed().as_millis();
        let t1 = Instant::now();
        verify_vm_descriptor2_with_config(&v2_desc, &proof, &v2_dpis, &config)
            .expect("IR-v2 transfer verifies at this grid point");
        let verify_ms = t1.elapsed().as_micros() as f64 / 1000.0;
        let label = format!("lb={lb} q={q}");
        let bytes = breakdown(&label, &proof);
        println!(
            "[{label}] {bytes} B ({:.1} KiB) | prove+selfverify: {prove_ms} ms | \
             verify: {verify_ms:.1} ms | conj bits: {}",
            kib(bytes),
            lb * q + 16,
        );
    }
}
