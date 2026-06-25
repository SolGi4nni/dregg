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

// (formerly `#![cfg(feature = "prover")]` — that dregg-circuit feature is GONE; the
// descriptor-level prove/verify (`prove_vm_descriptor2`/`verify_vm_descriptor2`) is
// now unconditional in dregg-circuit, so this test compiles + runs by default.)

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
        188,
        "canonical 188-col EffectVM layout (186 + record-digest + asset-class)"
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
        v2_desc.trace_width, 216,
        "graduated transfer = 188 base + 7·4 chip lane cols (Phase B-GATE: 4 hash sites)"
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

/// THE INTERIOR-MEMORY CONVERSION PROTOTYPE: take the REAL deployed `setFieldDynVmDescriptor2`
/// (`circuit/descriptors/dregg-effectvm-set-field-dyn-ir2.json`) — the ONE deployed per-effect
/// descriptor whose interior state access is a flat `mem_op` pair (a `write` then a `read`-back
/// of the same field slot, w=188, ZERO chip lookups) — extract its exact `MemOp` specs, and
/// prove the SAME interior access pattern BOTH ways:
///   * **flat-MemOp** — the deployed shape: pulls in `{main, byte, memory, boundary}` (4
///     committed instances; the flat memory table's gap-decomposition + the boundary table).
///   * **umem** — the conversion: each `mem_op` becomes a `umem_op` on the Heap domain; pulls in
///     `{main, byte, umemory, umem_boundary}` (4 instances, NO chip), the ONE Blum multiset.
///
/// Both are proven through the production `ir2_config` and INDEPENDENTLY verified, so the KiB
/// numbers are real. The umem teeth still bite: the read-back's `prev_value`/`prev_serial` are
/// replayed against the boundary image (a forged prior is UNSAT — `umemTableFaithful`), and the
/// boundary witness declares the `(domain, key)` touched (a `read` returning a value not in the
/// declared image is rejected). This measures whether the umem table set is cheaper than the
/// flat-memory table set for the SAME real deployed access pattern.
#[test]
fn ir2_setfielddyn_mem_to_umem_conversion() {
    use dregg_circuit::descriptor_ir2::{
        EffectVmDescriptor2, MemBoundaryWitness as MBW, MemKind, UMemBoundaryWitness, UMemOpSpec,
        VmConstraint2, prove_vm_descriptor2_umem,
    };
    use dregg_circuit::effect_vm_descriptors::descriptor2_for_key;
    use dregg_circuit::lean_descriptor_air::LeanExpr;

    // ---- Pull the REAL deployed descriptor and lift out its flat MemOp specs. ----
    let json = descriptor2_for_key("setFieldDynVmDescriptor2").expect("set-field-dyn descriptor");
    let deployed = parse_vm_descriptor2(json).expect("set-field-dyn parses");
    let mem_specs: Vec<_> = deployed
        .constraints
        .iter()
        .filter_map(|k| match k {
            VmConstraint2::MemOp(m) => Some(m.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(
        mem_specs.len(),
        2,
        "deployed setFieldDyn carries exactly the write+read-back flat MemOp pair"
    );
    println!(
        "== deployed setFieldDynVmDescriptor2: w={} pi={} | {} flat mem_ops, 0 chip lookups ==",
        deployed.trace_width,
        deployed.public_input_count,
        mem_specs.len()
    );

    // The interior access pattern, re-expressed over a tiny 4-col witness trace whose columns
    // are [addr_or_key, value, guard, _serial_pad]. The deployed write installs `value` at a
    // field-slot address; the read-back returns it. We pick a concrete (addr=100, init=77,
    // new=99) and replay it both ways. (Lifting the FULL 188-col EffectVM trace is unnecessary
    // for the interior-memory cost question — both provers see the SAME access pattern.)
    let addr = BabyBear::new(100);
    let init = BabyBear::new(77);
    let newv = BabyBear::new(99);

    // ==== (a) FLAT MemOp — the deployed shape ====
    let mem_desc = EffectVmDescriptor2 {
        name: "setfielddyn-mem-interior".to_string(),
        trace_width: 4,
        public_input_count: 0,
        tables: vec![],
        constraints: vec![
            VmConstraint2::MemOp(dregg_circuit::descriptor_ir2::MemOpSpec {
                guard: LeanExpr::Var(2),
                addr: LeanExpr::Var(0),
                value: LeanExpr::Var(1), // installs new value
                prev_value: LeanExpr::Const(77),
                prev_serial: LeanExpr::Const(0),
                kind: MemKind::Write,
            }),
            VmConstraint2::MemOp(dregg_circuit::descriptor_ir2::MemOpSpec {
                guard: LeanExpr::Var(2),
                addr: LeanExpr::Var(0),
                value: LeanExpr::Var(1), // reads back the just-written value
                prev_value: LeanExpr::Var(1),
                prev_serial: LeanExpr::Const(1),
                kind: MemKind::Read,
            }),
        ],
        hash_sites: vec![],
        ranges: vec![],
    };
    let mut mem_rows = vec![vec![addr, newv, BabyBear::ZERO, BabyBear::ZERO]; 4];
    mem_rows[0][2] = BabyBear::ONE; // guard the real ops on row 0
    let mem_boundary = MBW {
        addrs: vec![100],
        init_vals: vec![77],
    };
    let t0 = Instant::now();
    let mem_proof = prove_vm_descriptor2(&mem_desc, &mem_rows, &[], &mem_boundary, &[])
        .expect("flat-mem interior proves");
    let mem_ms = t0.elapsed().as_millis();
    verify_vm_descriptor2(&mem_desc, &mem_proof, &[]).expect("flat-mem interior verifies");
    let mem_bytes = breakdown("setfielddyn-FLATMEM", &mem_proof);
    let _ = init;

    // ==== (b) umem conversion — the SAME write+read-back on the Heap domain ====
    let umem_desc = EffectVmDescriptor2 {
        name: "setfielddyn-umem-interior".to_string(),
        trace_width: 4,
        public_input_count: 0,
        tables: vec![],
        constraints: vec![
            VmConstraint2::UMemOp(UMemOpSpec {
                guard: LeanExpr::Var(2),
                domain: 1, // Heap
                key: LeanExpr::Var(0),
                present: LeanExpr::Const(1),
                value: LeanExpr::Var(1),
                prev_present: LeanExpr::Const(1),
                prev_value: LeanExpr::Const(77),
                prev_serial: LeanExpr::Const(0),
                kind: MemKind::Write,
            }),
            VmConstraint2::UMemOp(UMemOpSpec {
                guard: LeanExpr::Var(2),
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
    let mut um_rows = vec![vec![addr, newv, BabyBear::ZERO, BabyBear::ZERO]; 4];
    um_rows[0][2] = BabyBear::ONE;
    let umem_boundary = UMemBoundaryWitness {
        addrs: vec![(1, addr)],
        init_vals: vec![Some(init)],
    };
    let t1 = Instant::now();
    let um_proof = prove_vm_descriptor2_umem(
        &umem_desc,
        &um_rows,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &umem_boundary,
    )
    .expect("umem interior proves");
    let um_ms = t1.elapsed().as_millis();
    verify_vm_descriptor2(&umem_desc, &um_proof, &[]).expect("umem interior verifies");
    let um_bytes = breakdown("setfielddyn-UMEM", &um_proof);

    // ---- The verdict line. ----
    let delta = mem_bytes as i64 - um_bytes as i64;
    let ratio = um_bytes as f64 / mem_bytes as f64;
    println!("== CONVERSION VERDICT (deployed setFieldDyn interior access, both verified) ==");
    println!(
        "flat-MemOp: {mem_bytes} B ({:.1} KiB, {mem_ms} ms, {} instances) | \
         umem: {um_bytes} B ({:.1} KiB, {um_ms} ms, {} instances) | \
         delta: {delta} B ({:+.1} KiB) | umem/mem ratio: {ratio:.3} ({:+.1}%)",
        kib(mem_bytes),
        mem_proof.degree_bits.len(),
        kib(um_bytes),
        um_proof.degree_bits.len(),
        (delta as f64) / 1024.0,
        (ratio - 1.0) * 100.0,
    );
}

/// THE CHIP-DROP CASE: the interior-memory bookkeeping of the deployed `attenuate`/`revoke-cap`
/// descriptors is a `map_op` READ + WRITE pair against a sorted-Merkle c-list (a membership
/// read then an in-place value update). A `map_op` opens its leaf through a sorted-Poseidon2
/// permutation that RIDES THE CHIP TABLE — so an interior map read+write PULLS IN
/// `{main, chip, byte, map_ops}`. The umem equivalent (the same read+write on the Caps domain)
/// hashes NOTHING: it commits `{main, byte, umemory, umem_boundary}` — the chip is DROPPED.
/// This isolates the per-op interior-memory cost in each form (the deployed attenuate/revoke-cap
/// ALSO carry 4 genuine state-recompute chip lookups, so they keep a chip table regardless; this
/// probe measures the bookkeeping leg ALONE, the part the conversion actually removes).
#[test]
fn ir2_mapop_interior_to_umem_chip_drop() {
    use dregg_circuit::descriptor_ir2::{
        EffectVmDescriptor2, MapKind, MapOpSpec, MemBoundaryWitness as MBW, MemKind,
        UMemBoundaryWitness, UMemOpSpec, VmConstraint2, prove_vm_descriptor2_umem,
    };
    use dregg_circuit::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf};
    use dregg_circuit::lean_descriptor_air::LeanExpr;

    // A 2-entry sorted c-list (the deployed bookkeeping shape: read membership, write update).
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
    let upd = tree
        .update_witness(HeapLeaf {
            addr: BabyBear::new(100),
            value: BabyBear::new(99),
        })
        .expect("key present");

    // ==== (a) map_op interior: a READ (membership) + WRITE (update) — chip-bearing ====
    // cols: [root, key, value_read, new_root, value_write, guard]
    let map_desc = EffectVmDescriptor2 {
        name: "clist-mapop-interior".to_string(),
        trace_width: 6,
        public_input_count: 0,
        tables: vec![],
        constraints: vec![
            VmConstraint2::MapOp(MapOpSpec {
                guard: LeanExpr::Var(5),
                root: LeanExpr::Var(0),
                key: LeanExpr::Var(1),
                value: LeanExpr::Var(2),
                new_root: LeanExpr::Var(0), // read: root unchanged
                op: MapKind::Read,
            }),
            VmConstraint2::MapOp(MapOpSpec {
                guard: LeanExpr::Var(5),
                root: LeanExpr::Var(0),
                key: LeanExpr::Var(1),
                value: LeanExpr::Var(4),
                new_root: LeanExpr::Var(3),
                op: MapKind::Write,
            }),
        ],
        hash_sites: vec![],
        ranges: vec![],
    };
    let mut map_rows = vec![
        vec![
            root,
            BabyBear::new(100),
            BabyBear::new(77), // read returns current value
            upd.new_root,
            BabyBear::new(99), // write installs new value
            BabyBear::ZERO,
        ];
        4
    ];
    map_rows[0][5] = BabyBear::ONE;
    let t0 = Instant::now();
    let map_proof =
        prove_vm_descriptor2(&map_desc, &map_rows, &[], &MBW::default(), &[heap.clone()])
            .expect("map-op interior proves");
    let map_ms = t0.elapsed().as_millis();
    verify_vm_descriptor2(&map_desc, &map_proof, &[]).expect("map-op interior verifies");
    let map_bytes = breakdown("clist-MAPOP", &map_proof);

    // ==== (b) umem conversion: the SAME read + write on the Caps domain — NO chip ====
    let umem_desc = EffectVmDescriptor2 {
        name: "clist-umem-interior".to_string(),
        trace_width: 6,
        public_input_count: 0,
        tables: vec![],
        constraints: vec![
            VmConstraint2::UMemOp(UMemOpSpec {
                guard: LeanExpr::Var(5),
                domain: 2, // Caps
                key: LeanExpr::Var(1),
                present: LeanExpr::Const(1),
                value: LeanExpr::Var(2),
                prev_present: LeanExpr::Const(1),
                prev_value: LeanExpr::Var(2),
                prev_serial: LeanExpr::Const(0),
                kind: MemKind::Read,
            }),
            VmConstraint2::UMemOp(UMemOpSpec {
                guard: LeanExpr::Var(5),
                domain: 2,
                key: LeanExpr::Var(1),
                present: LeanExpr::Const(1),
                value: LeanExpr::Var(4),
                prev_present: LeanExpr::Const(1),
                prev_value: LeanExpr::Var(2),
                prev_serial: LeanExpr::Const(1),
                kind: MemKind::Write,
            }),
        ],
        hash_sites: vec![],
        ranges: vec![],
    };
    let mut um_rows = vec![
        vec![
            root,
            BabyBear::new(100),
            BabyBear::new(77),
            upd.new_root,
            BabyBear::new(99),
            BabyBear::ZERO,
        ];
        4
    ];
    um_rows[0][5] = BabyBear::ONE;
    let umem_boundary = UMemBoundaryWitness {
        addrs: vec![(2, BabyBear::new(100))],
        init_vals: vec![Some(BabyBear::new(77))],
    };
    let t1 = Instant::now();
    let um_proof = prove_vm_descriptor2_umem(
        &umem_desc,
        &um_rows,
        &[],
        &MBW::default(),
        &[],
        &umem_boundary,
    )
    .expect("umem interior proves");
    let um_ms = t1.elapsed().as_millis();
    verify_vm_descriptor2(&umem_desc, &um_proof, &[]).expect("umem interior verifies");
    let um_bytes = breakdown("clist-UMEM", &um_proof);

    let delta = map_bytes as i64 - um_bytes as i64;
    let ratio = um_bytes as f64 / map_bytes as f64;
    println!("== CHIP-DROP VERDICT (c-list read+write interior, both verified) ==");
    println!(
        "map_op (chip-bearing): {map_bytes} B ({:.1} KiB, {map_ms} ms, {} instances) | \
         umem (no chip): {um_bytes} B ({:.1} KiB, {um_ms} ms, {} instances) | \
         delta: {delta} B ({:+.1} KiB) | umem/map ratio: {ratio:.3} ({:+.1}%)",
        kib(map_bytes),
        map_proof.degree_bits.len(),
        kib(um_bytes),
        um_proof.degree_bits.len(),
        (delta as f64) / 1024.0,
        (ratio - 1.0) * 100.0,
    );
    // The map_op interior commits a CHIP table (the sorted-Poseidon2 leaf openings ride it):
    // its instances are [main, chip(2^6), byte]. The umem conversion commits
    // [main, byte, umemory, umem_boundary] — NO chip. That dropped chip table is the win.
    assert_eq!(
        map_proof.degree_bits.len(),
        3,
        "map_op interior = main + chip + byte"
    );
    assert_eq!(
        um_proof.degree_bits.len(),
        4,
        "umem conversion = main + byte + umemory + umem_boundary (NO chip)"
    );
    assert!(
        um_bytes < map_bytes,
        "dropping the chip table shrinks the umem proof below the map_op proof"
    );
}
