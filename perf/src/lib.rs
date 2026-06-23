//! Shared workload builders + timing utilities for the dregg perf harnesses.
//!
//! Every workload here is constructed through the SAME production code paths the
//! node / SDK / circuit use at runtime — `generate_effect_vm_trace` for the
//! Effect-VM witness, the ROTATED `prove_full_turn` (with a real
//! `RotationTurnWitness` minted by `dregg_turn::rotation_witness::produce`, the
//! live commit path under the `recursion` default — the v1 `prove_turn_self_sovereign`
//! fallback is retired and panics), and the audited `prove_*_p3` / multi-table batch
//! provers for each sub-proof. The timings therefore reflect the real prover, not a toy.

use std::time::Instant;

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit::generate_effect_vm_trace;

// ---------------------------------------------------------------------------
// SMOKE vs FULL: every criterion bench in this crate runs a TINY input by
// default so `cargo bench --no-run` and a smoke run are cheap, and a REALISTIC
// input when `PERF_FULL=1` (the persvati capture run). This is the single
// switch the benches and the capture-baseline script agree on.
// ---------------------------------------------------------------------------

/// True when `PERF_FULL=1` — the realistic / persvati capture configuration.
/// Default (unset / "0") is SMOKE: tiny inputs, seconds-scale.
pub fn perf_full() -> bool {
    matches!(
        std::env::var("PERF_FULL").ok().as_deref(),
        Some("1") | Some("true") | Some("yes")
    )
}

/// A label for the current input regime, for criterion group/ids and logs.
pub fn regime() -> &'static str {
    if perf_full() { "full" } else { "smoke" }
}

/// A named turn workload: an initial cell state plus the effect bundle that
/// makes up one turn.
pub struct Workload {
    pub name: &'static str,
    pub initial: CellState,
    pub effects: Vec<Effect>,
}

/// The reference workload set, SMOKE-vs-FULL aware.
///
/// * SMOKE (default): the single smallest real turn (`transfer_1effect`) only —
///   so `cargo bench --no-run` and a smoke run stay seconds-scale.
/// * FULL (`PERF_FULL=1`): the 1/4/16-effect ladder, to show how prove time
///   scales with turn size on the fixed-height EffectVM AIR. This is the
///   persvati capture set.
pub fn workloads() -> Vec<Workload> {
    let one = Workload {
        name: "transfer_1effect",
        initial: CellState::new(1_000_000, 0),
        effects: vec![Effect::Transfer {
            amount: 100,
            direction: 1,
        }],
    };
    if !perf_full() {
        return vec![one];
    }
    vec![
        one,
        Workload {
            name: "transfer_4effect",
            initial: CellState::new(1_000_000, 0),
            effects: (0..4)
                .map(|i| Effect::Transfer {
                    amount: 10,
                    direction: (i % 2) as u32,
                })
                .collect(),
        },
        Workload {
            name: "transfer_16effect",
            initial: CellState::new(1_000_000, 0),
            effects: (0..16)
                .map(|i| Effect::Transfer {
                    amount: 1,
                    direction: (i % 2) as u32,
                })
                .collect(),
        },
    ]
}

/// Build the (base_trace, public_inputs) pair for a workload — the exact inputs
/// `prove_effect_vm_p3` consumes.
pub fn build_trace(w: &Workload) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    generate_effect_vm_trace(&w.initial, &w.effects)
}

/// A canonical single-Transfer turn — the smallest real turn, and the shape the
/// descriptor-interpreter cutover path is validated for.
pub fn single_transfer() -> (CellState, Vec<Effect>) {
    (
        CellState::new(1_000_000, 0),
        vec![Effect::Transfer {
            amount: 100,
            direction: 1,
        }],
    )
}

// ---------------------------------------------------------------------------
// THE LIVE FULL-TURN PROVE PATH (rotated). Under the `recursion` default the
// node proves a self-sovereign turn through the ROTATED descriptor leg: it mints
// the acting cell's before/after `RotationWitness` (`rotation_witness::produce`)
// and proves via `prove_full_turn` (the v1 `prove_turn_self_sovereign` entry with
// no rotation witness is RETIRED — it panics "thread a rotation witness"). This
// builder mirrors the validated C1 reference (`sdk/tests/sovereign_rotated_c1.rs`
// wall_a) so the proving leg is the real one. Gated on `recursion`.
// ---------------------------------------------------------------------------

/// A rotated full turn: the witness the prove bench re-proves, plus the rotated
/// leg's bound OLD/NEW commit PI carriers the verify bench checks against. The
/// commits are READ FROM A PROVEN PROOF's `"effect-vm-rotated"` leg PI (the trace's
/// own before/after state-commit carriers, NOT a separately-recomputed v9 — that is
/// what `verify_full_turn` cross-binds; the C1 reference reads them the same way).
#[cfg(feature = "prover")]
pub struct RotatedTurn {
    pub witness: dregg_sdk::full_turn_proof::FullTurnWitness,
    pub old_commit: [BabyBear; 8],
    pub new_commit: [BabyBear; 8],
}

/// Build a valid ROTATED full-turn witness for one outgoing transfer of `amount`
/// from a sovereign cell of `balance` — the live single-cell commit path. Mirrors
/// `AgentCipherclerk::prove_sovereign_turn_rotated` (the C1 reference): produce the
/// before/after rotation witnesses, seed the cap-rooted circuit pre-state, attach
/// the per-effect rotation manifest. Returns the witness + the post-prove commit PIs.
#[cfg(feature = "prover")]
pub fn rotated_transfer_turn(balance: u64, amount: u64) -> RotatedTurn {
    use dregg_cell::{Cell, CellMode, Ledger};
    use dregg_sdk::full_turn_proof::{FullTurnWitness, RotationTurnWitness};
    use dregg_turn::rotation_witness as rw;

    let token_id = *blake3::hash(b"perf-rotated-domain").as_bytes();
    let mut before_cell = Cell::with_balance([7u8; 32], token_id, balance as i64);
    before_cell.mode = CellMode::Sovereign;

    // after-state: an outgoing transfer debits the balance.
    let mut after_cell = before_cell.clone();
    after_cell
        .state
        .set_balance(after_cell.state.balance().saturating_sub(amount as i64));

    // circuit pre-state (cap-root-seeded), identical to the live producer.
    let initial_vm_state = CellState::with_capability_root(
        before_cell.state.balance() as u64,
        before_cell.state.nonce() as u32,
        dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
    );

    let vm_effects = vec![Effect::Transfer {
        amount,
        direction: 1, // outgoing
    }];

    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_hashes: Vec<[u8; 32]> = Vec::new();
    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(before_cell.clone());

    let before_w = rw::produce(&before_cell, &ctx_ledger, &nullifier_root, &commitments_root, &receipt_hashes);
    let after_w = rw::produce(&after_cell, &ctx_ledger, &nullifier_root, &commitments_root, &receipt_hashes);

    let rotation = RotationTurnWitness::for_effects(before_w, after_w, &vm_effects);

    // WIDE FLAG-DAY: the trusted 8-felt (~124-bit) commit anchors `verify_full_turn` binds — the
    // rotation's `wire_commit_8` before/after commits, the SAME the wide producer publishes at the
    // rotated leg's PI tail. Derived from the rotation witness before it MOVES into the witness.
    let (old_commit, new_commit) = rotation
        .wide_commit_anchors(&initial_vm_state, &vm_effects, None)
        .expect("wide_commit_anchors");
    let witness = FullTurnWitness {
        initial_cell_state: initial_vm_state,
        effects: vm_effects,
        authorization: None,
        membership: None,
        conservation: None,
        non_revocation: None,
        cap_membership: None,
        turn_hash: *blake3::hash(b"perf-rotated-turn").as_bytes(),
        rotation: Some(rotation),
        cap_turn_identity: None,
    };
    RotatedTurn {
        witness,
        old_commit,
        new_commit,
    }
}

/// The rotated-turn workload ladder (transfer amounts), SMOKE-vs-FULL aware.
/// SMOKE: one transfer. FULL: a 1/4/16-effect-equivalent amount ladder (the
/// single-cell rotated leg is fixed-height, so size scales via the manifest).
#[cfg(feature = "prover")]
pub fn rotated_turns() -> Vec<(&'static str, RotatedTurn)> {
    if !perf_full() {
        return vec![("transfer_100", rotated_transfer_turn(1_000_000, 100))];
    }
    vec![
        ("transfer_100", rotated_transfer_turn(1_000_000, 100)),
        ("transfer_10", rotated_transfer_turn(1_000_000, 10)),
        ("transfer_1", rotated_transfer_turn(1_000_000, 1)),
    ]
}

// ---------------------------------------------------------------------------
// Timing helpers — warm once, then time `iters` runs, report the mean.
// ---------------------------------------------------------------------------

/// Time `iters` runs of `f` after one warm-up run, returning the mean seconds.
pub fn time_mean<T>(iters: u32, mut f: impl FnMut() -> T) -> f64 {
    let _warm = f();
    let t0 = Instant::now();
    for _ in 0..iters {
        std::hint::black_box(f());
    }
    t0.elapsed().as_secs_f64() / iters as f64
}

/// Format a duration in seconds with an adaptive unit.
pub fn fmt_secs(secs: f64) -> String {
    if secs < 1e-6 {
        format!("{:.0} ns", secs * 1e9)
    } else if secs < 1e-3 {
        format!("{:.1} us", secs * 1e6)
    } else if secs < 1.0 {
        format!("{:.1} ms", secs * 1e3)
    } else {
        format!("{:.3} s", secs)
    }
}

/// Format a byte size with an adaptive unit.
pub fn fmt_bytes(n: usize) -> String {
    if n < 1024 {
        format!("{n} B")
    } else if n < 1024 * 1024 {
        format!("{:.1} KiB", n as f64 / 1024.0)
    } else {
        format!("{:.2} MiB", n as f64 / (1024.0 * 1024.0))
    }
}

// ---------------------------------------------------------------------------
// Executor-turn workload: build a real Ledger with two open cells + a Transfer
// turn so the live Rust `TurnExecutor::execute` (the executor entry the node
// drives) can be benchmarked through its PUBLIC API. Mirrors the executor's own
// `setup_two_open_cells` / `effect_transfer` test shape.
// ---------------------------------------------------------------------------

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_turn::{ActionBuilder, Turn, TurnBuilder, TurnExecutor};

/// Open permissions (every action `AuthRequired::None`) — the simplest cell
/// shape for an unauthenticated executor turn, matching the executor tests'
/// `make_open_cell`.
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

fn open_cell(seed: u8, balance: i64) -> Cell {
    let mut cell = Cell::with_balance([seed; 32], [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// Build a ledger with two open cells and a single-Transfer turn from the
/// agent to the target — the smallest real executor turn. Returns the pieces
/// `TurnExecutor::execute(&turn, &mut ledger)` consumes.
pub fn executor_transfer_turn() -> (Ledger, Turn) {
    let mut ledger = Ledger::new();
    let agent = open_cell(1, 1_000_000);
    let target = open_cell(2, 0);
    let agent_id = ledger.insert_cell(agent).expect("insert agent");
    let target_id = ledger.insert_cell(target).expect("insert target");

    let mut builder = TurnBuilder::new(agent_id, 0);
    let action = ActionBuilder::new_unchecked_for_tests(agent_id, "transfer", agent_id)
        .effect_transfer(agent_id, target_id, 200)
        .build();
    builder.add_action(action);
    let turn = builder.fee(0).build();
    (ledger, turn)
}

/// A fresh zero-cost executor (the cheapest configuration — the executor logic,
/// not the fee accounting, is what we time).
pub fn fresh_executor() -> TurnExecutor {
    TurnExecutor::new(dregg_turn::ComputronCosts::zero())
}

// ---------------------------------------------------------------------------
// LEAN FFI turn workloads — the SAME root-agreeing turn shapes the verified Lean
// producer (`execute_via_lean`) runs, mirrored from `executor_transfer_turn` so
// the Rust-executor and Lean-FFI legs are timed over identical input. A turn must
// be in the swap-safe root-agreeing set (Transfer / SetField are) for the FFI
// producer to run end-to-end. The multi-cell turn scales the wire footprint so the
// per-cell cost the OUT-delta optimization targets is visible.
// ---------------------------------------------------------------------------

/// Build a ledger with N open cells (cell 0 funded, the rest empty), so a turn can
/// touch a configurable footprint. Returns the ledger + the cell ids in order.
pub fn ledger_with_open_cells(n: usize, funded_balance: i64) -> (Ledger, Vec<dregg_cell::CellId>) {
    let mut ledger = Ledger::new();
    let mut ids = Vec::with_capacity(n);
    for i in 0..n {
        let bal = if i == 0 { funded_balance } else { 0 };
        let id = ledger
            .insert_cell(open_cell(i as u8 + 1, bal))
            .expect("insert open cell");
        ids.push(id);
    }
    (ledger, ids)
}

/// The smallest FFI-eligible turn: a single Transfer cell0 → cell1 (the same shape
/// as `executor_transfer_turn`, the executor bench's input). Touches 2 cells, writes 2.
pub fn ffi_transfer_turn() -> (Ledger, Turn) {
    let (ledger, ids) = ledger_with_open_cells(2, 1_000_000);
    let mut builder = TurnBuilder::new(ids[0], 0);
    let action = ActionBuilder::new_unchecked_for_tests(ids[0], "transfer", ids[0])
        .effect_transfer(ids[0], ids[1], 200)
        .build();
    builder.add_action(action);
    // The wire marshaller requires a concrete `valid_until` (the admission clock leg); the
    // diagnostic host clock is 0, so any future bound passes.
    let turn = builder.fee(0).valid_until(1000).build();
    (ledger, turn)
}

/// A single-SetField FFI-eligible turn: cell0 writes its own state slot 6 (a DIFFERENT
/// effect type than Transfer through the same producer path — the field-reconstitution
/// leg). References 1 cell (touched=1), writes 1. Mirrors the known-good
/// `setfield_lean_produced_ledger_agrees_with_rust` differential. The 3-cell ledger has
/// two un-referenced cells, so the contrast between ledger size and the wire footprint
/// (which is the turn's referenced set, not the whole ledger) is explicit.
pub fn ffi_setfield_turn() -> (Ledger, Turn) {
    let (ledger, ids) = ledger_with_open_cells(3, 1_000_000);
    let action = ActionBuilder::new_unchecked_for_tests(ids[0], "setfield", ids[0])
        .effect_set_field(ids[0], 6, field_from_u64(42))
        .build();
    let mut builder = TurnBuilder::new(ids[0], 0);
    builder.add_action(action);
    let turn = builder.fee(0).valid_until(1000).build();
    (ledger, turn)
}

/// A single-Transfer turn from a sender whose state is already POPULATED (several state
/// fields set). The richer pre-state cell record makes the IN wire bytes larger than the
/// bare `ffi_transfer_turn`, exposing how the per-cell serialization cost scales with cell
/// content — the same effect/shape, a heavier cell. Touches 2 cells; writes 2.
pub fn ffi_transfer_populated_turn() -> (Ledger, Turn) {
    let mut ledger = Ledger::new();
    let mut sender = open_cell(1, 1_000_000);
    // Populate several state fields so the cell record marshals to a larger wire payload.
    for slot in 2..7 {
        sender.state.fields[slot] = field_from_u64(0xABCD_0000 + slot as u64);
    }
    let agent_id = ledger.insert_cell(sender).expect("insert sender");
    let target_id = ledger.insert_cell(open_cell(2, 0)).expect("insert target");
    let action = ActionBuilder::new_unchecked_for_tests(agent_id, "transfer", agent_id)
        .effect_transfer(agent_id, target_id, 200)
        .build();
    let mut builder = TurnBuilder::new(agent_id, 0);
    builder.add_action(action);
    let turn = builder.fee(0).valid_until(1000).build();
    (ledger, turn)
}

fn field_from_u64(v: u64) -> dregg_cell::state::FieldElement {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&v.to_be_bytes());
    out
}

/// The diagnostic host context the FFI producer uses on the bench (clock 0, genesis
/// head, generous budget) — the same `ShadowHostCtx::diag()` the differential tests use.
pub fn ffi_host() -> dregg_exec_lean::lean_shadow::ShadowHostCtx {
    dregg_exec_lean::lean_shadow::ShadowHostCtx::diag()
}

/// Count the cells whose post-state differs from pre-state — the WRITTEN footprint.
/// `touched` (the wire serialization footprint) minus this is the echoed-but-unchanged
/// waste a delta-OUT optimization would remove. Diffs by canonical state commitment.
pub fn written_cells(pre: &Ledger, post: &Ledger) -> usize {
    let mut written = 0;
    for (id, post_cell) in post.iter() {
        match pre.get(id) {
            Some(pre_cell) => {
                if pre_cell.state_commitment() != post_cell.state_commitment() {
                    written += 1;
                }
            }
            None => written += 1, // a created cell counts as written
        }
    }
    // a removed cell (e.g. MakeSovereign) also counts as written
    for (id, _) in pre.iter() {
        if post.get(id).is_none() {
            written += 1;
        }
    }
    written
}

// ---------------------------------------------------------------------------
// Commitment workload: a populated `Cell` for the canonical state commitment.
// ---------------------------------------------------------------------------

/// A populated cell for the commitment benches: balance + some fields set, so
/// the commitment hashes a non-trivial state (not an all-zero cell).
pub fn commitment_cell() -> Cell {
    let mut cell = Cell::with_balance([7u8; 32], [11u8; 32], 1_000_000);
    // Touch a few state fields so the commitment isn't over an all-zero state.
    for i in 0..4 {
        cell.state.fields[i] = [i as u8 + 1; 32];
    }
    cell
}

/// A default v9 rotation context (zeroed roots) for the rotated-commitment
/// bench — the rotation long pole the umem path drives.
pub fn v9_context() -> dregg_cell::commitment::V9RotationContext {
    dregg_cell::commitment::V9RotationContext {
        cells_root: BabyBear::new(0),
        nullifier_root: [0u8; 32],
        commitments_root: [0u8; 32],
        iroot: BabyBear::new(0),
    }
}

// ---------------------------------------------------------------------------
// IR-v2 MULTI-TABLE COHORT witnesses (the rotated multi-table circuit, per
// effect-cohort). The graduated `transferVmDescriptor2` is proven over a REAL
// transfer trace; the memory-op cohorts (map-write / umem write+read / absent)
// are the distinct table-set shapes — chip-table vs the no-chip universal-memory
// multiset — that differentiate per-cohort prove cost. These mirror exactly the
// statements `circuit/tests/effect_vm_ir2_*` prove, lifted into a bench.
// ---------------------------------------------------------------------------

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MapKind, MapOpSpec, MemBoundaryWitness, MemKind, UMemBoundaryWitness,
    UMemOpSpec, VmConstraint2,
};
use dregg_circuit::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf};
use dregg_circuit::lean_descriptor_air::LeanExpr;

/// One IR-v2 multi-table cohort: a parsed descriptor, the base trace, the public
/// inputs, and the memory witnesses `prove_vm_descriptor2[_umem]` consumes.
pub struct Cohort {
    pub name: &'static str,
    pub desc: EffectVmDescriptor2,
    pub trace: Vec<Vec<BabyBear>>,
    pub pis: Vec<BabyBear>,
    pub mem_boundary: MemBoundaryWitness,
    pub map_heaps: Vec<Vec<HeapLeaf>>,
    /// `Some` only for the universal-memory cohort (the no-chip Blum multiset).
    pub umem_boundary: Option<UMemBoundaryWitness>,
}

/// The graduated transfer cohort: the live `transferVmDescriptor2` (five-table
/// EPOCH batch STARK: main + poseidon2-chip + range + memory + map-ops) over a
/// REAL `generate_effect_vm_trace` transfer.
pub fn cohort_transfer() -> Cohort {
    use dregg_circuit::descriptor_ir2::parse_vm_descriptor2;
    use dregg_circuit::effect_vm_descriptors::descriptor2_for_key;
    let json = descriptor2_for_key("transferVmDescriptor2").expect("transfer v2 descriptor");
    let desc = parse_vm_descriptor2(json).expect("transfer v2 descriptor parses");
    let (st, effs) = single_transfer();
    let (trace, full_pis) = build_trace(&Workload {
        name: "transfer",
        initial: st,
        effects: effs,
    });
    let pis = full_pis[..desc.public_input_count].to_vec();
    Cohort {
        name: "transfer_5table",
        desc,
        trace,
        pis,
        mem_boundary: MemBoundaryWitness::default(),
        map_heaps: vec![],
        umem_boundary: None,
    }
}

/// A 2-leaf heap + its root, shared by the memory-op cohorts.
fn probe_heap() -> (Vec<HeapLeaf>, BabyBear) {
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
    let root = CanonicalHeapTree::new(heap.clone(), HEAP_TREE_DEPTH).root();
    (heap, root)
}

/// The MAP-WRITE cohort: one in-place sorted-Poseidon2 write riding the chip bus
/// (the boundary map-op shape — it pays the chip table).
pub fn cohort_map_write() -> Cohort {
    let (heap, root) = probe_heap();
    let tree = CanonicalHeapTree::new(heap.clone(), HEAP_TREE_DEPTH);
    let w = tree
        .update_witness(HeapLeaf {
            addr: BabyBear::new(100),
            value: BabyBear::new(99),
        })
        .expect("key present");
    let desc = EffectVmDescriptor2 {
        name: "bench-map-write".to_string(),
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
    let mut rows = vec![
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
    rows[0][5] = BabyBear::ONE;
    Cohort {
        name: "map_write_chip",
        desc,
        trace: rows,
        pis: vec![],
        mem_boundary: MemBoundaryWitness::default(),
        map_heaps: vec![heap],
        umem_boundary: None,
    }
}

/// The UNIVERSAL-MEMORY cohort: the same write+read-back expressed as universal
/// memory ops (the ONE Blum multiset) — commits NO chip table (zero intra-proof
/// hashing), the no-chip cost shape.
pub fn cohort_umem() -> Cohort {
    let desc = EffectVmDescriptor2 {
        name: "bench-umem-write".to_string(),
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
    let mut rows = vec![
        vec![
            BabyBear::new(100),
            BabyBear::new(99),
            BabyBear::ZERO,
            BabyBear::ZERO,
        ];
        4
    ];
    rows[0][3] = BabyBear::ONE;
    let boundary = UMemBoundaryWitness {
        addrs: vec![(1, BabyBear::new(100))],
        init_vals: vec![Some(BabyBear::new(77))],
    };
    Cohort {
        name: "umem_write_read_nochip",
        desc,
        trace: rows,
        pis: vec![],
        mem_boundary: MemBoundaryWitness::default(),
        map_heaps: vec![],
        umem_boundary: Some(boundary),
    }
}

/// The ABSENT (non-membership) cohort: the boundary-gap leg — a sorted-Poseidon2
/// non-membership proof against the heap (it pays the chip).
pub fn cohort_absent() -> Cohort {
    let (heap, root) = probe_heap();
    let desc = EffectVmDescriptor2 {
        name: "bench-absent".to_string(),
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
    let mut rows = vec![vec![root, BabyBear::new(150), root, BabyBear::ZERO]; 4];
    rows[0][3] = BabyBear::ONE;
    Cohort {
        name: "absent_chip",
        desc,
        trace: rows,
        pis: vec![],
        mem_boundary: MemBoundaryWitness::default(),
        map_heaps: vec![heap],
        umem_boundary: None,
    }
}

/// The reference cohort set, SMOKE-vs-FULL aware. SMOKE: transfer only. FULL: the
/// four distinct table-set shapes (transfer / map-write / umem / absent).
pub fn cohorts() -> Vec<Cohort> {
    if !perf_full() {
        return vec![cohort_transfer()];
    }
    vec![
        cohort_transfer(),
        cohort_map_write(),
        cohort_umem(),
        cohort_absent(),
    ]
}

/// Prove a cohort through the production `ir2_config` multi-table batch prover,
/// routing the universal-memory cohort through the `_umem` entry.
pub fn prove_cohort(
    c: &Cohort,
) -> dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig> {
    use dregg_circuit::descriptor_ir2::{prove_vm_descriptor2, prove_vm_descriptor2_umem};
    match &c.umem_boundary {
        Some(b) => prove_vm_descriptor2_umem(
            &c.desc,
            &c.trace,
            &c.pis,
            &c.mem_boundary,
            &c.map_heaps,
            b,
        )
        .expect("cohort umem proves"),
        None => prove_vm_descriptor2(&c.desc, &c.trace, &c.pis, &c.mem_boundary, &c.map_heaps)
            .expect("cohort proves"),
    }
}

// ---------------------------------------------------------------------------
// RECURSIVE AGGREGATION FOLD witnesses (the bundle-tree fold the joint-turn /
// bundle aggregation folds N child digests through). `build_tree_fold_trace`
// builds the Poseidon2 compress-chain; `prove_tree_fold_v2` proves it satisfies
// the Lean-emitted `bundle_tree_fold_descriptor` (law #1) via the multi-table
// batch STARK (the chip table commits the compress chain).
// ---------------------------------------------------------------------------

/// N distinct child digests to fold — the leaves a bundle aggregates.
pub fn fold_digests(n: usize) -> Vec<BabyBear> {
    (0..n).map(|i| BabyBear::new(0x1000_0000 + i as u32)).collect()
}

/// The fold fan-out ladder: SMOKE folds 2 leaves; FULL folds 2/8/32/128 (the
/// aggregation cost scaling with bundle size).
pub fn fold_sizes() -> Vec<usize> {
    if perf_full() {
        vec![2, 8, 32, 128]
    } else {
        vec![2]
    }
}

// ---------------------------------------------------------------------------
// EMBEDDED-EXECUTOR commit_turn witness (the starbridge-v2 / node hot path).
// The node and the seL4 `executor` PD drive the VERIFIED Lean kernel via
// `dregg_lean_ffi::shadow_exec_full_forest_auth` — the `@[export]
// dregg_exec_full_forest_auth` proved in `metatheory/` (admission ∘ the gated
// forest). This is the real on-device commit: a wire-encoded (host, state, turn)
// goes in, a committed/rejected verdict + post-state wire comes out. We time that.
// ---------------------------------------------------------------------------

/// Build the canonical embedded-executor commit wire THROUGH THE REAL CODEC
/// (`marshal::marshal_turn`, which prepends the diagnostic host context — clock 0,
/// genesis head, so no spurious expiry). This reproduces the GOLDEN committing turn
/// the firmament boots (`wideDemoState` + `gatedDemoTurn`, FFI.lean:2745/3072 —
/// HORIZONLOG: the 5-PD assembly runs it `status:2 ok:1`): the root transfers 30 of
/// asset 0 cell-0 → cell-1 under a GENUINE `.signature 7 7` (the §1 portal needs the
/// proof to echo the statement — `.unchecked` only commits the prologue, NOT the body)
/// plus a trivially-true monotone caveat ⟨0,0,0,0⟩, so the gated tree COMMITS,
/// conserving asset 0 (100+5 = 70+35), loglen 1. Building it through the marshal API
/// (not a frozen string) keeps it byte-correct as the codec evolves — a hardcoded
/// host-less wire silently rots into the malformed-wire sentinel.
pub fn embedded_commit_wire() -> String {
    use dregg_lean_ffi::marshal::{
        Auth, Cap, Digest, WForest, WireAction, WireAuth, WireCaveat, WireEscrow, WireQueue,
        WireState, WireSwiss, WireTurn, WireValue, marshal_turn,
    };
    // `wideDemoState`: cell0 bal[asset0]=100 nonce=7, cell1 bal[asset0]=5, a cap table
    // (holder 9 → node 0), and one entry in each side-table (the wide shape the boot uses).
    let state = WireState {
        cells: vec![
            (
                0,
                WireValue::Record(vec![
                    ("balance".into(), WireValue::Int(100)),
                    ("nonce".into(), WireValue::Int(7)),
                ]),
            ),
            (
                1,
                WireValue::Record(vec![("balance".into(), WireValue::Int(5))]),
            ),
        ],
        caps: vec![(9, vec![Cap::Node(0)])],
        bal: vec![(0, 0, 100), (1, 0, 5)],
        escrows: vec![WireEscrow {
            id: 1,
            creator: 0,
            recipient: 1,
            amount: 7,
            resolved: false,
            asset: 0,
            bridge: false,
            queue_dep: None,
            queue_msg: None,
        }],
        nullifiers: vec![111],
        commitments: vec![222],
        queues: vec![WireQueue {
            id: 1,
            owner: 0,
            capacity: 4,
            buffer: vec![333, 444],
        }],
        swiss: vec![WireSwiss {
            swiss: 5,
            exporter: 0,
            target: 1,
            rights: vec![Auth::Read, Auth::Write],
            refcount: 1,
            cert: Some(99),
        }],
        ..WireState::default()
    };
    // `gatedDemoTurn` (minus the child escrow → the clean conserved transfer, loglen 1).
    let turn = WireTurn {
        agent: 0,
        nonce: 7,
        fee: 5,
        valid_until: 1000,
        block_height: 0,
        prev_hash: Digest::default(),
        root: WForest {
            auth: WireAuth::Signature {
                pubkey: Digest::from_u64(7),
                sig: 7,
            },
            caveats: vec![WireCaveat {
                tier: 0,
                cell: 0,
                asset: 0,
                min: 0,
            }],
            action: WireAction::Balance {
                actor: 0,
                src: 0,
                dst: 1,
                amt: 30,
                asset: 0,
            },
            children: vec![],
        },
    };
    marshal_turn(&state, &turn).expect("canonical embedded commit wire marshals")
}
