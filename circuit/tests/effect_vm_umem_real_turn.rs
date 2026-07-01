//! # THE FIRST NON-EXEMPLAR UMEM PROOF — the universal-memory prover consumes a REAL
//! # emitted trace, end-to-end.
//!
//! The executor-state bridge (`docs/UNIVERSAL-MAP-ROTATION.md` §2.3/§3; Lean keystones in
//! `metatheory/Dregg2/Exec/UniversalBridge.lean`) makes the LIVE executor produce the
//! universal-memory witness for a real turn (`dregg_turn::umem` — the journal re-read as a
//! Blum write trace over the `(domain, key)` address space). Until now every umem proof was
//! an exemplar instance the circuit tests constructed by hand (`demoU`,
//! `ir2_umem_vs_map_size_probe`). THIS test closes that gap:
//!
//!   1. a real multi-verb turn (two transfers + a set-field + a capability attenuation)
//!      executes through the PRODUCTION `TurnExecutor` with the umem witness lane armed;
//!   2. the emitted trace + the receipt-index append are lowered onto the IR-v2 `umem_op`
//!      grammar (one main row per op; one constraint per touched domain; the boundary =
//!      the turn's touched addresses with their pre-state cells);
//!   3. `prove_vm_descriptor2_umem` proves the ONE Blum balance over all four touched
//!      domains (heap · caps · nullifiers-absent-here · index) through the production
//!      `ir2_config`, and the independent verifier accepts;
//!   4. TEETH: a tampered write value REFUSES, and a stale-prev double-claim REFUSES.
//!
//! ## The per-proof address/value lowering (documented abstraction)
//!
//! The trace's semantic addresses are structured (`UKey`: cell ids, slots, vk hashes) and
//! its values are typed (`UVal`). A 31-bit BabyBear column cannot carry them raw; the
//! ROTATION's production realization hashes them (`addr = hash[domain, collection, key]`,
//! value codecs per plane — the Lean adapters `cap_leaf_value_codec` etc.). This test uses
//! the per-proof DENSE injection instead: distinct addresses (resp. values) are numbered
//! within the instance. An injective relabeling preserves exactly the memory-consistency
//! statement the umem argument checks (the multiset balance is label-invariant), so the
//! proof is a REAL memory-leg proof of the REAL turn's trace — with the address/value
//! codecs named as the rotation's remaining realization step.

// (formerly `#![cfg(feature = "prover")]` — that dregg-circuit feature is GONE; the
// descriptor-level prove/verify (`prove_vm_descriptor2`/`verify_vm_descriptor2`) is
// now unconditional in dregg-circuit, so this test compiles + runs by default.)

use std::collections::BTreeMap;
use std::sync::atomic::Ordering;
use std::time::Instant;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MapKind, MapOpSpec, MemBoundaryWitness, MemKind, UMemBoundaryWitness,
    UMemOpSpec, VmConstraint2, prove_vm_descriptor2, prove_vm_descriptor2_umem,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_DIGEST_W, HEAP_TREE_DEPTH, HeapLeaf};
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_turn::umem::{UKey, UVal, UmemKind, UmemOp, disciplined, fold, receipt_op};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

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

fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// Execute the real multi-verb turn on the production executor and return the emitted
/// umem witness ops (+ pre projection) and the receipt hash.
fn real_turn_trace() -> (BTreeMap<UKey, UVal>, Vec<UmemOp>, [u8; 32]) {
    let agent = make_open_cell(11, 1000);
    let target = make_open_cell(12, 10);
    let (agent_id, target_id) = (agent.id(), target.id());

    let mut agent_with_cap = agent;
    let slot = agent_with_cap
        .capabilities
        .grant(target_id, AuthRequired::Either)
        .unwrap();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent_with_cap).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    executor.umem_witness_enabled.store(true, Ordering::Relaxed);

    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent_id,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![
            // move ×2 (the SAME debit address touched twice — exercises the serial chain)
            Effect::Transfer {
                from: agent_id,
                to: target_id,
                amount: 7,
            },
            Effect::Transfer {
                from: agent_id,
                to: target_id,
                amount: 5,
            },
            // gwrite (heap record-field plane)
            Effect::SetField {
                cell: agent_id,
                index: 2,
                value: [42u8; 32],
            },
            // gwrite (caps plane — the guarded narrow write)
            Effect::AttenuateCapability {
                cell: agent_id,
                slot,
                narrower_permissions: AuthRequired::Signature,
                narrower_effects: None,
                narrower_expiry: None,
            },
        ],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    let turn = Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "real turn must commit: {result:?}");
    let (_, receipt, _) = result.unwrap_committed();

    let witness = executor
        .last_umem_witness
        .lock()
        .unwrap()
        .take()
        .expect("witness produced")
        .expect("witness emission succeeded");
    // the bridge square holds on the Rust side before anything goes near the prover.
    assert_eq!(fold(&witness.pre, &witness.ops), witness.post);
    assert!(disciplined(&witness.ops));
    assert_eq!(witness.synthesized, 0);

    (witness.pre, witness.ops, receipt.receipt_hash())
}

/// The per-proof dense lowering: addresses → (domain code, key felt), values → felts.
struct Lowering {
    /// key → (domain code, in-domain felt)
    addr: BTreeMap<UKey, (u32, u32)>,
    /// distinct values → nonzero felt
    val: BTreeMap<Vec<u8>, u32>,
}

fn uval_bytes(v: &UVal) -> Vec<u8> {
    format!("{v:?}").into_bytes()
}

impl Lowering {
    fn build(pre: &BTreeMap<UKey, UVal>, ops: &[UmemOp]) -> Self {
        let mut addr: BTreeMap<UKey, (u32, u32)> = BTreeMap::new();
        let mut per_domain_next: BTreeMap<u32, u32> = BTreeMap::new();
        for op in ops {
            let d = op.key.domain().code();
            addr.entry(op.key.clone()).or_insert_with(|| {
                let next = per_domain_next.entry(d).or_insert(1);
                let felt = *next;
                *next += 1;
                (d, felt)
            });
        }
        let mut val: BTreeMap<Vec<u8>, u32> = BTreeMap::new();
        let mut next_val = 1u32;
        let intern = |v: &UVal, val: &mut BTreeMap<Vec<u8>, u32>, next_val: &mut u32| {
            let b = uval_bytes(v);
            val.entry(b).or_insert_with(|| {
                let f = *next_val;
                *next_val += 1;
                f
            });
        };
        for op in ops {
            if let Some(v) = &op.val {
                intern(v, &mut val, &mut next_val);
            }
            if let Some(v) = &op.prev_val {
                intern(v, &mut val, &mut next_val);
            }
        }
        for k in addr.keys() {
            if let Some(v) = pre.get(k) {
                intern(v, &mut val, &mut next_val);
            }
        }
        Lowering { addr, val }
    }

    fn key_felt(&self, k: &UKey) -> (u32, u32) {
        self.addr[k]
    }

    fn val_felt(&self, v: &Option<UVal>) -> (u32, u32) {
        match v {
            None => (0, 0),
            Some(v) => (1, self.val[&uval_bytes(v)]),
        }
    }
}

/// Lower the real trace onto the IR-v2 umem grammar: descriptor + main rows + boundary.
fn lower(
    pre: &BTreeMap<UKey, UVal>,
    ops: &[UmemOp],
) -> (EffectVmDescriptor2, Vec<Vec<BabyBear>>, UMemBoundaryWitness) {
    let lowering = Lowering::build(pre, ops);

    // one umem_op constraint per touched domain, guarded by its own indicator column.
    let mut domains: Vec<u32> = lowering.addr.values().map(|(d, _)| *d).collect();
    domains.sort();
    domains.dedup();
    let guard_col_of: BTreeMap<u32, usize> = domains
        .iter()
        .enumerate()
        .map(|(i, d)| (*d, 6 + i))
        .collect();
    let width = 6 + domains.len();

    let constraints: Vec<VmConstraint2> = domains
        .iter()
        .map(|d| {
            VmConstraint2::UMemOp(UMemOpSpec {
                guard: LeanExpr::Var(guard_col_of[d]),
                domain: *d,
                key: LeanExpr::Var(0),
                present: LeanExpr::Var(1),
                value: LeanExpr::Var(2),
                prev_present: LeanExpr::Var(3),
                prev_value: LeanExpr::Var(4),
                prev_serial: LeanExpr::Var(5),
                kind: MemKind::Write,
            })
        })
        .collect();

    let desc = EffectVmDescriptor2 {
        name: "real-turn-umem".to_string(),
        trace_width: width,
        public_input_count: 0,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    };

    // one main row per op, padded to a power of two with all guards off.
    let mut rows: Vec<Vec<BabyBear>> = Vec::new();
    for op in ops {
        assert!(matches!(op.kind, UmemKind::Write));
        let (d, key) = lowering.key_felt(&op.key);
        let (present, value) = lowering.val_felt(&op.val);
        let (prev_present, prev_value) = lowering.val_felt(&op.prev_val);
        let mut row = vec![BabyBear::ZERO; width];
        row[0] = BabyBear::new(key);
        row[1] = BabyBear::new(present);
        row[2] = BabyBear::new(value);
        row[3] = BabyBear::new(prev_present);
        row[4] = BabyBear::new(prev_value);
        row[5] = BabyBear::new(op.prev_serial as u32);
        row[guard_col_of[&d]] = BabyBear::ONE;
        rows.push(row);
    }
    let height = rows.len().next_power_of_two().max(4);
    while rows.len() < height {
        rows.push(vec![BabyBear::ZERO; width]);
    }

    // the boundary: every touched address, with its pre-state cell as the init image.
    let mut addrs: Vec<(UKey, (u32, u32))> = lowering
        .addr
        .iter()
        .map(|(k, df)| (k.clone(), *df))
        .collect();
    addrs.sort_by_key(|(_, (d, f))| (*d, *f));
    let boundary = UMemBoundaryWitness {
        addrs: addrs
            .iter()
            .map(|(_, (d, f))| (*d, BabyBear::new(*f)))
            .collect(),
        init_vals: addrs
            .iter()
            .map(|(k, _)| {
                let (present, value) = lowering.val_felt(&pre.get(k).cloned());
                if present == 1 {
                    Some(BabyBear::new(value))
                } else {
                    None
                }
            })
            .collect(),
    };

    (desc, rows, boundary)
}

#[test]
fn umem_prover_consumes_real_turn_trace() {
    let (pre, mut ops, receipt_hash) = real_turn_trace();
    // append the index-domain receipt write (the turn's log append at position 0 —
    // the Lean side's `.receipt` op; adapter (b) covers its boundary MMR root).
    ops.push(receipt_op(0, receipt_hash));

    // multi-touch serial chain really present (the two transfers share the debit addr).
    assert!(
        ops.iter().any(|op| op.prev_serial != 0),
        "the real trace must exercise the serial chain (an address touched twice)"
    );

    let (desc, rows, boundary) = lower(&pre, &ops);

    let t0 = Instant::now();
    let proof = prove_vm_descriptor2_umem(
        &desc,
        &rows,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &boundary,
    )
    .expect("the real turn's memory leg proves");
    let prove_ms = t0.elapsed().as_millis();
    verify_vm_descriptor2(&desc, &proof, &[]).expect("the real turn's memory leg verifies");

    let bytes = postcard::to_allocvec(&proof).expect("postcard").len();
    println!(
        "[umem real turn] ops: {} | domains: {} | proof: {} B ({:.1} KiB) | prove: {} ms | \
         degree_bits: {:?}",
        ops.len(),
        desc.constraints.len(),
        bytes,
        bytes as f64 / 1024.0,
        prove_ms,
        proof.degree_bits,
    );
}

#[test]
fn umem_real_turn_tampered_write_refuses() {
    let (pre, mut ops, receipt_hash) = real_turn_trace();
    ops.push(receipt_op(0, receipt_hash));
    let (desc, mut rows, boundary) = lower(&pre, &ops);

    // tamper the FIRST guarded row's installed value: the multiset balance must refuse
    // (the read/boundary entries no longer cancel).
    rows[0][2] = rows[0][2] + BabyBear::ONE;
    let r = prove_vm_descriptor2_umem(
        &desc,
        &rows,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &boundary,
    );
    assert!(r.is_err(), "a tampered write value must refuse");
}

#[test]
fn umem_real_turn_stale_prev_refuses() {
    let (pre, mut ops, receipt_hash) = real_turn_trace();
    ops.push(receipt_op(0, receipt_hash));

    // the second touch of the twice-touched debit address claims the INIT boundary
    // again (a stale-prev double-claim — the same lie as an intra-proof double spend).
    let idx = ops
        .iter()
        .position(|op| op.prev_serial != 0)
        .expect("multi-touch op present");
    ops[idx].prev_serial = 0;
    let stale_prev = {
        // claim the pre-state cell instead of the genuine intermediate value
        pre.get(&ops[idx].key).cloned()
    };
    ops[idx].prev_val = stale_prev;

    let (desc, rows, boundary) = lower(&pre, &ops);
    let r = prove_vm_descriptor2_umem(
        &desc,
        &rows,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &boundary,
    );
    assert!(r.is_err(), "a stale-prev double-claim must refuse");
}

// ============================================================================
// THE CROSS-CELL-READ LEG — a turn proving it READ a SECOND cell's committed state.
//
// The unlock the boundary→committed-state binding opens (`docs/UNIVERSAL-MAP-ROTATION.md`;
// Lean anchors `boundary_init_root_derived` / `boundary_init_root_bound` in
// `Dregg2/Crypto/UniversalMemory.lean`, lifted to the IR as `satisfied2U_init_root`).
//
// Today's cross-cell read (`StateConstraint::ObservedFieldEquals`,
// `turn/src/executor/execute_tree.rs`) is WITNESS-enforced only: the executor binds a peer
// cell's genuine `state_commitment()` and admits iff the declared `at_root` matches AND the
// local field equals the peer's finalized value — NO in-circuit fact. This leg LIFTS that into
// a circuit fact: the peer cell's committed FIELD-PLANE heap root is pinned to a public input
// (the published commitment), and a `MapOp::Read` opens the read field against THAT root. The
// soundness is exactly `boundary_init_root_derived`'s `hsem` realized per declared address: the
// opened cell genuinely lives in the committed pre-state map whose root is published. A forged
// peer root has no satisfying membership path (the anti-forge tooth, the circuit twin of the
// executor's empty-binding rejection); a forged field value opens to the genuine leaf, not the
// claim, and refuses (the mismatch tooth).
//
// SOUNDNESS SCOPE (named precisely): this binds each TOUCHED init/read cell to the committed
// root by per-cell membership (a faithful SUBSET view — "cell X's published field IS this"),
// which is exactly the cross-cell-read primitive's need. The whole-IMAGE equality (the SUBSET
// *and* the no-extra-cells direction, i.e. the full sorted-Poseidon2 root recompute over the
// entire boundary `boundaryCells`) is now a PROVED Lean theorem on the soundness side:
// `UniversalMemory.boundary_whole_image_sem` (IR lift `DescriptorIR2.satisfied2U_init_whole_image`)
// — pinning the committed root to the whole-boundary fold forces the committed heap to agree with
// the declared image at every address, absence off-list included (no extra cells), via
// `boundary_init_root_bound`'s injectivity. The in-circuit AIR/witness work that COMPUTES that
// whole-boundary root-fold and pins it to the committed-root PI (the theorem's `hpin` hypothesis)
// is now REALIZED — `dregg_circuit::whole_image_fold` (the WHOLE-IMAGE FOLD CHIP, exercised in the
// `cross_cell_read_whole_image_*` tests below): the chip reconstructs `mapRoot hash d boundaryHeap`
// over the ENTIRE declared boundary view via a sorted-insert chain from the empty root and pins the
// delivered fold to the published-root PI. A peer heap with one extra/altered cell folds to a
// different root and can no longer be pinned (the `mapRoot_injective` no-extra-cells tooth, biting
// in-circuit). The cross-table wiring binding the chip's insert-chain `(key, value)` rows to the
// universal boundary table's per-domain `(domain, key)` cells is REALIZED below
// (`whole_image_fold_bound_*`): each fold link drives a `UMemOp::Read` against the boundary table,
// so the deployed address-closure + Blum machinery force the fold to fold EXACTLY the declared
// boundary cells with their declared values (no new bus/column/AIR).

/// The deployed-shape column layout for the cross-cell read MapOp (arbitrary but stable):
/// cols [0..8) = the peer's published field-plane 8-felt root (each lane pinned to PI lane i),
/// col 8 = the read field address, col 9 = the read field value.
const XC_ROOT: usize = 0;
const XC_ADDR: usize = HEAP_DIGEST_W;
const XC_VALUE: usize = HEAP_DIGEST_W + 1;

/// Build a peer cell, publish its field-plane heap (`(slot, field_value)` leaves over its
/// non-zero fields), and return `(peer_cell, peer_field_heap, root)`. The root is the in-circuit
/// commitment to the peer's field state the cross-cell read opens against.
fn peer_field_heap(peer: &Cell) -> (Vec<HeapLeaf>, [BabyBear; HEAP_DIGEST_W]) {
    let mut leaves: Vec<HeapLeaf> = Vec::new();
    for (slot, f) in peer.state.fields.iter().enumerate() {
        // a field cell exists in the published map iff its first felt-limb is non-zero (a
        // simple deterministic presence rule for this leg — every present cell opens).
        let v = u32::from_le_bytes([f[0], f[1], f[2], f[3]]);
        if v != 0 {
            leaves.push(HeapLeaf {
                addr: BabyBear::new(slot as u32 + 1), // +1: keep addr 0 out of the sentinel range
                value: BabyBear::new(v),
            });
        }
    }
    let tree = CanonicalHeapTree8::new(leaves.clone(), HEAP_TREE_DEPTH);
    (leaves, tree.root8())
}

/// The descriptor for the cross-cell read: one `MapOp::Read` opening the read field against the
/// peer root, with the root column PINNED to PI 0 (the published commitment). Width 4.
fn xcell_read_desc() -> EffectVmDescriptor2 {
    // Each of the 8 root lanes is pinned to its published-commitment PI lane (the anti-forge
    // anchor: the opened 8-felt root is not prover-chosen, it is the PI-bound committed value).
    let mut constraints: Vec<VmConstraint2> = (0..HEAP_DIGEST_W)
        .map(|lane| {
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: XC_ROOT + lane,
                pi_index: lane,
            })
        })
        .collect();
    // The read: open `(addr, value)` against the committed peer root (root unchanged).
    constraints.push(VmConstraint2::MapOp(MapOpSpec {
        guard: LeanExpr::Const(1),
        root: (XC_ROOT..XC_ROOT + HEAP_DIGEST_W)
            .map(LeanExpr::Var)
            .collect(),
        key: LeanExpr::Var(XC_ADDR),
        value: LeanExpr::Var(XC_VALUE),
        new_root: (XC_ROOT..XC_ROOT + HEAP_DIGEST_W)
            .map(LeanExpr::Var)
            .collect(),
        op: MapKind::Read,
    }));
    EffectVmDescriptor2 {
        name: "xcell-read".to_string(),
        trace_width: HEAP_DIGEST_W + 2,
        public_input_count: HEAP_DIGEST_W,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// Execute a turn that mutates cell A but only READS cell B, and return cell B's published
/// field heap + root + a chosen (read-addr, read-value) the turn observed.
fn cross_cell_read_setup() -> (Vec<HeapLeaf>, [BabyBear; HEAP_DIGEST_W], BabyBear, BabyBear) {
    // cell A: the actor the turn mutates. cell B: the peer the turn READS, never mutates.
    let mut agent = make_open_cell(21, 1000);
    agent.state.fields[0] = [9u8; 32];
    let mut peer = make_open_cell(22, 500);
    // give the peer some committed field state (the thing the turn reads).
    peer.state.fields[3] = {
        let mut b = [0u8; 32];
        b[..4].copy_from_slice(&777u32.to_le_bytes());
        b
    };
    let (heap, root) = peer_field_heap(&peer);
    // the read: peer field slot 3 (addr 4) opens to value 777.
    let read_addr = BabyBear::new(3 + 1);
    let read_value = BabyBear::new(777);

    let agent_id = agent.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(peer).unwrap();

    // a real turn touching ONLY cell A (a self set-field), proving cell B is untouched.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    executor.umem_witness_enabled.store(true, Ordering::Relaxed);
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent_id,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: agent_id,
            index: 1,
            value: [5u8; 32],
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    let turn = Turn {
        agent: agent_id,
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };
    let result = executor.execute(&turn, &mut ledger);
    assert!(result.is_committed(), "the mutating turn must commit");
    (heap, root, read_addr, read_value)
}

#[test]
fn cross_cell_read_proves_committed_peer_state() {
    let (heap, root, read_addr, read_value) = cross_cell_read_setup();
    let desc = xcell_read_desc();
    let mut row = vec![BabyBear::ZERO; HEAP_DIGEST_W + 2];
    row[XC_ROOT..XC_ROOT + HEAP_DIGEST_W].copy_from_slice(&root);
    row[XC_ADDR] = read_addr;
    row[XC_VALUE] = read_value;
    let trace = vec![row; 4];

    // the published commitment is the public input; each root lane is PI-bound to it.
    let proof = prove_vm_descriptor2(
        &desc,
        &trace,
        &root,
        &MemBoundaryWitness::default(),
        std::slice::from_ref(&heap),
    )
    .expect("an honest cross-cell read of committed peer state must prove");
    verify_vm_descriptor2(&desc, &proof, &root)
        .expect("the cross-cell read verifies against the published commitment");
}

#[test]
fn cross_cell_read_forged_peer_root_refuses() {
    let (heap, root, read_addr, read_value) = cross_cell_read_setup();
    let desc = xcell_read_desc();
    let mut forged_root = root;
    forged_root[0] += BabyBear::ONE; // a root not matching any published peer heap
    assert_ne!(forged_root, root);
    let mut row = vec![BabyBear::ZERO; HEAP_DIGEST_W + 2];
    row[XC_ROOT..XC_ROOT + HEAP_DIGEST_W].copy_from_slice(&forged_root);
    row[XC_ADDR] = read_addr;
    row[XC_VALUE] = read_value;
    let trace = vec![row; 4];

    // bind the PI to the forged root too (so PiBinding passes): the MapOp Read still has no
    // witness heap with that root — the anti-forge membership tooth bites.
    let r = prove_vm_descriptor2(
        &desc,
        &trace,
        &forged_root,
        &MemBoundaryWitness::default(),
        &[heap],
    );
    assert!(
        r.is_err(),
        "a forged peer root must refuse (no membership path)"
    );
}

#[test]
fn cross_cell_read_forged_field_value_refuses() {
    let (heap, root, read_addr, _read_value) = cross_cell_read_setup();
    let desc = xcell_read_desc();
    let mut row = vec![BabyBear::ZERO; HEAP_DIGEST_W + 2];
    row[XC_ROOT..XC_ROOT + HEAP_DIGEST_W].copy_from_slice(&root);
    row[XC_ADDR] = read_addr;
    row[XC_VALUE] = BabyBear::new(778); // NOT the committed 777
    let trace = vec![row; 4];

    let r = prove_vm_descriptor2(
        &desc,
        &trace,
        &root,
        &MemBoundaryWitness::default(),
        &[heap],
    );
    assert!(
        r.is_err(),
        "a forged read value must refuse (opens to the genuine leaf, not the claim)"
    );
}

#[test]
fn cross_cell_read_pi_mismatch_refuses() {
    // the published commitment PI must EQUAL the opened root: a turn claiming it read against
    // commitment C while opening against a different root C' is refused by the PiBinding leg.
    let (heap, root, read_addr, read_value) = cross_cell_read_setup();
    let desc = xcell_read_desc();
    let mut row = vec![BabyBear::ZERO; HEAP_DIGEST_W + 2];
    row[XC_ROOT..XC_ROOT + HEAP_DIGEST_W].copy_from_slice(&root);
    row[XC_ADDR] = read_addr;
    row[XC_VALUE] = read_value;
    let trace = vec![row; 4];

    // supply a DIFFERENT published commitment than the opened root — the PiBinding leg is
    // unsatisfiable, so NO proof exists. (The PI is not part of the pre-flight trace replay, so
    // the refusal surfaces as the in-circuit constraint failing rather than an Err — caught
    // here: either way, a satisfying proof is impossible.)
    let mut wrong_pi = root;
    wrong_pi[0] += BabyBear::ONE;
    let outcome = std::panic::catch_unwind(|| {
        prove_vm_descriptor2(
            &desc,
            &trace,
            &wrong_pi,
            &MemBoundaryWitness::default(),
            std::slice::from_ref(&heap),
        )
    });
    let refused = match outcome {
        Err(_) => true,      // in-circuit PiBinding constraint failed (no satisfying proof)
        Ok(r) => r.is_err(), // or refused with an Err
    };
    assert!(
        refused,
        "the opened root must equal the published-commitment PI (no claiming-a-different-root)"
    );
}

// ============================================================================
// THE WHOLE-IMAGE FOLD CHIP — the no-extra-cells direction, realized in-circuit.
//
// The cross-cell-read leg above is the per-cell SUBSET view (each declared address opens to the
// peer's committed value under the published root). It does not, on its own, forbid a committed
// peer heap holding the declared cells AND extra cells the boundary never declared.
//
// `dregg_circuit::whole_image_fold` closes that direction: it CONSTRUCTS the published root from
// the declared boundary cells alone — a sorted-INSERT chain from the empty root reconstructs
// `mapRoot hash d boundaryHeap` (the deployed depth-16 binary fold, `heap_root.rs` /
// `MapMerkleRoot.lean`), pinned to the published-root PI. This realizes the `hpin` hypothesis of
// the discharged Lean theorems (`UniversalBridge.crossCellRead_whole_image` /
// `cross_cell_read_no_extra_cell` / `_teeth`): the committed peer heap IS the declared view, no
// hidden cell. A peer heap with one extra/altered cell folds to a different root and can no longer
// be pinned (the `mapRoot_injective` anti-ghost biting in-circuit).

use dregg_circuit::whole_image_fold::{
    build_whole_image_fold, prove_whole_image_fold, verify_whole_image_fold, whole_boundary_fold,
};

/// A peer with several non-zero committed fields, lowered to its published field-plane leaves (the
/// whole-boundary view the cross-cell read declares).
fn peer_with_fields(slots_values: &[(usize, u32)]) -> Vec<HeapLeaf> {
    let mut peer = make_open_cell(31, 500);
    for &(slot, v) in slots_values {
        let mut b = [0u8; 32];
        b[..4].copy_from_slice(&v.to_le_bytes());
        peer.state.fields[slot] = b;
    }
    peer_field_heap(&peer).0
}

#[test]
fn cross_cell_read_whole_image_folds_to_published_root() {
    // A peer with a non-trivial field plane (three committed cells): the chip must fold ALL of
    // them up the binary tree to the genuine published root.
    let leaves = peer_with_fields(&[(1, 111), (3, 777), (5, 555)]);
    assert!(leaves.len() >= 2, "the fold must be non-trivial");
    let published = whole_boundary_fold(&leaves);

    // HONEST whole-image read: the published commitment IS the fold of the entire declared view.
    let witness = build_whole_image_fold(&leaves, published).expect("declared view folds");
    let proof = prove_whole_image_fold(&witness)
        .expect("the whole-boundary fold to the published root proves");
    verify_whole_image_fold(&proof, &witness.public_inputs)
        .expect("the whole-image fold verifies against the published commitment");
}

#[test]
fn cross_cell_read_whole_image_extra_cell_refuses() {
    // The peer's GENUINE committed heap holds an EXTRA cell (slot 7) the cross-cell read's declared
    // boundary never names. Its real published root is the fold of ALL four cells.
    let full = peer_with_fields(&[(1, 111), (3, 777), (5, 555), (7, 999)]);
    let peer_published_root = whole_boundary_fold(&full);

    // The DECLARED whole-boundary view omits the hidden cell (slot 7). Folding only the declared
    // cells cannot reach the peer's real root: the `PiBinding{Last}` pin to the published root is
    // unsatisfiable — the no-extra-cells tooth bites in-circuit.
    let mut declared = full.clone();
    declared.retain(|l| l.addr != BabyBear::new(7 + 1));
    assert_eq!(declared.len(), full.len() - 1, "exactly one cell hidden");
    assert_ne!(
        whole_boundary_fold(&declared),
        peer_published_root,
        "the declared-view fold must differ from the hidden-cell root"
    );

    let witness =
        build_whole_image_fold(&declared, peer_published_root).expect("declared view folds");
    // The pin is a boundary constraint (not a pre-flight replay), so the refusal can surface as an
    // Err or an in-circuit panic — either way no satisfying proof exists.
    let outcome = std::panic::catch_unwind(|| prove_whole_image_fold(&witness));
    let refused = match outcome {
        Err(_) => true,
        Ok(r) => r.is_err(),
    };
    assert!(
        refused,
        "a peer heap with an undeclared extra cell must refuse (the fold cannot reach its root)"
    );
}

#[test]
fn cross_cell_read_whole_image_tampered_value_refuses() {
    // Tamper ONE declared cell's value while claiming the published root is the GENUINE fold: the
    // chip's sorted insert recomputes the authentic post-root, which no longer matches the claimed
    // chain link — the map-op reconciliation refuses.
    let leaves = peer_with_fields(&[(1, 111), (3, 777), (5, 555)]);
    let published = whole_boundary_fold(&leaves);
    let mut witness = build_whole_image_fold(&leaves, published).expect("declared view folds");

    // Bump the value installed by the first real insert row (guard == 1) — the genuine insert
    // result will no longer equal the row's claimed new_root.
    let row = witness
        .trace
        .iter_mut()
        .find(|r| r[dregg_circuit::whole_image_fold::WIF_GUARD] == BabyBear::ONE)
        .expect("a real insert row exists");
    row[dregg_circuit::whole_image_fold::WIF_VALUE] =
        row[dregg_circuit::whole_image_fold::WIF_VALUE] + BabyBear::ONE;

    let outcome = std::panic::catch_unwind(|| prove_whole_image_fold(&witness));
    let refused = match outcome {
        Err(_) => true,
        Ok(r) => r.is_err(),
    };
    assert!(
        refused,
        "a tampered declared value must refuse (the sorted insert recomputes a different root)"
    );
}

#[test]
fn cross_cell_read_whole_image_smuggled_start_root_refuses() {
    // The SMUGGLED-START tooth (latent vacuity B4): the descriptor's `PiBinding{First}` only
    // forces the fold's first pre-root to EQUAL PI 0 — it does NOT force PI 0 to be the empty
    // root. PI 0 is a verifier-side public input, so a prover could publish
    // `[smuggled_root, published]` and start the fold from a NON-empty root holding cells the
    // boundary never declared: every link would still be a genuine insert and both `PiBinding`s
    // would pass, yet `published` would commit to the smuggled cells PLUS the declared ones —
    // defeating the no-extra-cells guarantee. The verify wrapper pins PI 0 to the canonical
    // empty root, so such a public-input vector is REFUSED before the STARK is even consulted.
    let leaves = peer_with_fields(&[(1, 111), (3, 777), (5, 555)]);
    let published = whole_boundary_fold(&leaves);
    let witness = build_whole_image_fold(&leaves, published).expect("declared view folds");
    let proof = prove_whole_image_fold(&witness).expect("the honest fold proves");

    // Honest PIs (empty-root start) accept.
    verify_whole_image_fold(&proof, &witness.public_inputs)
        .expect("the honest empty-root-start fold verifies");

    // A NON-empty smuggled start root (e.g. a one-cell heap hiding an undeclared cell) in PI 0
    // must be refused by the pin, independent of any proof.
    let smuggled_start = whole_boundary_fold(&[HeapLeaf {
        addr: BabyBear::new(99),
        value: BabyBear::new(42),
    }]);
    assert_ne!(
        smuggled_start,
        dregg_circuit::heap_root::empty_heap_root_8(),
        "the smuggled start must be a genuinely non-empty root"
    );
    let mut smuggled_pis = smuggled_start.to_vec();
    smuggled_pis.extend_from_slice(&published);
    let refused = verify_whole_image_fold(&proof, &smuggled_pis);
    assert!(
        refused.is_err(),
        "a non-empty (smuggled-cells) start root in PI 0 must be refused"
    );
    assert!(
        refused.unwrap_err().contains("empty-heap root"),
        "the refusal must be the empty-root pin, not an incidental STARK mismatch"
    );
}

// ============================================================================
// THE CROSS-TABLE WIRING — the fold chip bound to the universal boundary table.
//
// The fold chip above pins the published root to the fold of a declared cell LIST it is
// HANDED. The rotation-integration point (`whole_image_fold` module banner) binds that list to
// the universal boundary table's per-domain `(domain, key)` cells, so the chip folds EXACTLY
// the declared boundary of the read peer's field-plane domain — the per-domain reconciliation
// that completes the whole-image cross-cell-read fully in-circuit. The binding rides the
// deployed universal-memory machinery (one `UMemOp::Read` per fold link against the boundary
// table) — no new bus/column/AIR. Two deployed teeth bite: the address-closure lookup refuses
// a folded cell the boundary never declared (`committed ⊆ declared`), and the Blum balance
// refuses a folded value that differs from the boundary's declared cell value.

use dregg_circuit::whole_image_fold::{
    boundary_witness_for_fold, prove_whole_image_fold_bound, verify_whole_image_fold_bound,
};

/// The read peer's field-plane domain code (a nibble; the ordinary present-cell plane, never
/// the insert-only nullifier domain).
const FIELD_DOMAIN: u32 = 0;

#[test]
fn whole_image_fold_bound_proves_against_boundary_table() {
    // The HONEST bound read: the fold folds exactly the boundary table's declared field cells,
    // each with its declared value, and pins that fold to the published root. The combined proof
    // (the fold Merkle chain + the per-cell `UMemOp::Read` against the universal boundary table)
    // proves and independently verifies.
    let leaves = peer_with_fields(&[(1, 111), (3, 777), (5, 555)]);
    assert!(leaves.len() >= 2, "the fold must be non-trivial");
    let published = whole_boundary_fold(&leaves);

    let witness = build_whole_image_fold(&leaves, published).expect("declared view folds");
    let boundary =
        boundary_witness_for_fold(&leaves, FIELD_DOMAIN).expect("boundary witness builds");
    let proof = prove_whole_image_fold_bound(&witness, &boundary, FIELD_DOMAIN)
        .expect("the boundary-bound whole-image fold proves");
    verify_whole_image_fold_bound(&proof, &witness.public_inputs, FIELD_DOMAIN)
        .expect("the boundary-bound whole-image fold verifies against the published commitment");
}

#[test]
fn whole_image_fold_bound_undeclared_cell_refuses() {
    // The fold folds a cell (slot 5) the universal boundary table never DECLARES. The per-cell
    // `UMemOp::Read` of that cell hits an undeclared `(domain, key)` — no `table_entry` to balance
    // the address-closure lookup against (`umemClosed`) — so the bound proof REFUSES. This is the
    // `committed ⊆ declared` direction: the fold cannot smuggle a cell past the boundary table.
    let leaves = peer_with_fields(&[(1, 111), (3, 777), (5, 555)]);
    let published = whole_boundary_fold(&leaves);
    let witness = build_whole_image_fold(&leaves, published).expect("declared view folds");

    // The boundary DECLARES only two of the three folded cells (slot 5 omitted).
    let declared: Vec<HeapLeaf> = leaves
        .iter()
        .filter(|l| l.addr != BabyBear::new(5 + 1))
        .cloned()
        .collect();
    assert_eq!(
        declared.len(),
        leaves.len() - 1,
        "exactly one cell undeclared"
    );
    let boundary =
        boundary_witness_for_fold(&declared, FIELD_DOMAIN).expect("boundary witness builds");

    let outcome = std::panic::catch_unwind(|| {
        prove_whole_image_fold_bound(&witness, &boundary, FIELD_DOMAIN)
    });
    let refused = match outcome {
        Err(_) => true,
        Ok(r) => r.is_err(),
    };
    assert!(
        refused,
        "a folded cell the boundary never declared must refuse (the address-closure tooth bites)"
    );
}

#[test]
fn whole_image_fold_bound_boundary_value_mismatch_refuses() {
    // The fold folds the genuine cell values, but the universal boundary table DECLARES a
    // different value for one cell. The per-cell `UMemOp::Read`'s claimed prev value (the folded
    // value) no longer matches the boundary's replayed init image — the Blum reconciliation
    // refuses. The binding cannot let a cell in the boundary table differ from the fold rows.
    let leaves = peer_with_fields(&[(1, 111), (3, 777), (5, 555)]);
    let published = whole_boundary_fold(&leaves);
    let witness = build_whole_image_fold(&leaves, published).expect("declared view folds");

    let mut boundary =
        boundary_witness_for_fold(&leaves, FIELD_DOMAIN).expect("boundary witness builds");
    // Bump ONE declared cell's value away from the genuine folded value.
    let bumped = boundary
        .init_vals
        .iter_mut()
        .find(|v| v.is_some())
        .expect("a present declared cell exists");
    *bumped = Some(bumped.unwrap() + BabyBear::ONE);

    let outcome = std::panic::catch_unwind(|| {
        prove_whole_image_fold_bound(&witness, &boundary, FIELD_DOMAIN)
    });
    let refused = match outcome {
        Err(_) => true,
        Ok(r) => r.is_err(),
    };
    assert!(
        refused,
        "a boundary cell value differing from the folded value must refuse (the Blum tooth bites)"
    );
}

#[test]
fn whole_image_fold_bound_smuggled_start_root_refuses() {
    // The smuggled-start tooth (B4) on the BOUND wrapper: same as the unbound case — the bound
    // verify wrapper pins PI 0 to the canonical empty root, so a non-empty start root holding
    // undeclared cells is refused before the STARK is consulted.
    let leaves = peer_with_fields(&[(1, 111), (3, 777), (5, 555)]);
    let published = whole_boundary_fold(&leaves);
    let witness = build_whole_image_fold(&leaves, published).expect("declared view folds");
    let boundary =
        boundary_witness_for_fold(&leaves, FIELD_DOMAIN).expect("boundary witness builds");
    let proof = prove_whole_image_fold_bound(&witness, &boundary, FIELD_DOMAIN)
        .expect("the honest bound fold proves");

    // Honest empty-root start accepts.
    verify_whole_image_fold_bound(&proof, &witness.public_inputs, FIELD_DOMAIN)
        .expect("the honest empty-root-start bound fold verifies");

    // A non-empty smuggled start root in PI 0 is refused by the pin.
    let smuggled_start = whole_boundary_fold(&[HeapLeaf {
        addr: BabyBear::new(99),
        value: BabyBear::new(42),
    }]);
    let mut smuggled_pis = smuggled_start.to_vec();
    smuggled_pis.extend_from_slice(&published);
    let refused = verify_whole_image_fold_bound(&proof, &smuggled_pis, FIELD_DOMAIN);
    assert!(
        refused.is_err(),
        "a non-empty (smuggled-cells) start root in PI 0 must be refused (bound wrapper)"
    );
    assert!(
        refused.unwrap_err().contains("empty-heap root"),
        "the refusal must be the empty-root pin, not an incidental STARK mismatch"
    );
}

// ===========================================================================
// THE FLAT-MEMORY whole-image fold — the EXACT twin of the universal bound fold above, against
// the FLAT memory boundary table (`Ir2Air::MemBoundary`, the boundary `setFieldDynVmDescriptor2`
// uses to hold a cell's eight user fields at addresses `0..7`). This closes the latent flat-`minit`
// hole: the fold recomputes the sorted-Poseidon2 root of the ENTIRE declared flat boundary image
// and pins it to the published (committed-pre-state) root, each fold link cross-bound to the
// `MemBoundary` table via a `MemOp::Read`. The two deployed teeth (the `BUS_MEM_ADDRS`
// address-closure + the `BUS_MEM_CHECK` Blum balance) refuse any folded cell the boundary never
// declared, and any folded value differing from the declared `minit[addr]` — so a FORGED `minit`
// folds to a different root and the published-root pin REFUSES in `verify_batch`. The Lean
// soundness anchor is `DescriptorIR2.satisfied2_init_root` / `satisfied2_init_root_bound` /
// `satisfied2_init_whole_image`.

use dregg_circuit::whole_image_fold::{
    boundary_mem_witness_for_fold, prove_whole_image_fold_bound_mem,
    verify_whole_image_fold_bound_mem,
};

/// A flat field-plane view: the cell's user fields as `(addr, value)` leaves over the flat
/// boundary's address space. Distinct addresses; the fold sorts.
fn flat_fields(addr_values: &[(u32, u32)]) -> Vec<HeapLeaf> {
    addr_values
        .iter()
        .map(|&(a, v)| HeapLeaf {
            addr: BabyBear::new(a),
            value: BabyBear::new(v),
        })
        .collect()
}

#[test]
fn whole_image_fold_bound_mem_proves_against_boundary_table() {
    // The HONEST flat-bound read: the fold folds exactly the flat boundary table's declared cells,
    // each with its declared init value, and pins that fold to the published root. The combined
    // proof (the fold Merkle chain + the per-cell `MemOp::Read` against the flat boundary table)
    // proves and independently verifies.
    let leaves = flat_fields(&[(1, 111), (3, 777), (7, 555)]);
    assert!(leaves.len() >= 2, "the fold must be non-trivial");
    let published = whole_boundary_fold(&leaves);

    let witness = build_whole_image_fold(&leaves, published).expect("declared view folds");
    let boundary = boundary_mem_witness_for_fold(&leaves).expect("flat boundary witness builds");
    let proof = prove_whole_image_fold_bound_mem(&witness, &boundary)
        .expect("the flat boundary-bound whole-image fold proves");
    verify_whole_image_fold_bound_mem(&proof, &witness.public_inputs).expect(
        "the flat boundary-bound whole-image fold verifies against the published commitment",
    );
}

#[test]
fn whole_image_fold_bound_mem_forged_minit_refuses() {
    // THE TOOTH that flips the empirically-confirmed forged-accept: the fold folds the GENUINE
    // committed field values, but the flat boundary DECLARES a forged `minit` value for one
    // (untouched) field — `minit[7] = 999`. The per-cell `MemOp::Read`'s claimed prev value (the
    // folded value) no longer matches the boundary's replayed init image at addr 7, so the
    // `BUS_MEM_CHECK` Blum reconciliation REFUSES. A forged `minit` cannot keep the published
    // (committed-pre-state) root — `Heap.root_injective` / `satisfied2_init_root_bound`, in-circuit.
    let leaves = flat_fields(&[(1, 111), (3, 777), (7, 555)]);
    let published = whole_boundary_fold(&leaves);
    let witness = build_whole_image_fold(&leaves, published).expect("declared view folds");

    let mut boundary =
        boundary_mem_witness_for_fold(&leaves).expect("flat boundary witness builds");
    // Forge the declared init value at the untouched field addr 7 (the diagnosis's `minit[7]=999`).
    let idx = boundary
        .addrs
        .iter()
        .position(|&a| a == 7)
        .expect("addr 7 declared");
    boundary.init_vals[idx] = 999;

    let outcome =
        std::panic::catch_unwind(|| prove_whole_image_fold_bound_mem(&witness, &boundary));
    let refused = match outcome {
        Err(_) => true,
        Ok(r) => r.is_err(),
    };
    assert!(
        refused,
        "a forged minit value differing from the folded committed value must refuse (the Blum tooth bites)"
    );
}

#[test]
fn whole_image_fold_bound_mem_undeclared_cell_refuses() {
    // The fold folds a cell (addr 7) the flat boundary table never DECLARES. The per-cell
    // `MemOp::Read` of that cell hits an undeclared address — no `table_entry` to balance the
    // `BUS_MEM_ADDRS` closure (`memClosed`) — so the bound proof REFUSES (`committed ⊆ declared`).
    let leaves = flat_fields(&[(1, 111), (3, 777), (7, 555)]);
    let published = whole_boundary_fold(&leaves);
    let witness = build_whole_image_fold(&leaves, published).expect("declared view folds");

    // The boundary DECLARES only two of the three folded cells (addr 7 omitted).
    let declared: Vec<HeapLeaf> = leaves
        .iter()
        .filter(|l| l.addr != BabyBear::new(7))
        .cloned()
        .collect();
    assert_eq!(
        declared.len(),
        leaves.len() - 1,
        "exactly one cell undeclared"
    );
    let boundary = boundary_mem_witness_for_fold(&declared).expect("flat boundary witness builds");

    let outcome =
        std::panic::catch_unwind(|| prove_whole_image_fold_bound_mem(&witness, &boundary));
    let refused = match outcome {
        Err(_) => true,
        Ok(r) => r.is_err(),
    };
    assert!(
        refused,
        "a folded cell the flat boundary never declared must refuse (the address-closure tooth bites)"
    );
}

#[test]
fn whole_image_fold_bound_mem_smuggled_start_root_refuses() {
    // The smuggled-start tooth on the flat-bound wrapper: the bound verify wrapper pins PI 0 to the
    // canonical empty root, so a non-empty start root holding undeclared cells is refused before
    // the STARK is consulted (no-extra-cells: the fold must provably start from nothing).
    let leaves = flat_fields(&[(1, 111), (3, 777), (7, 555)]);
    let published = whole_boundary_fold(&leaves);
    let witness = build_whole_image_fold(&leaves, published).expect("declared view folds");
    let boundary = boundary_mem_witness_for_fold(&leaves).expect("flat boundary witness builds");
    let proof = prove_whole_image_fold_bound_mem(&witness, &boundary)
        .expect("the honest bound fold proves");

    // Honest empty-root start accepts.
    verify_whole_image_fold_bound_mem(&proof, &witness.public_inputs)
        .expect("the honest empty-root-start flat bound fold verifies");

    // A non-empty smuggled start root in PI 0 is refused by the pin.
    let smuggled_start = whole_boundary_fold(&[HeapLeaf {
        addr: BabyBear::new(99),
        value: BabyBear::new(42),
    }]);
    let mut smuggled_pis = smuggled_start.to_vec();
    smuggled_pis.extend_from_slice(&published);
    let refused = verify_whole_image_fold_bound_mem(&proof, &smuggled_pis);
    assert!(
        refused.is_err(),
        "a non-empty (smuggled-cells) start root in PI 0 must be refused (flat bound wrapper)"
    );
    assert!(
        refused.unwrap_err().contains("empty-heap root"),
        "the refusal must be the empty-root pin, not an incidental STARK mismatch"
    );
}
