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

#![cfg(feature = "recursion")]

use std::collections::BTreeMap;
use std::sync::atomic::Ordering;
use std::time::Instant;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, MemKind, UMemBoundaryWitness, UMemOpSpec,
    VmConstraint2, prove_vm_descriptor2_umem, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::LeanExpr;
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
fn real_turn_trace() -> (
    BTreeMap<UKey, UVal>,
    Vec<UmemOp>,
    [u8; 32],
) {
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
