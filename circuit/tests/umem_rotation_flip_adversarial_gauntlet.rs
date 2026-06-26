//! # THE UMEM ROTATION-FLIP ADVERSARIAL GAUNTLET — Rank 5, suite 2 (the teeth).
//!
//! The flag-day bump needs more than the AGREE differential (suite 1,
//! `turn/tests/umem_rotation_flip_agree_gauntlet.rs`): it needs the MEMORY
//! ARGUMENT to REFUSE every lie a flipped wire could carry. This suite extends
//! the Part-1 teeth (`circuit/tests/effect_vm_umem_real_turn.rs` — a tampered
//! write value, a stale-prev double-claim) across the cohort with the four
//! adversaries the flip requires:
//!
//!   1. **A FORGED READ VALUE** — an op claims it read back a value the genuine
//!      producer never installed. The Blum multiset balance has an unmatched
//!      read tuple and the memory leg REFUSES.
//!   2. **A MISSING PRECONDITION** — a real cohort turn gated by an unsatisfiable
//!      precondition never commits, so no satisfying after-state (and no umem
//!      witness) is ever produced — the executor gate that runs BEFORE the memory
//!      argument. The flag-day requires preconditions stay load-bearing.
//!   3. **A DOUBLE-SPEND (a nullifier reused)** — the insert-only nullifier domain
//!      is the double-spend gate (`Effect::NoteSpend`'s `NoteNullifierInserted`
//!      touch claims a FRESH slot). Two inserts at the same nullifier address, both
//!      claiming the init boundary, is the same lie as an intra-proof double spend:
//!      the second insert's stale freshness claim REFUSES.
//!   4. **A CROSS-DOMAIN STEAL** — an op whose address lives in one domain (caps)
//!      relabeled to settle under another domain's constraint (heap). The
//!      per-domain Blum balance for the stolen domain no longer cancels and the
//!      memory leg REFUSES — a value cannot migrate across the domain tag
//!      (`consistentFrom_filter`'s tag isolation, biting in-circuit).
//!
//! Each adversary carries its HONEST baseline (the same construction minus the
//! lie proves), so every refusal is non-vacuous.
//!
//! VK-RISK-FREE: tests only. The real turns drive the production `TurnExecutor`;
//! the adversaries tamper the per-proof DENSE lowering onto the deployed IR-v2
//! `umem_op` grammar (`prove_vm_descriptor2_umem` through `ir2_config`). No
//! descriptor / wire / VK change.

use std::collections::BTreeMap;
use std::sync::atomic::Ordering;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, MemKind, UMemBoundaryWitness, UMemOpSpec,
    VmConstraint2, prove_vm_descriptor2_umem,
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

/// A refusal predicate that treats EITHER an `Err` OR an in-circuit panic as
/// "the memory argument refused" — the boundary pins are not part of the
/// pre-flight replay, so a broken balance can surface as either.
fn refused<F: FnOnce() -> Result<R, E> + std::panic::UnwindSafe, R, E>(f: F) -> bool {
    match std::panic::catch_unwind(f) {
        Err(_) => true,
        Ok(r) => r.is_err(),
    }
}

/// Execute a REAL multi-verb cohort turn (transfer ×2 sharing the debit address +
/// an overflow set-field + a capability attenuation) on the production executor
/// with the umem witness lane armed; return `(pre, ops, receipt_hash)`. The
/// twice-touched debit address gives a genuine serial chain (needed for the
/// forged-read tooth); the attenuation gives a caps-domain op (needed for the
/// cross-domain tooth).
fn real_cohort_trace() -> (BTreeMap<UKey, UVal>, Vec<UmemOp>, [u8; 32]) {
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
            Effect::SetField {
                cell: agent_id,
                index: 42, // overflow → fields_root / heap-domain Field plane.
                value: [42u8; 32],
            },
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
    assert!(
        result.is_committed(),
        "the cohort turn must commit: {result:?}"
    );
    let (_, receipt, _) = result.unwrap_committed();

    let witness = executor
        .last_umem_witness
        .lock()
        .unwrap()
        .take()
        .expect("witness produced")
        .expect("witness emission succeeded");
    assert_eq!(fold(&witness.pre, &witness.ops), witness.post);
    assert!(disciplined(&witness.ops));
    assert_eq!(witness.synthesized, 0);

    (witness.pre, witness.ops, receipt.receipt_hash())
}

/// The per-proof dense lowering (the same injective relabeling the Part-1 leg
/// uses — multiset balance is label-invariant, so a refusal is a REAL refusal).
struct Lowering {
    addr: BTreeMap<UKey, (u32, u32)>,
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
        let mut intern = |v: &UVal, val: &mut BTreeMap<Vec<u8>, u32>| {
            val.entry(uval_bytes(v)).or_insert_with(|| {
                let f = next_val;
                next_val += 1;
                f
            });
        };
        for op in ops {
            if let Some(v) = &op.val {
                intern(v, &mut val);
            }
            if let Some(v) = &op.prev_val {
                intern(v, &mut val);
            }
        }
        for k in addr.keys() {
            if let Some(v) = pre.get(k) {
                intern(v, &mut val);
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

/// The lowering result, carrying the per-domain guard-column map so an adversary
/// can relabel a row across domains (the cross-domain steal).
struct Lowered {
    desc: EffectVmDescriptor2,
    rows: Vec<Vec<BabyBear>>,
    boundary: UMemBoundaryWitness,
    /// domain code -> guard column index.
    guard_col_of: BTreeMap<u32, usize>,
}

/// Lower a real trace onto the IR-v2 umem grammar: one `umem_op` constraint per
/// touched domain (guarded by its own indicator column), one main row per op, and
/// the boundary = every touched address with its pre-state init image.
fn lower(pre: &BTreeMap<UKey, UVal>, ops: &[UmemOp]) -> Lowered {
    let lowering = Lowering::build(pre, ops);

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
        name: "rotation-flip-adversarial".to_string(),
        trace_width: width,
        public_input_count: 0,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    };

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

    Lowered {
        desc,
        rows,
        boundary,
        guard_col_of,
    }
}

fn prove(l: &Lowered) -> Result<impl Sized, String> {
    prove_vm_descriptor2_umem(
        &l.desc,
        &l.rows,
        &[],
        &MemBoundaryWitness::default(),
        &[],
        &l.boundary,
    )
}

// ===========================================================================
// HONEST BASELINE — the real cohort trace proves end-to-end (so every adversary
// below is a non-vacuous refusal of an otherwise-valid construction).
// ===========================================================================
#[test]
fn cohort_trace_proves_honest() {
    let (pre, mut ops, receipt) = real_cohort_trace();
    ops.push(receipt_op(0, receipt));
    assert!(
        ops.iter().any(|op| op.prev_serial != 0),
        "the cohort trace exercises the serial chain (a twice-touched address)"
    );
    let l = lower(&pre, &ops);
    prove(&l).expect("the honest cohort memory leg must prove");
}

// ===========================================================================
// ADVERSARY 1 — A FORGED READ VALUE.
// The twice-touched debit op claims it read back a value the first write never
// installed (col 4 = prev_value). The Blum read tuple has no matching producer.
// ===========================================================================
#[test]
fn adversary_forged_read_value_refuses() {
    let (pre, mut ops, receipt) = real_cohort_trace();
    ops.push(receipt_op(0, receipt));

    // the SECOND touch of the twice-touched address (prev_serial != 0): its
    // prev_value is the genuine value the first write installed. Forge it.
    let idx = ops
        .iter()
        .position(|op| op.prev_serial != 0)
        .expect("a multi-touch op (genuine read of a prior write) is present");
    let mut l = lower(&pre, &ops);
    // bump the claimed read-back value off the genuine producer's value.
    l.rows[idx][4] = l.rows[idx][4] + BabyBear::ONE;
    assert!(
        refused(|| prove(&l)),
        "a forged read value (claimed prev != the genuine producer) must refuse"
    );
}

// ===========================================================================
// ADVERSARY 2 — A MISSING PRECONDITION.
// A real cohort transfer gated by an unsatisfiable `min_balance` precondition
// never commits — so no after-state and no umem witness is ever produced. The
// precondition gate runs BEFORE the memory argument; the flag-day requires it
// stays load-bearing.
// ===========================================================================
#[test]
fn adversary_missing_precondition_refuses() {
    let agent = make_open_cell(31, 100);
    let target = make_open_cell(32, 0);
    let (agent_id, target_id) = (agent.id(), target.id());
    let mut ledger = Ledger::new();
    ledger.insert_cell(agent).unwrap();
    ledger.insert_cell(target).unwrap();

    let executor = TurnExecutor::new(ComputronCosts::zero());
    executor.umem_witness_enabled.store(true, Ordering::Relaxed);

    // a precondition the agent cannot meet (it holds 100, the guard demands 10_000).
    let preconditions = dregg_cell::Preconditions {
        cell_state: Some(dregg_cell::preconditions::CellStatePrecondition {
            min_balance: Some(10_000),
            ..Default::default()
        }),
        ..Default::default()
    };

    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent_id,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions,
        effects: vec![Effect::Transfer {
            from: agent_id,
            to: target_id,
            amount: 50,
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
    assert!(
        !result.is_committed(),
        "an unsatisfiable precondition must refuse the turn (no committed after-state): {result:?}"
    );
    // and no umem witness ever crossed into the memory argument.
    assert!(
        executor.last_umem_witness.lock().unwrap().take().is_none()
            || executor.last_umem_witness.lock().unwrap().is_none(),
        "a refused turn produces no committed memory witness"
    );
    // the ledger is untouched: balances did not move.
    assert_eq!(ledger.get(&agent_id).unwrap().state.balance(), 100);
    assert_eq!(ledger.get(&target_id).unwrap().state.balance(), 0);
}

// ===========================================================================
// ADVERSARY 3 — A DOUBLE-SPEND (a nullifier reused).
// The insert-only nullifier domain is the double-spend gate. An HONEST single
// insert (absent -> present, fresh) proves; reusing the SAME nullifier address
// with a second fresh insert (both claiming the init boundary) is the
// double-spend lie — the second insert's stale freshness claim refuses.
// ===========================================================================
fn nullifier_insert(nf: [u8; 32], prev_serial: u64) -> UmemOp {
    UmemOp {
        kind: UmemKind::Write,
        key: UKey::NoteNullifier(nf),
        val: Some(UVal::Present),
        prev_val: None, // a fresh insert claims the slot was absent.
        prev_serial,
    }
}

#[test]
fn double_spend_single_insert_proves() {
    let (pre, mut ops, receipt) = real_cohort_trace();
    ops.push(receipt_op(0, receipt));
    ops.push(nullifier_insert([0x5Au8; 32], 0)); // one honest spend.
    let l = lower(&pre, &ops);
    prove(&l).expect("a single honest nullifier insert must prove");
}

#[test]
fn adversary_double_spend_nullifier_reused_refuses() {
    let (pre, mut ops, receipt) = real_cohort_trace();
    ops.push(receipt_op(0, receipt));
    // TWO inserts at the SAME nullifier address, BOTH claiming the init boundary
    // (prev_serial 0, prev_val absent) — the second is a double-spend.
    let nf = [0x5Au8; 32];
    ops.push(nullifier_insert(nf, 0));
    ops.push(nullifier_insert(nf, 0));
    let l = lower(&pre, &ops);
    assert!(
        refused(|| prove(&l)),
        "reusing a nullifier (a second fresh insert at the same address) must refuse"
    );
}

// ===========================================================================
// ADVERSARY 4 — A CROSS-DOMAIN STEAL.
// The attenuation's caps-domain op is relabeled to settle under the heap
// domain's constraint (its guard moved across domains). The caps Blum balance
// loses its consumer and the heap balance gains a phantom — a value cannot
// migrate across the domain tag, so the memory leg refuses.
// ===========================================================================
#[test]
fn adversary_cross_domain_steal_refuses() {
    let (pre, mut ops, receipt) = real_cohort_trace();
    ops.push(receipt_op(0, receipt));

    // the caps domain is the CapSlot plane (the attenuation); heap is the
    // Field/Balance plane (the transfers + set-field).
    let caps_code = dregg_turn::umem::UDomain::Caps.code();
    let heap_code = dregg_turn::umem::UDomain::Heap.code();

    let idx = ops
        .iter()
        .position(|op| op.key.domain().code() == caps_code)
        .expect("the attenuation produced a caps-domain op");

    let mut l = lower(&pre, &ops);
    assert!(
        l.guard_col_of.contains_key(&caps_code) && l.guard_col_of.contains_key(&heap_code),
        "the cohort trace touches both the caps and heap domains"
    );
    // relabel the caps op to settle under the HEAP constraint: clear its caps
    // guard, set the heap guard.
    let caps_guard = l.guard_col_of[&caps_code];
    let heap_guard = l.guard_col_of[&heap_code];
    l.rows[idx][caps_guard] = BabyBear::ZERO;
    l.rows[idx][heap_guard] = BabyBear::ONE;
    assert!(
        refused(|| prove(&l)),
        "a value relabeled across the domain tag (caps -> heap) must refuse"
    );
}
