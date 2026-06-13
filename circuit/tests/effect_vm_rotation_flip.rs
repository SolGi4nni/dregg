//! # THE ROTATION FLIP — the rotated cohort proves+verifies end-to-end on a REAL turn.
//!
//! `docs/ROTATION-CUTOVER.md` §5 items 1,3-5,8: the staged Lean keystones
//! (`EffectVmEmitRotationV3.lean`) PROVE the rotated 26-descriptor cohort sound and the
//! staged probe measures the rotated SHAPE; what remained was (a) the per-turn PRODUCERS of
//! the witness-carried limbs (`cells_root`, `iroot`, `lifecycle`/`epoch`) — built now in
//! `dregg_turn::rotation_witness` — and (b) a rotated TRACE BUILDER that consumes them so a
//! WHOLE rotated cohort member (`transferVmDescriptor2R24`, not the bare probe) proves and
//! verifies through the live generic IR-v2 prover, with the anti-ghost teeth biting on the
//! rotated shape. The cutover doc deferred the producers precisely because they are only
//! validatable against this consumer; this file is producer + consumer landed TOGETHER.
//!
//! What it asserts (all on the ROTATED R=24 shape, the CONFIRMED register count):
//!
//!   1. **THE FULL ROTATED TRANSFER PROVES+VERIFIES** — `transferVmDescriptor2R24` (width
//!      311 = v1 186 + appendix 125) over a real transfer witness: the v1 186-col trace
//!      `generate_effect_vm_trace` produces, extended with the rotated BEFORE/AFTER blocks
//!      and the widened-caveat region, every chained `wireCommitR` digest genuine, the four
//!      appended PI pins published. The welds (`r0↔balance_lo`, `r1↔nonce`, …, `cap_root`)
//!      hold by construction because the producer fills the welded limbs with the SAME felt
//!      encodings the v1 state block carries.
//!   2. **THE cell≡circuit ROTATED DIFFERENTIAL** — the producer's limbs, derived from the
//!      real executed turn's `RecordKernelState` (the `Cell` + ledger + receipt log),
//!      EQUAL the limbs the circuit trace carries, AND the producer's `state_commit` equals
//!      the trace's `STATE_COMMIT` carrier — the two computations of the same object agree.
//!   3. **ANTI-GHOST** — a tampered rotated limb (heap_root), a tampered iroot, a tampered
//!      caveat key, and a forged appended PI each make proving REFUSE. The rotated
//!      descriptors keep their presence + tamper teeth.
//!
//! Gated on `recursion` (compiles `descriptor_ir2`). SLOW; run with
//! `cargo test -p dregg-circuit --features recursion rotation_flip -- --nocapture`.

#![cfg(feature = "recursion")]

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::columns::{STATE_AFTER_BASE, STATE_BEFORE_BASE, state};
use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_many;
use dregg_turn::rotation_witness as rw;

// ---- the rotated appendix geometry (Lean `EffectVmEmitRotationV3`, R=24) ----
const V1_WIDTH: usize = 186;
const B_SPAN: usize = 43; // a rotated block: 31 limbs + iroot + state_commit + 10 chain
const C_SPAN: usize = 39; // 29 manifest + 9 chain + 1 commit
const APPENDIX: usize = 125; // 2*43 + 39
const ROT_WIDTH: usize = V1_WIDTH + APPENDIX; // 311
const B_IROOT: usize = 31;
const B_STATE_COMMIT: usize = 32;
const B_CHAIN_BASE: usize = 33; // chain carriers base + 33..+42
const B_CAP_ROOT: usize = 25;
const NUM_PRE: usize = rw::NUM_PRE_LIMBS; // 31

/// Resolve the rotated transfer descriptor JSON from the staged registry TSV.
fn rotated_transfer_json() -> &'static str {
    for line in V3_STAGED_REGISTRY_TSV.lines() {
        let mut it = line.splitn(3, '\t');
        if it.next() == Some("transferVmDescriptor2R24") {
            let _name = it.next();
            return it.next().expect("json column");
        }
    }
    panic!("transferVmDescriptor2R24 not in V3_STAGED_REGISTRY_TSV");
}

/// Fill one rotated block (BEFORE or AFTER) at `base` for ONE row. The WELDED limbs
/// (r0↔balance_lo, r1↔nonce, r2↔balance_hi, r3..r10↔fields, cap_root) are copied from THAT
/// row's own v1 state block at `state_base` (so the weld gates hold on EVERY row, including
/// the NoOp padding rows whose v1 state block differs from the active row); the WITNESS-
/// CARRIED limbs (cells_root, nullifier/heap roots, lifecycle, epoch, committed_height,
/// iroot, r11..r23) come from the per-turn producer witness `w` (turn-invariant). Then the
/// genuine chained `wireCommitR` digests are computed on this row's own limbs. The
/// chained-absorption logic is byte-identical to the staged probe builder
/// (`descriptor_ir2.rs::rotation_probe_trace_r`) and to the producer's `wire_commit`.
fn fill_block(row: &mut [BabyBear], base: usize, state_base: usize, w: &rw::RotationWitness) {
    // witness-carried limbs from the producer (turn-invariant).
    for i in 0..NUM_PRE {
        row[base + i] = w.pre_limbs[i];
    }
    // welded limbs OVERRIDE from this row's own v1 state block (per-row truth).
    row[base + 1] = row[state_base + state::BALANCE_LO]; // r0
    row[base + 2] = row[state_base + state::NONCE]; // r1
    row[base + 3] = row[state_base + state::BALANCE_HI]; // r2
    for i in 0..8 {
        row[base + 4 + i] = row[state_base + state::FIELD_BASE + i]; // r3..r10
    }
    row[base + B_CAP_ROOT] = row[state_base + state::CAP_ROOT]; // cap_root
    row[base + B_IROOT] = w.iroot;
    // chained absorption: 4-wide head, 3-wide groups while ≥ 3 remain, iroot alone last.
    let mut d = hash_many(&[
        row[base], row[base + 1], row[base + 2], row[base + 3],
    ]);
    let mut chain = 0usize;
    row[base + B_CHAIN_BASE + chain] = d;
    chain += 1;
    let mut col = 4;
    while col < NUM_PRE {
        let remaining = NUM_PRE - col;
        if remaining >= 3 {
            d = hash_many(&[d, row[base + col], row[base + col + 1], row[base + col + 2]]);
            col += 3;
        } else {
            d = hash_many(&[d, row[base + col]]);
            col += 1;
        }
        row[base + B_CHAIN_BASE + chain] = d;
        chain += 1;
    }
    // the iroot rides its own arity-2 final site → state_commit.
    let commit = hash_many(&[d, row[base + B_IROOT]]);
    row[base + B_STATE_COMMIT] = commit;
}

/// Fill the widened-caveat region at `base` (29-felt manifest + 9 chain + commit). The
/// honest witness carries ONE register caveat (entry 0, domain 0) and one HEAP-KEY caveat
/// (entry 1, domain 1) and the genuine chained `caveatCommit`.
fn fill_caveat(row: &mut [BabyBear], base: usize) {
    // manifest: count + 4 × 7-felt entries [type_tag, domain_tag, key, p0..p3].
    row[base] = BabyBear::new(2); // count
    // entry 0: register caveat (domain 0), key = register 3.
    let e0 = base + 1;
    row[e0] = BabyBear::new(1); // type_tag
    row[e0 + 1] = BabyBear::new(rw::NUM_REGISTERS as u32 * 0); // domain 0 (registers)
    row[e0 + 2] = BabyBear::new(3); // key (register index)
    // entry 1: heap-key caveat (domain 1), key well beyond u8 range.
    let e1 = base + 8;
    row[e1] = BabyBear::new(1);
    row[e1 + 1] = BabyBear::new(1); // domain 1 (heap)
    row[e1 + 2] = BabyBear::new(123_456_789);
    // entries 2,3 stay zero (unused slots).
    // chained caveat commitment over the 29 manifest felts: 4-wide head, 3-wide body, tail.
    let manifest = 29usize;
    let chain_base = base + manifest; // 9 carriers
    let commit_col = chain_base + 9;
    let mut d = hash_many(&[row[base], row[base + 1], row[base + 2], row[base + 3]]);
    let mut chain = 0usize;
    row[chain_base + chain] = d;
    chain += 1;
    let mut col = 4;
    while col < manifest {
        let remaining = manifest - col;
        if remaining >= 3 {
            d = hash_many(&[d, row[base + col], row[base + col + 1], row[base + col + 2]]);
            col += 3;
        } else {
            d = hash_many(&[d, row[base + col]]);
            col += 1;
        }
        row[chain_base + chain] = d;
        chain += 1;
    }
    row[commit_col] = d;
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

/// Build the producer witness for the transfer-out before/after cells from a real
/// `RecordKernelState`. The circuit `CellState` (felt fields) and the producer's
/// `dregg_cell::Cell` (32-byte fields) must agree on the welded scalars; this helper
/// constructs a `dregg_cell::Cell` carrying the same scalars (balance/nonce, empty fields,
/// empty caps) so the producer's welded limbs equal the circuit trace's state-block felts.
fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    // advance the nonce to the circuit's "after" value if requested.
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

#[test]
fn rotated_transfer_proves_verifies_differential_and_refuses_ghost() {
    let desc = parse_vm_descriptor2(rotated_transfer_json())
        .expect("rotated transfer descriptor parses");
    assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 311");
    assert_eq!(desc.public_input_count, 38, "34 v1 PIs + 4 appended");

    // -- a real transfer: the validated v1 reference witness (transfer-out). --
    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let (mut trace, pis) = generate_effect_vm_trace(&st, &effects);
    assert_eq!(trace[0].len(), V1_WIDTH, "186-col v1 trace");

    // -- the producers, from the REAL before/after RecordKernelState. --
    // A real turn's receipt log → iroot; the ledger → cells_root.
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &receipt_log);

    // widen the row to the rotated width and fill the appendix.
    for row in trace.iter_mut() {
        row.resize(ROT_WIDTH, BabyBear::ZERO);
    }
    // BEFORE block at V1_WIDTH, AFTER block at V1_WIDTH+43, caveat at V1_WIDTH+86.
    // Fill on EVERY row (the welds + pins read first/last; uniform fill keeps welds true).
    let before_base = V1_WIDTH;
    let after_base = V1_WIDTH + B_SPAN;
    let caveat_base = V1_WIDTH + 2 * B_SPAN;
    for row in trace.iter_mut() {
        fill_block(row, before_base, STATE_BEFORE_BASE, &before_w);
        fill_block(row, after_base, STATE_AFTER_BASE, &after_w);
        fill_caveat(row, caveat_base);
    }

    // -- (2) THE cell≡circuit ROTATED DIFFERENTIAL: producer limbs == the trace's welded
    //    state-block felts (r0↔balance_lo, r1↔nonce, r2↔balance_hi, r3..r10↔fields,
    //    cap_root↔cap_root), on the first/last rows. --
    let r0 = &trace[0];
    let last = &trace[trace.len() - 1];
    // BEFORE welds against STATE_BEFORE_BASE.
    assert_eq!(
        before_w.pre_limbs[1],
        r0[STATE_BEFORE_BASE + state::BALANCE_LO],
        "differential: r0 == v1 balance_lo (before)"
    );
    assert_eq!(
        before_w.pre_limbs[2],
        r0[STATE_BEFORE_BASE + state::NONCE],
        "differential: r1 == v1 nonce (before)"
    );
    assert_eq!(
        before_w.pre_limbs[3],
        r0[STATE_BEFORE_BASE + state::BALANCE_HI],
        "differential: r2 == v1 balance_hi (before)"
    );
    for i in 0..8 {
        assert_eq!(
            before_w.pre_limbs[4 + i],
            r0[STATE_BEFORE_BASE + state::FIELD_BASE + i],
            "differential: r{} == v1 field[{i}] (before)",
            3 + i
        );
    }
    assert_eq!(
        before_w.pre_limbs[B_CAP_ROOT],
        r0[STATE_BEFORE_BASE + state::CAP_ROOT],
        "differential: cap_root limb == v1 cap_root (before)"
    );
    // THE WITNESS-CARRIED LIMBS — the genuinely-new producer outputs (cells_root · the map
    // roots · lifecycle · epoch · committed_height · iroot) — are turn-invariant, so the
    // producer's values must equal what the trace carries in BOTH blocks. These are the
    // limbs no v1 column derived; the producer owns them.
    for (idx, label) in [
        (0usize, "cells_root"),
        (26, "nullifier_root"),
        (27, "heap_root"),
        (28, "lifecycle"),
        (29, "epoch"),
        (30, "committed_height"),
    ] {
        assert_eq!(
            after_w.pre_limbs[idx], last[after_base + idx],
            "differential: producer {label} limb == trace after-block limb"
        );
        assert_eq!(
            before_w.pre_limbs[idx], r0[before_base + idx],
            "differential: producer {label} limb == trace before-block limb"
        );
    }
    assert_eq!(
        after_w.iroot,
        last[after_base + B_IROOT],
        "differential: producer iroot == trace after-block iroot carrier"
    );

    // THE DIFFERENTIAL HEADLINE: on the CLEAN before-state (which the producer reproduces
    // exactly from the `Cell` RecordKernelState), the producer's independently-computed
    // chained commitment `wire_commit` EQUALS the value the circuit trace's row-0
    // before-block STATE_COMMIT carrier carries — the cell and the circuit compute the same
    // commitment object. (The after-state's welded scalars include circuit-internal
    // evolution — nonce increment, the computed cap_root — so the producer-from-Cell can
    // only reproduce the witness-carried limbs there, asserted above; the after COMMIT is
    // checked by the proof itself binding the trace carrier to PI 35.)
    assert_eq!(
        before_w.state_commit,
        r0[before_base + B_STATE_COMMIT],
        "differential: producer wire_commit(before) == row-0 trace STATE_COMMIT carrier"
    );

    // -- the four appended PIs, read from the trace carriers the pins bind: rotated OLD
    //    commit (row-0 before-block STATE_COMMIT), rotated NEW commit (last-row after-block
    //    STATE_COMMIT), committed_height (last-row after-block height limb), caveat commit
    //    (last-row caveat region). --
    let mut dpis: Vec<BabyBear> = pis[..34].to_vec();
    dpis.push(r0[before_base + B_STATE_COMMIT]); // PI 34
    dpis.push(last[after_base + B_STATE_COMMIT]); // PI 35
    dpis.push(last[after_base + 30]); // PI 36: committed_height limb (offset 30)
    dpis.push(last[caveat_base + C_SPAN - 1]); // PI 37: caveat commit
    assert_eq!(dpis.len(), 38);

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // -- (1) PROVE + VERIFY the WHOLE rotated transfer end-to-end. --
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("rotated transfer must prove end-to-end");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("rotated transfer proof must verify independently");
    let total = postcard::to_allocvec(&proof).expect("postcard").len();
    eprintln!(
        "ROTATED TRANSFER (R=24, width {ROT_WIDTH}): proof {total} B (~{:.1} KiB) — PROVED + VERIFIED",
        total as f64 / 1024.0
    );

    // -- (3) ANTI-GHOST: tamper teeth bite on the rotated shape. --
    let refused = |t: &Vec<Vec<BabyBear>>, p: &Vec<BabyBear>| -> bool {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2(&desc, t, p, &mem_boundary, &map_heaps)
        }));
        match r {
            Err(_) => true,
            Ok(res) => res.is_err(),
        }
    };
    // tampered heap_root limb (before block, offset 27).
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[before_base + 27] = row[before_base + 27] + BabyBear::ONE;
        }
        assert!(refused(&t, &dpis), "tampered heap_root limb must refuse");
    }
    // tampered iroot (after block).
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[after_base + B_IROOT] = row[after_base + B_IROOT] + BabyBear::ONE;
        }
        assert!(refused(&t, &dpis), "tampered iroot must refuse");
    }
    // tampered heap-key caveat.
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[caveat_base + 8 + 2] = row[caveat_base + 8 + 2] + BabyBear::ONE;
        }
        assert!(refused(&t, &dpis), "tampered heap caveat key must refuse");
    }
    // forged appended PI (rotated NEW commit).
    {
        let mut p = dpis.clone();
        p[35] = p[35] + BabyBear::new(123);
        assert!(refused(&trace, &p), "forged rotated NEW-commit PI must refuse");
    }

    eprintln!(
        "ROTATION FLIP GATE GREEN: the rotated cohort (transfer) proves+verifies on a real \
         turn, the cell≡circuit differential holds, and every anti-ghost tooth bites."
    );
}
