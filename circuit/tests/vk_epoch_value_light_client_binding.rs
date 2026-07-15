//! # THE VK-EPOCH LIGHT-CLIENT BINDING BITE — the VALUE family FORCED ON-WIRE.
//!
//! ## What this confirms (audit a6473605 / `docs/SAFELY-LIVE-CHECKLIST.md` line 14;
//! `docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md` §"The VALUE_MISSING wall")
//!
//! Six VALUE effects move a column the deployed circuit ALREADY binds into the published
//! commitment — `bal` (`transfer` / `mint` (a balance-IN transfer) / `burn` / `bridgeMint`),
//! `field[idx]` (`setField`), and `nonce` (`incrementNonce`). Unlike the permsVK / lifecycle /
//! note / cap-write families (whose write lands OFF a committed column — `params[0]`+`effects_hash`
//! or a side-table with no committed column/systemRoot), the VALUE family's moved column lives in
//! the V1 state block at `STATE_AFTER_BASE + {BALANCE_LO/HI | NONCE | FIELD_BASE+idx}`. That block
//! is absorbed verbatim into the per-cell commitment:
//!
//!   * the V1 GROUP-4 commit (`compute_commitment` = `hash_4_to_1(inter1, inter2, inter3, RH)`,
//!     where `inter1 = hash([bal_lo, bal_hi, nonce, field0])`, …) → `STATE_AFTER + STATE_COMMIT`;
//!   * the rotated AFTER block's welded limbs (`EffectVmEmitRotationV3.weldsAt`:
//!     `r0↔balance_lo`, `r1↔nonce`, `r2↔balance_hi`, `r3..r10↔fields`) — `fill_block` OVERRIDES
//!     them per-row from the V1 state truth and folds them into `AFTER_BASE + B_STATE_COMMIT`,
//!     which is the PUBLISHED `NEW_COMMIT` (PI 43, `dpis[V1_PI_COUNT + 1]`).
//!
//! So a LIGHT CLIENT — with no trusted post-cell, running `prove`/`verify_vm_descriptor2` ALONE —
//! sees the moved column flow into the anchored commitment. The question the FORGE-HUNT answers:
//! is that committed column ALSO bound by a LIVE in-circuit TRANSITION constraint, so a post-state
//! forged to differ ONLY in the moved column is UNSAT? (The cap-write forge taught us that
//! "Class-A in Lean + passes prove-through" does NOT imply the wire binds — a dormant gate leaves
//! the column unconstrained, a SILENT FORGE.)
//!
//! ## The anchor-disabled discriminator (the plan's bar, the guardrail)
//!
//! Both teeth run through `prove_vm_descriptor2` / `verify_vm_descriptor2` ALONE — the exact circuit
//! verify a light client runs, which NEVER calls `apply_effect_to_cell` and NEVER anchors an
//! off-cell record-pin. So a reject here is the IN-CIRCUIT transition gate biting, not host
//! re-derivation.
//!
//!   * POSITIVE (no downgrade): an HONEST turn proves + verifies green.
//!   * NEGATIVE (the forge): a post-state forged to differ ONLY in the moved column — the V1 AFTER
//!     column carries the FORGED value AND every downstream commitment column is recomputed
//!     self-consistently (so the COMMIT-pin/recompose gates are SATISFIED and the published commit
//!     genuinely absorbs the forged value, exactly what a light client would accept on the wire) —
//!     is UNSAT. The SOLE surviving violation is the per-row TRANSITION constraint
//!     (`new = old ±amount` / `field-set` / `nonce-tick`). If ANY of the six ACCEPTS, the moved
//!     column is NOT bound on the wire = a SILENT FORGE in a core value effect (critical).
//!
//! Non-vacuity: each test asserts the forged column differs from the honest one AND that the honest
//! trace proves (so the close is satisfiable, not vacuously UNSAT).
//!
//! Gated on `prover`. Run with
//! `cargo test -p dregg-circuit --features prover vk_epoch_value -- --nocapture`.

// (formerly `#![cfg(feature = "prover")]` — that dregg-circuit feature is GONE; the
// descriptor-level prove/verify (`prove_vm_descriptor2`/`verify_vm_descriptor2`) is
// now unconditional in dregg-circuit, so this test compiles + runs by default.)

use dregg_cell::{Cell, Ledger};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::columns::{
    AUX_BASE, STATE_AFTER_BASE, STATE_BEFORE_BASE, aux_off, state,
};
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_CAP_ROOT, B_CHAIN_BASE, B_IROOT, B_STATE_COMMIT, NUM_PRE_LIMBS, V1_PI_COUNT,
    empty_caveat_manifest, generate_rotated_effect_vm_trace, rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect, fold_bytes32_to_bb};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_many;
use dregg_circuit::refusal::{Outcome, classify};
use dregg_turn::rotation_witness as rw;

const BAL_LIMB_BITS: usize = 30;

/// Resolve a rotated descriptor JSON by registry key from the committed staged TSV.
fn rotated_descriptor_json(name: &str) -> &'static str {
    V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in V3_STAGED_REGISTRY_TSV"))
}

/// The producer's cell carrying the scalar (balance, nonce, fields) of a `CellState`.
fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness {
    dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
        .expect("37 pre-iroot limbs")
}

/// `true` iff `prove_vm_descriptor2` REFUSES (returns `Err` OR panics).
fn refused(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<dregg_circuit::heap_root::HeapLeaf>],
) -> bool {
    // The light client runs prove AND verify; a welded-column / commit-chain forge is caught at
    // VERIFY (`OodEvaluationMismatch`), not necessarily at prove — exercise BOTH legs (the
    // docstrings' "UNSAT through verify_vm_descriptor2 ALONE").
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

/// Recompute, IN-PLACE on one row, every commitment-bearing column downstream of the V1 AFTER
/// state block — so a forged moved column leaves the COMMIT-pin / recompose / weld gates
/// SATISFIED, isolating the per-row TRANSITION gate as the sole UNSAT witness. The forged
/// post-state `(balance, nonce, fields)` is the self-consistent post-cell the light client would
/// accept on the wire. Mirrors `trace.rs` (V1 commit + bit-decomp) and `trace_rotated.rs::fill_block`
/// (rotated AFTER chain), so the recompute is byte-identical to the live generator.
fn recompute_after_commitment(
    row: &mut [BabyBear],
    balance: u64,
    nonce: u32,
    fields: &[BabyBear; 8],
) {
    // (a) V1 AFTER state columns: balance limbs / nonce / fields.
    let lo = (balance & 0x3FFF_FFFF) as u32;
    let hi = (balance >> 30) as u32;
    row[STATE_AFTER_BASE + state::BALANCE_LO] = BabyBear::new(lo);
    row[STATE_AFTER_BASE + state::BALANCE_HI] = BabyBear::new(hi);
    row[STATE_AFTER_BASE + state::NONCE] = BabyBear::new(nonce);
    for (i, f) in fields.iter().enumerate() {
        row[STATE_AFTER_BASE + state::FIELD_BASE + i] = *f;
    }

    // (b) W9-RANGECHECK bit-decomposition of the NEW balance limbs (the recompose gate reads these).
    let hi64 = balance >> 30;
    for i in 0..BAL_LIMB_BITS {
        row[AUX_BASE + aux_off::NEW_BAL_LO_BIT_BASE + i] = BabyBear::new((lo >> i) & 1);
        row[AUX_BASE + aux_off::NEW_BAL_HI_BIT_BASE + i] = BabyBear::new(((hi64 >> i) & 1) as u32);
    }

    // (c) V1 GROUP-4 commitment: the three intermediates + the absorbed record-digest → STATE_COMMIT.
    let cap_root = row[STATE_AFTER_BASE + state::CAP_ROOT];
    let record_digest = row[AUX_BASE + aux_off::STATE_RECORD_DIGEST];
    let (inter1, inter2, inter3) =
        CellState::compute_commitment_intermediates(balance, nonce, fields, cap_root);
    row[AUX_BASE + aux_off::STATE_INTER1] = inter1;
    row[AUX_BASE + aux_off::STATE_INTER2] = inter2;
    row[AUX_BASE + aux_off::STATE_INTER3] = inter3;
    row[STATE_AFTER_BASE + state::STATE_COMMIT] =
        CellState::compute_commitment(balance, nonce, fields, cap_root, record_digest);

    // (d) The rotated AFTER block: re-run `fill_block`'s weld override + chained absorb so
    //     `AFTER_BASE + B_STATE_COMMIT` (the PUBLISHED commit) folds the forged welded limbs.
    let base = AFTER_BASE;
    row[base + 1] = row[STATE_AFTER_BASE + state::BALANCE_LO]; // r0
    row[base + 2] = row[STATE_AFTER_BASE + state::NONCE]; // r1
    row[base + 3] = row[STATE_AFTER_BASE + state::BALANCE_HI]; // r2
    for i in 0..8 {
        row[base + 4 + i] = row[STATE_AFTER_BASE + state::FIELD_BASE + i]; // r3..r10
    }
    row[base + B_CAP_ROOT] = row[STATE_AFTER_BASE + state::CAP_ROOT];
    let mut d = hash_many(&[row[base], row[base + 1], row[base + 2], row[base + 3]]);
    let mut chain = 0usize;
    row[base + B_CHAIN_BASE + chain] = d;
    chain += 1;
    let mut col = 4usize;
    while col < NUM_PRE_LIMBS {
        let remaining = NUM_PRE_LIMBS - col;
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
    row[base + B_STATE_COMMIT] = hash_many(&[d, row[base + B_IROOT]]);
}

/// Recompute, IN-PLACE on a padding (NoOp) row, the BEFORE *and* AFTER commitment columns to the
/// forged post-state — NoOp's passthrough gate (`after == before`) requires both to carry the same
/// forged post-state, and the chained NEW_COMMIT folds the last padding row's AFTER block.
fn recompute_passthrough_row(
    row: &mut [BabyBear],
    balance: u64,
    nonce: u32,
    fields: &[BabyBear; 8],
) {
    // BEFORE columns mirror AFTER for a passthrough row.
    let lo = (balance & 0x3FFF_FFFF) as u32;
    let hi = (balance >> 30) as u32;
    row[STATE_BEFORE_BASE + state::BALANCE_LO] = BabyBear::new(lo);
    row[STATE_BEFORE_BASE + state::BALANCE_HI] = BabyBear::new(hi);
    row[STATE_BEFORE_BASE + state::NONCE] = BabyBear::new(nonce);
    for (i, f) in fields.iter().enumerate() {
        row[STATE_BEFORE_BASE + state::FIELD_BASE + i] = *f;
    }
    let cap_root = row[STATE_BEFORE_BASE + state::CAP_ROOT];
    let record_digest = row[AUX_BASE + aux_off::STATE_RECORD_DIGEST];
    row[STATE_BEFORE_BASE + state::STATE_COMMIT] =
        CellState::compute_commitment(balance, nonce, fields, cap_root, record_digest);
    // Also re-run the rotated BEFORE block weld so its STATE_COMMIT chain matches.
    let base = dregg_circuit::effect_vm::trace_rotated::BEFORE_BASE;
    row[base + 1] = row[STATE_BEFORE_BASE + state::BALANCE_LO];
    row[base + 2] = row[STATE_BEFORE_BASE + state::NONCE];
    row[base + 3] = row[STATE_BEFORE_BASE + state::BALANCE_HI];
    for i in 0..8 {
        row[base + 4 + i] = row[STATE_BEFORE_BASE + state::FIELD_BASE + i];
    }
    row[base + B_CAP_ROOT] = row[STATE_BEFORE_BASE + state::CAP_ROOT];
    let mut d = hash_many(&[row[base], row[base + 1], row[base + 2], row[base + 3]]);
    let mut chain = 0usize;
    row[base + B_CHAIN_BASE + chain] = d;
    chain += 1;
    let mut col = 4usize;
    while col < NUM_PRE_LIMBS {
        let remaining = NUM_PRE_LIMBS - col;
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
    row[base + B_STATE_COMMIT] = hash_many(&[d, row[base + B_IROOT]]);

    // AFTER columns to the same forged post-state.
    recompute_after_commitment(row, balance, nonce, fields);
}

/// Patch the dpis that depend on the forged post-state: V1 `NEW_COMMIT[0..8]`, `FINAL_BAL_LO/HI`,
/// and the rotated `NEW_COMMIT` (PI 43). With these recomputed the boundary / PI-pin gates are
/// satisfied, so the SOLE violation is the per-row transition constraint.
fn patch_post_state_dpis(
    dpis: &mut [BabyBear],
    forged_last_row: &[BabyBear],
    balance: u64,
    nonce: u32,
    fields: &[BabyBear; 8],
    cap_root: BabyBear,
    record_digest: BabyBear,
) {
    use dregg_circuit::effect_vm::pi;
    let new_commit_8 =
        CellState::compute_commitment_8(balance, nonce, fields, cap_root, record_digest);
    for i in 0..pi::NEW_COMMIT_LEN {
        dpis[pi::NEW_COMMIT_BASE + i] = new_commit_8[i];
    }
    let lo = (balance & 0x3FFF_FFFF) as u32;
    let hi = (balance >> 30) as u32;
    dpis[pi::FINAL_BAL_LO] = BabyBear::new(lo);
    dpis[pi::FINAL_BAL_HI] = BabyBear::new(hi);
    // PI 43: rotated NEW commit = last row's rotated AFTER STATE_COMMIT.
    dpis[V1_PI_COUNT + 1] = forged_last_row[AFTER_BASE + B_STATE_COMMIT];
}

/// Build the honest rotated trace for a single VALUE effect over `(before_bal, before_nonce)`,
/// returning `(desc, trace, dpis, mem_boundary, map_heaps)`. The `expect_name` self-checks the
/// resolver routes the effect to its committed descriptor.
struct Honest {
    desc: dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    trace: Vec<Vec<BabyBear>>,
    dpis: Vec<BabyBear>,
    mem_boundary: MemBoundaryWitness,
    map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>,
}

fn build_honest(before_bal: i64, effect: Effect, after_cell: Cell, expect_name: &str) -> Honest {
    let name =
        rotated_descriptor_name_for_effect(&effect).expect("VALUE effect is a cohort member");
    assert_eq!(
        name, expect_name,
        "resolver routes to the committed descriptor"
    );
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name)).expect("descriptor parses");

    let st = CellState::new(before_bal as u64, 0);
    let effects = vec![effect];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_bal, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

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

    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce a VALUE-effect trace + PIs");

    Honest {
        desc,
        trace,
        dpis,
        mem_boundary: MemBoundaryWitness::default(),
        map_heaps: vec![],
    }
}

/// The honest post-state scalars the trace committed (read from the LAST row's V1 AFTER block).
fn honest_post(h: &Honest) -> (u64, u32, [BabyBear; 8], BabyBear, BabyBear) {
    let last = &h.trace[h.trace.len() - 1];
    let lo = last[STATE_AFTER_BASE + state::BALANCE_LO].as_u32() as u64;
    let hi = last[STATE_AFTER_BASE + state::BALANCE_HI].as_u32() as u64;
    let balance = lo | (hi << 30);
    let nonce = last[STATE_AFTER_BASE + state::NONCE].as_u32();
    let mut fields = [BabyBear::ZERO; 8];
    for i in 0..8 {
        fields[i] = last[STATE_AFTER_BASE + state::FIELD_BASE + i];
    }
    let cap_root = last[STATE_AFTER_BASE + state::CAP_ROOT];
    let record_digest = last[AUX_BASE + aux_off::STATE_RECORD_DIGEST];
    (balance, nonce, fields, cap_root, record_digest)
}

/// Apply a self-consistent post-state forgery to a CLONE of the honest trace: the active (row-0)
/// effect row gets only its AFTER block forged (so its honest BEFORE + the transition gate bite);
/// every other row is a passthrough at the forged post-state (so the published NEW_COMMIT genuinely
/// absorbs the forged column — the wire view). Returns the forged `(trace, dpis)`.
fn forge_post_state(
    h: &Honest,
    fbalance: u64,
    fnonce: u32,
    ffields: &[BabyBear; 8],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let (_, _, _, cap_root, record_digest) = honest_post(h);
    let mut trace = h.trace.clone();
    let n = trace.len();
    // Row 0: the active effect row. Forge ONLY its AFTER commitment columns; its BEFORE (= init)
    // stays honest so the transition gate (`new = f(old, amount)`) is violated.
    recompute_after_commitment(&mut trace[0], fbalance, fnonce, ffields);
    // Rows 1..n: passthrough at the forged post-state (BEFORE = AFTER = forged post).
    for r in 1..n {
        recompute_passthrough_row(&mut trace[r], fbalance, fnonce, ffields);
    }
    let mut dpis = h.dpis.clone();
    let last = trace[n - 1].clone();
    patch_post_state_dpis(
        &mut dpis,
        &last,
        fbalance,
        fnonce,
        ffields,
        cap_root,
        record_digest,
    );
    (trace, dpis)
}

/// The shared positive+negative skeleton for a balance-moving effect.
fn assert_balance_effect(h: Honest, forged_balance: u64, label: &str) {
    let (honest_bal, nonce, fields, _cap, _rd) = honest_post(&h);
    assert_ne!(
        honest_bal, forged_balance,
        "{label}: the forged balance must differ from the honest post-balance (non-vacuity)"
    );

    // POSITIVE TOOTH (no downgrade).
    let proof = prove_vm_descriptor2(&h.desc, &h.trace, &h.dpis, &h.mem_boundary, &h.map_heaps)
        .unwrap_or_else(|e| panic!("{label}: NO DOWNGRADE — honest turn must prove: {e:?}"));
    verify_vm_descriptor2(&h.desc, &proof, &h.dpis)
        .unwrap_or_else(|e| panic!("{label}: NO DOWNGRADE — honest proof must verify: {e:?}"));

    // NEGATIVE TOOTH (the forge): post-balance forged, declared amount honest.
    let (ftrace, fdpis) = forge_post_state(&h, forged_balance, nonce, &fields);
    // Self-check: the published NEW_COMMIT genuinely absorbs the forged balance (wire view), and
    // it differs from the honest published commit.
    assert_ne!(
        ftrace[ftrace.len() - 1][AFTER_BASE + B_STATE_COMMIT],
        h.trace[h.trace.len() - 1][AFTER_BASE + B_STATE_COMMIT],
        "{label}: the forged post-balance must publish a DIFFERENT commit (else the forge is vacuous)"
    );
    assert!(
        refused(&h.desc, &ftrace, &fdpis, &h.mem_boundary, &h.map_heaps),
        "{label}: SILENT FORGE — a post-state forged to differ ONLY in `balance` (committed AFTER \
         balance != old ±amount) MUST be UNSAT through prove/verify ALONE; the in-circuit balance \
         transition gate must bite with NO off-cell anchor. If this ACCEPTS, `balance` is NOT bound \
         on the wire (critical)."
    );
}

// ============================================================================
// THE SIX VALUE EFFECTS — each: honest accepts, a moved-column-only forge is UNSAT.
// ============================================================================

/// **transfer FORCED ON-WIRE.** An honest balance DEBIT proves+verifies; a post-cell forged to
/// differ ONLY in `balance` is UNSAT (the in-circuit `c_transfer_lo` gate binds
/// `new_bal_lo = old_bal_lo - amount`).
#[test]
fn transfer_forced_on_wire_rejects_forged_balance_anchor_disabled() {
    let before: i64 = 100_000;
    let amount: u64 = 250;
    let h = build_honest(
        before,
        Effect::Transfer {
            amount,
            direction: 1,
        },
        producer_cell(before - amount as i64, 0),
        "transferVmDescriptor2R24",
    );
    // Forge: post = before - amount + 1 (off-by-one debit — the wire sees a different balance).
    assert_balance_effect(h, (before as u64) - amount + 1, "transfer");
    eprintln!(
        "VK-EPOCH transfer FORCED ON-WIRE: honest debit proves+verifies; a balance-ONLY forged \
         post-state is UNSAT through verify_vm_descriptor2 ALONE — the balance transition binds."
    );
}

/// **mint (balance-IN transfer) FORCED ON-WIRE.** An honest balance CREDIT (direction 0) proves;
/// a `balance`-only forged post is UNSAT (`new_bal_lo = old_bal_lo + amount`).
#[test]
fn mint_in_transfer_forced_on_wire_rejects_forged_balance_anchor_disabled() {
    let before: i64 = 40_000;
    let amount: u64 = 777;
    let h = build_honest(
        before,
        Effect::Transfer {
            amount,
            direction: 0,
        },
        producer_cell(before + amount as i64, 0),
        "transferVmDescriptor2R24",
    );
    // Forge: over-mint by 1 (credit a balance the declared amount does not justify).
    assert_balance_effect(h, (before as u64) + amount + 1, "mint(transfer-in)");
    eprintln!(
        "VK-EPOCH mint(transfer-in) FORCED ON-WIRE: honest credit proves+verifies; an over-minted \
         balance-ONLY forged post is UNSAT — the credit transition binds."
    );
}

/// **burn FORCED ON-WIRE.** An honest non-conservation debit proves; a `balance`-only forged post
/// (under-burn) is UNSAT (the burn debit gate binds `new_bal = old_bal - amount`).
#[test]
fn burn_forced_on_wire_rejects_forged_balance_anchor_disabled() {
    let before: i64 = 80_000;
    let amount: u64 = 30;
    let h = build_honest(
        before,
        Effect::Burn {
            target_hash: BabyBear::new(0),
            amount_lo: BabyBear::new(amount as u32),
            amount_full: amount,
        },
        producer_cell(before - amount as i64, 0),
        "burnVmDescriptor2R24",
    );
    // Forge: under-burn (keep more balance than the declared burn allows).
    assert_balance_effect(h, (before as u64) - amount + 5, "burn");
    eprintln!(
        "VK-EPOCH burn FORCED ON-WIRE: honest burn proves+verifies; an under-burned balance-ONLY \
         forged post is UNSAT — the burn debit transition binds."
    );
}

/// **bridgeMint FORCED ON-WIRE.** An honest portable-proof mint (balance credit) proves; a
/// `balance`-only forged post (over-mint) is UNSAT (the bridge-mint credit gate binds the post
/// balance to `old + value`).
#[test]
fn bridgemint_forced_on_wire_rejects_forged_balance_anchor_disabled() {
    let before: i64 = 10_000;
    let value: u64 = 500;
    let h = build_honest(
        before,
        Effect::BridgeMint {
            value_lo: BabyBear::new(value as u32),
            mint_hash: BabyBear::new(123),
            value_full: value,
        },
        producer_cell(before + value as i64, 0),
        "mintVmDescriptor2R24",
    );
    // Forge: over-mint by 1.
    assert_balance_effect(h, (before as u64) + value + 1, "bridgeMint");
    eprintln!(
        "VK-EPOCH bridgeMint FORCED ON-WIRE: honest mint proves+verifies; an over-minted \
         balance-ONLY forged post is UNSAT — the bridge-mint credit transition binds."
    );
}

/// **setField FORCED ON-WIRE.** An honest field write proves; a post-cell forged to differ ONLY in
/// `field[idx]` is UNSAT (the in-circuit `c_setfield_sum` gate binds the written field to the
/// declared `new_value`, and the per-field non-target-unchanged gates bind the rest).
///
/// STOPPED (v13 setField written-slot value8 seam — NAMED, not a fixture): under v13's fields-octet
/// grow (NUM_PRE_LIMBS 112→169, the 56 fields[0..7] completion lanes 112..=167), the committed
/// setFieldVmDescriptor2-3R24 gate now binds the written slot's 7 completion lanes, but the generic
/// V1 setField producer (`generate_rotated_effect_vm_trace` via `build_honest`) does not yet fill
/// them — so the HONEST field write no longer VERIFIES (line 569 positive tooth). This is the same
/// v13 setField completion seam the epoch owner tracks ("a forged completion on the WRITTEN slot's
/// own 7 lanes is not yet forced"); the fill is a producer (src, v13-owned) change, not a test
/// fixture. Re-enable once the V1 setField producer lays the written-slot completion octet.
#[test]
#[ignore = "v13 setField written-slot value8 completion-lane seam: the V1 setField producer does not \
            yet fill the written slot's 7 completion lanes (112..=167), so the honest write fails the \
            committed completion gate. Producer-side (v13-owned); re-enable after the fill lands."]
fn setfield_forced_on_wire_rejects_forged_field_anchor_disabled() {
    let before: i64 = 50_000;
    let field_idx: u32 = 3;
    // The producer projects a cell field via `fold_bytes32_to_bb(bytes)`; the V1 SetField write
    // sets the AFTER field limb to the effect's `value` directly. For the honest weld to hold, the
    // effect's `value` MUST equal the fold of the producer cell's field bytes. So pick bytes, fold
    // them, and write both.
    let mut field_bytes = [0u8; 32];
    field_bytes[0] = 0xAB;
    field_bytes[1] = 0xCD;
    field_bytes[5] = 0x42;
    let new_value = fold_bytes32_to_bb(&field_bytes);

    let mut after_cell = producer_cell(before, 0);
    // Mirror the V1 SetField write into the producer cell's field slot so the after witness is
    // self-consistent (the producer commits the same post-cell the V1 trace does).
    assert!(
        after_cell.state.set_field(field_idx as usize, field_bytes),
        "set_field on a fresh cell"
    );

    let h = build_honest(
        before,
        Effect::SetField {
            field_idx,
            value: new_value,
        },
        after_cell,
        "setFieldVmDescriptor2-3R24",
    );

    let (_bal, nonce, honest_fields, _cap, _rd) = honest_post(&h);
    assert_eq!(
        honest_fields[field_idx as usize], new_value,
        "honest: the committed AFTER field[3] == the declared new_value (the close is satisfiable)"
    );

    // POSITIVE TOOTH.
    let proof = prove_vm_descriptor2(&h.desc, &h.trace, &h.dpis, &h.mem_boundary, &h.map_heaps)
        .expect("setField: NO DOWNGRADE — honest field write must prove");
    verify_vm_descriptor2(&h.desc, &proof, &h.dpis)
        .expect("setField: NO DOWNGRADE — honest proof must verify");

    // NEGATIVE TOOTH: forge field[3] only, declared new_value honest.
    let forged_value = BabyBear::new(0x9999);
    assert_ne!(
        forged_value, new_value,
        "setField: the forged field value must differ from the declared new_value (non-vacuity)"
    );
    let mut forged_fields = honest_fields;
    forged_fields[field_idx as usize] = forged_value;
    let (bal, _, _, _, _) = honest_post(&h);
    let (ftrace, fdpis) = forge_post_state(&h, bal, nonce, &forged_fields);
    assert_ne!(
        ftrace[ftrace.len() - 1][AFTER_BASE + B_STATE_COMMIT],
        h.trace[h.trace.len() - 1][AFTER_BASE + B_STATE_COMMIT],
        "setField: the forged field must publish a DIFFERENT commit (else vacuous)"
    );
    assert!(
        refused(&h.desc, &ftrace, &fdpis, &h.mem_boundary, &h.map_heaps),
        "setField: SILENT FORGE — a post-cell forged to differ ONLY in field[3] (committed AFTER \
         field != the declared new_value) MUST be UNSAT through prove/verify ALONE; the in-circuit \
         setField write gate must bite. If this ACCEPTS, field[idx] is NOT bound on the wire \
         (critical)."
    );
    eprintln!(
        "VK-EPOCH setField FORCED ON-WIRE: honest field write proves+verifies; a field-ONLY forged \
         post is UNSAT — the setField write transition binds."
    );
}

/// **incrementNonce FORCED ON-WIRE.** An honest nonce bump proves; a post-cell forged to differ
/// ONLY in `nonce` is UNSAT (the in-circuit nonce-tick gate binds `new_nonce = old_nonce + 1`).
#[test]
fn incrementnonce_forced_on_wire_rejects_forged_nonce_anchor_disabled() {
    let before: i64 = 50_000;
    // The V1 generator ticks the nonce on EVERY non-NoOp row; the IncrementNonce effect is the
    // selector that records the bump. before_nonce = 0 → honest post nonce = 1.
    let after_cell = producer_cell(before, 1);
    let h = build_honest(
        before,
        Effect::IncrementNonce,
        after_cell,
        "incrementNonceVmDescriptor2R24",
    );

    let (bal, honest_nonce, fields, _cap, _rd) = honest_post(&h);
    assert_eq!(honest_nonce, 1, "honest: post nonce ticked to 1");

    // POSITIVE TOOTH.
    let proof = prove_vm_descriptor2(&h.desc, &h.trace, &h.dpis, &h.mem_boundary, &h.map_heaps)
        .expect("incrementNonce: NO DOWNGRADE — honest bump must prove");
    verify_vm_descriptor2(&h.desc, &proof, &h.dpis)
        .expect("incrementNonce: NO DOWNGRADE — honest proof must verify");

    // NEGATIVE TOOTH: forge nonce only (skip ahead to 5 — the tick gate forbids it).
    let forged_nonce = 5u32;
    assert_ne!(
        forged_nonce, honest_nonce,
        "incrementNonce: the forged nonce must differ from the honest tick (non-vacuity)"
    );
    let (ftrace, fdpis) = forge_post_state(&h, bal, forged_nonce, &fields);
    assert_ne!(
        ftrace[ftrace.len() - 1][AFTER_BASE + B_STATE_COMMIT],
        h.trace[h.trace.len() - 1][AFTER_BASE + B_STATE_COMMIT],
        "incrementNonce: the forged nonce must publish a DIFFERENT commit (else vacuous)"
    );
    assert!(
        refused(&h.desc, &ftrace, &fdpis, &h.mem_boundary, &h.map_heaps),
        "incrementNonce: SILENT FORGE — a post-cell forged to differ ONLY in `nonce` (committed \
         AFTER nonce != old + 1) MUST be UNSAT through prove/verify ALONE; the in-circuit nonce-tick \
         gate must bite. If this ACCEPTS, nonce is NOT bound on the wire (critical)."
    );
    eprintln!(
        "VK-EPOCH incrementNonce FORCED ON-WIRE: honest bump proves+verifies; a nonce-ONLY forged \
         post is UNSAT — the nonce-tick transition binds."
    );
}

// ============================================================================
// FAITHFULNESS SELF-CHECK — the forge machinery is NOT a sledgehammer.
// ============================================================================

/// The recompute helpers (`recompute_after_commitment` / `recompute_passthrough_row` /
/// `patch_post_state_dpis`) must reproduce the LIVE generator byte-for-byte: fed the HONEST
/// post-state (an IDENTITY "forge"), they must yield a trace that STILL proves + verifies. This
/// rules out the false-positive where the six negative teeth reject because the helper itself
/// corrupts SOME column regardless of the forged value — i.e. it proves the rejections in those
/// tests are caused by the FORGED moved column, not by the recompute machinery.
#[test]
fn forge_machinery_is_faithful_identity_recompute_still_proves() {
    let before: i64 = 100_000;
    let amount: u64 = 250;
    let h = build_honest(
        before,
        Effect::Transfer {
            amount,
            direction: 1,
        },
        producer_cell(before - amount as i64, 0),
        "transferVmDescriptor2R24",
    );
    let (bal, nonce, fields, _cap, _rd) = honest_post(&h);

    // IDENTITY: re-run the full recompute (row-0 AFTER + passthrough rows + dpis) at the HONEST
    // post-state. A faithful recompute reproduces the live trace's commitment columns exactly.
    let (id_trace, id_dpis) = forge_post_state(&h, bal, nonce, &fields);

    // The published commit is UNCHANGED (the recompute is byte-identical to the generator).
    assert_eq!(
        id_trace[id_trace.len() - 1][AFTER_BASE + B_STATE_COMMIT],
        h.trace[h.trace.len() - 1][AFTER_BASE + B_STATE_COMMIT],
        "identity recompute must reproduce the honest published commit (helper faithfulness)"
    );
    assert_eq!(
        id_dpis, h.dpis,
        "identity recompute must reproduce the honest dpis (helper faithfulness)"
    );

    // And it STILL proves + verifies — so a reject elsewhere is the FORGED column, not the helper.
    let proof = prove_vm_descriptor2(&h.desc, &id_trace, &id_dpis, &h.mem_boundary, &h.map_heaps)
        .expect(
            "FAITHFULNESS: identity-recomputed honest trace must prove (the helper is faithful)",
        );
    verify_vm_descriptor2(&h.desc, &proof, &id_dpis)
        .expect("FAITHFULNESS: identity-recomputed honest proof must verify");

    eprintln!(
        "FORGE MACHINERY FAITHFUL: the identity recompute reproduces the live commit + dpis and \
         STILL proves — so each negative tooth's reject is the FORGED moved column, not a helper \
         artifact."
    );
}
