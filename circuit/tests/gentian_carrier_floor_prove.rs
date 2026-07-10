//! # GENTIAN carrier-bound-floor gadget — REAL-STARK EXERCISE over `settleEscrowSatVmDescriptor2R24`
//! (STAGED / ADDITIVE — a new test file only; no deployed descriptor, producer, registry, VK, or
//! routing is touched).
//!
//! This file welds [`carrier_floor_weld::carrier_floor_gates`] (the decode + first-row selector-force +
//! caveat-uniformity gates that decode the escrow floor DIRECTLY from the caveat-commit-bound type-tag
//! columns 291/298/305/312) onto a CLONE of the deployed satisfaction descriptor
//! `settleEscrowSatVmDescriptor2R24`, then drives the assembled descriptor through
//! `prove_vm_descriptor2` / `verify_vm_descriptor2` over the genuine rotated settle producer
//! (`generate_rotated_settle_escrow_trace`).
//!
//! ## THE ROW-LOCALITY FIX (this is what the file now establishes — empirical, real `--release` STARK)
//!
//! An earlier shape of the carrier weld (`10ac36c54`) made the honest escrow-declared settle
//! UNSATISFIABLE: the selector-force gate was EVERY-ROW, and over the uniformly-`fill_caveat`'d escrow
//! manifest (`FLOOR = 1` every row) it forced `sel = 1` on the carry-forward PADDING rows, where the
//! base satisfaction gate `sel·(before_leg − Deposited)` then bit (`before_leg = Consumed` there). So
//! no selector assignment satisfied both gates over a height>1 trace (`OodEvaluationMismatch`), and the
//! teeth had no satisfiable baseline to bite against.
//!
//! The fix (`carrier_floor_weld`): (1) scope the selector-force to the FIRST (settle) row
//! (`Boundary{First}`) so it is INERT on padding ⟹ the honest settle is SATISFIABLE while the `sel = 0`
//! dodge stays closed on the settle row; (2) add four cross-row caveat-uniformity `windowGate`s
//! (`nxt(tag_k) − loc(tag_k) == 0`) coupling the row-0 decode to the LAST-row-pinned committed caveat
//! (PI 45). This file proves, in real `--release` STARKs:
//!   * the honest escrow-declared settle PROVES + VERIFIES (the satisfiability positive control — the
//!     keystone: an honest settle must *prove*, not merely "no false reject");
//!   * the no-escrow settle still PROVES + VERIFIES (the inert control);
//!   * a forged PARTIAL / PHANTOM settle on a declared-escrow cell is REFUSED (the satisfaction teeth);
//!   * the `sel = 0` dodge on the settle row is REFUSED (the first-row force tooth);
//!   * a forged NON-UNIFORM caveat manifest (no-escrow on the settle row, escrow committed to PI 45) is
//!     REFUSED (the uniformity tooth — the decode/commit decoupling closed).
//!
//! SLOW (full batch STARKs). Run:
//!   `cargo test -p dregg-circuit --test gentian_carrier_floor_prove --release -- --nocapture \
//!    --test-threads=1`

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::CellState;
use dregg_circuit::effect_vm::authority_digest_weld::FLOOR_ESCROW_COL;
use dregg_circuit::effect_vm::carrier_floor_weld::{
    bit_col, carrier_floor_gates, caveat_tag_col, inv_col, or_col,
};
use dregg_circuit::effect_vm::columns::rotation::caveat as cav;
use dregg_circuit::effect_vm::pi::{
    SETTLE_ESCROW_STATUS_CONSUMED, SETTLE_ESCROW_STATUS_DEPOSITED, SLOT_CAVEAT_TAG_SETTLE_ESCROW,
};
use dregg_circuit::effect_vm::satisfaction_weld::ESCROW_SEL_COL;
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, RotatedCaveatEntry, RotatedCaveatManifest, empty_caveat_manifest,
    generate_rotated_settle_escrow_trace, generate_rotated_settle_escrow_trace_forged,
};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_turn::rotation_witness as rw;

const LEG_A: usize = 0;
const LEG_B: usize = 1;
const DEP: u32 = SETTLE_ESCROW_STATUS_DEPOSITED;
const CON: u32 = SETTLE_ESCROW_STATUS_CONSUMED;
const EMPTY: u32 = 0;

// ----------------------------------------------------------------------------------------------------
// Fixtures (residue-free producer cell + rotation witnesses).
// ----------------------------------------------------------------------------------------------------

fn welded_escrow_json() -> &'static str {
    V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some("settleEscrowSatVmDescriptor2R24") {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .expect("settleEscrowSatVmDescriptor2R24 in V3_STAGED_REGISTRY_TSV")
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

fn producer_cell(balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

fn carrier_inputs() -> (CellState, RotatedBlockWitness, RotatedBlockWitness) {
    let balance: i64 = 100_000;
    let initial_state = CellState::new(balance as u64, 0);
    let cell = producer_cell(balance);
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let w = rw::produce(
        &cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );
    (initial_state, bridge(&w), bridge(&w))
}

/// An escrow-DECLARING caveat manifest: slot 0 type tag = `SLOT_CAVEAT_TAG_SETTLE_ESCROW` (17), so the
/// bound type-tag column `caveat_tag_col(0)` (= 291) reads 17 and the genuine `caveatCommit` (PI 45)
/// reflects it.
fn escrow_manifest() -> RotatedCaveatManifest {
    let mut m = RotatedCaveatManifest::default();
    m.entries[0] = RotatedCaveatEntry {
        type_tag: SLOT_CAVEAT_TAG_SETTLE_ESCROW,
        domain_tag: cav::DOMAIN_REGISTERS,
        key: BabyBear::ZERO,
        params: [BabyBear::ZERO; 4],
    };
    m
}

// ----------------------------------------------------------------------------------------------------
// The carrier descriptor: clone the deployed escrow descriptor, extend with the carrier gates, widen.
// ----------------------------------------------------------------------------------------------------

fn carrier_descriptor() -> EffectVmDescriptor2 {
    let mut desc =
        parse_vm_descriptor2(welded_escrow_json()).expect("welded escrow descriptor parses");
    assert_eq!(
        desc.public_input_count, 47,
        "rotated 46 + the selector slot"
    );
    desc.name = format!("{}-gentian-carrier-demo", desc.name);
    desc.constraints.extend(carrier_floor_gates()); // the carrier adds NO public input
    desc.trace_width = [
        or_col(cav::MAX_CAVEATS - 2) + 1, // or_col(2) is the widest aux column
        inv_col(cav::MAX_CAVEATS - 1) + 1,
        bit_col(cav::MAX_CAVEATS - 1) + 1,
        FLOOR_ESCROW_COL + 1,
        ESCROW_SEL_COL + 1,
        caveat_tag_col(cav::MAX_CAVEATS - 1) + 1,
        desc.trace_width,
    ]
    .into_iter()
    .max()
    .unwrap();
    desc
}

/// Fill the carrier decode aux columns (bit/inv/or + the running-OR final on `FLOOR_ESCROW_COL`) on one
/// row, EXACTLY per `carrier_floor_weld`'s decode-witness logic, reading the four bound type-tag columns
/// from the row. Does NOT touch `ESCROW_SEL_COL`. Rows are grown to `width` first.
fn fill_carrier_decode(row: &mut Vec<BabyBear>, width: usize) {
    if row.len() < width {
        row.resize(width, BabyBear::ZERO);
    }
    let mut running_or = 0u32;
    for k in 0..cav::MAX_CAVEATS {
        let tag = row[caveat_tag_col(k)].as_u32();
        let is_escrow = tag == SLOT_CAVEAT_TAG_SETTLE_ESCROW;
        let b = if is_escrow { 1 } else { 0 };
        row[bit_col(k)] = BabyBear::new(b);
        if !is_escrow {
            let d = BabyBear::new(tag) - BabyBear::new(SLOT_CAVEAT_TAG_SETTLE_ESCROW);
            row[inv_col(k)] = d.inverse().expect("nonzero tag-escrow has an inverse");
        } else {
            row[inv_col(k)] = BabyBear::ZERO;
        }
        let next_or = running_or | b;
        if k == 0 {
            row[or_col(0)] = BabyBear::new(next_or);
        } else if k < cav::MAX_CAVEATS - 1 {
            row[or_col(k)] = BabyBear::new(next_or);
        } else {
            row[FLOOR_ESCROW_COL] = BabyBear::new(next_or);
        }
        running_or = next_or;
    }
}

/// Build the honest settle carrier trace + PIs over `manifest`, then fill the carrier decode aux on
/// every row.
fn carrier_trace(
    manifest: &RotatedCaveatManifest,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, EffectVmDescriptor2) {
    let desc = carrier_descriptor();
    let (st, bw, aw) = carrier_inputs();
    let (mut trace, dpis) =
        generate_rotated_settle_escrow_trace(&st, &bw, &aw, manifest, LEG_A, LEG_B)
            .expect("the settle carrier must generate");
    assert_eq!(dpis.len(), 47);
    let w = desc.trace_width;
    for row in trace.iter_mut() {
        fill_carrier_decode(row, w);
    }
    (trace, dpis, desc)
}

/// Build a FORGED settle carrier trace (caller-chosen leg statuses) + PIs over `manifest`, then fill the
/// carrier decode aux on every row — the producer for the satisfaction teeth.
fn carrier_trace_forged(
    manifest: &RotatedCaveatManifest,
    before_status: (u32, u32),
    after_status: (u32, u32),
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, EffectVmDescriptor2) {
    let desc = carrier_descriptor();
    let (st, bw, aw) = carrier_inputs();
    let (mut trace, dpis) = generate_rotated_settle_escrow_trace_forged(
        &st,
        &bw,
        &aw,
        manifest,
        LEG_A,
        LEG_B,
        before_status,
        after_status,
    )
    .expect("the forged settle carrier must generate");
    assert_eq!(dpis.len(), 47);
    let w = desc.trace_width;
    for row in trace.iter_mut() {
        fill_carrier_decode(row, w);
    }
    (trace, dpis, desc)
}

fn mem() -> MemBoundaryWitness {
    MemBoundaryWitness::default()
}
type Heaps = Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>;

/// Does the descriptor accept this (trace, dpis)? `prove` may panic/refuse on an unsatisfiable witness;
/// `verify` is the real acceptance. Returns `true` iff a verifying proof exists.
fn accepts(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], dpis: &[BabyBear]) -> bool {
    let heaps: Heaps = vec![];
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_vm_descriptor2(desc, trace, dpis, &mem(), &heaps)
    })) {
        Ok(Ok(proof)) => verify_vm_descriptor2(desc, &proof, dpis).is_ok(),
        Ok(Err(_)) | Err(_) => false,
    }
}

// ====================================================================================================
// POSITIVE CONTROL 1: the carrier descriptor proves+verifies a NO-escrow settle (the inert control —
// the carrier aux columns do not collide with the descriptor's chip lanes, and the gadget never
// false-rejects where the cell declares no escrow).
// ====================================================================================================
#[test]
fn carrier_no_escrow_settle_proves_and_verifies() {
    let m = empty_caveat_manifest();
    let (trace, dpis, desc) = carrier_trace(&m);
    assert_eq!(
        trace[0][FLOOR_ESCROW_COL],
        BabyBear::ZERO,
        "no escrow ⟹ FLOOR 0"
    );
    assert_eq!(
        trace[0][ESCROW_SEL_COL],
        BabyBear::ONE,
        "generator selector ON on row 0"
    );
    assert!(
        accepts(&desc, &trace, &dpis),
        "the no-escrow settle MUST prove + verify against the carrier descriptor (inert control)"
    );
    eprintln!("CARRIER (no-escrow inert control): PROVED + VERIFIED.");
}

// ====================================================================================================
// POSITIVE CONTROL 2 (THE ROW-LOCALITY FIX KEYSTONE): the carrier descriptor proves+verifies an HONEST
// escrow-DECLARED settle. This is the satisfiability the earlier every-row force destroyed — the honest
// settle now has a satisfying multi-row witness (the first-row force is inert on the carry-forward
// padding rows, the uniformity gates hold over the uniform manifest).
// ====================================================================================================
#[test]
fn carrier_honest_escrow_settle_proves_and_verifies() {
    let m = escrow_manifest();
    let (trace, dpis, desc) = carrier_trace(&m);
    // the escrow tag IS bound (caveat_tag_col(0) = 17 on every row); FLOOR decodes 1; the selector is 1
    // on the settle row.
    assert_eq!(
        trace[0][caveat_tag_col(0)],
        BabyBear::new(SLOT_CAVEAT_TAG_SETTLE_ESCROW)
    );
    assert_eq!(
        trace[0][FLOOR_ESCROW_COL],
        BabyBear::ONE,
        "escrow ⟹ FLOOR 1"
    );
    assert_eq!(
        trace[0][ESCROW_SEL_COL],
        BabyBear::ONE,
        "selector ON on the settle row"
    );
    assert!(
        trace.len() > 1,
        "a real settle trace has carry-forward padding rows"
    );
    assert!(
        accepts(&desc, &trace, &dpis),
        "THE ROW-LOCALITY FIX: an HONEST escrow-declared settle MUST prove + verify (a satisfiable \
         baseline) — the every-row force made this unsatisfiable; the first-row scoping restores it"
    );
    eprintln!(
        "CARRIER (honest escrow settle): PROVED + VERIFIED — the satisfiable baseline EXISTS."
    );
}

// ====================================================================================================
// TOOTH 1 — a forged PARTIAL settle on a declared-escrow cell is REFUSED. The selector is forced 1 on
// the settle row (escrow declared, first-row force), so the leg-B AFTER gate `sel·(after_B − Consumed)`
// bites on the unswapped leg.
// ====================================================================================================
#[test]
fn carrier_forged_partial_settle_refused() {
    let m = escrow_manifest();
    // partial: leg B left Deposited after (only leg A consumed).
    let (trace, dpis, desc) = carrier_trace_forged(&m, (DEP, DEP), (CON, DEP));
    assert_eq!(
        trace[0][ESCROW_SEL_COL],
        BabyBear::ONE,
        "selector ON on the settle row"
    );
    assert!(
        !accepts(&desc, &trace, &dpis),
        "a forged PARTIAL settle on a declared-escrow cell MUST be refused (leg-B AFTER gate bites)"
    );
    eprintln!("CARRIER (forged partial settle): REFUSED.");
}

// ====================================================================================================
// TOOTH 2 — a forged PHANTOM settle (leg A never Deposited before) on a declared-escrow cell is
// REFUSED. The selector is forced 1, so the leg-A BEFORE gate `sel·(before_A − Deposited)` bites.
// ====================================================================================================
#[test]
fn carrier_forged_phantom_settle_refused() {
    let m = escrow_manifest();
    // phantom: leg A is Empty before (never locked); both Consumed after.
    let (trace, dpis, desc) = carrier_trace_forged(&m, (EMPTY, DEP), (CON, CON));
    assert!(
        !accepts(&desc, &trace, &dpis),
        "a forged PHANTOM settle on a declared-escrow cell MUST be refused (leg-A BEFORE gate bites)"
    );
    eprintln!("CARRIER (forged phantom settle): REFUSED.");
}

// ====================================================================================================
// TOOTH 3 — the `sel = 0` dodge on the settle row is REFUSED. A forger who, on a declared-escrow cell,
// tries to turn the selector OFF on the settle row (to render the satisfaction gates inert) trips the
// FIRST-ROW selector-force gate `FLOOR·(sel − 1) = 1·(0 − 1) = −1 ≠ 0`.
// ====================================================================================================
#[test]
fn carrier_sel_zero_dodge_on_settle_row_refused() {
    let m = escrow_manifest();
    let (mut trace, mut dpis, desc) = carrier_trace(&m);
    // Forge the selector OFF on the settle row + drop the PI 46 pin to match (so the PI binding does not
    // independently reject — isolate the first-row force tooth).
    trace[0][ESCROW_SEL_COL] = BabyBear::ZERO;
    dpis[46] = BabyBear::ZERO;
    assert_eq!(
        trace[0][FLOOR_ESCROW_COL],
        BabyBear::ONE,
        "escrow ⟹ FLOOR 1 on the settle row"
    );
    assert!(
        !accepts(&desc, &trace, &dpis),
        "the sel=0 dodge on the settle row MUST be refused — the first-row selector-force gate bites"
    );
    eprintln!("CARRIER (sel=0 dodge on settle row): REFUSED.");
}

// ====================================================================================================
// TOOTH 4 — a forged NON-UNIFORM caveat manifest is REFUSED. A forger commits the cell's REAL escrow
// manifest to PI 45 (the last row), but lights a NO-escrow manifest on the SETTLE row (so the row-0
// decode reads FLOOR = 0 and the first-row force goes inert) — the caveat-uniformity windowGate
// `nxt(tag_0) − loc(tag_0)` bites between the settle row (no-escrow) and the next row (escrow). This
// closes the decode/commit decoupling (the secondary defect).
// ====================================================================================================
#[test]
fn carrier_nonuniform_caveat_refused() {
    let m = escrow_manifest();
    let (mut trace, dpis, desc) = carrier_trace(&m);
    let w = desc.trace_width;
    // Forge the SETTLE row's slot-0 type tag to a non-escrow value (6) + re-fill its decode aux so the
    // decode is self-consistent (FLOOR = 0 there) — isolating the uniformity gate as the biting one.
    trace[0][caveat_tag_col(0)] = BabyBear::new(6);
    fill_carrier_decode(&mut trace[0], w);
    assert_eq!(
        trace[0][FLOOR_ESCROW_COL],
        BabyBear::ZERO,
        "forged no-escrow decode on the settle row"
    );
    // ...while the committed manifest (PI 45, last row) still declares escrow.
    assert_eq!(
        trace[trace.len() - 1][caveat_tag_col(0)],
        BabyBear::new(SLOT_CAVEAT_TAG_SETTLE_ESCROW),
        "the committed (last-row) manifest still declares escrow"
    );
    assert!(
        !accepts(&desc, &trace, &dpis),
        "a non-uniform caveat manifest (no-escrow on the settle row, escrow committed) MUST be refused \
         — the caveat-uniformity windowGate bites"
    );
    eprintln!("CARRIER (forged non-uniform caveat): REFUSED.");
}
