//! # GENTIAN carrier-bound-floor gadget — REAL-STARK EXERCISE over `settleEscrowSatVmDescriptor2R24`
//! (STAGED / ADDITIVE — a new test file only; no deployed descriptor, producer, registry, VK, or
//! routing is touched).
//!
//! This file welds [`carrier_floor_weld::carrier_floor_gates`] (the 13 decode + selector-force gates
//! that decode the escrow floor DIRECTLY from the caveat-commit-bound type-tag columns 291/298/305/312)
//! onto a CLONE of the deployed satisfaction descriptor `settleEscrowSatVmDescriptor2R24`, then drives
//! the assembled descriptor through `prove_vm_descriptor2` / `verify_vm_descriptor2` over the genuine
//! rotated settle producer (`generate_rotated_settle_escrow_trace`).
//!
//! ## EMPIRICAL FINDING (this is what the file establishes; honesty over forced-green)
//!
//! The two STAGED gadgets have CONFLICTING row-locality assumptions, and welding them is UNSATISFIABLE
//! for a genuine ESCROW-DECLARED multi-row settle:
//!
//!  * `satisfaction_weld` makes the capacity selector `ESCROW_SEL_COL` PRODUCER-controlled: the
//!    producer sets it `1` only on the settle row (row 0) and `0` on the carry-forward padding rows,
//!    because those padding rows carry the POST-settle `Consumed` status in the before-block (the v1
//!    cross-row continuity `next.before == local.after`, transitions hi=lo=0..13 over offsets that
//!    include the leg fields 3/4). With the selector `0` there, the four `sel·(field−const)` gates are
//!    inert on padding — which is exactly why they must be inert.
//!
//!  * `carrier_floor_weld` makes the selector FORCED, every row: it decodes `FLOOR_ESCROW_COL` from the
//!    caveat type-tag columns (which `fill_caveat` writes UNIFORMLY on every row) and adds the every-row
//!    gate `FLOOR · (ESCROW_SEL_COL − 1) == 0`. With a uniform escrow manifest `FLOOR = 1` on EVERY
//!    row, so the carrier forces `ESCROW_SEL_COL = 1` on EVERY row.
//!
//! These cannot both hold on a padding row:
//!   - selector `0` on padding ⟹ carrier selector-force gate `1·(0−1) = −1 ≠ 0` (carrier bites), but
//!   - selector `1` on padding ⟹ base satisfaction gate `1·(before_leg − Deposited) = 1·(Consumed −
//!     Deposited) ≠ 0` (satisfaction bites),
//!   - and forcing every row to a FULL settle (`before=Deposited, after=Consumed, sel=1`) to dodge both
//!     violates the v1 continuity transition `next.before(Deposited) == local.after(Consumed)`.
//! So for any selector/field assignment, SOME row-local gate is non-zero. The escrow-declared honest
//! case has NO satisfying assignment over a height>1 trace (and a STARK trace cannot be height 1).
//!
//! In a REAL STARK this manifests as: `prove_vm_descriptor2` still emits a proof (the prover does not
//! reject eagerly here), but `verify_vm_descriptor2` REJECTS it (`OodEvaluationMismatch`). The teeth
//! the task asked to exercise (honest-proves, forged-partial/phantom-refused, floor-binding) therefore
//! CANNOT bite, because their common premise — a verifying honest escrow-declared proof — does not
//! exist for this weld.
//!
//! ## SECONDARY (structural) FINDING — the decode/commit ROW MISMATCH
//!
//! The descriptor pins the caveat-commit public input PI 45 to the LAST row (`pi_binding row=last col
//! 328 pi 45`), while the carrier decode gates are EVERY-row gates over the caveat type-tag columns.
//! The descriptor carries NO cross-row uniformity gate on the caveat columns. So even setting the
//! satisfiability tension aside, a prover could declare escrow on the settle row (lighting the decode
//! there) while committing a NO-escrow manifest on the last row (PI 45) — the floor decode is not bound
//! to the COMMITTED caveat for a non-uniform manifest. A faithful weld would either force the manifest
//! uniform across rows, or read the decode from the SAME (last) row PI 45 binds, or gate the carrier
//! decode by the (settle-row-only) capacity selector so it is inert on the carry-forward rows.
//!
//! ## What DOES hold in a real STARK (the positive control)
//!
//! The carrier descriptor is SATISFIABLE and proves+verifies for a NO-escrow settle (`FLOOR = 0`
//! everywhere ⟹ the selector-force gate is vacuous ⟹ the selector is inert). This empirically rules
//! out a column collision: `bit_col(0)=609 … or_col(2)=619` all sit strictly ABOVE the descriptor's
//! own top chip-lane column (608), and `FLOOR_ESCROW_COL=72` / `ESCROW_SEL_COL=70` are not referenced
//! by any base gate. The gadget's "no false reject" direction is sound in-proof; only its actual TOOTH
//! (forcing the selector when escrow IS declared) is unreachable on this weld target.
//!
//! SLOW (full batch STARKs). Run:
//!   `cargo test -p dregg-circuit --test gentian_carrier_floor_prove --release -- --nocapture \
//!    --test-threads=1`

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, eval_lean_expr, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::CellState;
use dregg_circuit::effect_vm::authority_digest_weld::FLOOR_ESCROW_COL;
use dregg_circuit::effect_vm::carrier_floor_weld::{
    bit_col, carrier_floor_gates, caveat_tag_col, inv_col, or_col,
};
use dregg_circuit::effect_vm::columns::rotation::caveat as cav;
use dregg_circuit::effect_vm::pi::{SETTLE_ESCROW_STATUS_CONSUMED, SLOT_CAVEAT_TAG_SETTLE_ESCROW};
use dregg_circuit::effect_vm::satisfaction_weld::{
    ESCROW_SEL_COL, after_field_col, before_field_col, settle_escrow_satisfaction_gates,
};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, RotatedCaveatEntry, RotatedCaveatManifest, empty_caveat_manifest,
    generate_rotated_settle_escrow_trace,
};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint};
use dregg_turn::rotation_witness as rw;

const LEG_A: usize = 0;
const LEG_B: usize = 1;
const CON: u32 = SETTLE_ESCROW_STATUS_CONSUMED;

// ----------------------------------------------------------------------------------------------------
// Fixtures (copied from the escrow weld template — residue-free producer cell + rotation witnesses).
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
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let w = rw::produce(
        &cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
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
    desc.constraints.extend(carrier_floor_gates()); // +13, the carrier adds NO public input
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
/// row, EXACTLY per `carrier_floor_weld`'s `make_row` witness logic, reading the four bound type-tag
/// columns from the row. Does NOT touch `ESCROW_SEL_COL` (the selector is the producer's / the test's
/// to set). Rows are grown to `width` first.
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
        fill_carrier_decode(row, w); // the generator already set ESCROW_SEL_COL per row (1 on settle)
    }
    (trace, dpis, desc)
}

fn gate_body(c: &dregg_circuit::descriptor_ir2::VmConstraint2) -> &LeanExpr {
    match c {
        dregg_circuit::descriptor_ir2::VmConstraint2::Base(VmConstraint::Gate(b)) => b,
        _ => panic!("expected a Gate"),
    }
}

/// Does every gate in `gates` vanish on `row`?
fn all_zero(gates: &[dregg_circuit::descriptor_ir2::VmConstraint2], row: &[BabyBear]) -> bool {
    gates
        .iter()
        .all(|g| eval_lean_expr(gate_body(g), row) == BabyBear::ZERO)
}

fn mem() -> MemBoundaryWitness {
    MemBoundaryWitness::default()
}
type Heaps = Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>;

// ====================================================================================================
// TOOTH context 1 (POSITIVE CONTROL): the carrier descriptor proves+verifies a NO-escrow settle, so
// the carrier aux columns do NOT collide with the descriptor's chip lanes, and the gadget never
// false-rejects. (This is the only honest case that yields a verifying proof on this weld.)
// ====================================================================================================
#[test]
fn carrier_no_escrow_settle_proves_and_verifies() {
    // empty manifest ⟹ no escrow tag ⟹ FLOOR decodes 0 on every row ⟹ the selector-force gate is
    // vacuous (the generator keeps ESCROW_SEL_COL=1 on row 0, dpis[46]=1; the base satisfaction gates
    // still force the honest both-legs flip, which the genuine trace satisfies).
    let m = empty_caveat_manifest();
    let (trace, dpis, desc) = carrier_trace(&m);

    // FLOOR is 0 on the settle row (no escrow declared); the selector rides the generator's 1.
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
    assert_eq!(trace[0][caveat_tag_col(0)], BabyBear::ZERO, "no escrow tag");

    let heaps: Heaps = vec![];
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem(), &heaps)
        .expect("the no-escrow settle MUST prove against the carrier descriptor");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("the no-escrow settle proof MUST verify independently");
    let total = postcard::to_allocvec(&proof).expect("postcard").len();
    eprintln!(
        "CARRIER (no-escrow positive control): PROVED + VERIFIED (real BatchProof, {total} B / \
         ~{:.1} KiB). Carrier aux columns 609..619 + FLOOR(72) do NOT collide.",
        total as f64 / 1024.0
    );
}

// ====================================================================================================
// TOOTH context 2 (THE FINDING — row-local unsatisfiability of the escrow-declared honest case): for
// the escrow manifest, NO selector policy satisfies BOTH the base satisfaction gates and the carrier
// gates on the carry-forward padding rows. This is the precise reason the honest tooth cannot bite.
// ====================================================================================================
#[test]
fn carrier_escrow_declared_is_rowlocal_unsatisfiable() {
    let m = escrow_manifest();
    let (trace, _dpis, _desc) = carrier_trace(&m);
    assert!(
        trace.len() > 1,
        "a real settle trace has carry-forward padding rows"
    );

    // The escrow tag IS bound: caveat_tag_col(0)=17 on every row, FLOOR decodes 1 on every row.
    assert_eq!(
        trace[0][caveat_tag_col(0)],
        BabyBear::new(SLOT_CAVEAT_TAG_SETTLE_ESCROW)
    );
    for (r, row) in trace.iter().enumerate() {
        assert_eq!(
            row[FLOOR_ESCROW_COL],
            BabyBear::ONE,
            "FLOOR=1 (escrow) on row {r}"
        );
    }

    let carrier = carrier_floor_gates();
    let base_sat = settle_escrow_satisfaction_gates(ESCROW_SEL_COL, LEG_A, LEG_B);

    // Pick the FIRST padding row (carry-forward: before-leg = Consumed, generator selector = 0).
    let pad = 1usize;
    assert_eq!(
        trace[pad][before_field_col(LEG_A)],
        BabyBear::new(CON),
        "padding before=Consumed"
    );
    assert_eq!(
        trace[pad][after_field_col(LEG_A)],
        BabyBear::new(CON),
        "padding after=Consumed"
    );

    // Policy A — selector 0 on the padding row (what the base settle demands so its gates stay inert):
    //   base satisfaction: all inert (sel=0), but the carrier selector-force gate BITES (FLOOR=1).
    let mut row_sel0 = trace[pad].clone();
    row_sel0[ESCROW_SEL_COL] = BabyBear::ZERO;
    assert!(
        all_zero(&base_sat, &row_sel0),
        "sel=0 ⟹ base satisfaction inert on padding"
    );
    assert!(
        !all_zero(&carrier, &row_sel0),
        "sel=0 with FLOOR=1 ⟹ the carrier selector-force gate FLOOR·(SEL−1) BITES on padding"
    );

    // Policy B — selector 1 on the padding row (what the carrier forces, FLOOR=1):
    //   carrier: all vanish (sel=1), but a base satisfaction gate BITES (before-leg = Consumed ≠ Dep).
    let mut row_sel1 = trace[pad].clone();
    row_sel1[ESCROW_SEL_COL] = BabyBear::ONE;
    assert!(
        all_zero(&carrier, &row_sel1),
        "sel=1 with FLOOR=1 ⟹ carrier selector-force vanishes"
    );
    assert!(
        !all_zero(&base_sat, &row_sel1),
        "sel=1 ⟹ the base satisfaction gate sel·(before_leg − Deposited) BITES on a carry-forward row"
    );

    eprintln!(
        "CARRIER (escrow-declared): ROW-LOCAL UNSATISFIABLE on the carry-forward padding row — sel=0 \
         trips the carrier floor-force, sel=1 trips the base satisfaction. No assignment satisfies \
         both. The honest escrow tooth has no satisfying multi-row witness."
    );
}

// ====================================================================================================
// TOOTH context 3 (THE FINDING in a REAL STARK): the escrow-declared honest case yields NO verifying
// proof under either selector policy — `prove` may emit a proof, but `verify` REJECTS it.
// ====================================================================================================
#[test]
fn carrier_escrow_declared_yields_no_verifying_proof() {
    let m = escrow_manifest();
    let (trace, dpis, desc) = carrier_trace(&m);
    let heaps: Heaps = vec![];

    // Policy B: selector forced 1 on EVERY row (what the carrier gate demands for a uniform escrow
    // manifest). dpis[46] stays 1 (the generator pinned it).
    let mut trace_b = trace.clone();
    for row in trace_b.iter_mut() {
        row[ESCROW_SEL_COL] = BabyBear::ONE;
    }
    let verified_b = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_vm_descriptor2(&desc, &trace_b, &dpis, &mem(), &heaps)
    })) {
        Ok(Ok(proof)) => {
            let v = verify_vm_descriptor2(&desc, &proof, &dpis);
            eprintln!("CARRIER escrow (sel=1 everywhere): prove OK, verify = {v:?}");
            v.is_ok()
        }
        Ok(Err(e)) => {
            eprintln!("CARRIER escrow (sel=1 everywhere): prove refused: {e}");
            false
        }
        Err(_) => {
            eprintln!("CARRIER escrow (sel=1 everywhere): prove panicked (refused)");
            false
        }
    };
    assert!(
        !verified_b,
        "the escrow-declared honest case (selector forced everywhere) MUST NOT yield a verifying proof"
    );

    // Policy A: the generator's per-row selector (1 on the settle row, 0 on padding) — the carrier
    // selector-force gate is then violated on the padding rows.
    let verified_a = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_vm_descriptor2(&desc, &trace, &dpis, &mem(), &heaps)
    })) {
        Ok(Ok(proof)) => {
            let v = verify_vm_descriptor2(&desc, &proof, &dpis);
            eprintln!("CARRIER escrow (sel only on settle row): prove OK, verify = {v:?}");
            v.is_ok()
        }
        Ok(Err(e)) => {
            eprintln!("CARRIER escrow (sel only on settle row): prove refused: {e}");
            false
        }
        Err(_) => {
            eprintln!("CARRIER escrow (sel only on settle row): prove panicked (refused)");
            false
        }
    };
    assert!(
        !verified_a,
        "the escrow-declared honest case (producer selector) MUST NOT yield a verifying proof either"
    );

    eprintln!(
        "CARRIER (escrow-declared) FINDING: neither selector policy produces a verifying proof — the \
         carrier-floor weld over settleEscrowSatVmDescriptor2R24 is unsatisfiable for a genuine \
         escrow-declared multi-row settle. The honest/forged teeth cannot be exercised on this weld."
    );
}

// ====================================================================================================
// SECONDARY FINDING (structural): the caveat commit PI 45 is pinned to the LAST row, while the carrier
// decode gates are EVERY-row; with no cross-row uniformity gate on the caveat columns, the floor decode
// is not bound to the COMMITTED caveat for a non-uniform manifest.
// ====================================================================================================
#[test]
fn carrier_decode_and_committed_caveat_read_different_rows() {
    // The carrier gates are all every-row Base(Gate)s (no row gating).
    let carrier = carrier_floor_gates();
    assert_eq!(carrier.len(), 13);
    assert!(
        carrier.iter().all(|g| matches!(
            g,
            dregg_circuit::descriptor_ir2::VmConstraint2::Base(VmConstraint::Gate(_))
        )),
        "carrier gates are every-row Gates (they read caveat_tag_col on EVERY row)"
    );

    // The deployed descriptor pins the caveat commit (PI 45) to the LAST row.
    let desc = parse_vm_descriptor2(welded_escrow_json()).expect("parse");
    let pi45_last = desc.constraints.iter().any(|c| {
        matches!(
            c,
            dregg_circuit::descriptor_ir2::VmConstraint2::Base(VmConstraint::PiBinding {
                row: dregg_circuit::lean_descriptor_air::VmRow::Last,
                pi_index: 45,
                ..
            })
        )
    });
    assert!(
        pi45_last,
        "settleEscrowSatVmDescriptor2R24 pins the caveat-commit PI 45 to the LAST row, but the carrier \
         decode reads the type-tag columns on EVERY row — they coincide only for a uniform manifest, \
         which the descriptor does not force. The floor binding is row-decoupled for non-uniform \
         manifests."
    );
    eprintln!(
        "STRUCTURAL FINDING: PI 45 (committed caveat) = LAST row; carrier decode = every row; no \
         cross-row caveat-uniformity gate ⟹ the floor decode is not bound to the committed caveat for \
         a non-uniform manifest."
    );
}
