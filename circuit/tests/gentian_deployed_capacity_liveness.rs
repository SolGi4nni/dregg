//! # GENTIAN flip — the LIVENESS tooth: an honest declared-capacity turn PROVES + VERIFIES through the
//! DEPLOYED welded satisfaction descriptor (the real `rotation-v3-staged-registry.tsv` member, NOT a
//! test clone), and the declaration-keyed resolver ROUTES to that exact member.
//!
//! The flag-day flipped the SOUNDNESS side: every bare cohort member carries the `floor == 0`-refuse,
//! so a declared-capacity turn is UNSATISFIABLE under the bare descriptor (a forger cannot launder it
//! through `transferVmDescriptor2R24`). This file is the LIVENESS complement: it confirms an HONEST
//! declared-capacity turn is not merely refused-elsewhere but actively PROVABLE through the member the
//! routing names — closing the flip both ways (soundness: forger UNSAT under bare; liveness: honest
//! proves through the welded satisfaction member).
//!
//! Distinct from `gentian_carrier_floor_prove` / `gentian_discharge_vault_prove` (which weld extra
//! decode/force gates onto a RENAMED clone to exercise the soundness teeth): this file parses the three
//! satisfaction descriptors DIRECTLY from `V3_STAGED_REGISTRY_TSV` — the committed bytes, unchanged, no
//! `-gentian-demo` rename, no extra weld — and proves the deployed member itself accepts an honest turn.
//! It also asserts `rotated_descriptor_name_for_declared_capacity` routes each declared tag to the exact
//! member it proves through — the routing and the provability are the same member.
//!
//! SLOW (full batch STARKs). Run:
//!   `cargo test -p dregg-circuit --test gentian_deployed_capacity_liveness --release -- --nocapture \
//!    --test-threads=1`

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::CellState;
use dregg_circuit::effect_vm::columns::rotation::caveat as cav;
use dregg_circuit::effect_vm::discharge_weld::{
    DISCHARGE_SEL_COL, FLOOR_DISCHARGE_COL, fill_discharge_aux,
};
use dregg_circuit::effect_vm::pi::{
    SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION, SLOT_CAVEAT_TAG_SETTLE_ESCROW,
    SLOT_CAVEAT_TAG_VAULT_DEPOSIT,
};
use dregg_circuit::effect_vm::satisfaction_weld::ESCROW_SEL_COL;
use dregg_circuit::effect_vm::trace_rotated::{
    DISCHARGE_SAT_DESCRIPTOR_NAME, RotatedBlockWitness, RotatedCaveatEntry, RotatedCaveatManifest,
    SETTLE_ESCROW_SAT_DESCRIPTOR_NAME, VAULT_SAT_DESCRIPTOR_NAME,
    generate_rotated_settle_escrow_trace, generate_rotated_settle_escrow_trace_forged,
    rotated_descriptor_name_for_declared_capacity,
};
use dregg_circuit::effect_vm::vault_weld::{FLOOR_VAULT_COL, VAULT_SEL_COL, fill_vault_aux};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_turn::rotation_witness as rw;

// Escrow legs 0/1; discharge cur/tot/due 0/1/2; vault asset/share 0/1 (the emitted defs).
const LEG_A: usize = 0;
const LEG_B: usize = 1;
const CUR: usize = 0;
const TOT: usize = 1;
const DUE: usize = 2;
const ASSET: usize = 0;
const SHARE: usize = 1;

// The honest discharge schedule (identical to `gentian_discharge_vault_prove`): cursor +100, total +50,
// committed due block 1000, published clock 1000 (due ≤ clock).
const PERIOD: u32 = 100;
const AMOUNT: u32 = 50;
const DUE_BLOCK: u32 = 1000;
const CLOCK: u32 = 1000;

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

fn producer_cell(balance: i64, committed_height: u32) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell.state.set_committed_height(committed_height as u64);
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

fn carrier_inputs(
    due_block: u32,
    committed_height: u32,
) -> (CellState, RotatedBlockWitness, RotatedBlockWitness) {
    let balance: i64 = 100_000;
    let mut initial_state = CellState::new(balance as u64, 0);
    initial_state.fields[DUE] = BabyBear::new(due_block);
    let cell = producer_cell(balance, committed_height);
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

/// A capacity-declaring caveat manifest: slot 0 type tag = `tag`, params = declared terms — bound into
/// the caveat-commit chain (PI 45), exactly the gentian pattern.
fn capacity_manifest(tag: u32, params: [u32; 4]) -> RotatedCaveatManifest {
    let mut m = RotatedCaveatManifest::default();
    m.entries[0] = RotatedCaveatEntry {
        type_tag: tag,
        domain_tag: cav::DOMAIN_REGISTERS,
        key: BabyBear::ZERO,
        params: params.map(BabyBear::new),
    };
    m
}

fn mem() -> MemBoundaryWitness {
    MemBoundaryWitness::default()
}
type Heaps = Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>;

/// Parse a satisfaction descriptor DIRECTLY from the committed registry (no rename, no weld) — the
/// deployed member the routing names.
fn deployed_member(name: &str) -> EffectVmDescriptor2 {
    let json = V3_STAGED_REGISTRY_TSV
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
        .unwrap_or_else(|| panic!("{name} is a committed V3 registry member"));
    parse_vm_descriptor2(json).unwrap_or_else(|e| panic!("{name} parses: {e}"))
}

/// Does the descriptor accept this (trace, dpis)? `prove` may panic/refuse on an unsatisfiable witness;
/// `verify` is the real acceptance.
fn accepts(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], dpis: &[BabyBear]) -> bool {
    let heaps: Heaps = vec![];
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_vm_descriptor2(desc, trace, dpis, &mem(), &heaps)
    })) {
        Ok(Ok(proof)) => verify_vm_descriptor2(desc, &proof, dpis).is_ok(),
        Ok(Err(_)) | Err(_) => false,
    }
}

/// Grow every row to the descriptor's committed `trace_width` (the deployed member is proved at its own
/// width; the generator base trace is narrower, the tail columns are zero — the satisfaction gates read
/// only the generator-filled field/selector columns).
fn pad_rows(trace: &mut [Vec<BabyBear>], width: usize) {
    for row in trace.iter_mut() {
        if row.len() < width {
            row.resize(width, BabyBear::ZERO);
        }
    }
}

// ====================================================================================================
// ESCROW — the honest settle proves through the DEPLOYED `settleEscrowSatVmDescriptor2R24`, and the
// declaration route names that member.
// ====================================================================================================
#[test]
fn honest_escrow_settle_proves_through_deployed_member() {
    let desc = deployed_member(SETTLE_ESCROW_SAT_DESCRIPTOR_NAME);
    assert_eq!(
        desc.public_input_count, 47,
        "rotated 46 + the selector slot"
    );
    // The routing names the member we prove through.
    let settle = dregg_circuit::effect_vm::Effect::Transfer {
        amount: 0,
        direction: 0,
    };
    assert_eq!(
        rotated_descriptor_name_for_declared_capacity(&settle, &[SLOT_CAVEAT_TAG_SETTLE_ESCROW]),
        Some(SETTLE_ESCROW_SAT_DESCRIPTOR_NAME),
        "the declared-escrow route names the deployed member"
    );

    let (st, bw, aw) = carrier_inputs(0, 0);
    let m = capacity_manifest(SLOT_CAVEAT_TAG_SETTLE_ESCROW, [0; 4]);
    let (mut trace, dpis) = generate_rotated_settle_escrow_trace(&st, &bw, &aw, &m, LEG_A, LEG_B)
        .expect("honest settle generates");
    assert_eq!(dpis.len(), 47);
    pad_rows(&mut trace, desc.trace_width);
    assert_eq!(
        trace[0][ESCROW_SEL_COL],
        BabyBear::ONE,
        "the generator forces the escrow selector on the settle row"
    );
    assert!(
        accepts(&desc, &trace, &dpis),
        "an HONEST escrow settle MUST prove + verify through the DEPLOYED satisfaction member"
    );
    eprintln!("LIVENESS (escrow → deployed settleEscrowSatVmDescriptor2R24): PROVED + VERIFIED.");
}

// ====================================================================================================
// DISCHARGE — the honest discharge proves through the DEPLOYED `dischargeSatVmDescriptor2R24`.
// ====================================================================================================
#[test]
fn honest_discharge_proves_through_deployed_member() {
    let desc = deployed_member(DISCHARGE_SAT_DESCRIPTOR_NAME);
    assert_eq!(desc.public_input_count, 47);
    let settle = dregg_circuit::effect_vm::Effect::Transfer {
        amount: 0,
        direction: 0,
    };
    assert_eq!(
        rotated_descriptor_name_for_declared_capacity(
            &settle,
            &[SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION]
        ),
        Some(DISCHARGE_SAT_DESCRIPTOR_NAME),
    );

    let (st, bw, aw) = carrier_inputs(DUE_BLOCK, CLOCK);
    let m = capacity_manifest(SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION, [PERIOD, AMOUNT, 0, 0]);
    let (mut trace, dpis) = generate_rotated_settle_escrow_trace_forged(
        &st,
        &bw,
        &aw,
        &m,
        CUR,
        TOT,
        (1000, 0),
        (1100, 50),
    )
    .expect("honest discharge generates");
    assert_eq!(dpis.len(), 47);
    fill_discharge_aux(&mut trace, desc.trace_width, DUE, PERIOD, AMOUNT, CLOCK);
    assert_eq!(
        trace[0][FLOOR_DISCHARGE_COL],
        BabyBear::ONE,
        "discharge declared ⟹ floor 1"
    );
    assert_eq!(trace[0][DISCHARGE_SEL_COL], BabyBear::ONE);
    assert!(
        accepts(&desc, &trace, &dpis),
        "an HONEST discharge MUST prove + verify through the DEPLOYED satisfaction member"
    );
    eprintln!("LIVENESS (discharge → deployed dischargeSatVmDescriptor2R24): PROVED + VERIFIED.");
}

// ====================================================================================================
// VAULT — the honest fair-mint deposit proves through the DEPLOYED `vaultSatVmDescriptor2R24`.
// ====================================================================================================
#[test]
fn honest_vault_deposit_proves_through_deployed_member() {
    let desc = deployed_member(VAULT_SAT_DESCRIPTOR_NAME);
    assert_eq!(desc.public_input_count, 47);
    let settle = dregg_circuit::effect_vm::Effect::Transfer {
        amount: 0,
        direction: 0,
    };
    assert_eq!(
        rotated_descriptor_name_for_declared_capacity(&settle, &[SLOT_CAVEAT_TAG_VAULT_DEPOSIT]),
        Some(VAULT_SAT_DESCRIPTOR_NAME),
    );

    let (st, bw, aw) = carrier_inputs(0, 0);
    let m = capacity_manifest(SLOT_CAVEAT_TAG_VAULT_DEPOSIT, [0; 4]);
    // Established vault Ta=2, Sa=4; deposit d=10, m=20: fair (2·20 = 4·10).
    let (mut trace, dpis) = generate_rotated_settle_escrow_trace_forged(
        &st,
        &bw,
        &aw,
        &m,
        ASSET,
        SHARE,
        (2, 4),
        (12, 24),
    )
    .expect("honest vault generates");
    assert_eq!(dpis.len(), 47);
    fill_vault_aux(&mut trace, desc.trace_width, ASSET, SHARE);
    assert_eq!(
        trace[0][FLOOR_VAULT_COL],
        BabyBear::ONE,
        "vault declared ⟹ floor 1"
    );
    assert_eq!(trace[0][VAULT_SEL_COL], BabyBear::ONE);
    assert!(
        accepts(&desc, &trace, &dpis),
        "an HONEST fair-mint vault deposit MUST prove + verify through the DEPLOYED satisfaction member"
    );
    eprintln!("LIVENESS (vault → deployed vaultSatVmDescriptor2R24): PROVED + VERIFIED.");
}
