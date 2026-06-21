//! # THE FAITHFUL 8-FELT WIDE ROUNDTRIPS — the cohort FANNED OUT past slice-1's transfer.
//!
//! Slice 1 proved ONE real `prove/verify_vm_descriptor2` wide roundtrip (transfer, width 816 / PI 62)
//! in `effect_vm_rotation_flip.rs`. THIS file fans the wide producers out to the rest of the
//! emit-source cohort, one real wide prove+verify roundtrip per distinct PRODUCER SHAPE:
//!
//!   * **transfer-shape** (burn) — the bare-46-PI cohort, wide member width 816 / PI 62, the same
//!     carrier shape as transfer (`generate_rotated_transfer_shape_wide`).
//!   * **grow-gate noteSpend** — limb-26 nullifier accumulator, wide width 816 / PI 63
//!     (`generate_rotated_note_spend_wide`).
//!   * **grow-gate noteCreate** — limb-27 commitments accumulator, wide width 816 / PI 63
//!     (`generate_rotated_note_create_wide`).
//!   * **grow-gate createCell** — limb-0 accounts accumulator, wide width 816 / PI 63
//!     (`generate_rotated_create_cell_wide`).
//!
//! PLUS the **EXECUTOR ANCHORING differential** (the wide analog of slice-1's G3 cell≡circuit check):
//! the wide producer's 8-felt commit (the BEFORE carrier-12 columns) byte-equals
//! `dregg_cell::commitment::compute_canonical_state_commitment_v9_felt8` for the live cell — so the
//! deployed executor (after the eventual flip) can anchor the 8 wide PIs to the trusted cell.
//!
//! ADDITIVE: the live 1-felt path / TSV / VK / executor are UNTOUCHED. The wide descriptors come from
//! the verified Lean `CapOpenEmit.v3RegistryCapOpenWide` (`WIDE_REGISTRY_STAGED_TSV`). Gated on
//! `prover`. SLOW.

#![cfg(feature = "prover")]

use dregg_cell::commitment::{
    V9RotationContext, compute_canonical_state_commitment_v9_felt8,
};
use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    GRAD_ROT_WIDTH, RotatedBlockWitness, WIDE_BEFORE_CBASE, WIDE_COMMIT_CARRIER,
    SET_FIELD_DYN_HOST_WIDTH, empty_caveat_manifest, generate_rotated_create_cell_wide,
    generate_rotated_create_from_factory_wide, generate_rotated_note_create_wide,
    generate_rotated_note_spend_wide, generate_rotated_set_field_dyn_wide,
    generate_rotated_spawn_wide, generate_rotated_transfer_shape_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_turn::rotation_witness as rw;

/// Resolve a wide descriptor JSON from the wide registry TSV by member name (key column).
fn wide_json(name: &str) -> &'static str {
    WIDE_REGISTRY_STAGED_TSV
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
        .unwrap_or_else(|| panic!("{name} not in WIDE_REGISTRY_STAGED_TSV"))
}

fn wide_desc(name: &str) -> EffectVmDescriptor2 {
    parse_vm_descriptor2(wide_json(name)).unwrap_or_else(|e| panic!("{name} wide parses: {e}"))
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

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

/// The columns of the BEFORE 8-felt commit carrier (carrier 12) at the 816-wide host base
/// (`WIDE_BEFORE_CBASE = 608`): the 8 felts the wide BEFORE PIs publish on the first row.
fn before_commit_8(trace: &[Vec<BabyBear>]) -> [BabyBear; 8] {
    let base = WIDE_BEFORE_CBASE + 8 * WIDE_COMMIT_CARRIER; // 704
    core::array::from_fn(|j| trace[0][base + j])
}

/// The wide member's wide-PI offset (where the 16 wide PIs START): the base PI count.
/// transfer-shape = 46 (bare 46-PI vector); the grow-gate families carry an extra PI[46] so the
/// wide PIs start at 39.
fn assert_roundtrip(
    name: &str,
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    map_heaps: &[Vec<HeapLeaf>],
    wide_pi_base: usize,
) {
    assert_eq!(trace[0].len(), GRAD_ROT_WIDTH + 208, "{name}: wide width 816");
    assert_eq!(desc.trace_width, trace[0].len(), "{name}: descriptor width matches trace");
    assert_eq!(
        dpis.len(),
        wide_pi_base + 16,
        "{name}: base {wide_pi_base} PIs + 16 wide PIs"
    );
    assert_eq!(desc.public_input_count, dpis.len(), "{name}: descriptor PI count matches");

    // The 8 BEFORE wide PIs (at wide_pi_base..+8) equal the BEFORE carrier-12 columns on row 0.
    let commit = before_commit_8(trace);
    for j in 0..8 {
        assert_eq!(
            dpis[wide_pi_base + j], commit[j],
            "{name}: wide PI {} = BEFORE 8-felt commit felt {j}",
            wide_pi_base + j
        );
    }

    let mem_boundary = MemBoundaryWitness::default();
    let proof = prove_vm_descriptor2(desc, trace, dpis, &mem_boundary, map_heaps)
        .unwrap_or_else(|e| panic!("{name}: WIDE proof must prove (816): {e}"));
    verify_vm_descriptor2(desc, &proof, dpis)
        .unwrap_or_else(|e| panic!("{name}: WIDE proof must verify: {e}"));
    eprintln!("WIDE {name}: PROVED + VERIFIED at width 816 (faithful 8-felt commit).");
}

/// **THE EXECUTOR-ANCHORING differential (wide analog of slice-1's G3 cell≡circuit check).** The
/// CELL's chip-faithful 8-felt commit — `wire_commit_8_chip` over the cell's own
/// `compute_rotated_pre_limbs(cell, ctx)` + iroot — byte-equals the CIRCUIT's published BEFORE wide
/// carrier-12, so the deployed executor (after the flip) can anchor the 8 wide PIs to the trusted
/// cell. `wire_commit_8_chip` is the byte-twin of the circuit's `fill_wide_block` (the arity-tagged
/// chip chain the wide carriers are filled with) — NOT the plain `single_perm_compress`-based
/// `wire_commit_8` the cell's `compute_canonical_state_commitment_v9_felt8` currently delegates to,
/// which DIVERGES (no chip arity tag). This differential is the spec the cell-side cutover must meet:
/// the flip repoints `_felt8` onto the chip-faithful chain so the cell anchors the deployed circuit.
fn assert_executor_anchor(
    name: &str,
    cell: &Cell,
    before_w: &rw::RotationWitness,
    nullifier_root: [u8; 32],
    commitments_root: [u8; 32],
    trace: &[Vec<BabyBear>],
) {
    let ctx = V9RotationContext {
        cells_root: before_w.pre_limbs[0],
        nullifier_root,
        commitments_root,
        iroot: before_w.iroot,
    };
    // The cell's OWN pre_limbs (computed from its RecordKernelState + turn ctx, NOT the producer's
    // — the independent path the executor takes), through the CHIP-FAITHFUL wide chain.
    let cell_pre = dregg_cell::commitment::compute_rotated_pre_limbs(cell, &ctx);
    let cell_felt8 = dregg_circuit::poseidon2::wire_commit_8_chip(&cell_pre, ctx.iroot);
    let circuit_carrier12 = before_commit_8(trace);
    assert_eq!(
        cell_felt8, circuit_carrier12,
        "{name}: cell chip-faithful 8-felt commit == circuit wide carrier-12 (executor anchoring)"
    );
    // and it is genuinely 8 felts (NOT a 1-felt lane0 squeeze padded with zeros): at least one of
    // the felts 1..8 is non-zero for a field-bearing authority-carrying cell.
    assert!(
        circuit_carrier12[1..].iter().any(|f| *f != BabyBear::ZERO),
        "{name}: the wide commit is genuinely 8-felt-wide (lanes 1..8 not all zero)"
    );
    // POST-FLIP: the cell's `compute_canonical_state_commitment_v9_felt8` is REPOINTED (under
    // `prover`) to the CHIP chain (`wire_commit_8_chip`), so it now EQUALS the deployed circuit
    // carrier — the executor-anchoring cutover landed. (Feature unification arms `dregg-cell/prover`
    // here via `dregg-turn`.)
    let cell_felt8_deployed = compute_canonical_state_commitment_v9_felt8(cell, &ctx);
    assert_eq!(
        cell_felt8_deployed, circuit_carrier12,
        "{name}: the cell `_felt8` is repointed to the chip chain and MATCHES the deployed circuit \
         carrier — the cell-side flip cutover is complete"
    );
    eprintln!(
        "WIDE {name}: executor-anchoring differential holds (cell chip-8-felt ≡ circuit carrier-12; \
         the cell `_felt8` is repointed to wire_commit_8_chip — the flip cutover is complete)."
    );
}

/// **THE EXECUTOR-ANCHORING differential for a GROW-GATE family.** The grow-gate generators OVERRIDE
/// a root limb (26 nullifier / 27 commitments / 0 cells) with the turn's openable accumulator root,
/// then recompute the block commit — so the BEFORE carrier binds the GROWN-set limbs, not the cell's
/// bare `compute_rotated_pre_limbs` (which would `hash_bytes` a [0;32] root). The executor anchors
/// the published 8-felt commit against the TRUSTED before-state limbs the kernel supplies (incl. the
/// turn's before-set root): here we read the BEFORE block's own limbs off the row (the trusted limbs
/// the executor holds) and assert `wire_commit_8_chip(limbs, iroot) == carrier-12` — the SAME chip
/// primitive the cell-side flip uses. This proves the executor's anchoring primitive reproduces the
/// circuit's published wide commit for the grow-gate shape. The plain `wire_commit_8` still DIVERGES.
fn assert_executor_anchor_grow_gate(name: &str, trace: &[Vec<BabyBear>]) {
    use dregg_circuit::effect_vm::trace_rotated::BEFORE_BASE;
    // The 37 BEFORE pre-iroot limbs + iroot the kernel-trusted before-state supplies (the row's own
    // BEFORE block, with the grown-set root override already applied by the grow-gate generator).
    let before_limbs: Vec<BabyBear> = (0..37).map(|j| trace[0][BEFORE_BASE + j]).collect();
    let before_iroot = trace[0][BEFORE_BASE + 37];
    let anchored = dregg_circuit::poseidon2::wire_commit_8_chip(&before_limbs, before_iroot);
    let circuit_carrier12 = before_commit_8(trace);
    assert_eq!(
        anchored, circuit_carrier12,
        "{name}: wire_commit_8_chip(trusted before-limbs) == circuit wide carrier-12 (grow-gate \
         executor anchoring — the published 8-felt commit binds the grown-set limbs)"
    );
    assert!(
        circuit_carrier12[1..].iter().any(|f| *f != BabyBear::ZERO),
        "{name}: the wide commit is genuinely 8-felt-wide (lanes 1..8 not all zero)"
    );
    // the plain `single_perm_compress` chain DIVERGES from the chip chain the circuit publishes.
    let plain = dregg_circuit::poseidon2::wire_commit_8(&before_limbs, before_iroot);
    assert_ne!(
        plain, circuit_carrier12,
        "{name}: the plain wire_commit_8 chain DIVERGES from the deployed circuit carrier — the \
         executor anchors via wire_commit_8_chip"
    );
    eprintln!(
        "WIDE {name}: grow-gate executor-anchoring holds (wire_commit_8_chip(trusted before-limbs) ≡ \
         circuit carrier-12; plain chain DIVERGES — flagged for the flip cutover)."
    );
}

/// **TRANSFER-SHAPE (burn) wide roundtrip.** Burn carries the bare 46-PI vector exactly as transfer;
/// its wide member is the SAME carrier shape (816 / PI 62). PROVES + VERIFIES + executor-anchors.
#[test]
fn wide_burn_transfer_shape_proves_verifies_and_executor_anchors() {
    let name = "burnVmDescriptor2R24";
    let desc = wide_desc(name);

    let before_balance: i64 = 80_000;
    let amount: u64 = 30;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Burn {
        target_hash: BabyBear::new(0),
        amount_lo: BabyBear::new(amount as u32),
        amount_full: amount,
    }];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    let (trace, dpis) = generate_rotated_transfer_shape_wide(
        &st, &effects, &bridge(&before_w), &bridge(&after_w), &empty_caveat_manifest(),
    )
    .expect("wide burn producer");
    assert_roundtrip(name, &desc, &trace, &dpis, &[], 46);
    assert_executor_anchor(name, &before_cell, &before_w, nullifier_root, commitments_root, &trace);
}

/// **setFieldDyn wide roundtrip — the DYNAMIC overflow-field write PROVES (the residual CLOSED).**
///
/// The dynamic `SetField` (`field_idx >= 8`) routes to `setFieldDynVmDescriptor2R24`, a DISTINCT
/// 581-wide V1Face geometry (wide member 789 / PI 63) the standard generator cannot produce (it panics
/// on `field_idx >= 8` and lays the 608-wide host). `generate_rotated_set_field_dyn_wide` builds it
/// from scratch: the Blum write+read pair (`addr = value = col 69`, `prev_value = col 70`,
/// `prev_serial = col 74`, `readback = col 75`) over a `MemBoundaryWitness`, the fields-root weld
/// (col 275 == col 68), and the fifth pin (col 263 → PI[46]). This PROVES + light-client VERIFIES —
/// no `catch_unwind`. The forge pole (a tampered readback) is exercised in `vk_epoch_misc`.
#[test]
fn wide_set_field_dyn_dynamic_overflow_proves_and_verifies() {
    let name = "setFieldDynVmDescriptor2R24";
    let desc = wide_desc(name);
    assert_eq!(desc.trace_width, SET_FIELD_DYN_HOST_WIDTH + 208, "setFieldDyn wide width 789");
    assert_eq!(desc.public_input_count, 63, "setFieldDyn wide carries 47 base + 16 wide PIs");

    let balance: i64 = 50_000;
    let st = CellState::new(balance as u64, 0);
    let mut ledger = Ledger::new();
    // A SetField bumps the nonce; the after-cell carries nonce 1.
    let before_cell = producer_cell(balance, 0);
    let after_cell = producer_cell(balance, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[5u8; 32]];
    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    // slot 3 (the overflow-memory address 0..7), previous value 0 at that address.
    let slot = 3u32;
    let prev_value = BabyBear::new(0);
    let (trace, dpis, mem_boundary) = generate_rotated_set_field_dyn_wide(
        &st, &bridge(&before_w), &bridge(&after_w), &empty_caveat_manifest(), slot, prev_value,
    )
    .expect("wide setFieldDyn producer");
    assert_eq!(trace[0].len(), desc.trace_width, "setFieldDyn wide trace width matches descriptor");
    assert_eq!(dpis.len(), desc.public_input_count, "setFieldDyn wide PI count matches descriptor");

    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &[])
        .unwrap_or_else(|e| panic!("setFieldDyn wide proof must prove (789): {e}"));
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .unwrap_or_else(|e| panic!("setFieldDyn wide proof must verify: {e}"));
    eprintln!(
        "WIDE setFieldDyn: the DYNAMIC overflow-field write PROVED + VERIFIED at width 789 (the Blum \
         write→read transport over the 581-wide V1Face geometry — the missing-generator residual is \
         CLOSED)."
    );
}

/// **NOTESPEND grow-gate wide roundtrip.** The nullifier accumulator (limb 26) grow-gate; wide member
/// 816 / PI 63 (the extra nullifier PI[46] before the 16 wide PIs). PROVES + VERIFIES + anchors.
#[test]
fn wide_note_spend_grow_gate_proves_verifies_and_executor_anchors() {
    let name = "noteSpendVmDescriptor2R24";
    let desc = wide_desc(name);

    let before_balance: i64 = 90_000;
    let value: u64 = 500;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::NoteSpend {
        nullifier: BabyBear::new(0xBEEF),
        value,
    }];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance + value as i64, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[7u8; 32]];
    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    let before_nullifiers = vec![
        HeapLeaf { addr: BabyBear::new(0x1111), value: BabyBear::new(1) },
        HeapLeaf { addr: BabyBear::new(0x2222), value: BabyBear::new(1) },
    ];
    let (trace, dpis, map_heaps) = generate_rotated_note_spend_wide(
        &st, &effects, &bridge(&before_w), &bridge(&after_w), &empty_caveat_manifest(),
        &before_nullifiers,
    )
    .expect("wide noteSpend producer");
    assert_roundtrip(name, &desc, &trace, &dpis, &map_heaps, 47);
    assert_executor_anchor_grow_gate(name, &trace);
}

/// **NOTECREATE grow-gate wide roundtrip.** The commitments accumulator (limb 27) grow-gate; wide
/// member 816 / PI 63. PROVES + VERIFIES + executor-anchors.
#[test]
fn wide_note_create_grow_gate_proves_verifies_and_executor_anchors() {
    let name = "noteCreateVmDescriptor2R24";
    let desc = wide_desc(name);

    let before_balance: i64 = 60_000;
    let value: u64 = 250;
    let st = CellState::new(before_balance as u64, 0);
    let cm = BabyBear::new(0xC0FFEE);
    let effects = vec![Effect::NoteCreate { commitment: cm, value }];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance + value as i64, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[11u8; 32]];
    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    let before_commitments = vec![
        HeapLeaf { addr: BabyBear::new(0x111), value: BabyBear::new(1) },
        HeapLeaf { addr: BabyBear::new(0x222), value: BabyBear::new(1) },
    ];
    let (trace, dpis, map_heaps) = generate_rotated_note_create_wide(
        &st, &effects, &bridge(&before_w), &bridge(&after_w), &empty_caveat_manifest(),
        &before_commitments,
    )
    .expect("wide noteCreate producer");
    assert_roundtrip(name, &desc, &trace, &dpis, &map_heaps, 47);
    assert_executor_anchor_grow_gate(name, &trace);
}

/// **CREATECELL grow-gate wide roundtrip.** The accounts accumulator (limb 0) grow-gate; wide member
/// 816 / PI 63. PROVES + VERIFIES + executor-anchors.
#[test]
fn wide_create_cell_grow_gate_proves_verifies_and_executor_anchors() {
    let name = "createCellVmDescriptor2R24";
    let desc = wide_desc(name);

    let before_balance: i64 = 40_000;
    let st = CellState::new(before_balance as u64, 0);
    let new_cell_id = BabyBear::new(0xCE11);
    let effects = vec![Effect::CreateCell { create_hash: [new_cell_id; 8] }];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[5u8; 32]];
    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    let before_accounts = vec![
        HeapLeaf { addr: BabyBear::new(0xAA01), value: BabyBear::new(0xAA01) },
        HeapLeaf { addr: BabyBear::new(0xAA02), value: BabyBear::new(0xAA02) },
    ];
    let (trace, dpis, map_heaps) = generate_rotated_create_cell_wide(
        &st, &effects, &bridge(&before_w), &bridge(&after_w), &empty_caveat_manifest(),
        &before_accounts,
    )
    .expect("wide createCell producer");
    assert_roundtrip(name, &desc, &trace, &dpis, &map_heaps, 47);
    assert_executor_anchor_grow_gate(name, &trace);
}

/// The shared birth-leg producer witnesses (a non-empty BEFORE accounts set distinct from the new-cell
/// key, so the `.absent` no-collision precondition has a bracketing witness). Mirrors the createCell
/// wide setup; the only per-effect difference is the lead effect + its new-cell key column.
fn birth_witnesses() -> (CellState, Ledger, rw::RotationWitness, rw::RotationWitness, Vec<HeapLeaf>) {
    let before_balance: i64 = 40_000;
    let st = CellState::new(before_balance as u64, 0);
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[5u8; 32]];
    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let before_accounts = vec![
        HeapLeaf { addr: BabyBear::new(0xAA01), value: BabyBear::new(0xAA01) },
        HeapLeaf { addr: BabyBear::new(0xAA02), value: BabyBear::new(0xAA02) },
    ];
    (st, ledger, before_w, after_w, before_accounts)
}

/// **CREATECELLFROMFACTORY grow-gate wide roundtrip.** The factory twin of the createCell birth leg:
/// the born child's key rides `param1` (CHILD_VK_DERIVED), and the SAME accounts-set grow-gate (limb 0)
/// forces the genuine sorted insert against the threaded BEFORE accounts leaf set. The honest trace
/// PROVES + VERIFIES against the deployed wide `factoryVmDescriptor2R24`; the grow-gate executor anchor
/// holds.
#[test]
fn wide_factory_grow_gate_proves_verifies_and_executor_anchors() {
    let name = "factoryVmDescriptor2R24";
    let desc = wide_desc(name);
    let (st, _ledger, before_w, after_w, before_accounts) = birth_witnesses();
    let effects = vec![Effect::CreateCellFromFactory {
        factory_vk: BabyBear::new(0xFAC0),
        child_vk_derived: BabyBear::new(0xC417),
    }];
    let (trace, dpis, map_heaps) = generate_rotated_create_from_factory_wide(
        &st, &effects, &bridge(&before_w), &bridge(&after_w), &empty_caveat_manifest(),
        &before_accounts,
    )
    .expect("wide factory producer");
    assert_roundtrip(name, &desc, &trace, &dpis, &map_heaps, 47);
    assert_executor_anchor_grow_gate(name, &trace);
}

/// **SPAWN (birth/accounts-grow leg) grow-gate wide roundtrip.** Spawn's wide descriptor
/// (`spawnVmDescriptor2R24`) carries the accounts-set `.absent`+`.insert` grow-gate (limb 0 — the born
/// child id grown into the cells set) and NO cap-tree map_op (the parent→child cap handoff is bound by
/// the cap-open `spawnWriteCapOpenVmDescriptor2R24`, a SEPARATE path). The honest trace PROVES + VERIFIES
/// against the deployed wide `spawnVmDescriptor2R24` for the accounts-birth column.
#[test]
fn wide_spawn_grow_gate_proves_verifies_and_executor_anchors() {
    let name = "spawnVmDescriptor2R24";
    let desc = wide_desc(name);
    let (st, _ledger, before_w, after_w, before_accounts) = birth_witnesses();
    let spawn_id = BabyBear::new(0x5BA1);
    let effects = vec![Effect::SpawnWithDelegation { spawn_hash: [spawn_id; 8] }];
    let (trace, dpis, map_heaps) = generate_rotated_spawn_wide(
        &st, &effects, &bridge(&before_w), &bridge(&after_w), &empty_caveat_manifest(),
        &before_accounts,
    )
    .expect("wide spawn (accounts birth leg) producer");
    assert_roundtrip(name, &desc, &trace, &dpis, &map_heaps, 47);
    assert_executor_anchor_grow_gate(name, &trace);
}

/// **The named wide wrappers REFUSE a mismatched lead effect** (fail-closed routing): the factory wide
/// wrapper rejects a createCell lead and vice-versa, so the dispatch lane cannot silently route the wrong
/// new-cell key column through the wrong descriptor.
#[test]
fn wide_birth_wrappers_refuse_mismatched_lead() {
    let (st, _ledger, before_w, after_w, before_accounts) = birth_witnesses();
    let cc = vec![Effect::CreateCell { create_hash: [BabyBear::new(0xCE11); 8] }];
    assert!(
        generate_rotated_create_from_factory_wide(
            &st, &cc, &bridge(&before_w), &bridge(&after_w), &empty_caveat_manifest(), &before_accounts,
        )
        .is_err(),
        "factory wide wrapper must refuse a createCell lead"
    );
    assert!(
        generate_rotated_spawn_wide(
            &st, &cc, &bridge(&before_w), &bridge(&after_w), &empty_caveat_manifest(), &before_accounts,
        )
        .is_err(),
        "spawn wide wrapper must refuse a createCell lead"
    );
}
