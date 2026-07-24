//! # Refusal exact-fields epoch + lifecycle payload light-client binding
//!
//! Refusal no longer authenticates a field-reduced surrogate of its audit write.  The deployed wide
//! member opens the reserved raw `u64` key in the canonical FLD2/FLN2 tree, proves the before/after path
//! with full Poseidon2 state16 transitions, feeds both eight-lane roots into the faithful outer state
//! commitment, and publishes the complete 32-byte audit as sixteen canonical u16 public inputs.  The
//! legacy scalar `map_op` is absent.  The full-node verifier recomputes those sixteen limbs from the
//! trusted Turn effect; a statement-only light client must supply the same expected public statement.
//!
//! This file pins three facts: the exact descriptor/ABI shape, one honest end-to-end proof and all
//! sixteen public-audit mutation refusals, plus the existing cell-lifecycle payload hash weld.  The
//! structural test is cheap; the proof test belongs on the proof-heavy path.

// (formerly `#![cfg(feature = "prover")]` — that dregg-circuit feature is GONE; the
// descriptor-level prove/verify (`prove_vm_descriptor2`/`verify_vm_descriptor2`) is
// now unconditional in dregg-circuit, so this test compiles + runs by default.)

use dregg_cell::{Cell, Ledger};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, VmConstraint2, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_LIFECYCLE, REFUSAL_EXACT_AUDIT_PI_BASE, REFUSAL_EXACT_AUDIT_PI_LEN,
    REFUSAL_WRITE_HOST_WIDTH, ROT_PI_COUNT, RotatedBlockWitness, WIDE_CARRIER_APPENDIX,
    compact_e1_columns, compact_s2_columns, empty_caveat_manifest,
    generate_rotated_effect_vm_trace, generate_rotated_refusal_write_wide,
    rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect, bytes32_to_8_limbs};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_turn::rotation_witness as rw;

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

/// The producer's before-cell (the pre-state the turn opens over).
fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("37 pre-iroot limbs")
}

fn h8(b: &[u8; 32]) -> [BabyBear; 8] {
    bytes32_to_8_limbs(blake3::hash(b).as_bytes())
}

/// `true` iff `prove_vm_descriptor2` + `verify_vm_descriptor2` ACCEPT (the light-client path).
/// `false` iff `prove` refuses (Err/panic) or the proof fails to verify.
fn accepts(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<dregg_circuit::heap_root::HeapLeaf>],
) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, dpis, mem_boundary, map_heaps).ok()?;
        verify_vm_descriptor2(desc, &proof, dpis).ok()
    }));
    matches!(r, Ok(Some(())))
}

/// **THE FULL-NODE OFF-CELL ANCHOR (modelled).** The deployed full-node verifier (`proof_verify.rs`
/// step 6b) recomputes PI[46] from the TRUSTED pre-cell + the effect — it has the ledger. We model that
/// by overriding `dpis[ROT_PI_COUNT]` with the HONEST post-payload limb (the value the full node
/// recomputes by `apply_effect_to_cell(trusted pre, effect)` then `compute_authority_digest_felt(post)`
/// / `lifecycle_felt_cell(post)`). A LEDGERLESS LIGHT CLIENT CANNOT do this — it has no pre-cell — so
/// this anchor is the light-client-vs-full-node discriminator: with it the forge rejects (full node);
/// without it the forge is accepted (light client — the OPEN residual STAGE B must close).
fn full_node_anchor(dpis: &mut [BabyBear], honest_anchor: BabyBear) {
    dpis[ROT_PI_COUNT] = honest_anchor;
}

/// The folded audit-value felt the refusal writes at the reserved audit slot — the in-circuit map-op's
/// inserted VALUE, light-client-recomputable from the published refusal params. It is
/// `fold_bytes32(audit_bytes)` where `audit_bytes` is the deployed
/// `apply_refusal` audit fold (`blake3("dregg-refusal-audit-v1", offered_action_commitment, reason)`);
/// the post-cell carries it at `fields_map[REFUSAL_AUDIT_EXT_KEY]`.
fn refusal_audit_value(after_cell: &Cell) -> [u8; 32] {
    after_cell
        .state
        .fields_map
        .get(&dregg_cell::state::REFUSAL_AUDIT_EXT_KEY)
        .copied()
        .expect("a refused cell carries the audit slot in fields_map")
}

/// The refusal epoch is an exact statement, not the former scalar map-op approximation.  Its descriptor
/// has a state16 permutation table, no `MapOp`, and publishes every byte of the raw audit commitment as
/// sixteen canonical u16 limbs before the DFA and faithful-state tails.  This structural tooth is cheap
/// enough for the default suite and catches accidental fallback to the collision-prone one-felt ABI.
#[test]
fn refusal_exact_statement_is_raw_state16_and_nonlegacy() {
    let balance: i64 = 50_000;
    let before_cell = producer_cell(balance, 0);
    let cell_id = before_cell.id();
    let kernel_effect = dregg_turn::Effect::Refusal {
        cell: cell_id,
        offered_action_commitment: [11u8; 32],
        refusal_reason: dregg_turn::action::RefusalReason::Declined,
        proof_witness_index: 0,
    };

    let vm_effect = Effect::Refusal {
        target: h8(cell_id.as_bytes()),
        reason_hash: bytes32_to_8_limbs(&[0u8; 32]),
    };
    let st = CellState::new(balance as u64, 0);
    let effects = vec![vm_effect];
    let mut honest_after = producer_cell(balance, 0);
    rw::apply_effect_to_cell(&mut honest_after, &cell_id, &kernel_effect, 100);
    let mut ledger = Ledger::new();
    ledger.insert_cell(honest_after.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

    let before_w = rw::produce(
        &before_cell,
        &Ledger::new(),
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &honest_after,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );

    let caveat = empty_caveat_manifest();
    let before_leaves = dregg_cell::state::exact_fields_root_leaves(&before_cell.state.fields_map);
    let audit_value = refusal_audit_value(&honest_after);
    let (mut trace, dpis, map_heaps) = generate_rotated_refusal_write_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
        &before_leaves,
        audit_value,
    )
    .expect("exact wide refusal generation");

    assert!(
        map_heaps.is_empty(),
        "the exact epoch must not use scalar map-op heaps"
    );
    assert_eq!(dpis.len(), 90);
    assert_eq!(
        trace[0].len(),
        REFUSAL_WRITE_HOST_WIDTH + WIDE_CARRIER_APPENDIX
    );
    let raw_limbs = dregg_circuit::exact_nullifier_aafi::raw_to_u16_le(audit_value);
    for (lane, expected) in raw_limbs.into_iter().enumerate() {
        assert_eq!(
            dpis[REFUSAL_EXACT_AUDIT_PI_BASE + lane],
            BabyBear::new(u32::from(expected)),
            "audit PI lane {lane} must publish the raw canonical u16 limb"
        );
    }

    compact_s2_columns(&mut trace, "refusalVmDescriptor2R24").expect("exact refusal S2 compaction");
    compact_e1_columns(&mut trace, "refusalVmDescriptor2R24").expect("exact refusal E1 compaction");
    let desc = parse_vm_descriptor2(wide_json("refusalVmDescriptor2R24"))
        .expect("exact refusal descriptor parses");
    assert_eq!(desc.trace_width, exact_refusal_committed_width());
    assert_eq!(desc.public_input_count, 90);
    assert_eq!(
        trace[0].len(),
        exact_refusal_compacted_producer_width(),
        "the gentian floor-refuse columns are prover-filled, not producer-emitted"
    );
    assert!(
        desc.tables
            .iter()
            .any(|table| table.id == 9 && table.arity == 33)
    );
    assert!(
        desc.constraints
            .iter()
            .all(|constraint| !matches!(constraint, VmConstraint2::MapOp(_))),
        "exact refusal must not retain the legacy one-felt map-op"
    );
}

/// The declared payload-hash column the lifecycle-payload gate welds the AFTER lifecycle limb to:
/// `prmCol 3` = `PARAM_BASE + 3` (col 71). A FREE param column for all three lifecycle movers; the
/// producer fills it with the felt-domain `lifecycle_felt`, the LIGHT CLIENT recomputes it from the
/// PI-bound `reason_hash` + the turn-header height. `EffectVmEmitRotationV3.declaredLifecyclePayloadCol`.
const LC_PAYLOAD_COL: usize = dregg_circuit::effect_vm::columns::PARAM_BASE + 3;

/// **The lifecycle PAYLOAD — the light-client residual is CLOSED (the in-circuit lifecycle-payload HASH
/// gate).** The deployed `cellSealVmDescriptor2R24` now carries, BESIDE the disc gate, the in-circuit
/// `lifecyclePayloadHashGate`: a selector-gated weld of the AFTER lifecycle limb (`B_LIFECYCLE = 29`) to
/// the declared payload-hash column `prmCol 3`. The producer fills `prmCol 3` with the FELT-DOMAIN
/// `lifecycle_felt(disc, reason_hash, sealed_at)` — recomputable in-circuit from the LIGHT-CLIENT-KNOWN
/// inputs (the PI-bound `reason_hash` + the turn-header `block_height`), NOT a byte-packed sponge the gate
/// cannot open. So a cellSeal whose committed AFTER lifecycle limb DIVERGES from the recomputed payload
/// hash (a forged `reason_hash` / `sealed_at` riding a committed limb the producer did NOT derive from
/// the declared payload) is UNSAT through `verify_vm_descriptor2` ALONE — the LIGHT-CLIENT path, NO
/// off-cell anchor. This is the LIVE realization of
/// `EffectVmEmitRotationV3.cellSealV3_payload_rejects_forged_lightclient`, threaded to the apex.
#[test]
fn lifecycle_payload_forge_rejected_by_hash_gate_anchor_disabled() {
    let balance: i64 = 50_000;

    let before_cell = producer_cell(balance, 0);
    let cell_id = before_cell.id();
    let honest_reason = [22u8; 32];
    let honest_kernel = dregg_turn::Effect::CellSeal {
        target: cell_id,
        reason: honest_reason,
    };
    let vm_effect = Effect::CellSeal {
        target: h8(cell_id.as_bytes()),
        reason_hash: h8(&honest_reason),
    };
    let name = rotated_descriptor_name_for_effect(&vm_effect)
        .expect("CellSeal is a rotated cohort member");
    assert_eq!(name, "cellSealVmDescriptor2R24");
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
        .expect("rotated cellSeal descriptor parses");
    assert_eq!(
        desc.public_input_count, 51,
        "cellSeal PIs = 50 rotated base (46 + 4 dsl rc) + 1 appended record pin = 51 \
         (committed cellSealVmDescriptor2R24)"
    );

    let st = CellState::new(balance as u64, 0);
    let effects = vec![vm_effect];

    let mut honest_after = producer_cell(balance, 0);
    rw::apply_effect_to_cell(&mut honest_after, &cell_id, &honest_kernel, 100);

    let mut ledger = Ledger::new();
    ledger.insert_cell(honest_after.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

    let before_w = rw::produce(
        &before_cell,
        &Ledger::new(),
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &honest_after,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );

    assert_ne!(
        before_w.pre_limbs[B_LIFECYCLE], after_w.pre_limbs[B_LIFECYCLE],
        "the seal MOVES the AFTER lifecycle limb (Live -> Sealed) — non-vacuity"
    );

    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce a cellSeal trace + 47 PIs");

    // The honest declared payload-hash column IS the felt-domain `lifecycle_felt` of the sealed cell —
    // the value the light client recomputes from `(disc=Sealed, reason_hash, block_height)`. It equals
    // the committed AFTER lifecycle limb (the gate's weld is honest by construction).
    let honest_payload_felt = after_w.pre_limbs[B_LIFECYCLE];
    assert_eq!(
        trace[0][LC_PAYLOAD_COL], honest_payload_felt,
        "the producer fills prmCol 3 with the felt-domain lifecycle_felt (= the AFTER limb)"
    );

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // POSITIVE TOOTH (no downgrade): the honest cellSeal — with the gate's weld satisfied — proves +
    // verifies on the light-client path.
    assert!(
        accepts(&desc, &trace, &dpis, &mem_boundary, &map_heaps),
        "NO DOWNGRADE: the honest cellSeal (AFTER lifecycle limb == recomputed payload hash) must prove + \
         verify through the light-client path"
    );

    // THE FORGE (light-client, anchor-disabled): a cellSeal forged to differ ONLY in the sealing PAYLOAD
    // — a committed AFTER lifecycle limb (`B_LIFECYCLE`) that does NOT equal the recomputed payload hash
    // the light client holds in `prmCol 3`. We pin `prmCol 3` to the HONEST recomputed felt (what the
    // light-client verifier supplies from the PI-bound reason_hash + height) and forge ONLY the committed
    // limb. The `lifecyclePayloadHashGate` (`sel · (after_lc − prmCol3)`) then has NO satisfying
    // assignment on the active seal row: `after_lc != prmCol3`, so `prove_vm_descriptor2` REFUSES.
    let mut forged_trace = trace.clone();
    let forged_payload_limb = honest_payload_felt + BabyBear::new(1);
    for row in forged_trace.iter_mut() {
        // forge the committed AFTER lifecycle limb; KEEP prmCol 3 at the recomputed payload hash.
        row[AFTER_BASE + B_LIFECYCLE] = forged_payload_limb;
        // (We deliberately do NOT re-derive the commitment chain — the in-circuit gate alone rejects the
        // forged limb vs the recomputed payload column, independent of the commitment pins.)
    }

    // THE LIGHT-CLIENT CLOSE (anchor-disabled): with the producer-free dpis — exactly what the deployed
    // `verify_effect_vm_rotated_with_cutover` runs — the forged-payload cellSeal is now REJECTED. The
    // `lifecyclePayloadHashGate` makes the forged committed lifecycle limb UNSAT vs the recomputed payload
    // hash. NO full-node anchor.
    assert!(
        !accepts(&desc, &forged_trace, &dpis, &mem_boundary, &map_heaps),
        "LIGHT-CLIENT CLOSE: a cellSeal forged to publish an AFTER lifecycle limb that is NOT the \
         recomputed lifecycle_felt(disc, reason_hash, block_height) is REJECTED through \
         verify_vm_descriptor2 ALONE — the in-circuit lifecycle-payload hash gate bites for a ledgerless \
         client (NO off-cell anchor). This is the residual the opaque byte-packed lifecycle_felt could NOT \
         close; the felt-domain realization makes limb 29 recomputable + bindable."
    );

    // NON-VACUITY of the close: the forge perturbs ONLY the committed AFTER lifecycle limb (col
    // `AFTER_BASE + B_LIFECYCLE`); every other column (incl. the recomputed `prmCol 3`) is unchanged — so
    // the rejection is the gate's weld biting on the forged limb, not an unrelated trace malformation.
    assert!(
        forged_trace.iter().zip(trace.iter()).all(|(f, h)| f
            .iter()
            .enumerate()
            .all(|(c, v)| c == AFTER_BASE + B_LIFECYCLE || *v == h[c])),
        "the forge perturbs ONLY the after-lifecycle limb (29) — the rejection is the payload hash gate \
         biting on the forged limb, not an unrelated trace break"
    );

    // CONTRAST (the full-node leg is ALSO sound, belt-and-suspenders): the off-cell anchor likewise
    // rejects — but the gate above already closed it WITHOUT the anchor (the light-client property).
    let mut anchored_forged_dpis = dpis.clone();
    full_node_anchor(&mut anchored_forged_dpis, honest_payload_felt);
    assert!(
        !accepts(
            &desc,
            &forged_trace,
            &anchored_forged_dpis,
            &mem_boundary,
            &map_heaps
        ),
        "FULL-NODE leg also sound (belt-and-suspenders): the off-cell anchor likewise rejects the \
         forged-payload limb"
    );

    eprintln!(
        "VK-EPOCH FAMILY-2 lifecycle payload: DISC closed (disc gate) AND PAYLOAD closed (in-circuit \
         lifecycle-payload hash gate — forge REJECTED anchor-disabled). The felt-domain lifecycle_felt \
         makes limb 29 recomputable from (disc, reason_hash, block_height); the gate welds it \
         (EffectVmEmitRotationV3.cellSealV3_payload_rejects_forged_lightclient → the apex)."
    );
}

/// The number of columns THIS member's own E1 kill-set deletes, summed from the Lean-emitted
/// `E1_COMPACT_TABLE` (the single source `compact_e1_columns` itself drains).
fn e1_killed(key: &str) -> usize {
    dregg_circuit::effect_vm::e1_compact_generated::E1_COMPACT_TABLE
        .iter()
        .find(|(k, _)| *k == key)
        .map(|(_, runs)| runs.iter().map(|(a, b)| b - a).sum())
        .unwrap_or_else(|| panic!("{key} not in E1_COMPACT_TABLE"))
}

/// The exact refusal producer's row width AFTER both flag-day deletions — what
/// `compact_s2_columns` + `compact_e1_columns` leave behind.
fn exact_refusal_compacted_producer_width() -> usize {
    REFUSAL_WRITE_HOST_WIDTH + WIDE_CARRIER_APPENDIX
        - dregg_circuit::effect_vm::s2_compact_generated::S2_DELETED_COLS
        - e1_killed("refusalVmDescriptor2R24")
}

/// The COMMITTED width of the deployed exact refusal member, DERIVED rather than hand-pinned: the
/// compacted producer row PLUS the gentian floor-refuse aux block, which the PROVER fills
/// (`fill_refuse_aux`, after the producer's `compact_e1`) and the producer never emits. The
/// bare-cohort emit allocates the block a full `CAPACITY_TAGS · REFUSE_STRIDE` (48) — three
/// columns past the 45 the last block's `floor_col` actually reaches.
///
/// This USED to be the literal `2097`, and it was WRONG at HEAD by exactly the amount our own
/// `3ebf42e25f` narrowed the E1 kill-set (106 → 94 columns): a hand-pinned literal over a surface
/// two flag-days move. Every term now comes from its own Lean-emitted source, so a stride / kill-set
/// / carrier-block change moves this tooth with it instead of stranding it.
fn exact_refusal_committed_width() -> usize {
    use dregg_circuit::effect_vm::bare_floor_refuse_weld as refuse;
    exact_refusal_compacted_producer_width() + refuse::CAPACITY_TAGS.len() * refuse::REFUSE_STRIDE
}

/// Resolve a WIDE-registry descriptor JSON by registry KEY (col 0) from the committed staged TSV.
fn wide_json(name: &str) -> &'static str {
    dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV
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

/// The deployed exact refusal proves and verifies end to end.  FLD2/FLN2 membership and update are
/// served by the raw state16 chip; the before/after eight-lane fields roots feed the ordinary faithful
/// state commitments; and the verifier-visible audit is the complete 32-byte value, not a field fold.
#[test]
fn wide_fields_write_proves_and_verifies() {
    let balance: i64 = 50_000;
    let before_cell = producer_cell(balance, 0);
    let cell_id = before_cell.id();
    let kernel_effect = dregg_turn::Effect::Refusal {
        cell: cell_id,
        offered_action_commitment: [11u8; 32],
        refusal_reason: dregg_turn::action::RefusalReason::Declined,
        proof_witness_index: 0,
    };
    let vm_effect = Effect::Refusal {
        target: h8(cell_id.as_bytes()),
        reason_hash: bytes32_to_8_limbs(&[0u8; 32]),
    };
    let st = CellState::new(balance as u64, 0);
    let effects = vec![vm_effect];

    let mut honest_after = producer_cell(balance, 0);
    rw::apply_effect_to_cell(&mut honest_after, &cell_id, &kernel_effect, 100);

    let mut ledger = Ledger::new();
    ledger.insert_cell(honest_after.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &Ledger::new(),
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &honest_after,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let caveat = empty_caveat_manifest();
    let before_leaves = dregg_cell::state::exact_fields_root_leaves(&before_cell.state.fields_map);
    let audit_value = refusal_audit_value(&honest_after);

    let (mut trace, dpis, map_heaps) = generate_rotated_refusal_write_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
        &before_leaves,
        audit_value,
    )
    .expect("wide refusal fields-write generation");

    let name = "refusalVmDescriptor2R24";
    let desc = parse_vm_descriptor2(wide_json(name)).unwrap();
    compact_s2_columns(&mut trace, name).expect("exact refusal S2 compaction");
    compact_e1_columns(&mut trace, name).expect("exact refusal E1 compaction");
    assert_eq!(
        desc.trace_width,
        exact_refusal_committed_width(),
        "the exact wide host after the S2 + E1 deletions, plus the prover-filled gentian block"
    );
    assert_eq!(
        desc.public_input_count, 90,
        "46 rotated + 8 authority + 16 raw-audit + 4 DFA + 16 wide anchors"
    );
    assert_eq!(trace[0].len(), exact_refusal_compacted_producer_width());
    assert_eq!(dpis.len(), 90);
    assert!(map_heaps.is_empty());

    let mb = MemBoundaryWitness::default();
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mb, &map_heaps)
        .unwrap_or_else(|e| panic!("exact refusal WIDE proof must prove: {e}"));
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .unwrap_or_else(|e| panic!("exact refusal WIDE proof must verify: {e}"));

    // Every raw-audit limb is part of the proof statement.  Altering any one lane while keeping the
    // proof fixed must fail; exercise all sixteen to prevent an off-by-one ABI regression.
    for lane in 0..REFUSAL_EXACT_AUDIT_PI_LEN {
        let mut forged = dpis.clone();
        forged[REFUSAL_EXACT_AUDIT_PI_BASE + lane] += BabyBear::ONE;
        assert!(
            verify_vm_descriptor2(&desc, &proof, &forged).is_err(),
            "raw audit PI lane {lane} must be proof-bound"
        );
    }
    eprintln!(
        "EXACT refusal: PROVED + VERIFIED (FLD2/FLN2 state16 update, faithful eight-lane outer \
         commitments, 16 raw audit u16 public limbs); every audit-lane mutation was rejected."
    );
}
