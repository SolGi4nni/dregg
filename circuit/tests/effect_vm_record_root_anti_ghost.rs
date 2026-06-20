//! RECORD-LAYER STAGE 2 — the EffectVM `record` descriptor binds the user-field-map
//! `fields_root` into `state_commit` (the GROUP-4 hash chain), with the anti-ghost tooth.
//!
//! This is the DIRECT (FRI-free + real-Plonky3) verification of the Lean keystone
//! `Dregg2.Circuit.Emit.EffectVmEmitRecordRoot.recordDescriptor_commit_binds_fieldsRoot`:
//! the runnable `dregg-effectvm-record-v1` descriptor (transfer + GROUP-4 site 3's spare 4th
//! input now absorbing col 89 = `state_after.FIELDS_ROOT` = the RESERVED carrier) is run
//! through the SAME generic interpreter (`EffectVmDescriptorAir`) the cutover prover uses.
//!
//! Three teeth, all over the real `check_all_constraints` predicate + real prove/verify:
//!   * LEGACY NO-OP (SAT): with the carrier = 0 (empty map), the record descriptor accepts the
//!     honest transfer base trace BYTE-IDENTICALLY (state_commit = H4(i1,i2,i3,0), unchanged).
//!   * POPULATED-MAP HONEST (SAT): with a NON-ZERO `fields_root` in the carrier and the row's
//!     `state_commit` recomputed as H4(i1,i2,i3,fields_root), the record descriptor accepts +
//!     proves + verifies.
//!   * ANTI-GHOST (UNSAT): tampering the committed map root cell (col 89) WITHOUT updating
//!     state_commit makes the record descriptor REJECT (and refuse to prove) — the map field is
//!     genuinely bound. A `fields_root := 0` stub would make the populated-honest commitment equal
//!     the legacy one and collapse this tooth (forbidden).

use dregg_circuit::effect_vm::{
    CellState, Effect, STATE_AFTER_BASE, STATE_BEFORE_BASE, generate_effect_vm_trace, state,
};
use dregg_circuit::effect_vm_descriptors::descriptor_for_name;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{
    descriptor_air_accepts, parse_vm_descriptor, prove_vm_descriptor, verify_vm_descriptor,
};
use dregg_circuit::poseidon2::hash_4_to_1;

/// The carrier column (absolute index) for `fields_root` in `state_after`: col 89.
const FIELDS_ROOT_COL: usize = STATE_AFTER_BASE + state::RESERVED;

/// Recompute the row's `state_commit` as the record-layer GROUP-4 digest
/// `H4(inter1, inter2, inter3, fields_root)` — the SAME tree as transfer but with the 4th
/// root input set to the carrier `fields_root` instead of zero. Returns the felt to write
/// into `state_after.state_commit`.
fn record_state_commit(row: &[BabyBear], fields_root: BabyBear) -> BabyBear {
    let sa = |off: usize| row[STATE_AFTER_BASE + off];
    let inter1 = hash_4_to_1(&[
        sa(state::BALANCE_LO),
        sa(state::BALANCE_HI),
        sa(state::NONCE),
        sa(state::FIELD_BASE),
    ]);
    let inter2 = hash_4_to_1(&[
        sa(state::FIELD_BASE + 1),
        sa(state::FIELD_BASE + 2),
        sa(state::FIELD_BASE + 3),
        sa(state::FIELD_BASE + 4),
    ]);
    let inter3 = hash_4_to_1(&[
        sa(state::FIELD_BASE + 5),
        sa(state::FIELD_BASE + 6),
        sa(state::FIELD_BASE + 7),
        sa(state::CAP_ROOT),
    ]);
    hash_4_to_1(&[inter1, inter2, inter3, fields_root])
}

/// Same record-layer GROUP-4 tree over the `state_before` block (used for row 0's pre-state
/// commit, which also binds the populated map root).
fn record_state_commit_before(row: &[BabyBear], fields_root: BabyBear) -> BabyBear {
    let sb = |off: usize| row[STATE_BEFORE_BASE + off];
    let inter1 = hash_4_to_1(&[
        sb(state::BALANCE_LO),
        sb(state::BALANCE_HI),
        sb(state::NONCE),
        sb(state::FIELD_BASE),
    ]);
    let inter2 = hash_4_to_1(&[
        sb(state::FIELD_BASE + 1),
        sb(state::FIELD_BASE + 2),
        sb(state::FIELD_BASE + 3),
        sb(state::FIELD_BASE + 4),
    ]);
    let inter3 = hash_4_to_1(&[
        sb(state::FIELD_BASE + 5),
        sb(state::FIELD_BASE + 6),
        sb(state::FIELD_BASE + 7),
        sb(state::CAP_ROOT),
    ]);
    hash_4_to_1(&[inter1, inter2, inter3, fields_root])
}

#[test]
fn record_descriptor_binds_fields_root_and_rejects_map_tamper() {
    // A single honest transfer turn — the record descriptor shares transfer's per-row gates,
    // so a transfer trace is its honest base witness.
    let st = CellState::new(100_000, 0);
    let effects = vec![Effect::Transfer {
        amount: 50,
        direction: 1,
    }];
    let (base_trace, pis) = generate_effect_vm_trace(&st, &effects);
    assert_eq!(
        base_trace[0].len(),
        188,
        "canonical 188-col layout (width-neutral)"
    );

    let json = descriptor_for_name("dregg-effectvm-record-v1")
        .expect("record descriptor must be registered");
    let desc = parse_vm_descriptor(json).expect("record descriptor must parse");
    assert_eq!(
        desc.trace_width, 188,
        "record descriptor is width-neutral (188)"
    );
    let dpis = &pis[..desc.public_input_count];
    let last = base_trace.len() - 1;

    // ---- (1) LEGACY NO-OP: carrier = 0 (the trace generator leaves RESERVED = 0 on a
    //          transfer row), so state_commit = H4(i1,i2,i3,0). The record descriptor accepts
    //          the honest transfer base trace byte-identically. ----
    assert_eq!(
        base_trace[last][FIELDS_ROOT_COL],
        BabyBear::ZERO,
        "transfer base row carries fields_root = 0 (legacy / empty map)"
    );
    assert!(
        descriptor_air_accepts(&desc, &base_trace, dpis),
        "record descriptor must ACCEPT the honest legacy (fields_root=0) transfer trace"
    );
    let legacy_proof = prove_vm_descriptor(&desc, &base_trace, dpis)
        .expect("record descriptor must PROVE the honest legacy witness");
    verify_vm_descriptor(&desc, &legacy_proof, dpis)
        .expect("record descriptor legacy proof must independently verify");

    // ---- (2) POPULATED-MAP HONEST: a cell whose committed user-field map is non-empty across
    //          this transfer. The transfer frame FREEZES the map (the cell isn't writing it), so
    //          `fields_root` is the SAME in state_before and state_after (the `gResPass` frame
    //          gate over the carrier holds). We recompute each row's state_after.state_commit as
    //          H4(i1,i2,i3,fields_root). The record descriptor accepts + proves + verifies. ----
    let fields_root = BabyBear::new(424_242); // a populated user-field-map digest
    let mut honest = base_trace.clone();
    // (a) carrier fields_root set in BOTH state_before and state_after on every row (the cell's
    //     committed map is non-empty and FROZEN across this idle/transfer chain), so the frame
    //     `gResPass` passthrough over the carrier holds. (b) recompute state_after.state_commit as
    //     H4(i1,i2,i3,fields_root) on every row. (c) thread the recomputed commit into the NEXT
    //     row's state_before.state_commit so the `transition` continuity holds.
    let sb_commit = STATE_BEFORE_BASE + state::STATE_COMMIT;
    let sa_commit = STATE_AFTER_BASE + state::STATE_COMMIT;
    let mut prev_after_commit: Option<BabyBear> = None;
    for row in honest.iter_mut() {
        row[STATE_BEFORE_BASE + state::RESERVED] = fields_root;
        row[FIELDS_ROOT_COL] = fields_root;
        // chain: this row's state_before.commit = previous row's state_after.commit.
        if let Some(pc) = prev_after_commit {
            row[sb_commit] = pc;
        } else {
            // row 0: state_before is the populated PRE-state; its commit also binds fields_root.
            row[sb_commit] = record_state_commit_before(row, fields_root);
        }
        let new_after = record_state_commit(row, fields_root);
        row[sa_commit] = new_after;
        prev_after_commit = Some(new_after);
    }
    // The published OLD_COMMIT / NEW_COMMIT PIs track the row-0 state_before / last-row state_after
    // recomputed commits (the boundary pins read these).
    let mut hpis = pis.clone();
    {
        use dregg_circuit::effect_vm::pi;
        hpis[pi::OLD_COMMIT] = honest[0][sb_commit];
        hpis[pi::NEW_COMMIT] = honest[last][sa_commit];
    }
    let hdpis = &hpis[..desc.public_input_count];
    assert!(
        descriptor_air_accepts(&desc, &honest, hdpis),
        "record descriptor must ACCEPT an honest POPULATED-map row (fields_root bound)"
    );
    let pop_proof = prove_vm_descriptor(&desc, &honest, hdpis)
        .expect("record descriptor must PROVE the honest populated-map witness");
    verify_vm_descriptor(&desc, &pop_proof, hdpis)
        .expect("record descriptor populated proof must independently verify");

    // NON-VACUITY: the populated commit DIFFERS from the legacy commit (a `fields_root := 0`
    // stub would make these EQUAL — forbidden).
    assert_ne!(
        honest[last][STATE_AFTER_BASE + state::STATE_COMMIT],
        base_trace[last][STATE_AFTER_BASE + state::STATE_COMMIT],
        "populated-map state_commit must DIFFER from the legacy state_commit (binding is load-bearing)"
    );

    // ---- (3) ANTI-GHOST: tamper the committed map root cell (col 89) WITHOUT updating
    //          state_commit. The GROUP-4 site-3 binding (state_commit == H4(.., fields_root))
    //          now fails, so the record descriptor REJECTS and refuses to prove. ----
    {
        let mut tampered = honest.clone();
        tampered[last][FIELDS_ROOT_COL] = tampered[last][FIELDS_ROOT_COL] + BabyBear::new(1);
        assert!(
            !descriptor_air_accepts(&desc, &tampered, hdpis),
            "ANTI-GHOST: record descriptor took a tampered fields_root cell (map field NOT bound)"
        );
        assert!(
            prove_vm_descriptor(&desc, &tampered, hdpis).is_err(),
            "ANTI-GHOST: record descriptor PROVED a tampered fields_root"
        );
    }

    // ---- (3b) ANTI-GHOST dual: tamper the last-row state_commit cell (the published commitment)
    //          WITHOUT changing fields_root — also UNSAT (the digest no longer matches). ----
    {
        let mut tampered = honest.clone();
        tampered[last][STATE_AFTER_BASE + state::STATE_COMMIT] =
            tampered[last][STATE_AFTER_BASE + state::STATE_COMMIT] + BabyBear::new(1);
        assert!(
            !descriptor_air_accepts(&desc, &tampered, hdpis),
            "ANTI-GHOST: record descriptor took a forged published state_commit"
        );
    }
}
