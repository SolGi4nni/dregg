//! # THE CAP-OPEN FAN-OUT PROVE-THROUGHS — the AUTHORITY-crown members, end-to-end.
//!
//! Seven deployed `<effect>CapOpenVmDescriptor2R24` members had NO prove+verify roundtrip anywhere
//! (`producer_descriptor_coverage_gate`'s cap-open block carried them as `Uncovered("no cap-open
//! prove-through test exists for this member")`). That was a MISSING TEST, not a prover wall: the
//! blanket "IR-v2 cap-node lookup multiplicity gap" the block used to name for the whole family was
//! withdrawn on 2026-07-26 and re-measured as a row-0 witness gap, and the transfer / attenuate /
//! exercise members prove through today. This file writes the missing tests.
//!
//! Each test resolves its member from the COMMITTED registry (`V3_STAGED_REGISTRY_TSV`), builds a
//! genuine rotated base trace for that effect through the deployed producer, widens it with the
//! depth-16 cap-membership crown at the member's OWN effect-kind bit, and drives it through
//! `prove_vm_descriptor2` + `verify_vm_descriptor2`.
//!
//! LAW #1: this file fills COLUMNS only. Every constraint is the Lean-declared chip lookup / base
//! gate the IR-v2 interpreter realizes generically from the committed descriptor — the AIR is
//! authored in `metatheory/Dregg2/Circuit/Emit/CapOpenEmit.lean` and emitted to the registry TSV.
//! No constraint, gadget or descriptor is hand-written here.
//!
//! ## The two base faces, read off the committed descriptors
//!
//! The fan-out splits into two base shapes, and the split is visible in the committed constraints:
//!
//!   * **nonce-FREEZE + cap-root ADVANCE** (`delegate`, `grantCap`, `revokeCapability`): the member
//!     carries `(c78 − c56) == 0` (after.nonce == before.nonce) and `(c87 − c70) == 0` (after
//!     cap_root == param2). That is exactly `patch_attenuate_base_for_cap_open`'s job, and it is
//!     what the deployed SDK route sets `needs_attenuate_patch: true` for.
//!   * **nonce-TICK passthrough** (`introduce`, `revoke`, `refreshDelegation`, `spawn`): the member
//!     carries `(c78 − c56) − (1 − sel[NOOP]) == 0` and `(c87 − c65) == 0` (cap_root FROZEN). The
//!     bare generator already emits that face; the patch would BREAK it.
//!
//! ## The `effBit` crown
//!
//! Every member pins its own effect-kind bit into the `effBit` column (`CAP_OPEN_BASE + 296` =
//! absolute col 1943) via `effBitGateFor`, and forces the corresponding bit of the leaf's full mask
//! (`selectedBitGate`). Read off the committed JSON: delegate/revoke/refresh/spawn = `1<<16`,
//! introduce = `1<<13`, grantCap = `1<<2`, revokeCapability = `1<<3`. The held cap is a BROAD honest
//! cap (`EFFECT_ALL` — both mask limbs `0xFFFF`), which the genuine submask membership admits.
//!
//! Run: `cargo test -p dregg-circuit --test cap_open_fanout_prove_through -- --test-threads=4`.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    CAP_OPEN_BASE, CAP_OPEN_WIDTH, CapOpenWitness, DFA_RC_LEN, RotatedBlockWitness,
    SIGNATURE_AUTH_TAG, empty_caveat_manifest,
    generate_rotated_create_cell_trace_with_accounts_tree, generate_rotated_effect_vm_trace,
    patch_attenuate_base_for_cap_open, widen_to_cap_open,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_turn::rotation_witness as rw;

// ── The deployed `cell/facet.rs` effect-kind bits (`1 << n`), mirroring the SDK's cap-open router.
const EFFECT_GRANT_CAPABILITY: u32 = 1 << 2;
const EFFECT_REVOKE_CAPABILITY: u32 = 1 << 3;
const EFFECT_INTRODUCE: u32 = 1 << 13;
const EFFECT_DELEGATION_OPS: u32 = 1 << 16;

/// The absolute `effBit` column (`CAP_OPEN_BASE + 296`) — what `effBitGateFor` pins.
const EFF_BIT_COL: usize = CAP_OPEN_BASE + 296;
/// The absolute `src` column (`CAP_OPEN_BASE + 295`) — what `targetBindGate` roots.
const SRC_COL: usize = CAP_OPEN_BASE + 295;
/// The absolute `cap_root` group base (`CAP_OPEN_BASE + 287`, 8 lanes) — what `rootPinGate` binds.
const CAP_ROOT_COL: usize = CAP_OPEN_BASE + 287;

/// Resolve a registry descriptor JSON by key from the COMMITTED staged TSV. Never a hand-built
/// descriptor — the point of the gate is that the light client's own bytes accept the producer.
fn reg_json(name: &str) -> &'static str {
    dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV
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
    pk[0] = 9;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
}

/// Which base face a fan-out member rides — read off its COMMITTED constraints, not guessed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BaseFace {
    /// `(c78 − c56) == 0` + `(c87 − c70) == 0`: the nonce-FREEZE / cap-root-ADVANCE face
    /// (`patch_attenuate_base_for_cap_open`). Deployed route: `needs_attenuate_patch: true`.
    FreezeAdvance,
    /// `(c78 − c56) − (1 − sel[NOOP]) == 0` + `(c87 − c65) == 0`: the nonce-TICK passthrough face
    /// the bare generator already emits. Deployed route: `needs_attenuate_patch: false`.
    TickPassthrough,
    /// `TickPassthrough` PLUS the cells-tree accounts grow-gate: `spawnCapOpen` is the one fan-out
    /// member whose committed descriptor carries `map_op`s (`absent` then `aafi_insert` at the
    /// new-cell key, col 68, over the rotated cells-root limb group). Those need the accounts-tree
    /// producer and a NON-EMPTY map heap; the bare generator leaves the ops unwitnessed.
    TickWithAccountsTree,
}

/// Build the rotated base trace + the UNWRAPPED cap-open PI vector + the map-op heaps for `effects`
/// from real before/after producer witnesses, on the face the member declares.
///
/// The cap-open faces were never rc-wrapped in the Lean emit (every committed `*CapOpen*` member
/// carries the UNWRAPPED base), while the v13 generic base appends the 4 dsl rc pins — so the rc
/// tail is lifted off, exactly as the deployed SDK cap-open leg builder does.
#[allow(clippy::type_complexity)]
fn build_base(
    effects: Vec<Effect>,
    face: BaseFace,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, Vec<Vec<HeapLeaf>>) {
    let before_balance: i64 = 100_000;
    let st = CellState::new(before_balance as u64, 0);

    let mut ledger = Ledger::new();
    // Every fan-out effect here is an economic passthrough on the actor row; the nonce ticks (and
    // the FreezeAdvance face then freezes it back through the phase-B patch).
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];

    let produce = |cell: &Cell| {
        rw::produce(
            cell,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &rw::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        )
    };
    let before_w = produce(&before_cell);
    let after_w = produce(&after_cell);

    // Only the Transfer base threads the transfer caveat manifest; every fan-out base uses the
    // empty manifest (mirroring the deployed `RotationTurnWitness::for_effects` routing).
    let caveat = empty_caveat_manifest();
    let (mut trace, mut pis, heaps) = if face == BaseFace::TickWithAccountsTree {
        // The child key is fresh against the (empty) BEFORE accounts set — the `.absent` freshness
        // op brackets via the sentinel range, and a re-spawn of an existing cell id has no
        // bracketing witness and is REFUSED. Same wiring the deployed spawn producer uses.
        let before_accounts: Vec<HeapLeaf> = Vec::new();
        generate_rotated_create_cell_trace_with_accounts_tree(
            &st,
            &effects,
            &bridge(&before_w),
            &bridge(&after_w),
            &caveat,
            &before_accounts,
        )
        .expect("the rotated spawn base trace + accounts grow-gate must generate")
    } else {
        let (trace, pis) = generate_rotated_effect_vm_trace(
            &st,
            &effects,
            &bridge(&before_w),
            &bridge(&after_w),
            &caveat,
        )
        .expect("the rotated fan-out base trace must generate");
        (trace, pis, Vec::new())
    };
    pis.truncate(pis.len() - DFA_RC_LEN);

    let pis = match face {
        // The phase-B wiring: FREEZE the nonce in both v1 blocks + the rotated welds, bind
        // `param2 := after.cap_root`, and rebuild every state/block commit + the four rotated
        // commit PIs. This is the deployed producer routine, not a local re-derivation.
        BaseFace::FreezeAdvance => patch_attenuate_base_for_cap_open(&mut trace, &pis)
            .expect("the phase-B nonce-freeze / cap-root-advance wiring applies"),
        // ⚠ NEVER on a TICK member: the patch's whole job is to freeze the nonce, which is
        // precisely what `(c78 − c56) − (1 − sel[NOOP]) == 0` forbids. This is the measured `#10`
        // half of the old `[#4, #10]` row-0 UNSAT, in its other polarity.
        BaseFace::TickPassthrough | BaseFace::TickWithAccountsTree => pis,
    };
    (trace, pis, heaps)
}

/// A real depth-16 cap-membership witness for `eff_bit`: a BROAD honest cap (`EFFECT_ALL` — both
/// mask limbs `0xFFFF`, so the genuine `(eff_bit & full_mask) == eff_bit` submask admits every
/// fan-out bit) at a non-trivial position in a small c-list, with `src` pinned to `leaf.target`.
///
/// ⚑ `w.eff_bit` is ASSERTED against the requested bit. Until 2026-07-27 `build_for` VALIDATED its
/// `eff_bit` argument against the leaf mask and then stored `WRITE_MASK_LO` regardless — and since
/// `fill_cap_open` writes that field to the `effBit` column the member's `effBitGateFor` pins, every
/// honest fan-out trace was UNSAT for a reason no error message named. This assertion is that bug's
/// regression tooth.
fn fanout_cap_open_witness(eff_bit: u32) -> CapOpenWitness {
    // Leaf fields in CapOpenCols order: [slot_hash, target, auth_tag, mask_lo, mask_hi, expiry,
    // breadstuff]. The fan-out `capOpenConstraintsEff` appendix DECODES the tier off `auth_tag`
    // (no Signature pin) and checks the genuine SUBMASK facet membership, so a broad cap of any
    // tier opens — what it may NOT do is fail to carry the member's own bit.
    let chosen: [BabyBear; 7] = [
        BabyBear::new(0xC0FFEE),           // slot_hash
        BabyBear::new(5_555),              // target (== src, the conferred edge)
        BabyBear::new(SIGNATURE_AUTH_TAG), // auth_tag (Signature tier)
        BabyBear::new(0xFFFF),             // mask_lo (EFFECT_ALL low limb)
        BabyBear::new(0xFFFF),             // mask_hi (EFFECT_ALL high limb — carries bit 16)
        BabyBear::new(0x00FF_FFFF),        // expiry
        BabyBear::new(77),                 // breadstuff
    ];
    // A second, distinct leaf so the c-list is non-trivial and the chosen leaf rides a real
    // membership position (direction bit 1 at level 0) rather than the degenerate slot 0.
    let other: [BabyBear; 7] = [
        BabyBear::new(0xBEEF),
        BabyBear::new(321),
        BabyBear::new(1),
        BabyBear::new(1),
        BabyBear::new(0),
        BabyBear::new(9),
        BabyBear::new(0),
    ];
    let w = CapOpenWitness::build_for(&[other, chosen], 1, eff_bit)
        .expect("the broad honest cap permits the member's effect-kind bit");
    assert_eq!(
        w.eff_bit, eff_bit,
        "CapOpenWitness::build_for MUST store the effect-kind bit it validated — a witness that \
         silently reports EFFECT_TRANSFER makes every fan-out member UNSAT at the effBit gate"
    );
    assert_eq!(
        w.recomposes(),
        w.cap_root,
        "the membership path must recompose the committed cap_root (absorb-node fold)"
    );
    assert_eq!(
        w.src, w.leaf[1],
        "src must equal the leaf target (the targetBind edge)"
    );
    w
}

/// Assert a MUTATED trace is refused: the honest witness is the ONLY thing that proves. Returns the
/// prover/verifier diagnostic so each test can report the exact red it produced.
fn assert_refused(
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    map_heaps: &[Vec<HeapLeaf>],
    what: &str,
) -> String {
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_vm_descriptor2(desc, trace, dpis, &MemBoundaryWitness::default(), map_heaps)
            .and_then(|p| verify_vm_descriptor2(desc, &p, dpis))
    }));
    let diag = match outcome {
        Err(_) => "prover PANICKED (constraint unsatisfied)".to_string(),
        Ok(Err(e)) => format!("{e:?}"),
        Ok(Ok(())) => panic!(
            "[{}] TOOTHLESS: {what} still proved AND verified. A cap-open test that cannot be made \
             to fail is not a test.",
            desc.name
        ),
    };
    eprintln!("    RED-PROOF [{}] {what}: {diag}", desc.name);
    diag
}

/// The shared fan-out driver: resolve the COMMITTED member, build its base on the declared face,
/// widen with the crown at the member's own effect-kind bit, PROVE + VERIFY — then prove the test
/// can go RED by breaking, one at a time, each thing it claims to guard.
fn prove_verify_fanout(key: &str, effects: Vec<Effect>, face: BaseFace, eff_bit: u32) {
    let desc = parse_vm_descriptor2(reg_json(key)).unwrap_or_else(|e| {
        panic!("[{key}] the committed V3 descriptor must parse: {e}");
    });
    assert_eq!(
        desc.trace_width, CAP_OPEN_WIDTH,
        "[{key}] the authority-crown fan-out members are bare cap-open width"
    );

    let (mut trace, dpis, map_heaps) = build_base(effects, face);
    assert_eq!(
        dpis.len(),
        desc.public_input_count,
        "[{key}] the rc-stripped base PI vector must match the committed PI count"
    );
    assert_eq!(
        map_heaps.is_empty(),
        face != BaseFace::TickWithAccountsTree,
        "[{key}] only the accounts-grow member witnesses map-ops"
    );

    let w = fanout_cap_open_witness(eff_bit);
    widen_to_cap_open(&mut trace, &w).expect("widen to the cap-open crown");
    assert_eq!(trace[0].len(), CAP_OPEN_WIDTH, "[{key}] widened width");
    assert_eq!(
        trace[0][EFF_BIT_COL],
        BabyBear::new(eff_bit),
        "[{key}] the effBit column carries the member's OWN effect-kind bit"
    );
    assert_eq!(
        trace[0][SRC_COL], w.src,
        "[{key}] the src column carries the opened leaf's target (the conferred edge)"
    );

    let proof = prove_vm_descriptor2(
        &desc,
        &trace,
        &dpis,
        &MemBoundaryWitness::default(),
        &map_heaps,
    )
    .unwrap_or_else(|e| {
        panic!(
            "[{key}] the honest cap-open fan-out trace does NOT prove against the committed \
             descriptor `{}`: {e:?}",
            desc.name
        )
    });
    verify_vm_descriptor2(&desc, &proof, &dpis).unwrap_or_else(|e| {
        panic!(
            "[{key}] the honest cap-open fan-out proof does NOT light-client-verify against `{}`: \
             {e:?}",
            desc.name
        )
    });
    eprintln!(
        "[{key}] CAP-OPEN FAN-OUT GREEN ({}): proved + verified.",
        desc.name
    );

    // ── PROVEN ABLE TO GO RED. Each mutation breaks exactly one thing the member binds.
    // (A) the effBit column off the member's own bit — `effBitGateFor` must reject.
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[EFF_BIT_COL] = BabyBear::new(eff_bit + 1);
        }
        assert_refused(
            &desc,
            &t,
            &dpis,
            &map_heaps,
            "effBit off the member's pinned bit",
        );
    }
    // (B) one felt of the cap-open LEAF (the target) — the `targetBind` edge + the leaf digest
    //     chip lookup must reject (the opened cap no longer confers an edge to the turn's src).
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[CAP_OPEN_BASE + 1] += BabyBear::ONE;
        }
        assert_refused(
            &desc,
            &t,
            &dpis,
            &map_heaps,
            "one felt of the cap leaf (target)",
        );
    }
    // (C) one lane of the committed cap_root — `rootPinGate` must reject the forged membership.
    {
        let mut t = trace.clone();
        for row in t.iter_mut() {
            row[CAP_ROOT_COL] += BabyBear::ONE;
        }
        assert_refused(
            &desc,
            &t,
            &dpis,
            &map_heaps,
            "one lane of the committed cap_root",
        );
    }
    // (D) a corrupted PUBLIC INPUT — the light client's own vector must reject the honest proof.
    {
        let mut bad = dpis.to_vec();
        bad[0] += BabyBear::ONE;
        assert!(
            verify_vm_descriptor2(&desc, &proof, &bad).is_err(),
            "[{key}] a corrupted public input MUST be rejected by verify_vm_descriptor2"
        );
        eprintln!(
            "    RED-PROOF [{}] corrupted PI[0]: verify_vm_descriptor2 rejected",
            desc.name
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// THE SEVEN AUTHORITY-CROWN FAN-OUT MEMBERS
// ─────────────────────────────────────────────────────────────────────────────────────────────────

/// `delegateCapOpenVmDescriptor2R24` (`dregg-effectvm-delegateAtten-v1-rot24-v3-capopen`) — the
/// granter-side delegation authority crown. Selector `GRANT_CAP`, `effBit = EFFECT_DELEGATION_OPS`
/// (`1<<16`): a delegate IS a delegation op, so the consumed cap must permit delegation.
#[test]
fn delegate_cap_open_proves_and_verifies() {
    prove_verify_fanout(
        "delegateCapOpenVmDescriptor2R24",
        vec![Effect::GrantCapability {
            cap_entry: [BabyBear::new(0x71); 8],
            phase_b: None,
        }],
        BaseFace::FreezeAdvance,
        EFFECT_DELEGATION_OPS,
    );
}

/// `grantCapCapOpenVmDescriptor2R24` — the SAME `GRANT_CAP` freeze/advance base as `delegate`, but
/// the crown binds `EFFECT_GRANT_CAPABILITY` (`1<<2`): the authority-only route the deployed SDK
/// takes when the node cannot supply the granter's c-list.
#[test]
fn grant_cap_cap_open_proves_and_verifies() {
    prove_verify_fanout(
        "grantCapCapOpenVmDescriptor2R24",
        vec![Effect::GrantCapability {
            cap_entry: [BabyBear::new(0x72); 8],
            phase_b: None,
        }],
        BaseFace::FreezeAdvance,
        EFFECT_GRANT_CAPABILITY,
    );
}

/// `revokeCapabilityCapOpenVmDescriptor2R24` — selector `REVOKE_CAPABILITY` on the freeze/advance
/// face; the crown binds `EFFECT_REVOKE_CAPABILITY` (`1<<3`).
#[test]
fn revoke_capability_cap_open_proves_and_verifies() {
    prove_verify_fanout(
        "revokeCapabilityCapOpenVmDescriptor2R24",
        vec![Effect::RevokeCapability {
            slot_hash: [BabyBear::new(0x18); 8],
            phase_b: None,
        }],
        BaseFace::FreezeAdvance,
        EFFECT_REVOKE_CAPABILITY,
    );
}

/// `introduceCapOpenVmDescriptor2R24` — the 3-party introduction. Nonce-TICK passthrough with
/// `cap_root` FROZEN; the crown binds `EFFECT_INTRODUCE` (`1<<13`).
#[test]
fn introduce_cap_open_proves_and_verifies() {
    prove_verify_fanout(
        "introduceCapOpenVmDescriptor2R24",
        vec![Effect::Introduce {
            intro_hash: [BabyBear::new(0x23); 8],
        }],
        BaseFace::TickPassthrough,
        EFFECT_INTRODUCE,
    );
}

/// `revokeCapOpenVmDescriptor2R24` — the delegation revocation (`REVOKE_DELEGATION`), nonce-TICK
/// passthrough; the crown binds `EFFECT_DELEGATION_OPS` (`1<<16`).
#[test]
fn revoke_delegation_cap_open_proves_and_verifies() {
    prove_verify_fanout(
        "revokeCapOpenVmDescriptor2R24",
        vec![Effect::RevokeDelegation {
            child_hash: [BabyBear::new(0x5C); 8],
        }],
        BaseFace::TickPassthrough,
        EFFECT_DELEGATION_OPS,
    );
}

/// `refreshDelegationCapOpenVmDescriptor2R24` — re-arming a specific child's delegation snapshot,
/// nonce-TICK passthrough; the crown binds `EFFECT_DELEGATION_OPS` (`1<<16`).
#[test]
fn refresh_delegation_cap_open_proves_and_verifies() {
    prove_verify_fanout(
        "refreshDelegationCapOpenVmDescriptor2R24",
        vec![Effect::RefreshDelegation {
            child_hash: [BabyBear::new(0x5D); 8],
            snapshot_value: [BabyBear::new(0x5E); 8],
        }],
        BaseFace::TickPassthrough,
        EFFECT_DELEGATION_OPS,
    );
}

/// `spawnCapOpenVmDescriptor2R24` — the ONE fan-out member that is also a BIRTH leg: 47 PIs (the
/// extra pin is the new-cell key at `param0`, col 68) and TWO `map_op`s over the rotated cells-root
/// (`absent` then `aafi_insert` at that key), so the base rides the accounts grow-gate producer and
/// the proof carries a genuine map heap. The crown binds `EFFECT_DELEGATION_OPS` (`1<<16`) — the
/// parent confers a held cap permitting delegation, exactly like `delegate`.
#[test]
fn spawn_cap_open_proves_and_verifies() {
    prove_verify_fanout(
        "spawnCapOpenVmDescriptor2R24",
        vec![Effect::SpawnWithDelegation {
            spawn_hash: [BabyBear::new(0x99); 8],
        }],
        BaseFace::TickWithAccountsTree,
        EFFECT_DELEGATION_OPS,
    );
}
