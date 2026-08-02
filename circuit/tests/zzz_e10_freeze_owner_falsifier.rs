//! E10-FREEZE-FALSIFIER — the frozen-authority falsifier on the no-freeze member `cellSeal`,
//! made OWNER-LIMB-PRECISE (circuit-minimality campaign, item E10).
//!
//! ## ⚑ STATUS: THE HOLE IS CLOSED, AND THIS FILE IS NOW THE REGRESSION GUARD
//!
//! Everything below describes the wound as it stood, and it is kept because the wound is what the
//! guard guards. But the verdict has FLIPPED. `36541604a` ("E10: the AFTER owner limb was welded by
//! nothing — ownerFreezeWire puts the freeze on the wire") landed `Emit/OwnerFreezeWire.lean` and
//! wired it into `EmitRotationV3.lean`'s driver chain, so every rotated member — `cellSeal`
//! included — now carries one `colEq` per owner-key nonet lane (the octet `B_PUBKEY_OCTET`
//! 105..112 plus the ninth lane `B_PUBKEY_NINTH_LANE`, welded because it is an absorbed pre-limb).
//!
//! Measured over the re-emitted registry: the honest seal still PROVES and VERIFIES, the
//! owner-changed seal is REJECTED, and the control lifecycle-freeze forgery is still REJECTED. So
//! the assertion at the bottom is now `!owner_forge_accepted`, and this test's job changed from
//! *observing* the gap to *refusing to let it come back*: delete the freeze from the emit and this
//! file goes red.
//!
//! Both halves are asserted deliberately. A weld that rejected the forgery by rejecting
//! EVERYTHING would be a vacuous green, so the honest seal's PROVE+VERIFY is checked first and the
//! control is checked after — three verdicts, not one.
//!
//! ## The witness-gen-perimeter unknown this probe resolved (the wound, as it stood)
//!
//! 41 of the 57 rotated cohort members carry ZERO freeze-shaped `colEq` gates. `cellSeal` is one:
//! `cellSealVmDescriptor2R24` is `v3Of (rotateV3WithRecordPin B_LIFECYCLE …)` — it appends ONLY the
//! lifecycle record-pin (PI[46] ← the AFTER `B_LIFECYCLE` limb) + the lifecycle-payload hash gate.
//! It is NOT `v3OfFrozen`: it carries NONE of `frozenAuthorityColEqs`
//! (`EffectVmEmitRotationV3.lean`), because it is an authority MOVER (the lifecycle legitimately
//! flips Live→Sealed).
//!
//! The operated cell's OWNER key — the `pubkey8` octet at `B_PUBKEY_OCTET = 105..112`
//! (`rotation_witness.rs::produce`, `canonical_32_to_felts_8(cell.public_key())`) — is absorbed
//! UNCONDITIONALLY into `state_commit`/NEW_COMMIT via the `wireCommitR` chain, but is welded by NO
//! `colEq` (`frozenAuthorityColEqs` freezes r23 · lifecycle · perms · vk · mode · fields-root +
//! the 7 headroom + 14 perms/vk completion + 56 fields[0..7] completion limbs — the pubkey octet is
//! in NONE of them) and pinned to NO PI on the plain-seal path (the sovereign KEY_COMMIT rider
//! reads the BEFORE octet and only fires on `makeSovereign` wide). So `cellSeal`'s AFTER owner limb
//! is a free felt on the AFTER side.
//!
//! The one candidate compensator is verifier-side PI reconstruction. It does NOT compensate:
//! `proof_verify.rs::verify_and_commit_proof_rotated` (doc-comment lines 523-526) anchors PI[42]
//! (rotated OLD commit) to the ledger's stored pre-state commitment, but PI[43] (rotated NEW commit)
//! ← `turn.execution_proof_new_commitment` — the prover's CLAIMED post-state, tied by `pi_binding`
//! to the trace's AFTER `B_STATE_COMMIT`. It is NOT independently recomputed by re-executing
//! `apply` on the pre-state (that would defeat the STARK). So a self-consistent AFTER block with a
//! forged owner produces a self-consistent NEW_COMMIT the verifier accepts as the new ledger root.
//!
//! ## What this test observes (BYTE-SAFE: no regen, no descriptor-byte change)
//!
//! Over the LIVE deployed `cellSealVmDescriptor2R24` (parsed from the committed staged registry
//! TSV), generate an honest seal, then a SECOND self-consistent seal whose only difference is the
//! AFTER owner octet (owner A → owner B). Drive both through the descriptor-level AIR prove/verify
//! (`prove_vm_descriptor2`/`verify_vm_descriptor2` — the deployed per-descriptor verifier, NOT the
//! contended circuit-prove aggregation prover). The observation: what rejects the changed-owner
//! seal — the AIR, or NOTHING.
//!
//! Reads current behavior in regions untouched by the live heap-open/market dirt. Nothing is
//! regen'd; no VK or descriptor bytes are minted.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_LIFECYCLE, B_PUBKEY_OCTET, B_STATE_COMMIT, BEFORE_BASE, ROT_WIDTH,
    RotatedBlockWitness, empty_caveat_manifest, generate_rotated_effect_vm_trace,
    rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::refusal::{Outcome, classify};
use dregg_turn::rotation_witness as rw;

fn rotated_json(key: &str) -> &'static str {
    for line in V3_STAGED_REGISTRY_TSV.lines() {
        let mut it = line.splitn(3, '\t');
        if it.next() == Some(key) {
            let _name = it.next();
            return it.next().expect("json column");
        }
    }
    panic!("{key} not in V3_STAGED_REGISTRY_TSV");
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
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

/// A producer cell with an explicit owner byte, balance and nonce; everything else default/open.
fn cell_owned_by(owner0: u8, balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = owner0;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn produce(cell: &Cell, ledger: &Ledger, receipt_log: &[[u8; 32]]) -> rw::RotationWitness {
    rw::produce(
        cell,
        ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        receipt_log,
        &Default::default(),
    )
}

/// E10-FREEZE-FALSIFIER, cellSeal / owner limb.
///
/// Observes that the LIVE `cellSealVmDescriptor2R24` ACCEPTS a self-consistent seal whose AFTER
/// owner octet is forged away from the pre-state owner — the record-pin (lifecycle) holds, the
/// economic frame is frozen, the `wireCommitR` chain is self-consistent, and NO `colEq` freezes the
/// pubkey octet — so NOTHING at the AIR level rejects it. A control lifecycle-freeze forgery on the
/// SAME trace is UNSAT, proving the harness is live (the owner-accept is not a false green).
#[test]
fn e10_cellseal_after_owner_limb_is_unforced_at_air_level() {
    // The deployed descriptor for a CellSeal lead effect.
    let seal_effect = Effect::CellSeal {
        target: [BabyBear::new(0); 8],
        reason_hash: [BabyBear::new(9); 8],
    };
    let name = rotated_descriptor_name_for_effect(&seal_effect)
        .expect("CellSeal is a rotated cohort member");
    assert_eq!(name, "cellSealVmDescriptor2R24");
    let desc =
        parse_vm_descriptor2(rotated_json(name)).expect("rotated cellSeal descriptor parses");

    let balance: i64 = 50_000;
    let st = CellState::new(balance as u64, 0);
    let effects = vec![seal_effect];
    let caveat = empty_caveat_manifest();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // ---- HONEST seal: owner A (byte 7), lifecycle Live -> Sealed, nonce ticks. ----
    const OWNER_A: u8 = 7;
    const OWNER_B: u8 = 42; // the forged (stolen) owner
    let before_cell = cell_owned_by(OWNER_A, balance, 0);
    let mut after_cell = cell_owned_by(OWNER_A, balance, 1);
    after_cell.seal([9u8; 32], 0).expect("Live cell must seal");

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();

    let before_w = produce(&before_cell, &ledger, &receipt_log);
    let after_w = produce(&after_cell, &ledger, &receipt_log);

    let (trace_h, dpis_h) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce the honest cellSeal trace");
    assert_eq!(trace_h[0].len(), ROT_WIDTH, "rotated trace width");

    // Sanity: the honest seal PROVES + VERIFIES through the deployed descriptor.
    let proof_h = prove_vm_descriptor2(&desc, &trace_h, &dpis_h, &mem_boundary, &map_heaps)
        .expect("honest cellSeal must prove");
    verify_vm_descriptor2(&desc, &proof_h, &dpis_h).expect("honest cellSeal must verify");

    // ---- THE FORGE: a self-consistent seal whose ONLY difference is the AFTER owner octet. ----
    // owner B replaces owner A on the AFTER cell; balance / nonce / lifecycle(Sealed) / perms are
    // byte-identical to the honest AFTER cell. The producer recomputes the FULL `wireCommitR` chain
    // over the forged octet, so the AFTER block + NEW_COMMIT are internally self-consistent.
    let mut forged_after = cell_owned_by(OWNER_B, balance, 1);
    forged_after
        .seal([9u8; 32], 0)
        .expect("Live cell must seal");
    // Produce against the SAME (honest) ledger, so cells_root and every OTHER limb match the honest
    // AFTER witness — the single moved variable is the pubkey octet + its downstream chain/commit.
    let after_w_forged = produce(&forged_after, &ledger, &receipt_log);

    let (trace_f, dpis_f) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w_forged),
        &caveat,
    )
    .expect("generator must build the owner-forged seal trace (the octet rides a pre_limbs copy)");

    // ---- ANTI-VACUITY: the forge genuinely moved the owner, and nothing else soundness-relevant. ----
    let last_h = &trace_h[trace_h.len() - 1];
    let last_f = &trace_f[trace_f.len() - 1];
    let r0_f = &trace_f[0];

    // (i) the AFTER owner octet genuinely changed A -> B (at least limb 0 moves).
    assert_ne!(
        last_f[AFTER_BASE + B_PUBKEY_OCTET],
        last_h[AFTER_BASE + B_PUBKEY_OCTET],
        "the forge must move the AFTER owner octet (canonical(owner B) != canonical(owner A))"
    );
    // (ii) the BEFORE block still carries owner A — the pre-state owner is unchanged, so OLD_COMMIT
    //      still matches the ledger's stored pre-state (the verifier's PI[42] anchor holds).
    assert_ne!(
        r0_f[BEFORE_BASE + B_PUBKEY_OCTET],
        last_f[AFTER_BASE + B_PUBKEY_OCTET],
        "the forged seal has AFTER owner (B) != BEFORE owner (A) — an owner CHANGE inside a seal"
    );
    assert_eq!(
        r0_f[BEFORE_BASE + B_STATE_COMMIT],
        trace_h[0][BEFORE_BASE + B_STATE_COMMIT],
        "OLD_COMMIT is unchanged by the forge — still the true pre-state root (verifier PI[42] holds)"
    );
    // (iii) the lifecycle record-pin STILL holds on the forge: PI[46] == AFTER Sealed lifecycle.
    assert_eq!(
        dpis_f[46],
        last_f[AFTER_BASE + B_LIFECYCLE],
        "the lifecycle record-pin is satisfied on the forge (owner is orthogonal to the pin)"
    );
    assert_eq!(
        dpis_f[46], dpis_h[46],
        "the forged seal reaches the SAME (Sealed) lifecycle as the honest seal"
    );
    // (iv) NEW_COMMIT genuinely absorbed the forged owner: PI[43] moved (the octet is on the chain).
    assert_ne!(
        dpis_f[43], dpis_h[43],
        "NEW_COMMIT differs — the forged owner IS bound into the committed post-state (self-consistent)"
    );

    // ---- THE OBSERVATION: prove/verify the owner-forged seal through the deployed descriptor. ----
    let outcome = classify(
        "e10_cellseal_after_owner_limb_is_unforced_at_air_level",
        || {
            prove_vm_descriptor2(&desc, &trace_f, &dpis_f, &mem_boundary, &map_heaps)
                .and_then(|p| verify_vm_descriptor2(&desc, &p, &dpis_f))
        },
    );
    let owner_forge_accepted = matches!(outcome, Outcome::Accepted(_));

    // ---- CONTROL (harness liveness): the lifecycle-freeze forgery on the SAME trace IS rejected. ----
    // Freeze the AFTER lifecycle limb to the pre (Live) value while PI[46] claims Sealed — the
    // record-pin bites. This proves the descriptor + prove/verify path CAN reject, so the
    // owner-accept above is a genuine gap, not a dead/vacuous harness.
    let control_rejected = {
        let mut t = trace_f.clone();
        let li = t.len() - 1;
        t[li][AFTER_BASE + B_LIFECYCLE] = trace_f[0][BEFORE_BASE + B_LIFECYCLE]; // frozen Live
        match classify("e10_control_lifecycle_freeze", || {
            prove_vm_descriptor2(&desc, &t, &dpis_f, &mem_boundary, &map_heaps)
                .and_then(|p| verify_vm_descriptor2(&desc, &p, &dpis_f))
        }) {
            Outcome::Accepted(_) => false,
            _ => true,
        }
    };
    assert!(
        control_rejected,
        "CONTROL: the lifecycle-freeze forgery MUST be rejected — the harness is live, so the \
         owner-forge verdict is meaningful"
    );

    eprintln!(
        "E10-FREEZE-FALSIFIER (cellSeal / owner limb, LIVE cellSealVmDescriptor2R24): \
         honest PROVED+VERIFIED; owner-changed seal (AFTER owner B != BEFORE owner A, lifecycle-pin \
         satisfied, self-consistent NEW_COMMIT) prove/verify verdict = {}; control lifecycle-freeze \
         = REJECTED.",
        if owner_forge_accepted {
            "ACCEPTED (unforced — the E10 gap is OPEN again)"
        } else {
            "REJECTED (the `ownerFreezeWire` colEq bites — E10 closed)"
        }
    );

    // ⚑ THE FINDING, CLOSED — and the polarity of this assertion is the closure.
    //
    // It read `assert!(owner_forge_accepted)` while the hole was open: the deployed descriptor
    // accepted a seal that silently rewrote the operated cell's owner, because the pubkey octet
    // carried no freeze `colEq` and `proof_verify.rs` anchors NEW_COMMIT to the CLAIMED post rather
    // than recomputing it. The named fix was "an owner-freeze `colEq` authored in Lean and emitted
    // into the cohort", and that is exactly what `36541604a` shipped
    // (`Emit/OwnerFreezeWire.lean` → `EmitRotationV3.lean`'s `ownerFreezeWire` wrap).
    //
    // So the assertion inverts, and with it this file's job. The verifier-side hole it named
    // (NEW_COMMIT ← claimed post, never recomputed) is UNCHANGED and still real — what changed is
    // that the AIR no longer lets the claimed post disagree with the pre-state about who owns the
    // cell, which is what made that hole reachable for the owner limb.
    assert!(
        !owner_forge_accepted,
        "REGRESSION: the LIVE cellSealVmDescriptor2R24 ACCEPTED a self-consistent seal with a \
         forged AFTER owner octet. The owner freeze (`ownerFreezeWire`, one `colEq` per owner-key \
         nonet lane: the octet at B_PUBKEY_OCTET 105..112 plus B_PUBKEY_NINTH_LANE) is missing from \
         the emitted member or was dropped by a later wrap — E10 is open again, and NEW_COMMIT is \
         still anchored to the prover's claimed post, so nothing downstream will catch it."
    );
}
