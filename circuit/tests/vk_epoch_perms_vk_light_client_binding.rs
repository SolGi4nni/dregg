//! # THE VK-EPOCH LIGHT-CLIENT BINDING BITE — setPermissions / setVK FORCED ON-WIRE.
//!
//! ## What this closes (`docs/VK-EPOCH-PLAN.md`, STAGE B / Family 1)
//!
//! Before the VK epoch, setPermissions / setVK were *full-node-only*: the deployed verifier
//! (`turn::executor::proof_verify.rs` step 6b, ~`:718-735`) re-derived the post-cell via
//! `apply_effect_to_cell` and ANCHORED PI 46 (the record-pin, limb 24 `B_AUTHORITY_DIGEST`) to
//! the trusted post-cell's authority digest. A **ledgerless light client cannot run that
//! re-derivation** — it has the consumed effect's hash, not the pre-cell — so the authority
//! write was bound for a full node but NOT for a light client.
//!
//! The WAVE-2 perms/VK flag-day committed TWO dedicated authority sub-limbs beside the opaque
//! `record_digest` (limb 24): the perms-digest limb (`B_PERMS = 33`) and the vk-digest limb
//! (`B_VK = 34`). The LIVE setPerms / setVK descriptors carry an IN-CIRCUIT WELD
//! (`EffectVmEmitRotationV3.rotateV3WithPermsVKGate` → `permsVKWeldGate`):
//!
//!     sel · (loc(AFTER perms/vk-digest limb) − loc(declared param[0])) = 0
//!
//! On the ACTIVE row this FORCES the committed AFTER perms/vk-digest sub-limb EQUAL to the
//! declared param (`params[0]`, which the producer fills with `perms_digest_felt(P)` /
//! `vk_digest_felt(VK)` and which is PI-anchored, all 8 limbs, via `effects_hash`). The AFTER
//! perms/vk-digest limb is in turn ABSORBED by `wire_commit` into the published `B_STATE_COMMIT`
//! carrier → the wide v9 `NEW_COMMIT` anchor (`after8`). So the binding chain a LIGHT CLIENT
//! verifies, with NO trusted post-cell, is:
//!
//!     after8 (claimed NEW commit, PI-anchored)  ⟹  B_STATE_COMMIT carrier
//!       ⟹  AFTER perms/vk-digest limb (absorbed)  ⟹  (weld) == declared param[0]  ⟹  effects_hash PI
//!
//! A forged post-permissions / post-VK (a post-cell differing ONLY in perms / vk) absorbs a
//! DIFFERENT perms/vk-digest limb into the commitment — which then VIOLATES the weld (≠ the
//! declared param) → `verify_vm_descriptor2` UNSAT. **The off-cell anchor (PI 46) is NOT in this
//! chain** — it binds the opaque limb 24 for a full node; the weld binds the dedicated limb
//! 33 / 34 in-circuit for everyone.
//!
//! ## The light-client discriminator (the plan's bar, §6 / the guardrail)
//!
//! Both teeth run through `prove_vm_descriptor2` / `verify_vm_descriptor2` ALONE — the same
//! circuit verify a light client runs. That path NEVER calls `apply_effect_to_cell` and NEVER
//! anchors PI 46 off-cell, so these tests are INHERENTLY the *anchor-disabled* discriminator: a
//! reject here is the IN-CIRCUIT weld biting, not the host re-derivation.
//!
//!   * POSITIVE (no downgrade): an HONEST setPermissions / setVK turn proves + verifies green.
//!   * NEGATIVE (the bite): a post-cell forged to differ ONLY in permissions / vk — the
//!     committed AFTER perms/vk-digest limb (and the published commit absorbing it) carry the
//!     forged value while the declared param stays the honest declared one — is UNSAT.
//!
//! Gated on `prover` (compiles `descriptor_ir2`). Run with
//! `cargo test -p dregg-circuit --features prover vk_epoch_perms_vk -- --nocapture`.

// (formerly `#![cfg(feature = "prover")]` — that dregg-circuit feature is GONE; the
// descriptor-level prove/verify (`prove_vm_descriptor2`/`verify_vm_descriptor2`) is
// now unconditional in dregg-circuit, so this test compiles + runs by default.)

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions, VerificationKey};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::columns::PARAM_BASE;
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_PERMS, B_VK, ROT_WIDTH, RotatedBlockWitness, empty_caveat_manifest,
    generate_rotated_effect_vm_trace, rotated_descriptor_name_for_effect,
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

/// The producer's before-cell (the pre-state the turn opens over): open perms, no VK.
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
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("37 pre-iroot limbs")
}

/// The declared `permissions_hash` an honest setPermissions effect carries for `perms` — the
/// deployed `effect_vm_bridge.rs::SetPermissions` shape (`hash_to_8(blake3(postcard(perms)))`),
/// whose limb[0] is `dregg_cell::commitment::perms_digest_felt(perms)`.
fn perms_hash(perms: &Permissions) -> [BabyBear; 8] {
    let bytes = postcard::to_allocvec(perms).unwrap_or_default();
    bytes32_to_8_limbs(blake3::hash(&bytes).as_bytes())
}

/// The declared `vk_hash` an honest setVK effect carries for `vk`.
fn vk_hash(vk: &Option<VerificationKey>) -> [BabyBear; 8] {
    match vk {
        Some(v) => {
            let bytes = postcard::to_allocvec(v).unwrap_or_default();
            bytes32_to_8_limbs(blake3::hash(&bytes).as_bytes())
        }
        None => [BabyBear::ZERO; 8],
    }
}

/// `true` iff `prove_vm_descriptor2` REFUSES (returns `Err` OR panics) on the given trace + PIs.
fn refused(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<dregg_circuit::heap_root::HeapLeaf>],
) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_vm_descriptor2(desc, trace, dpis, mem_boundary, map_heaps)
    }));
    match r {
        Err(_) => true,
        Ok(res) => res.is_err(),
    }
}

/// **setPermissions FORCED ON-WIRE (light-client-verifiable).** An honest perms A→B turn proves +
/// verifies; a post-cell forged to differ ONLY in permissions (the committed AFTER perms-digest
/// limb — and the published commit absorbing it — carry the forged perms, while the declared
/// `permissions_hash` param stays the honest B) is UNSAT through `prove`/`verify` ALONE — the
/// in-circuit `permsVKWeldGate` bites with NO off-cell `apply_effect_to_cell` anchor.
#[test]
fn setpermissions_forced_on_wire_rejects_forged_perms_anchor_disabled() {
    let balance: i64 = 50_000;

    // The HONEST setPermissions A→B: pre = open perms, post = zkapp perms (a DISTINCT 8-field
    // struct). The effect declares `permissions_hash(B)`.
    let new_perms = Permissions::zkapp();
    let effect = Effect::SetPermissions {
        permissions_hash: perms_hash(&new_perms),
    };
    let name = rotated_descriptor_name_for_effect(&effect)
        .expect("SetPermissions is a rotated cohort member");
    assert_eq!(name, "setPermsVmDescriptor2R24");
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
        .expect("rotated setPerms descriptor parses");
    assert_eq!(
        desc.public_input_count, 47,
        "setPerms carries the appended record-forcing pin (47 PIs)"
    );

    let st = CellState::new(balance as u64, 0);
    let effects = vec![effect];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(balance, 0);
    let mut after_cell = producer_cell(balance, 1); // nonce ticks
    after_cell.permissions = new_perms.clone();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

    let before_w =
        rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w =
        rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    // The perms-digest limb GENUINELY MOVED (anti-vacuity: the bound limb distinguishes A from B).
    assert_ne!(
        before_w.pre_limbs[B_PERMS], after_w.pre_limbs[B_PERMS],
        "the producer witnesses a DISTINCT perms-digest limb for the post (anti-omission)"
    );
    // The honest AFTER perms-digest limb IS the declared param[0] (the weld is satisfiable — the
    // close is NOT vacuous).
    assert_eq!(
        after_w.pre_limbs[B_PERMS],
        perms_hash(&new_perms)[0],
        "honest: the committed AFTER perms-digest limb == the declared param[0] (weld holds)"
    );

    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce a setPerms trace + 47 PIs");
    assert_eq!(trace[0].len(), ROT_WIDTH, "rotated trace width");

    // The trace carries the declared param[0] and the honest AFTER perms-digest limb, and the weld
    // holds across them (loc(AFTER perms) == loc(param0)).
    let last = &trace[trace.len() - 1];
    assert_eq!(
        trace[0][PARAM_BASE], after_w.pre_limbs[B_PERMS],
        "row-0 param[0] = the declared perms-digest"
    );
    assert_eq!(
        last[AFTER_BASE + B_PERMS], after_w.pre_limbs[B_PERMS],
        "the AFTER block's perms-digest limb is the honest post value"
    );

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // POSITIVE TOOTH (no downgrade): the honest setPerms turn proves + verifies — light-client
    // path, no trusted post-cell.
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("NO DOWNGRADE: the honest setPermissions turn must prove end-to-end");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("NO DOWNGRADE: the honest setPermissions proof must verify independently");

    // NEGATIVE TOOTH (the bite): a post-cell forged to differ ONLY in permissions. The committed
    // AFTER perms-digest limb (and the published commit absorbing it) carry the FORGED perms
    // `B' != B`, while the declared param stays the honest `permissions_hash(B)`. The weld
    // `loc(AFTER perms) == loc(param0)` now FAILS → UNSAT. Built faithfully: regenerate the AFTER
    // witness over a cell carrying B', so the published commit is SELF-CONSISTENT for B' (a clean
    // perms-only post-cell delta) — the ONLY thing that breaks is the in-circuit weld.
    let mut forged_perms = Permissions::sovereign_default(); // B' != B (and != A)
    forged_perms.set_permissions = AuthRequired::None;
    assert_ne!(
        perms_hash(&forged_perms)[0],
        perms_hash(&new_perms)[0],
        "the forged perms must fold to a DISTINCT digest (or the bite is vacuous)"
    );
    let mut forged_after = producer_cell(balance, 1);
    forged_after.permissions = forged_perms.clone();
    let mut forged_ledger = Ledger::new();
    forged_ledger.insert_cell(forged_after.clone()).unwrap();
    let forged_after_w = rw::produce(
        &forged_after,
        &forged_ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
    );
    // The forged commit absorbs B' (a self-consistent post-cell that differs ONLY in perms).
    assert_ne!(
        forged_after_w.state_commit, after_w.state_commit,
        "the forged post-cell publishes a DIFFERENT commit (it differs only in perms)"
    );

    let (forged_trace, forged_dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects, // SAME effect: declared param stays the honest permissions_hash(B)
        &bridge(&before_w),
        &bridge(&forged_after_w),
        &caveat,
    )
    .expect("generator builds the forged-perms trace");

    // The smoking gun: the committed AFTER perms-digest limb is the FORGED B', but the declared
    // param[0] is still the honest B — the weld must reject this divergence.
    assert_eq!(
        forged_trace[forged_trace.len() - 1][AFTER_BASE + B_PERMS],
        perms_hash(&forged_perms)[0],
        "the forged AFTER perms-digest limb carries B'"
    );
    assert_eq!(
        forged_trace[0][PARAM_BASE],
        perms_hash(&new_perms)[0],
        "the declared param[0] is still the honest B (the effect is unchanged)"
    );
    assert_ne!(
        forged_trace[forged_trace.len() - 1][AFTER_BASE + B_PERMS],
        forged_trace[0][PARAM_BASE],
        "AFTER perms-digest != declared param — the weld's UNSAT precondition"
    );

    assert!(
        refused(&desc, &forged_trace, &forged_dpis, &mem_boundary, &map_heaps),
        "SOUNDNESS (light-client unfoolable, anchor-disabled): a post-cell forged to differ ONLY \
         in permissions — committed AFTER perms-digest != the declared param — MUST be UNSAT \
         through prove/verify ALONE; the in-circuit permsVKWeldGate bites with NO off-cell \
         apply_effect_to_cell re-derivation"
    );

    eprintln!(
        "VK-EPOCH setPermissions FORCED ON-WIRE: honest A->B proves+verifies; a perms-ONLY forged \
         post-cell is UNSAT through verify_vm_descriptor2 ALONE (no off-cell anchor) — the \
         in-circuit perms weld binds the post perms into the commitment for a ledgerless client."
    );
}

/// **setVK FORCED ON-WIRE (light-client-verifiable).** The vk twin of the perms bite: an honest
/// setVK turn proves + verifies; a post-cell forged to differ ONLY in the verification key is
/// UNSAT through `prove`/`verify` ALONE (the in-circuit vk weld, limb `B_VK = 34`, with NO
/// off-cell anchor).
#[test]
fn setvk_forced_on_wire_rejects_forged_vk_anchor_disabled() {
    let balance: i64 = 50_000;

    // The HONEST setVK None->VK(B): pre = no VK, post = a concrete VK. The effect declares
    // `vk_hash(B)`.
    let new_vk = Some(VerificationKey {
        hash: [7u8; 32],
        data: vec![1, 2, 3],
    });
    let effect = Effect::SetVerificationKey {
        vk_hash: vk_hash(&new_vk),
    };
    let name = rotated_descriptor_name_for_effect(&effect)
        .expect("SetVerificationKey is a rotated cohort member");
    assert_eq!(name, "setVKVmDescriptor2R24");
    let desc =
        parse_vm_descriptor2(rotated_descriptor_json(name)).expect("rotated setVK descriptor parses");
    assert_eq!(
        desc.public_input_count, 47,
        "setVK carries the appended record-forcing pin (47 PIs)"
    );

    let st = CellState::new(balance as u64, 0);
    let effects = vec![effect];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(balance, 0); // no VK
    let mut after_cell = producer_cell(balance, 1);
    after_cell.verification_key = new_vk.clone();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

    let before_w =
        rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w =
        rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    assert_ne!(
        before_w.pre_limbs[B_VK], after_w.pre_limbs[B_VK],
        "the producer witnesses a DISTINCT vk-digest limb for the post (anti-omission)"
    );
    assert_eq!(
        after_w.pre_limbs[B_VK],
        vk_hash(&new_vk)[0],
        "honest: the committed AFTER vk-digest limb == the declared param[0] (weld holds)"
    );

    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce a setVK trace + 47 PIs");

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // POSITIVE TOOTH (no downgrade).
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("NO DOWNGRADE: the honest setVK turn must prove end-to-end");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("NO DOWNGRADE: the honest setVK proof must verify independently");

    // NEGATIVE TOOTH: a post-cell forged to differ ONLY in the VK (B' != B), declared param stays
    // honest B. The vk weld (limb 34 == param0) bites.
    let forged_vk = Some(VerificationKey {
        hash: [9u8; 32],
        data: vec![4, 5, 6, 7],
    });
    assert_ne!(
        vk_hash(&forged_vk)[0],
        vk_hash(&new_vk)[0],
        "the forged vk must fold to a DISTINCT digest (or the bite is vacuous)"
    );
    let mut forged_after = producer_cell(balance, 1);
    forged_after.verification_key = forged_vk.clone();
    let mut forged_ledger = Ledger::new();
    forged_ledger.insert_cell(forged_after.clone()).unwrap();
    let forged_after_w = rw::produce(
        &forged_after,
        &forged_ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
    );
    assert_ne!(
        forged_after_w.state_commit, after_w.state_commit,
        "the forged post-cell publishes a DIFFERENT commit (it differs only in vk)"
    );

    let (forged_trace, forged_dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&forged_after_w),
        &caveat,
    )
    .expect("generator builds the forged-vk trace");

    assert_eq!(
        forged_trace[forged_trace.len() - 1][AFTER_BASE + B_VK],
        vk_hash(&forged_vk)[0],
        "the forged AFTER vk-digest limb carries B'"
    );
    assert_eq!(
        forged_trace[0][PARAM_BASE],
        vk_hash(&new_vk)[0],
        "the declared param[0] is still the honest B"
    );
    assert_ne!(
        forged_trace[forged_trace.len() - 1][AFTER_BASE + B_VK],
        forged_trace[0][PARAM_BASE],
        "AFTER vk-digest != declared param — the weld's UNSAT precondition"
    );

    assert!(
        refused(&desc, &forged_trace, &forged_dpis, &mem_boundary, &map_heaps),
        "SOUNDNESS (light-client unfoolable, anchor-disabled): a post-cell forged to differ ONLY \
         in the verification key — committed AFTER vk-digest != the declared param — MUST be \
         UNSAT through prove/verify ALONE; the in-circuit vk weld bites with NO off-cell anchor"
    );

    eprintln!(
        "VK-EPOCH setVK FORCED ON-WIRE: honest None->VK proves+verifies; a vk-ONLY forged \
         post-cell is UNSAT through verify_vm_descriptor2 ALONE (no off-cell anchor) — the \
         in-circuit vk weld binds the post vk into the commitment for a ledgerless client."
    );
}
