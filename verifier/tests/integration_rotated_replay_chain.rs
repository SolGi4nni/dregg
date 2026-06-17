#![cfg(feature = "prover")]
//! Integration tests: the ROTATED replay-chain verifier (the recursion-build
//! replacement for `integration_replay_chain.rs`, whose v1 hand-AIR is retired
//! under `recursion`).
//!
//! These mint REAL rotated `"effect-vm-rotated"` legs — each a multi-table IR-v2
//! batch proof (`Ir2BatchProof`) over a committed rotated R=24 cohort descriptor,
//! LIVE-generated from real producer witnesses (`dregg_turn::rotation_witness`)
//! exactly the way the SDK's `prove_cohort_run_chain` emits them — and verify
//! them through `dregg_verifier::verify_rotated_replay_chain`.
//!
//! Covers:
//!   - A single-leg rotated chain VERIFIES against its real pre/post commitments.
//!   - A two-leg heterogeneous chain VERIFIES, with interior adjacency closing
//!     (leg_1.OLD == leg_0.NEW).
//!   - ANTI-GHOST: a tampered proof byte (forged proof) is REJECTED.
//!   - ANTI-GHOST: a tampered vk_hash is REJECTED (the leg is selector-bound but
//!     the descriptor-identity metadata is pinned).
//!   - WRONG-ROOT: a caller expected_old / expected_new that disagrees with the
//!     chain endpoints is REJECTED at the endpoint check.
//!   - WRONG-CHAIN: a dropped / spliced middle leg breaks adjacency and is
//!     REJECTED.
//!
//! SLOW (real Plonky3 proving). Run with
//! `cargo test -p dregg-verifier --features recursion rotated_replay -- --nocapture`.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
};
use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, empty_caveat_manifest, generate_rotated_effect_vm_trace,
    rotated_descriptor_name_for_effect, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_turn::rotation_witness as rw;
use dregg_verifier::{RotatedReplayLeg, RotatedReplayVerdict, verify_rotated_replay_chain};

// ─────────────────────────────────────────────────────────────────────────────
// Helpers (the leg-minting bridge: the test depends on BOTH dregg-turn and
// dregg-circuit, so it owns the producer→generator bridge, exactly like the SDK).
// ─────────────────────────────────────────────────────────────────────────────

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

/// A producer cell carrying `balance`/`nonce` and open permissions (the welded
/// scalars the rotated state-block reads).
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
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
}

/// Resolve the committed rotated cohort descriptor JSON for a turn's lead effect,
/// returning `(name, json)` from the staged registry TSV.
fn rotated_json_for(effect: &Effect) -> (&'static str, &'static str) {
    let name = rotated_descriptor_name_for_effect(effect)
        .unwrap_or_else(|| panic!("{effect:?} has no rotated cohort descriptor"));
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
        .unwrap_or_else(|| panic!("{name} not in V3_STAGED_REGISTRY_TSV"));
    (name, json)
}

/// The fixed turn-level context every producer witness in these tests shares
/// (the `cells_root` / `iroot` source). A single nullifier-root + receipt-log,
/// matching the flip test.
fn nullifier_root() -> [u8; 32] {
    [0u8; 32]
}
fn receipt_log() -> Vec<[u8; 32]> {
    vec![[1u8; 32], [2u8; 32]]
}

/// Mint ONE real rotated `"effect-vm-rotated"` leg from EXPLICIT before/after
/// producer witnesses (the turn-level rotation context) — the EXACT lever
/// `prove_cohort_run_chain` pulls: LIVE-generate the 311-col rotated trace + PI,
/// prove through the IR-v2 batch prover, postcard-serialize, fingerprint the
/// cohort JSON for the leg's `vk_hash`. Returns the leg + its
/// `(OLD_COMMIT, NEW_COMMIT)` felts.
fn mint_rotated_leg_with_witnesses(
    initial_state: &CellState,
    effect: Effect,
    before_w: &rw::RotationWitness,
    after_w: &rw::RotationWitness,
) -> (RotatedReplayLeg, BabyBear, BabyBear) {
    let effects = vec![effect.clone()];
    let (name, json) = rotated_json_for(&effect);
    let desc = parse_vm_descriptor2(json).expect("rotated cohort descriptor parses");

    let caveat = match effect {
        Effect::Transfer { .. } => transfer_caveat_manifest(),
        _ => empty_caveat_manifest(),
    };

    let (trace, dpis) = generate_rotated_effect_vm_trace(
        initial_state,
        &effects,
        &bridge(before_w),
        &bridge(after_w),
        &caveat,
    )
    .expect("live rotated generator must produce a trace + PIs");

    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &MemBoundaryWitness::default(), &[])
        .unwrap_or_else(|e| panic!("rotated IR-v2 proof for {name} failed: {e}"));
    let proof_bytes = postcard::to_allocvec(&proof).expect("Ir2BatchProof serializes");

    let vk_hash = *blake3::hash(json.as_bytes()).as_bytes();
    let public_inputs: Vec<u32> = dpis.iter().map(|b| b.as_u32()).collect();

    (
        RotatedReplayLeg {
            proof_bytes,
            public_inputs,
            vk_hash,
        },
        dpis[pi::OLD_COMMIT],
        dpis[pi::NEW_COMMIT],
    )
}

/// Single-leg convenience: derive the before/after witnesses from explicit
/// before/after producer CELLS (the turn-level ledger = the after-cell's), then
/// mint the leg. For a single leg the before/after blocks legitimately differ.
fn mint_rotated_leg(
    initial_state: &CellState,
    effect: Effect,
    before_cell: &Cell,
    after_cell: &Cell,
) -> (RotatedReplayLeg, BabyBear, BabyBear) {
    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nr = nullifier_root();
    let commitments_root = [0u8; 32];
    let rl = receipt_log();
    let before_w = rw::produce(before_cell, &ledger, &nr, &commitments_root, &rl);
    let after_w = rw::produce(after_cell, &ledger, &nr, &commitments_root, &rl);
    mint_rotated_leg_with_witnesses(initial_state, effect, &before_w, &after_w)
}

/// Thread `s_k → s_{k+1}` off the LIVE v1 generator's own STATE_AFTER columns —
/// the exact step `prove_cohort_run_chain` uses to close the interior seam (no
/// hand-replay of the transition).
fn cell_state_after(s_k: &CellState, effect: &Effect) -> CellState {
    use dregg_circuit::effect_vm::columns::{STATE_AFTER_BASE, state};
    use dregg_circuit::effect_vm::generate_effect_vm_trace;
    let (trace, _pi) = generate_effect_vm_trace(s_k, std::slice::from_ref(effect));
    let row = &trace[trace.len().saturating_sub(1)];
    let lo = row[STATE_AFTER_BASE + state::BALANCE_LO].0 as u64;
    let hi = row[STATE_AFTER_BASE + state::BALANCE_HI].0 as u64;
    let balance = lo | (hi << 30);
    let nonce = row[STATE_AFTER_BASE + state::NONCE].0;
    let mut fields = [BabyBear::ZERO; 8];
    for (i, f) in fields.iter_mut().enumerate() {
        *f = row[STATE_AFTER_BASE + state::FIELD_BASE + i];
    }
    let capability_root = row[STATE_AFTER_BASE + state::CAP_ROOT];
    let reserved = row[STATE_AFTER_BASE + state::RESERVED].0;
    let mut s = CellState {
        balance,
        nonce,
        fields,
        capability_root,
        state_commitment: BabyBear::ZERO,
        sealed_field_mask: reserved & 0xFF,
        mode_flag: reserved >> 8,
    };
    s.refresh_commitment();
    s
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. Single-leg rotated chain with a real proof: VERIFIED against its endpoints.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn single_leg_rotated_chain_verifies() {
    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64, 0);

    let (leg, old_commit, new_commit) = mint_rotated_leg(
        &st,
        Effect::Transfer {
            amount,
            direction: 1,
        },
        &before_cell,
        &after_cell,
    );

    let out = verify_rotated_replay_chain(&[leg], old_commit, new_commit);
    assert!(
        out.overall_verified,
        "single real rotated leg must verify; output = {}",
        out.summary
    );
    assert_eq!(out.verified, 1);
    assert_eq!(out.per_leg[0], RotatedReplayVerdict::Verified);
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. Two-leg heterogeneous chain: VERIFIED with interior adjacency closing.
// ─────────────────────────────────────────────────────────────────────────────

/// Build two cohort legs that chain — exactly as `prove_cohort_run_chain` does
/// (PATH-PRESERVE §2.3): leg-0 (Transfer) takes s0→s1, leg-1 (IncrementNonce)
/// takes s1→s2. The turn-level rotation context (cells_root / iroot / lifecycle /
/// epoch, all turn-invariant) is ONE shared `before_w`; the interior after-block
/// (leg-0's) ALSO uses `before_w`, only the FINAL after-block uses the real
/// `after_w`. The changing per-run balance/nonce ride the welds (`fill_block`
/// overrides them per-row). So `leg_1.OLD_COMMIT == leg_0.NEW_COMMIT` by
/// construction — both are `wireCommitR(before_w carried-limbs, s1 welds)` — and
/// the verifier's adjacency check closes on a genuinely-chained pair.
#[test]
fn two_leg_heterogeneous_chain_verifies_with_adjacency() {
    let bal0: i64 = 100_000;
    let amount: u64 = 50;

    // s0 → s1 (Transfer) → s2 (IncrementNonce), threaded off the live generator.
    let s0 = CellState::new(bal0 as u64, 0);
    let transfer = Effect::Transfer {
        amount,
        direction: 1,
    };
    let s1 = cell_state_after(&s0, &transfer);
    let s2 = cell_state_after(&s1, &Effect::IncrementNonce);

    // The turn-level witnesses: ONE before (the turn context, reused for leg-0's
    // before AND after blocks — the interior seam), and the real final after.
    let nr = nullifier_root();
    let commitments_root = [0u8; 32];
    let rl = receipt_log();
    // The turn-context ledger snapshot is the actor's final-cell ledger (the
    // cells_root shape `produce` reads); both witnesses read the SAME ledger so
    // the turn-invariant carried limbs agree across legs.
    let final_cell = producer_cell(s2.balance as i64, s2.nonce as u64);
    let mut ledger = Ledger::new();
    ledger.insert_cell(final_cell.clone()).unwrap();
    let before_cell = producer_cell(bal0, 0);
    let before_w = rw::produce(&before_cell, &ledger, &nr, &commitments_root, &rl);
    let after_w = rw::produce(&final_cell, &ledger, &nr, &commitments_root, &rl);

    // leg 0: Transfer, s0→s1. Interior after-block uses `before_w` (turn context).
    let (leg0, old0, new0) = mint_rotated_leg_with_witnesses(&s0, transfer, &before_w, &before_w);
    // leg 1: IncrementNonce, s1→s2. Final after-block uses the real `after_w`.
    let (leg1, old1, new1) =
        mint_rotated_leg_with_witnesses(&s1, Effect::IncrementNonce, &before_w, &after_w);

    // The chain closes at the seam by construction.
    assert_eq!(
        old1, new0,
        "interior adjacency must close by construction (leg1.OLD == leg0.NEW)"
    );

    let out = verify_rotated_replay_chain(&[leg0, leg1], old0, new1);
    assert!(
        out.overall_verified,
        "two-leg heterogeneous chain must verify; output = {}",
        out.summary
    );
    assert_eq!(out.verified, 2);
    assert_eq!(out.per_leg[0], RotatedReplayVerdict::Verified);
    assert_eq!(out.per_leg[1], RotatedReplayVerdict::Verified);
}

/// The adjacency tooth as a DIRECT anti-ghost: two SOUND legs that do NOT chain
/// (leg-1 built from an independent state, so its OLD_COMMIT ≠ leg-0's
/// NEW_COMMIT) must be REJECTED at the adjacency check, even though each leg
/// verifies cryptographically on its own. This is the chain-layer anti-ghost that
/// catches a spliced-in foreign leg.
#[test]
fn two_sound_but_nonadjacent_legs_rejected() {
    let bal0: i64 = 100_000;
    let amount: u64 = 50;

    // leg 0: a genuine single transfer leg, s0→s1.
    let s0 = CellState::new(bal0 as u64, 0);
    let cell0 = producer_cell(bal0, 0);
    let cell1 = producer_cell(bal0 - amount as i64, 0);
    let (leg0, old0, new0) = mint_rotated_leg(
        &s0,
        Effect::Transfer {
            amount,
            direction: 1,
        },
        &cell0,
        &cell1,
    );

    // leg 1: a DIFFERENT genuine leg whose OLD does NOT continue leg-0 (a fresh,
    // unrelated state — a foreign leg spliced in).
    let foreign = CellState::new(777_777, 3);
    let fcell_b = producer_cell(777_777, 3);
    let fcell_a = producer_cell(777_777, 4);
    let (leg1, foreign_old, new1) =
        mint_rotated_leg(&foreign, Effect::IncrementNonce, &fcell_b, &fcell_a);

    // The seam genuinely does NOT close (different states).
    assert_ne!(
        foreign_old, new0,
        "the spliced foreign leg must not accidentally chain"
    );

    // Present them as a 2-leg chain claiming [old0 .. new1]. Both legs verify
    // cryptographically, but adjacency (leg1.OLD == leg0.NEW) breaks → REJECTED.
    let out = verify_rotated_replay_chain(&[leg0, leg1], old0, new1);
    assert!(
        !out.overall_verified,
        "two sound-but-nonadjacent legs must be rejected at the adjacency check; output = {}",
        out.summary
    );
    // Both legs pass crypto (step 1); the rejection lands on leg 1's adjacency.
    assert_eq!(out.first_failure, Some(1));
    let RotatedReplayVerdict::Rejected { reason } = &out.per_leg[1] else {
        panic!(
            "expected leg-1 Rejected (adjacency), got {:?}",
            out.per_leg[1]
        );
    };
    assert!(
        reason.contains("adjacency"),
        "rejection should name the adjacency break; got: {reason}"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. ANTI-GHOST: a forged (tampered) proof byte is REJECTED.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn tampered_proof_bytes_rejected() {
    let bal: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(bal as u64, 0);
    let before_cell = producer_cell(bal, 0);
    let after_cell = producer_cell(bal - amount as i64, 0);

    let (mut leg, old_commit, new_commit) = mint_rotated_leg(
        &st,
        Effect::Transfer {
            amount,
            direction: 1,
        },
        &before_cell,
        &after_cell,
    );

    // Flip bytes deep in the proof (past any length prefix) so it either fails to
    // deserialize or fails the FRI/constraint check — either way the leg must be
    // rejected, never accepted.
    let n = leg.proof_bytes.len();
    assert!(n > 64, "proof should be non-trivial");
    for b in leg.proof_bytes[n / 2..n / 2 + 16].iter_mut() {
        *b ^= 0xFF;
    }

    let out = verify_rotated_replay_chain(&[leg], old_commit, new_commit);
    assert!(
        !out.overall_verified,
        "a tampered rotated proof must be rejected; output = {}",
        out.summary
    );
    assert_eq!(out.first_failure, Some(0));
    assert!(matches!(
        out.per_leg[0],
        RotatedReplayVerdict::Rejected { .. }
    ));
}

// ─────────────────────────────────────────────────────────────────────────────
// 4. ANTI-GHOST: a tampered vk_hash is REJECTED (Wall A.1).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn tampered_vk_hash_rejected() {
    let bal: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(bal as u64, 0);
    let before_cell = producer_cell(bal, 0);
    let after_cell = producer_cell(bal - amount as i64, 0);

    let (mut leg, old_commit, new_commit) = mint_rotated_leg(
        &st,
        Effect::Transfer {
            amount,
            direction: 1,
        },
        &before_cell,
        &after_cell,
    );

    // The proof still verifies selector-bound, but we corrupt the attached
    // descriptor-identity fingerprint. The verifier re-derives the fingerprint
    // from the uniquely-accepting cohort descriptor and must reject the mismatch.
    leg.vk_hash[0] ^= 0xFF;

    let out = verify_rotated_replay_chain(&[leg], old_commit, new_commit);
    assert!(
        !out.overall_verified,
        "a tampered vk_hash must be rejected even when the proof is selector-bound; output = {}",
        out.summary
    );
    assert_eq!(out.first_failure, Some(0));
    let RotatedReplayVerdict::Rejected { reason } = &out.per_leg[0] else {
        panic!("expected Rejected, got {:?}", out.per_leg[0]);
    };
    assert!(
        reason.contains("vk_hash"),
        "rejection should name vk_hash; got: {reason}"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 5. WRONG-ROOT: a caller expected_old / expected_new mismatch is REJECTED.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn wrong_endpoint_commitment_rejected() {
    let bal: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(bal as u64, 0);
    let before_cell = producer_cell(bal, 0);
    let after_cell = producer_cell(bal - amount as i64, 0);

    let (leg, old_commit, _new_commit) = mint_rotated_leg(
        &st,
        Effect::Transfer {
            amount,
            direction: 1,
        },
        &before_cell,
        &after_cell,
    );

    // The leg itself is sound, but the caller claims a NEW commitment that the
    // chain does not reach. The endpoint check must reject (the proof binds the
    // turn's real post-state; a verifier expecting a different one is not fooled).
    let wrong_new = BabyBear::new_canonical(old_commit.as_u32().wrapping_add(1));
    let out = verify_rotated_replay_chain(&[leg], old_commit, wrong_new);
    assert!(
        !out.overall_verified,
        "a wrong expected_new_commit must be rejected at the endpoint; output = {}",
        out.summary
    );
    let RotatedReplayVerdict::Rejected { reason } = &out.per_leg[0] else {
        panic!("expected Rejected, got {:?}", out.per_leg[0]);
    };
    assert!(
        reason.contains("new_commitment"),
        "rejection should name the new_commitment endpoint; got: {reason}"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 6. WRONG-CHAIN: a dropped middle leg breaks adjacency → REJECTED.
// ─────────────────────────────────────────────────────────────────────────────

/// Build a genuine 2-leg chain, then DROP the first leg and present only the
/// second with the original (whole-turn) endpoints. The second leg's OLD no
/// longer equals expected_old, so the endpoint check breaks — a spliced /
/// truncated chain is rejected (anti-ghost at the chain layer).
#[test]
fn spliced_chain_breaks_endpoint() {
    let bal0: i64 = 100_000;
    let amount: u64 = 50;

    let s0 = CellState::new(bal0 as u64, 0);
    let cell0 = producer_cell(bal0, 0);
    let cell1 = producer_cell(bal0 - amount as i64, 0);
    let (_leg0, old0, _new0) = mint_rotated_leg(
        &s0,
        Effect::Transfer {
            amount,
            direction: 1,
        },
        &cell0,
        &cell1,
    );

    let s1 = CellState::new((bal0 - amount as i64) as u64, 0);
    let cell1b = producer_cell(bal0 - amount as i64, 0);
    let cell2 = producer_cell(bal0 - amount as i64, 1);
    let (leg1, _old1, new1) = mint_rotated_leg(&s1, Effect::IncrementNonce, &cell1b, &cell2);

    // Present ONLY leg1 but claim the whole turn's endpoints [old0 .. new1]. leg1.OLD
    // (== s1's commit) != old0 (== s0's commit), so the first-endpoint check breaks.
    let out = verify_rotated_replay_chain(&[leg1], old0, new1);
    assert!(
        !out.overall_verified,
        "a spliced chain (dropped leading leg) must be rejected; output = {}",
        out.summary
    );
    let RotatedReplayVerdict::Rejected { reason } = &out.per_leg[0] else {
        panic!("expected Rejected, got {:?}", out.per_leg[0]);
    };
    assert!(
        reason.contains("old_commitment"),
        "rejection should name the old_commitment endpoint; got: {reason}"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 7. Empty chain: vacuously verified only for an identity turn (old == new).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn empty_chain_identity_verified_nonidentity_rejected() {
    let c = BabyBear::new_canonical(12345);
    // Identity turn (old == new): an empty chain is vacuously consistent.
    let ok = verify_rotated_replay_chain(&[], c, c);
    assert!(ok.overall_verified, "empty identity chain must verify");
    assert_eq!(ok.total, 0);

    // Non-identity (old != new) with no legs: nothing moved the commitment → reject.
    let d = BabyBear::new_canonical(54321);
    let bad = verify_rotated_replay_chain(&[], c, d);
    assert!(
        !bad.overall_verified,
        "empty chain cannot move the commitment; output = {}",
        bad.summary
    );
}
