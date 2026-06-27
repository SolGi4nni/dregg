//! WHOLE-CHAIN IVC FOLD soundness teeth, on the MANDATORY ROTATED leg.
//!
//! Bucket-F (PATH-PRESERVE Phase 5a): the in-lib `#[cfg(test)]` whole-chain fold
//! teeth were DELETED when the v1 `DescriptorParticipant::v1(proof, trace)` leg was
//! dropped — the leaf is now the rotated multi-table `Ir2BatchProof`
//! (`RotatedParticipantLeg`), minted by
//! `dregg_turn::rotation_witness::mint_rotated_participant_leg`. The lib crate could
//! not host these teeth as integration tests because `circuit/tests/` can depend on
//! `dregg-cell` + `dregg-turn` (which the lib cannot — a dependency cycle), and the
//! rotated mint lives in `dregg-turn`. So the teeth are re-expressed HERE, through
//! the rotated mint, preserving the SAME assertions the deleted in-lib module made.
//!
//! The fold is the artifact that travels to a light client; these teeth pin its
//! soundness:
//!   - a continuous K-turn chain folds + verifies under its honest VK anchor, and
//!     RELABELED carried publics / a mismatched anchor are refused (the
//!     claimed-publics attestation + VK pin);
//!   - a BROKEN temporal order is refused at the chain check (`ChainBreak`);
//!   - an UNGATED prover that FORGES a rotated post-commit cannot obtain a verifying
//!     root (the rotated descriptor leaf is the in-circuit tooth, not the host gate);
//!   - a FOREIGN circuit's recursive root is refused by the VK pin even though the
//!     bare engine accepts it;
//!   - the 2-step inductive core folds a continuous pair and refuses a discontinuous one.
//!
//! Most teeth run a REAL recursion fold (minutes); they are `#[ignore]`. The cheap
//! host-side rejections (`broken_order_rejected`) stay runnable in CI.
//!
//! Run the slow ones with:
//!   cargo test -p dregg-circuit-prove --test ivc_turn_chain_rotated -- --ignored --nocapture
//!
//! NOTE: this file previously carried `#![cfg(feature = "prover")]`, a VESTIGIAL gate
//! from when it lived in `circuit/tests/` under `dregg-circuit`'s `recursion` feature.
//! `dregg-circuit-prove` defines no `prover` feature, so that gate compiled the ENTIRE
//! file out (0 tests) — every IVC soundness tooth here was silently dead. The recursion
//! machinery is unconditional in `dregg-circuit-prove` (and the rotated mint rides the
//! always-present `dregg-turn` dev-dep), so the gate is removed: the teeth run.

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, TurnChainError, WholeChainProof, WholeChainProofBytes, fold_two_turns,
    prove_turn_chain_recursive, prove_turn_chain_recursive_without_host_gate,
    verify_turn_chain_recursive, verify_turn_chain_recursive_from_blobs,
    verify_whole_chain_proof_bytes,
};
use dregg_circuit_prove::joint_turn_aggregation::{DescriptorParticipant, RotatedParticipantLeg};
use dregg_turn::rotation_witness::mint_rotated_participant_leg;

// A transfer's effect selector (`effect_vm::columns::sel::TRANSFER`), the selector
// the ungated chain prover is handed for each rotated transfer leg.
use dregg_circuit::effect_vm::sel;

// `WholeChainProof` is imported for type clarity even though it is only named via the
// `prove_*` return types; silence the unused-import lint without dropping the doc value.
#[allow(unused_imports)]
use dregg_circuit_prove::ivc_turn_chain::WholeChainProof as _WholeChainProof;

// ============================================================================
// THE CANONICAL ROTATED MINT FIXTURE (copied verbatim from
// `circuit/tests/proof_economics.rs` — the audited Bucket-F mint pattern).
//
// A finalized turn carries the MANDATORY ROTATED leg: the rotated multi-table
// `Ir2BatchProof` minted by `mint_rotated_participant_leg` over before/after actor
// `Cell`s. The chain roots are the ROTATED commitments read off the leg (PI 34/35).
// ============================================================================

/// OPEN permissions so the rotated producer-witness path admits the actor cell
/// without auth gating (mirrors `rotation_batchstark_leaf_smoke.rs`).
fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
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

/// The transfer actor cell at `(balance, nonce)` with open permissions — the
/// before/after `Cell` the rotated mint runs `rotation_witness::produce` over.
fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// Build a REAL finalized turn on the rotated descriptor path: execute a `Transfer`
/// DEBIT of `amount` from `(balance, nonce)`, mint the rotated multi-table
/// `Ir2BatchProof` leg via `mint_rotated_participant_leg` (which self-verifies), and
/// carry it as the mandatory leaf. Returns the turn plus its REAL ROTATED
/// `(old_root, new_root)` commitments (PI 34/35) — the genuine Poseidon2 state
/// commitments the rotated generator derives, NOT fabricated values.
fn make_turn(balance: u64, nonce: u32, amount: u64) -> (FinalizedTurn, BabyBear, BabyBear) {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    // The rotated transfer DEBIT keeps the nonce and decreases the balance by
    // `amount`: before/after actor cells at the same nonce, balance - amount.
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        None,
    )
    .expect("rotated transfer leg mints + self-verifies");
    // Read the ROTATED chain roots off the leg BEFORE it moves into the participant.
    let old_root = leg.old_root();
    let new_root = leg.new_root();
    (
        FinalizedTurn::new(DescriptorParticipant::rotated(leg)),
        old_root,
        new_root,
    )
}

/// Build a continuous chain of `k` real finalized turns: each turn debits `step`
/// from the balance and the next turn starts from the post-state. The rotated
/// trace's welded scalars (balance/nonce/...) come from the v1 sub-trace, which
/// BUMPS the nonce by 1 per non-NoOp (Transfer) effect — so turn i's after-state is
/// `(balance - step, nonce + 1)`. The next turn's before-state must therefore be
/// `(balance - step, nonce + 1)` for the rotated state-commit roots to link
/// (`old_root[i+1] == new_root[i]`): we advance BOTH balance and nonce per turn.
/// Returns the turns + genesis/final.
fn make_chain(
    start_balance: u64,
    start_nonce: u32,
    step: u64,
    k: usize,
) -> (Vec<FinalizedTurn>, BabyBear, BabyBear) {
    let mut turns = Vec::with_capacity(k);
    let mut balance = start_balance;
    let mut nonce = start_nonce;
    let mut genesis = BabyBear::ZERO;
    let mut final_root = BabyBear::ZERO;
    // `nonce`/`balance` are intertwined chain accumulators here; an enumerate rewrite isn't clean.
    #[allow(clippy::explicit_counter_loop)]
    for i in 0..k {
        let (turn, old_root, new_root) = make_turn(balance, nonce, step);
        if i == 0 {
            genesis = old_root;
        } else {
            assert_eq!(old_root, final_root, "real chain must already link");
        }
        final_root = new_root;
        turns.push(turn);
        balance -= step;
        nonce += 1; // the v1 sub-trace bumps the nonce by 1 per Transfer row.
    }
    (turns, genesis, final_root)
}

// ============================================================================
// THE TEETH
// ============================================================================

/// GOLD whole-chain: fold K=3 REAL rotated finalized turns into ONE recursive proof
/// that verifies under its honest VK anchor. Each turn's real ROTATED post-state
/// commitment is the next turn's real pre-state commitment (genesis -> r1 -> r2 ->
/// final). The verifier checks only the root (+ the VK pin and the carried binding
/// attestation).
///
/// Piggybacked REFUSED cases (no extra proving): a mismatched VK anchor is refused,
/// and RELABELED carried publics (final_root / chain_digest / num_turns /
/// genesis_root spliced after the fold) are refused by the claimed-publics
/// attestation — the verify path reads the publics against the carried binding proof
/// instead of trusting bare fields.
#[test]
#[ignore = "SLOW: real recursion fold (~minutes); run with --ignored"]
fn k_fold_turn_chain_proves_and_verifies() {
    let (turns, genesis, final_root) = make_chain(1000, 0, 7, 3);
    assert_eq!(turns.len(), 3);

    let mut whole: WholeChainProof = prove_turn_chain_recursive(&turns)
        .expect("a continuous 3-turn rotated finalized chain must fold recursively");
    assert_eq!(whole.num_turns, 3);
    assert_eq!(whole.genesis_root, [genesis; 8]);
    assert_eq!(whole.final_root, [final_root; 8]);

    // The trust anchor an honest setup would distribute.
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the whole-chain root proof must verify under its honest anchor");

    // REFUSED: a mismatched VK anchor (the caller pinned a different circuit).
    let mut wrong = vk;
    wrong.0[0] ^= 0xFF;
    match verify_turn_chain_recursive(&whole, &wrong) {
        Err(TurnChainError::VkFingerprintMismatch { .. }) => {}
        other => panic!("a mismatched VK anchor must be refused; got {other:?}"),
    }

    // REFUSED: relabeled final_root (splicing a foreign endpoint onto the artifact).
    let honest_final = whole.final_root;
    whole.final_root[0] = honest_final[0] + BabyBear::ONE;
    match verify_turn_chain_recursive(&whole, &vk) {
        Err(TurnChainError::ClaimedPublicsUnattested { .. }) => {}
        other => panic!("a relabeled final_root must be refused; got {other:?}"),
    }
    whole.final_root = honest_final;

    // REFUSED: relabeled chain_digest (claiming a different ordered history) — the digest
    // is now a multi-felt Poseidon2 commitment; relabel any lane.
    let honest_digest = whole.chain_digest;
    whole.chain_digest[0] = honest_digest[0] + BabyBear::ONE;
    match verify_turn_chain_recursive(&whole, &vk) {
        Err(TurnChainError::ClaimedPublicsUnattested { .. }) => {}
        other => panic!("a relabeled chain_digest must be refused; got {other:?}"),
    }
    whole.chain_digest = honest_digest;

    // REFUSED: relabeled num_turns (the binding proof Fiat–Shamir-binds pv[2]).
    let honest_n = whole.num_turns;
    whole.num_turns = honest_n + 1;
    match verify_turn_chain_recursive(&whole, &vk) {
        Err(TurnChainError::ClaimedPublicsUnattested { .. }) => {}
        other => panic!("a relabeled num_turns must be refused; got {other:?}"),
    }
    whole.num_turns = honest_n;

    // REFUSED: relabeled genesis_root.
    let honest_genesis = whole.genesis_root;
    whole.genesis_root[0] = honest_genesis[0] + BabyBear::ONE;
    match verify_turn_chain_recursive(&whole, &vk) {
        Err(TurnChainError::ClaimedPublicsUnattested { .. }) => {}
        other => panic!("a relabeled genesis_root must be refused; got {other:?}"),
    }
    whole.genesis_root = honest_genesis;

    // And the restored artifact still verifies (the refusals were the lies, not
    // collateral damage).
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the restored honest artifact must verify again");
}

/// THE BYTE PATH (S1, both polarities): a REAL whole-chain proof SERIALIZES into the
/// versioned [`WholeChainProofBytes`] envelope, DESERIALIZES back, and VERIFIES over
/// the wire against its honest anchor — re-witnessing nothing, never touching the
/// prover-only `root.1`. Then the tampered polarities are REFUSED:
///   - a corrupted root-proof byte fails the recursion verify;
///   - a relabeled carried public (in the envelope) fails the claimed-publics tooth;
///   - a wrong anchor fails the VK pin;
///   - a bumped envelope version / truncated blob fails the decode (fail-closed).
///
/// This is the keystone tooth the wasm over-wire verify and pg-dregg's tier-c gate
/// both rest on: the in-memory `verify_turn_chain_recursive` and the byte
/// `verify_whole_chain_proof_bytes` share ONE verifier body and AGREE on this proof.
#[test]
#[ignore = "SLOW: real recursion fold (~minutes); run with --ignored"]
fn whole_chain_proof_bytes_roundtrip_and_tamper() {
    let (turns, genesis, final_root) = make_chain(1000, 0, 7, 3);
    let whole: WholeChainProof = prove_turn_chain_recursive(&turns)
        .expect("a continuous 3-turn rotated finalized chain must fold recursively");
    let vk = whole.root_vk_fingerprint();

    // (A) ADMITS: serialize → bytes → deserialize → the env carries the true publics.
    let bytes = whole.to_bytes();
    assert!(!bytes.is_empty(), "the byte envelope must be non-empty");
    let env = WholeChainProofBytes::from_postcard(&bytes).expect("the honest envelope must decode");
    assert_eq!(
        env.version,
        dregg_circuit_prove::ivc_turn_chain::WHOLE_CHAIN_PROOF_ENVELOPE_V1
    );
    assert_eq!(env.genesis_root, [genesis.as_u32(); 8]);
    assert_eq!(env.final_root, [final_root.as_u32(); 8]);
    assert_eq!(env.num_turns, 3);
    assert_eq!(env.vk_fingerprint_hex, vk.to_hex());

    // The over-wire verify AGREES with the in-memory verify (the keystone): a real
    // whole-chain proof serializes, deserializes, and VERIFIES against its anchor.
    verify_whole_chain_proof_bytes(&bytes, &vk)
        .expect("the deserialized whole-chain proof must verify over the wire");
    // The lower blob seam (pg-dregg's path) accepts the same bytes' components.
    verify_turn_chain_recursive_from_blobs(
        &env.root_proof,
        &env.binding_proof,
        &env.genesis_root,
        &env.final_root,
        &env.chain_digest,
        env.num_turns as usize,
        &vk.0,
    )
    .expect("the blob seam must verify the same honest components");

    // (B) REFUSES: a corrupted root-proof byte. Flip a byte deep in the root blob
    // (past the length/version prefix) and re-pack; the recursion verify must reject
    // it (or the structural decode catches it first — both are fail-closed).
    {
        let mut bad = env.clone();
        let mid = bad.root_proof.len() / 2;
        bad.root_proof[mid] ^= 0xFF;
        let bad_bytes = bad.to_postcard();
        match verify_whole_chain_proof_bytes(&bad_bytes, &vk) {
            Err(
                TurnChainError::RecursionFailed { .. }
                | TurnChainError::VkFingerprintMismatch { .. }
                | TurnChainError::EnvelopeDecode { .. },
            ) => {}
            other => panic!("a corrupted root proof must be refused; got {other:?}"),
        }
    }

    // (C) REFUSES: a relabeled carried public in the ENVELOPE (a post-fold splice).
    // The claimed-publics tooth reads the publics against the binding proof.
    {
        let mut bad = env.clone();
        bad.final_root[0] = bad.final_root[0].wrapping_add(1);
        let bad_bytes = bad.to_postcard();
        match verify_whole_chain_proof_bytes(&bad_bytes, &vk) {
            Err(TurnChainError::ClaimedPublicsUnattested { .. }) => {}
            other => panic!("a relabeled envelope final_root must be refused; got {other:?}"),
        }
    }

    // (D) REFUSES: a wrong anchor (a different circuit) — the VK pin fires.
    {
        let mut wrong = vk;
        wrong.0[0] ^= 0xFF;
        match verify_whole_chain_proof_bytes(&bytes, &wrong) {
            Err(TurnChainError::VkFingerprintMismatch { .. }) => {}
            other => panic!("a wrong anchor must be refused over the wire; got {other:?}"),
        }
    }

    // (E) REFUSES (fail-closed decode): a bumped version, a truncated body, empty.
    {
        let mut bad = env.clone();
        bad.version = 999;
        match WholeChainProofBytes::from_postcard(&bad.to_postcard()) {
            Err(TurnChainError::EnvelopeDecode { .. }) => {}
            other => panic!("a bumped envelope version must be refused; got {other:?}"),
        }
        match WholeChainProofBytes::from_postcard(&[]) {
            Err(TurnChainError::EnvelopeDecode { .. }) => {}
            other => panic!("empty bytes must be refused; got {other:?}"),
        }
        match WholeChainProofBytes::from_postcard(&bytes[..bytes.len() / 2]) {
            Err(TurnChainError::EnvelopeDecode { .. }) => {}
            other => panic!("a truncated envelope must be refused; got {other:?}"),
        }
        // An empty proof-component is refused even with a valid version.
        let mut empty_root = env.clone();
        empty_root.root_proof = Vec::new();
        match WholeChainProofBytes::from_postcard(&empty_root.to_postcard()) {
            Err(TurnChainError::EnvelopeDecode { .. }) => {}
            other => panic!("an empty root-proof component must be refused; got {other:?}"),
        }
    }
}

/// TEMPORAL TOOTH (host): a turn whose real ROTATED old_root != previous new_root
/// breaks the finalized order and is rejected at the chain check — before any tree.
/// We splice an out-of-sequence turn (a fresh, unrelated chain's turn, whose rotated
/// pre-state commitment does not match) into the middle.
///
/// CHEAP enough to run in CI: it mints 3 chain legs + 1 foreign leg, but `ChainBreak`
/// fires in `prove_chain_core_rotated`'s host-side continuity check (after the host
/// admission loop) BEFORE any recursion proving begins. (The mints themselves take a
/// few seconds; kept non-ignored because no FULL fold runs.)
#[test]
fn broken_order_rejected() {
    let (mut turns, _g, _f) = make_chain(1000, 0, 7, 3);
    // Replace turn 1 with a turn from an UNRELATED chain (different starting balance),
    // so its real rotated old_root does not continue turn 0's new_root.
    let (foreign, foreign_old, _foreign_new) = make_turn(500, 50, 3);
    let prev_new = turns[0].new_root();
    assert_ne!(
        foreign_old, prev_new,
        "the foreign turn must NOT continue the chain (that is the point)"
    );
    turns[1] = foreign;

    match prove_turn_chain_recursive(&turns) {
        Err(TurnChainError::ChainBreak {
            index,
            expected_old_root,
            found_old_root,
        }) => {
            assert_eq!(index, 1);
            assert_eq!(expected_old_root, prev_new.0);
            assert_eq!(found_old_root, foreign_old.0);
        }
        Ok(_) => panic!("a broken finalized order must not produce a whole-chain proof"),
        Err(other) => panic!("expected ChainBreak, got {other:?}"),
    }
}

/// **THE LEAF TOOTH (host-gate-skipping prover, forged post-commit).** The claim is
/// that per-turn execution soundness does NOT rest on the prover having run the
/// host-side descriptor admission. So: run the UNGATED prover on a chain whose second
/// turn LIES about its rotated post-state root in the PIs (the execution witness is
/// honest; only the claimed rotated `NEW_COMMIT` at PI 35 is forged — exactly the lie
/// a malicious prover tells to advance the chain to a state that never happened). The
/// rotated descriptor AIR's PI binding + Poseidon2 state-commit hash sites make that
/// leaf UNSATISFIABLE, so the in-circuit re-proof fails and NO verifying root can be
/// produced — the host gate was never load-bearing.
///
/// We assert BOTH:
///   (a) the GATED prover rejects at host admission — the forged rotated PI no longer
///       verifies the production descriptor proof (`verify_descriptor_participant`
///       re-verifies the WHOLE 38-PI vector). The host runs admission BEFORE the
///       continuity check, so `TurnProofInvalid { index: 1 }` fires first; we accept
///       EITHER `TurnProofInvalid` OR `ChainBreak` at index 1 to stay robust to the
///       order in which the host reads roots vs re-verifies proofs.
///   (b) the UNGATED prover (which never runs the host gate) ALSO fails, at the
///       in-circuit leaf (catch_unwind: rejected if Err or panic).
#[test]
#[ignore = "SLOW: real recursion fold (~minutes); run with --ignored"]
fn ungated_prover_with_forged_post_commit_cannot_produce_a_root() {
    // The v1 sub-trace bumps the nonce by 1 per Transfer, so turn 0's after-state is (993, 1);
    // turn 1's before-state must be (993, 1) for the rotated roots to chain.
    let (t0, _o0, n0) = make_turn(1000, 0, 7);
    let (t1, o1, n1) = make_turn(993, 1, 7);
    assert_eq!(o1, n0, "honest rotated turns chain by construction");

    // FORGE the rotated NEW commitment (PI 35 = V1_PI_COUNT + 1) on turn 1's leg.
    // The leg's `proof`/`descriptor`/`public_inputs` are all `pub`, so we destructure
    // the participant, mutate the PI vector, and rebuild the leg — the proof object is
    // unchanged (the lie is purely in the claimed PI, which the in-circuit verifier
    // pins against the proof).
    const PI_ROTATED_NEW: usize = dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT + 1;
    let DescriptorParticipant { rotated } = t1.participant;
    let RotatedParticipantLeg {
        proof,
        descriptor,
        mut public_inputs,
    } = rotated;
    let lie = n1 + BabyBear::ONE;
    public_inputs[PI_ROTATED_NEW] = lie;
    let forged_leg = RotatedParticipantLeg {
        proof,
        descriptor,
        public_inputs,
    };
    let t1_forged = FinalizedTurn::new(DescriptorParticipant::rotated(forged_leg));
    let turns = [t0, t1_forged];

    // (a) The GATED prover rejects at host admission (the forged PI no longer verifies
    //     the production rotated descriptor proof). Accept TurnProofInvalid (host
    //     re-verify) OR ChainBreak (continuity) at index 1.
    match prove_turn_chain_recursive(&turns) {
        Err(TurnChainError::TurnProofInvalid { index, .. }) => assert_eq!(index, 1),
        Err(TurnChainError::ChainBreak { index, .. }) => assert_eq!(index, 1),
        Ok(_) => panic!("the gated prover accepted a forged rotated post-commit"),
        Err(other) => {
            panic!("expected TurnProofInvalid or ChainBreak at index 1, got {other:?}")
        }
    }

    // (b) THE TOOTH: the UNGATED prover — which never runs the host gate — must ALSO
    //     fail, at the in-circuit leaf. The unsatisfiable leaf surfaces as a prover
    //     panic (debug: check_constraints refuses) or an Err (release: self-verify
    //     rejects). Either is "no root".
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_turn_chain_recursive_without_host_gate(&turns, &[sel::TRANSFER, sel::TRANSFER])
    }));
    let rejected = match result {
        Ok(Ok(_)) => false, // a verifying root for a forged turn — soundness hole!
        Ok(Err(_)) => true,
        Err(_) => true,
    };
    assert!(
        rejected,
        "a host-gate-skipping prover with a forged rotated post-commit must NOT obtain a \
         whole-chain root — the rotated descriptor leaf is the in-circuit tooth"
    );
}

/// **THE VK-PIN TOOTH (from-scratch prover, REFUSED).** `verify_recursive_batch_proof`
/// reconstructs circuit common data FROM the proof, so ANY valid recursive proof —
/// here a wrap of the unrelated `AggregationAir` — passes the bare root check. The
/// pinned verifier must refuse it: its verifier-key fingerprint is not the chain
/// fold's. Both halves are asserted: the bare engine ACCEPTS the foreign root (the pin
/// is load-bearing), and `verify_turn_chain_recursive` REFUSES it with
/// `VkFingerprintMismatch`.
#[test]
#[ignore = "SLOW: real recursion fold (~minutes); run with --ignored"]
fn foreign_circuit_root_is_refused_by_vk_pin() {
    use dregg_circuit::plonky3_recursion::AggregationAir;
    use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
        prove_inner_for_air, prove_recursive_layer_for_air, verify_recursive_batch_proof,
    };
    use p3_baby_bear::BabyBear as P3BabyBear;
    use p3_field::PrimeCharacteristicRing;
    use p3_matrix::dense::RowMajorMatrix;

    // An honest K=2 fold (the artifact whose carried publics + binding proof the
    // attacker will try to pair with a foreign root).
    let (turns, _g, _f) = make_chain(1000, 0, 7, 2);
    let mut whole = prove_turn_chain_recursive(&turns).expect("the honest 2-turn chain must fold");
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk).expect("honest artifact verifies");

    // A from-scratch prover's root: a perfectly VALID recursive proof — of a DIFFERENT
    // circuit (the AggregationAir smoke wrap).
    let foreign = {
        let pv1 = P3BabyBear::from_u64(0xC0FFEE);
        let rows: Vec<P3BabyBear> = vec![
            P3BabyBear::ZERO,
            P3BabyBear::from_u64(1),
            P3BabyBear::from_u64(2),
            P3BabyBear::from_u64(10),
            P3BabyBear::from_u64(10),
            P3BabyBear::from_u64(3),
            P3BabyBear::from_u64(4),
            P3BabyBear::from_u64(20),
            P3BabyBear::from_u64(20),
            P3BabyBear::from_u64(5),
            P3BabyBear::from_u64(6),
            P3BabyBear::from_u64(30),
            P3BabyBear::from_u64(30),
            P3BabyBear::from_u64(7),
            P3BabyBear::from_u64(8),
            pv1,
        ];
        let matrix = RowMajorMatrix::new(rows, 4);
        let pis = vec![BabyBear::ZERO, BabyBear::new(0xC0FFEE)];
        let air = AggregationAir;
        let inner = prove_inner_for_air(&air, matrix, &pis);
        prove_recursive_layer_for_air(&air, &inner, &pis)
            .expect("the foreign AIR wraps fine — it is a VALID recursive proof")
    };

    // The bare engine check ACCEPTS the foreign root — the exact reason the pin exists.
    verify_recursive_batch_proof(&foreign.0)
        .expect("the bare engine accepts ANY valid recursive proof — the pre-pin hole");

    // Splice the foreign root under the honest carried publics/binding.
    whole.root = foreign;
    match verify_turn_chain_recursive(&whole, &vk) {
        Err(TurnChainError::VkFingerprintMismatch { .. }) => {}
        Ok(()) => panic!("a foreign circuit's root must NOT verify as the chain fold"),
        Err(other) => panic!("expected VkFingerprintMismatch, got {other:?}"),
    }
}

/// **CODEX FINDING #1 / #6 — THE OPEN HOLE, MADE EXECUTABLE (binding↔root not linked).**
///
/// The final verifier checks three things INDEPENDENTLY: the carried binding proof
/// (tooth 2), the root VK fingerprint (tooth 1), and the root batch proof (tooth 3). It
/// NEVER checks that the carried binding proof is the binding leaf folded INTO that root.
/// So a GENUINE root for history A, paired with a GENUINE binding proof for a DIFFERENT
/// history B (and B's publics), passes all three teeth — a false whole-chain claim
/// verifies.
///
/// This test CONSTRUCTS that forgery from two real same-shape folds and asserts that the
/// current verifier ACCEPTS it. It is a WITNESS THAT THE HOLE IS OPEN, not a closure: it
/// will start FAILING (i.e. the forgery will be REJECTED) once the in-band binding↔root
/// linkage lands — at which point this `assert!(forged_accepts)` flips to
/// `assert!(forged_rejected)`. Closing it requires the fork to re-expose the binding
/// leaf's chain publics at the ROOT as a checkable output (today the root's
/// `non_primitives` are only `[poseidon2_perm, recompose]`, BOTH with zero public values
/// — empirically confirmed; the leaf publics are consumed in-circuit and never surfaced),
/// so the host can verify `root-exposed publics == carried claim`.
///
/// **The EXACT remaining mechanism (root-caused at source 2026-06-24).** The only
/// host-readable, FRI-bound scalar channel a `BatchStarkProof` carries is
/// `non_primitives[i].public_values` (host reads them off the proof; `verify_all_tables`
/// binds them via the table's lookup argument). The binding leaf's 4 chain publics enter
/// every layer ONLY as the parent verifier circuit's `air_public_targets`, which the fork
/// allocates as `circuit.public_input()` (`Op::Public`) — i.e. they land in the parent's
/// *constraint-free `Public` PRIMITIVE table*, NOT in any non-primitive `public_values`.
/// The grandparent then allocates child-public targets solely from each child
/// `non_primitives[].public_values.len()` (primitive-table values are never threaded), so
/// the chain publics are CONSUMED one layer up and vanish before the root. No NPO table in
/// the fork ever populates `public_values` non-empty (`poseidon2`/`recompose` hardcode
/// `Vec::new()`), so the exposed-public channel is *unbuilt machinery*. A genuine REJECT
/// therefore requires the fork to (i) add an "exposed-claim" channel — either a new
/// constrained NPO table whose `public_values` carry the 4 chain claims, or an
/// "expose-target-as-proof-public" hook wired through `build_verifier_circuit` →
/// `prove_all_tables` → `non_primitives[].public_values` — emitted at the binding-leaf wrap,
/// and (ii) re-emit + in-circuit-bind those 4 values to the verified child at EACH
/// aggregation layer up to the root. That is multi-pass recursion-engine work on the shared
/// fork; it was NOT landed in this pass (deliberately, to avoid destabilizing the engine all
/// other dregg proofs depend on). The host-only fix is provably impossible: A and B share the
/// op-list (so identical preprocessed/VK commitment) and all their distinguishing data
/// (trace/FRI commitments) is consumed in-circuit, never surfaced at the root.
///
/// Two K=2 transfer chains have the SAME tree shape ⇒ the SAME root VK fingerprint, so
/// tooth 1 cannot tell them apart. They have DIFFERENT data ⇒ different roots/digests, so
/// the cross-paired claim is genuinely false.
#[test]
#[ignore = "SLOW: two real folds (~minutes); run with --ignored — the CLOSE of IVC hole #1/#6"]
fn carried_binding_proof_unlinked_to_root_is_rejected() {
    // History A: the GENUINE root we keep.
    let (turns_a, _ga, _fa) = make_chain(1000, 0, 7, 2);
    let whole_a = prove_turn_chain_recursive(&turns_a).expect("chain A folds");
    let vk = whole_a.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole_a, &vk).expect("A verifies honestly");

    // History B: a DIFFERENT history (different start balance ⇒ different roots/digest),
    // SAME K=2 transfer shape ⇒ SAME root VK fingerprint.
    let (turns_b, gb, fb) = make_chain(500, 0, 3, 2);
    let whole_b = prove_turn_chain_recursive(&turns_b).expect("chain B folds");
    assert_eq!(
        whole_a.root_vk_fingerprint(),
        whole_b.root_vk_fingerprint(),
        "same-shape K=2 transfer chains share a root VK fingerprint (tooth 1 cannot \
         distinguish them) — this is what makes the cross-pairing attack land"
    );
    assert_ne!(
        whole_a.chain_digest, whole_b.chain_digest,
        "the two histories are genuinely distinct (different ordered-history digests)"
    );

    // THE FORGERY: keep A's GENUINE root, but swap in B's GENUINE binding proof + B's
    // publics. Every field is internally consistent (B's binding proof attests B's
    // publics), and the root is a genuine same-shape root.
    let mut forged = whole_a;
    forged.binding_proof = whole_b.binding_proof;
    forged.genesis_root = [gb; 8];
    forged.final_root = [fb; 8];
    forged.chain_digest = whole_b.chain_digest;
    forged.num_turns = whole_b.num_turns;

    let verdict = verify_turn_chain_recursive(&forged, &vk);
    // CLOSED (IVC hole #1/#6). The EXPOSED-CLAIM CHANNEL ties the carried binding proof
    // to THIS root: A's root proof carries an `expose_claim` non-primitive table whose
    // public_values are A's 4 chain claims, bus-bound (WitnessChecks reader mult -1) to
    // the binding proof the fold actually verified and re-bound at every aggregation layer.
    // Tooth (4) compares the carried claim against those root-exposed publics — so A's
    // root paired with B's binding proof + B's claims now FAILS: A's root exposes A's
    // endpoints, while the swapped claim is B's.
    assert!(
        verdict.is_err(),
        "the binding↔root linkage REJECTS a genuine root for history A paired with a \
         genuine binding proof for a DIFFERENT history B (the cross-pairing forgery). \
         got: {verdict:?}"
    );
}

// ============================================================================
// CODEX FINDING #2 — CLOSED. The binding AIR now enforces the per-row Poseidon2
// digest hash + num_turns = real-row count IN-CIRCUIT, so a forged digest or a
// forged num_turns is UNSAT. These two teeth pin the verify→REJECT flip.
//
// They build the GENUINE wide binding trace by hand (mirroring the lib-private
// `binding_row`: 7 scalar cols `[old, new, acc_in, acc_out, idx, is_real,
// real_count]` + the 352-col Poseidon2 aux block), prove it (honest control
// passes), then TAMPER one field and assert the inner verify REJECTS. A single
// inner uni-STARK (no recursion fold) — CI-runnable.
// ============================================================================

/// Build the GENUINE binding trace for a 2-real-row chain `genesis -> mid -> final`
/// (padded_len == 2, so no padding rows). Returns `(matrix, pis)` ready for the inner
/// prover. The Poseidon2 aux block is the real `poseidon2_permute_aux_witness`, so the
/// in-circuit hash constraint (`acc_out == poseidon2([acc_in, old, new, idx], 4)[0]`)
/// is satisfied — the honest control. A caller tampers `matrix`/`pis` to forge.
fn honest_binding_2row(
    genesis: BabyBear,
    mid: BabyBear,
    final_root: BabyBear,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    use dregg_circuit::plonky3_prover::{POSEIDON2_WIDTH, poseidon2_permute_aux_witness};
    use dregg_circuit::poseidon2::hash_4_to_1;

    const HASH_ARITY_TAG: u32 = 4;
    let row =
        |old: BabyBear, new: BabyBear, acc_in: BabyBear, idx: BabyBear, real_count: BabyBear| {
            let acc_out = hash_4_to_1(&[acc_in, old, new, idx]);
            let mut st = [BabyBear::ZERO; POSEIDON2_WIDTH];
            st[0] = acc_in;
            st[1] = old;
            st[2] = new;
            st[3] = idx;
            st[4] = BabyBear::new(HASH_ARITY_TAG);
            let aux = poseidon2_permute_aux_witness(st);
            let mut r = vec![
                old,
                new,
                acc_in,
                acc_out,
                idx,
                BabyBear::ONE, // is_real (both rows real for a 2-turn chain)
                real_count,
            ];
            r.extend_from_slice(&aux);
            (acc_out, r)
        };

    let (h0, r0) = row(genesis, mid, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ONE);
    let (h1, r1) = row(mid, final_root, h0, BabyBear::ONE, BabyBear::new(2));
    let chain_digest = h1;
    let pis = vec![genesis, final_root, BabyBear::new(2), chain_digest];
    (vec![r0, r1], pis)
}

fn to_binding_matrix(rows: &[Vec<BabyBear>]) -> p3_matrix::dense::RowMajorMatrix<P3BabyBear> {
    use p3_field::PrimeCharacteristicRing;
    let width = rows[0].len();
    let flat: Vec<P3BabyBear> = rows
        .iter()
        .flat_map(|r| r.iter().map(|&v| P3BabyBear::from_u64(v.0 as u64)))
        .collect();
    p3_matrix::dense::RowMajorMatrix::new(flat, width)
}

use p3_baby_bear::BabyBear as P3BabyBear;

/// **CODEX FINDING #2 (digest) — CLOSED.** The in-AIR per-row Poseidon2 binding forces
/// `acc_out == hash_4_to_1([acc_in, old, new, idx])`, so a forged `chain_digest` (a
/// tampered last-row `acc_out` + public) has NO satisfying witness. Honest control
/// passes; the forgery is REJECTED.
#[test]
fn binding_air_forged_digest_unsat() {
    use dregg_circuit_prove::ivc_turn_chain::{TurnChainBindingAir, ir2_leaf_wrap_config};
    use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
        prove_inner_for_air_with_config, verify_inner_for_air_with_config,
    };

    let genesis = BabyBear::new(111);
    let mid = BabyBear::new(222);
    let final_root = BabyBear::new(333);
    let cfg = ir2_leaf_wrap_config();
    let air = TurnChainBindingAir;

    // HONEST CONTROL: the genuine trace proves + verifies.
    let (rows, pis) = honest_binding_2row(genesis, mid, final_root);
    let honest = prove_inner_for_air_with_config(&air, to_binding_matrix(&rows), &pis, &cfg);
    verify_inner_for_air_with_config(&air, &honest, &pis, &cfg)
        .expect("the honest wide binding trace must verify (control)");

    // FORGERY: claim a different chain_digest than the real hash chain. We move the
    // public AND the last-row acc_out to the forged value (so the carry chain still
    // links) — but the per-row Poseidon2 constraint now forces acc_out to the REAL
    // hash, so the tampered last row is UNSAT.
    let forged_digest = pis[3] + BabyBear::new(0xDEAD);
    let mut forged_rows = rows.clone();
    let last = forged_rows.len() - 1;
    forged_rows[last][3] = forged_digest; // COL_ACC_OUT on the last row
    let mut forged_pis = pis.clone();
    forged_pis[3] = forged_digest; // chain_digest public

    // A forged trace cannot satisfy the constraints. In DEBUG the prover's
    // `check_constraints` panics on the unsatisfied row; in RELEASE the prover emits a
    // proof that VERIFY rejects. Either way the prove→verify pipeline must NOT SUCCEED.
    let forged_rows2 = forged_rows.clone();
    let forged_pis2 = forged_pis.clone();
    let cfg2 = cfg.clone();
    let succeeded = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let air = TurnChainBindingAir;
        let p = prove_inner_for_air_with_config(
            &air,
            to_binding_matrix(&forged_rows2),
            &forged_pis2,
            &cfg2,
        );
        verify_inner_for_air_with_config(&air, &p, &forged_pis2, &cfg2).is_ok()
    }))
    .unwrap_or(false); // a panic (debug constraint failure) == rejected
    assert!(
        !succeeded,
        "FINDING #2 CLOSED: a forged chain_digest must be REJECTED by the in-AIR \
         Poseidon2 binding (acc_out is forced to the genuine hash), but the pipeline accepted it"
    );
}

/// **CODEX FINDING #2 (num_turns) — CLOSED.** `num_turns` (pv[2]) is pinned to
/// `real_count[last]`, the cumulative count of `is_real` rows. A forged `num_turns`
/// (≠ the genuine 2) mismatches the real-row count and is UNSAT.
#[test]
fn binding_air_forged_num_turns_unsat() {
    use dregg_circuit_prove::ivc_turn_chain::{TurnChainBindingAir, ir2_leaf_wrap_config};
    use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
        prove_inner_for_air_with_config, verify_inner_for_air_with_config,
    };

    let genesis = BabyBear::new(444);
    let mid = BabyBear::new(555);
    let final_root = BabyBear::new(666);
    let cfg = ir2_leaf_wrap_config();
    let air = TurnChainBindingAir;

    let (rows, pis) = honest_binding_2row(genesis, mid, final_root);
    // HONEST CONTROL.
    let honest = prove_inner_for_air_with_config(&air, to_binding_matrix(&rows), &pis, &cfg);
    verify_inner_for_air_with_config(&air, &honest, &pis, &cfg)
        .expect("the honest wide binding trace must verify (control)");

    // FORGERY: claim num_turns = 99 while the genuine real-row count is 2. Only pv[2]
    // changes; the trace (real_count[last] == 2) cannot satisfy `real_count == num_turns`.
    let mut forged_pis = pis.clone();
    forged_pis[2] = BabyBear::new(99);
    let rows2 = rows.clone();
    let forged_pis2 = forged_pis.clone();
    let cfg2 = cfg.clone();
    let succeeded = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let air = TurnChainBindingAir;
        let p =
            prove_inner_for_air_with_config(&air, to_binding_matrix(&rows2), &forged_pis2, &cfg2);
        verify_inner_for_air_with_config(&air, &p, &forged_pis2, &cfg2).is_ok()
    }))
    .unwrap_or(false);
    assert!(
        !succeeded,
        "FINDING #2 CLOSED: a forged num_turns (99 != real count 2) must be REJECTED by \
         the real_count[last] == num_turns binding, but the pipeline accepted it"
    );
}

/// 2-step inductive core: `fold_two_turns` over a continuous pair yields a verifying
/// whole-chain proof of the 2-turn window (the unbounded loop's inductive step).
#[test]
#[ignore = "SLOW: real recursion fold (~minutes); run with --ignored"]
fn two_step_inductive_core_proves_and_verifies() {
    let (turns, genesis, final_root) = make_chain(1000, 0, 11, 2);

    let folded =
        fold_two_turns(&turns[0], &turns[1]).expect("a continuous pair must fold via the core");
    assert_eq!(folded.num_turns, 2);
    assert_eq!(folded.genesis_root, [genesis; 8]);
    assert_eq!(folded.final_root, [final_root; 8]);
    let vk = folded.root_vk_fingerprint();
    verify_turn_chain_recursive(&folded, &vk).expect("the 2-step folded proof must verify");
}

/// `fold_two_turns` rejects a discontinuous pair (the inductive step refuses to extend
/// the running chain with a turn that does not consume its root).
///
/// CHEAP: the host-side `ChainBreak` fires before any recursion proving (only two leg
/// mints; no full fold), so this stays runnable in CI.
#[test]
fn two_step_core_rejects_discontinuity() {
    let (running, _o, _n) = make_turn(1000, 0, 11);
    let (bad_next, _bo, _bn) = make_turn(500, 50, 3); // unrelated chain

    match fold_two_turns(&running, &bad_next) {
        Err(TurnChainError::ChainBreak { index, .. }) => assert_eq!(index, 1),
        Ok(_) => panic!("a discontinuous pair must not fold"),
        Err(other) => panic!("expected ChainBreak, got {other:?}"),
    }
}

// ============================================================================
// CODEX RE-REVIEW #2 — THE DEEPER MIXED-ROOT FORGERY (binding-leaf vs descriptor-leaf).
//
// THE FIX (codex's ordered segment-accumulator). The separate binding leaf is GONE
// from the soundness path. Every DESCRIPTOR leaf now carries a constant-size ordered
// SEGMENT `[first_old, last_new, count, acc]`, with `first_old`/`last_new` bound
// IN-CIRCUIT to that leaf's descriptor proof's REAL rotated roots; aggregation COMBINES
// the segments (state continuity `L.last_new == R.first_old`, count additivity, ordered
// digest `acc = H(L.acc, R.acc)`) up to the root. The root's exposed segment is thus
// derived from the ACTUAL descriptor leaves it folded — there is no swappable binding
// leaf whose endpoints can disagree with the execution.
//
// The deeper attack codex described (fold A's descriptor leaves but make the root expose
// B's endpoints via a separately-injected B binding leaf) is now INEXPRESSIBLE: the only
// segment table at the root is the descriptor-derived one. The strongest remaining
// forgery is "fold A's REAL leaves, then carry B's claims" — which this test does, and
// which the SEGMENT tooth REJECTS (A's root exposes A's [genesis, final, num_turns,
// digest], so a B-claim mismatches).
//
// This test mirrors the lib-private `prove_chain_core_rotated` + `aggregate_tree` from
// the PUBLIC building blocks (`prove_descriptor_leaf_rotated_with_segment` + the segment
// combine), folds A's REAL descriptor leaves to a root, then runs the REAL verifier
// (`verify_turn_chain_recursive_from_parts`) carrying B's claims and asserts it REJECTS.
// THIS is the close of the mixed-root hole.
// ============================================================================

/// Find the instance index of the `expose_claim` (segment) non-primitive table in a
/// batch proof, in the same order the in-circuit verifier allocates `air_public_targets`
/// (primitive tables first, then non-primitives in order). Re-implemented here because
/// the lib's `expose_claim_instance_index` is `pub(crate)`.
fn expose_claim_idx(
    proof: &p3_circuit_prover::BatchStarkProof<
        dregg_circuit_prove::plonky3_recursion_impl::recursive::DreggRecursionConfig,
    >,
) -> Option<usize> {
    let num_primitive = p3_circuit_prover::batch_stark_prover::NUM_PRIMITIVE_TABLES;
    proof
        .non_primitives
        .iter()
        .position(|e| e.op_type.as_str() == "expose_claim")
        .map(|pos| num_primitive + pos)
}

// The in-circuit segment digest is the lib's `pub seg_poseidon_commit` (a multi-felt
// Poseidon2 sponge); the test calls it DIRECTLY so its combine matches the lib EXACTLY.

/// **CODEX RE-REVIEW #2 — THE MIXED-ROOT FORGERY, REJECTED (the close).**
///
/// Fold history A's GENUINE segment-bearing descriptor leaves into ONE root (the real
/// segment-accumulator fold), then carry B's claims to the verifier. The whole-chain
/// claim for B must FAIL against a root that executed A — the segment tooth fires because
/// A's root exposes A's endpoints, not B's. There is no separate binding leaf to inject
/// B's endpoints into the root.
#[test]
#[ignore = "SLOW: a real segment fold (~minutes); run with --ignored — codex re-review #2 CLOSE"]
// A/B are deliberate emphasis in the test name (root A forging a claim of B's endpoints).
#[allow(non_snake_case)]
fn mixed_root_forgery_executes_A_claims_B() {
    use dregg_circuit_prove::ivc_turn_chain::TurnChainBindingAir;
    use dregg_circuit_prove::ivc_turn_chain::{
        SEG_ANCHOR_WIDTH, SEG_COUNT, SEG_DIGEST_FIRST, SEG_DIGEST_WIDTH, SEG_FIRST_OLD,
        SEG_LAST_NEW, SEG_WIDTH, ir2_leaf_wrap_config, prove_descriptor_leaf_rotated_with_segment,
        seg_poseidon_commit, verify_turn_chain_recursive_from_parts,
    };
    use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
        DreggRecursionConfig, create_recursion_backend, prove_inner_for_air_with_config,
        recursion_vk_fingerprint, verify_inner_for_air_with_config,
    };
    use p3_recursion::{
        BatchOnly, ProveNextLayerParams, RecursionOutput,
        build_and_prove_aggregation_layer_with_expose,
    };

    const D: usize = 4;

    // ----- The two histories (same K=2 transfer shape ⇒ same root VK fingerprint). -----
    // History A: the descriptor/execution leaves we fold (the REAL executed history).
    let (turns_a, _ga, _fa) = make_chain(1000, 0, 7, 2);
    // History B: a DIFFERENT history; its CLAIMS are what the forgery carries (so the
    // whole-chain CLAIM is B while the EXECUTION was A).
    let (turns_b, gb, fb) = make_chain(500, 0, 3, 2);
    let refs_a: Vec<&FinalizedTurn> = turns_a.iter().collect();

    let config: DreggRecursionConfig = ir2_leaf_wrap_config();
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    // ----- B's carried claims. The attacker carries B's chain endpoints + a binding proof
    // (which is no longer a soundness dependency). B's `chain_digest` here is irrelevant to
    // the rejection — the segment tooth fails on B's genesis/final/count already — but we
    // build a real B binding proof so the carried artifact is internally well-formed. -----
    let b_genesis = turns_b[0].old_root();
    let b_mid = turns_b[0].new_root();
    let b_final = turns_b[1].new_root();
    assert_eq!(b_mid, turns_b[1].old_root(), "B chains by construction");
    assert_eq!(b_genesis, gb);
    assert_eq!(b_final, fb);
    let (b_rows, b_pis) = honest_binding_2row(b_genesis, b_mid, b_final);
    let b_binding_inner = prove_inner_for_air_with_config(
        &TurnChainBindingAir,
        to_binding_matrix(&b_rows),
        &b_pis,
        &config,
    );
    verify_inner_for_air_with_config(&TurnChainBindingAir, &b_binding_inner, &b_pis, &config)
        .expect("B's binding leaf proves + self-verifies");
    let b_genesis_root = b_pis[0];
    let b_final_root = b_pis[1];
    let b_num_turns = 2usize;
    // B's carried multi-felt digest (irrelevant to the rejection — the segment tooth fails on
    // B's genesis/final/count first — but well-formed: the single binding digest, zero-padded).
    let mut b_chain_digest = [BabyBear::ZERO; SEG_DIGEST_WIDTH];
    b_chain_digest[0] = b_pis[3];

    // ----- The fold: A's REAL segment-bearing descriptor leaves -> one root. -----
    let mut batch_leaves: Vec<RecursionOutput<DreggRecursionConfig>> = Vec::with_capacity(2);
    for t in &refs_a {
        let leg = &t.participant.rotated;
        let wrapped = prove_descriptor_leaf_rotated_with_segment(
            &leg.descriptor,
            &leg.proof,
            &leg.public_inputs,
            &config,
        )
        .expect("A's rotated descriptor leaf wraps with its segment");
        batch_leaves.push(wrapped);
    }

    // Aggregate the segment leaves to ONE root (mirror the lib `aggregate_tree` combine:
    // continuity + count additivity + ordered-digest fold, re-exposing the parent segment).
    let mut proofs = batch_leaves;
    while proofs.len() > 1 {
        let mut next_level: Vec<RecursionOutput<DreggRecursionConfig>> =
            Vec::with_capacity(proofs.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < proofs.len() {
            let left_idx = expose_claim_idx(&proofs[i].0).expect("left segment");
            let right_idx = expose_claim_idx(&proofs[i + 1].0).expect("right segment");
            let left = proofs[i].into_recursion_input::<BatchOnly>();
            let right = proofs[i + 1].into_recursion_input::<BatchOnly>();
            let expose = move |cb: &mut p3_circuit::CircuitBuilder<_>,
                               left_apt: &[Vec<p3_recursion::Target>],
                               right_apt: &[Vec<p3_recursion::Target>]| {
                let l = left_apt.get(left_idx).expect("left seg present");
                let r = right_apt.get(right_idx).expect("right seg present");
                assert!(l.len() >= SEG_WIDTH && r.len() >= SEG_WIDTH);
                // Continuity via direct connect (mirrors the lib `aggregate_tree`): avoids the
                // `sub`+`assert_zero` backward-add that would clobber the shared `WitnessId(0)`.
                for __k in 0..SEG_ANCHOR_WIDTH {
                    cb.connect(l[SEG_LAST_NEW + __k], r[SEG_FIRST_OLD + __k]);
                }
                let count = cb.add(l[SEG_COUNT], r[SEG_COUNT]);
                let mut acc_inputs = Vec::with_capacity(2 * SEG_DIGEST_WIDTH);
                acc_inputs
                    .extend_from_slice(&l[SEG_DIGEST_FIRST..SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
                acc_inputs
                    .extend_from_slice(&r[SEG_DIGEST_FIRST..SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
                let acc = seg_poseidon_commit(cb, &acc_inputs);
                let mut parent = Vec::with_capacity(SEG_WIDTH);
                parent.extend_from_slice(&l[SEG_FIRST_OLD..SEG_FIRST_OLD + SEG_ANCHOR_WIDTH]);
                parent.extend_from_slice(&r[SEG_LAST_NEW..SEG_LAST_NEW + SEG_ANCHOR_WIDTH]);
                parent.push(count);
                parent.extend_from_slice(&acc);
                cb.expose_as_public_output(&parent);
            };
            let out = build_and_prove_aggregation_layer_with_expose::<
                DreggRecursionConfig,
                BatchOnly,
                BatchOnly,
                _,
                D,
            >(
                &left,
                &right,
                &config,
                &backend,
                &params,
                None,
                Some(&expose),
            )
            .expect("segment aggregation layer");
            next_level.push(out);
            i += 2;
        }
        if i < proofs.len() {
            next_level.push(proofs.pop().unwrap());
        }
        proofs = next_level;
    }
    let a_root: RecursionOutput<DreggRecursionConfig> = proofs.pop().unwrap();

    // The honest anchor: recomputed from A's root (an honest setup over THIS same circuit
    // shape would distribute exactly this fingerprint — the attacker forges only the claim).
    let vk = recursion_vk_fingerprint(&a_root.0);

    // RUN THE REAL VERIFIER carrying B's claims against A's root (A's execution). The
    // segment tooth reads A's root-exposed segment (= A's genesis/final/count/digest) and
    // compares it to the carried B-claim — which MISMATCHES, so verification REJECTS.
    let verdict = verify_turn_chain_recursive_from_parts(
        &a_root.0,
        &b_binding_inner,
        [b_genesis_root; 8],
        [b_final_root; 8],
        b_chain_digest,
        b_num_turns,
        &vk,
    );

    eprintln!("[codex-#2 mixed-root] verdict = {verdict:?}  (is_err = CLOSED; is_ok = STILL OPEN)");

    // THE CLOSE: a whole-chain claim for B against a root that executed A is REJECTED. The
    // ordered segment-accumulator binds the root-exposed [genesis, final, num_turns,
    // digest] to the REAL descriptor leaves, so the B-claim cannot ride an A-execution.
    assert!(
        verdict.is_err(),
        "MIXED-ROOT HOLE CLOSED (codex re-review #2): a root that folded A's descriptor \
         leaves carrying a B whole-chain claim MUST be REJECTED by the segment tooth — A's \
         root exposes A's endpoints, not B's. got: {verdict:?}"
    );
}

/// **FORK FOLLOW-UP (a) — LEAF-CIRCUIT IDENTITY PINNED IN-BAND (the close).**
///
/// [`aggregate_tree`](dregg_circuit_prove::ivc_turn_chain) now folds every child of the K-fold
/// tree through `into_recursion_input_pinned`, baking each child's OWN preprocessed commitment
/// (its VK-identity core — the Merkle cap binding its static op-list) as a CONSTANT the parent
/// aggregation circuit `connect`s its child-commitment targets to. This test walks that exact
/// descriptor-leaf segment-combine path and witnesses BOTH sides:
///   1. the honest pin (each child pinned to its own genuine commitment) PROVES;
///   2. a FORGED leaf-identity — the left child pinned to a FOREIGN commitment (one field element
///      flipped, i.e. a different-circuit op-list) — is refused IN-BAND (the parent aggregation
///      circuit is UNSAT), NOT via a same-shape argument.
///
/// Previously the child's preprocessed commitment rode as unconstrained runtime targets the host
/// never checked, so a from-scratch prover could fold a proof of a DIFFERENT circuit. The pin
/// closes that: the constant lives in every node's op-list up to the root, so the root VK pin
/// (verify tooth 1) transitively certifies the whole tree's leaf identity. (The sibling
/// `accumulator::pinned_fold_rejects_foreign_vk_in_circuit` exercises the same fork lever on the
/// ONLINE fixed-point path; this is the K-fold light-client path.)
#[test]
#[ignore = "SLOW: a real segment fold (~minutes); run with --ignored — fork follow-up (a) close"]
fn pinned_leaf_identity_rejects_foreign_child_in_band() {
    use dregg_circuit_prove::ivc_turn_chain::{
        SEG_ANCHOR_WIDTH, SEG_COUNT, SEG_DIGEST_FIRST, SEG_DIGEST_WIDTH, SEG_FIRST_OLD,
        SEG_LAST_NEW, SEG_WIDTH, ir2_leaf_wrap_config, prove_descriptor_leaf_rotated_with_segment,
        seg_poseidon_commit,
    };
    use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
        DreggRecursionConfig, create_recursion_backend,
    };
    use p3_baby_bear::BabyBear as P3BabyBear;
    use p3_field::PrimeCharacteristicRing;
    use p3_recursion::{
        BatchOnly, ProveNextLayerParams, RecursionOutput,
        build_and_prove_aggregation_layer_with_expose,
    };
    use p3_symmetric::MerkleCap;

    const D: usize = 4;

    // Two genuine segment-bearing descriptor leaves of one continuous K=2 chain.
    let (turns, _g, _f) = make_chain(1000, 0, 7, 2);
    let config: DreggRecursionConfig = ir2_leaf_wrap_config();
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let mut leaves: Vec<RecursionOutput<DreggRecursionConfig>> = Vec::with_capacity(2);
    for t in &turns {
        let leg = &t.participant.rotated;
        leaves.push(
            prove_descriptor_leaf_rotated_with_segment(
                &leg.descriptor,
                &leg.proof,
                &leg.public_inputs,
                &config,
            )
            .expect("rotated descriptor leaf wraps with its segment"),
        );
    }

    let left_idx = expose_claim_idx(&leaves[0].0).expect("left segment");
    let right_idx = expose_claim_idx(&leaves[1].0).expect("right segment");

    // The children's GENUINE preprocessed commitments (their VK-identity cores).
    let left_commit = leaves[0]
        .running_preprocessed_commit()
        .expect("a recursion leaf-wrap has a preprocessed commitment");
    let right_commit = leaves[1]
        .running_preprocessed_commit()
        .expect("a recursion leaf-wrap has a preprocessed commitment");

    // (1) HONEST pin: each child pinned to its OWN commitment ⇒ the in-circuit connect +
    //     preprocessed-trace FRI check is satisfiable, the layer PROVES (exactly the combine
    //     `aggregate_tree` walks for the light client).
    {
        let expose = move |cb: &mut p3_circuit::CircuitBuilder<_>,
                           left_apt: &[Vec<p3_recursion::Target>],
                           right_apt: &[Vec<p3_recursion::Target>]| {
            let l = left_apt.get(left_idx).expect("left seg present");
            let r = right_apt.get(right_idx).expect("right seg present");
            assert!(l.len() >= SEG_WIDTH && r.len() >= SEG_WIDTH);
            for __k in 0..SEG_ANCHOR_WIDTH {
                cb.connect(l[SEG_LAST_NEW + __k], r[SEG_FIRST_OLD + __k]);
            }
            let count = cb.add(l[SEG_COUNT], r[SEG_COUNT]);
            let mut acc_inputs = Vec::with_capacity(2 * SEG_DIGEST_WIDTH);
            acc_inputs.extend_from_slice(&l[SEG_DIGEST_FIRST..SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
            acc_inputs.extend_from_slice(&r[SEG_DIGEST_FIRST..SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
            let acc = seg_poseidon_commit(cb, &acc_inputs);
            let mut parent = Vec::with_capacity(SEG_WIDTH);
            parent.extend_from_slice(&l[SEG_FIRST_OLD..SEG_FIRST_OLD + SEG_ANCHOR_WIDTH]);
            parent.extend_from_slice(&r[SEG_LAST_NEW..SEG_LAST_NEW + SEG_ANCHOR_WIDTH]);
            parent.push(count);
            parent.extend_from_slice(&acc);
            cb.expose_as_public_output(&parent);
        };
        let left = leaves[0].into_recursion_input_pinned::<BatchOnly>(left_commit.clone());
        let right = leaves[1].into_recursion_input_pinned::<BatchOnly>(right_commit.clone());
        build_and_prove_aggregation_layer_with_expose::<
            DreggRecursionConfig,
            BatchOnly,
            BatchOnly,
            _,
            D,
        >(
            &left,
            &right,
            &config,
            &backend,
            &params,
            None,
            Some(&expose),
        )
        .expect("a pinned segment fold against the GENUINE child VK identities must prove");
    }

    // (2) FORGED leaf-identity: pin the LEFT child to a FOREIGN commitment (one field element
    //     flipped — a different-circuit op-list). The left child's real preprocessed commitment
    //     no longer matches the pinned constant, so the parent aggregation circuit is UNSAT — the
    //     foreign leaf-circuit identity is refused IN-BAND, not via a same-shape argument.
    let mut roots = left_commit.into_roots();
    assert!(!roots.is_empty(), "the cap has at least one root");
    roots[0][0] += P3BabyBear::ONE; // a different-circuit preprocessed commitment
    let foreign_left = MerkleCap::new(roots);
    {
        let expose = move |cb: &mut p3_circuit::CircuitBuilder<_>,
                           left_apt: &[Vec<p3_recursion::Target>],
                           right_apt: &[Vec<p3_recursion::Target>]| {
            let l = left_apt.get(left_idx).expect("left seg present");
            let r = right_apt.get(right_idx).expect("right seg present");
            assert!(l.len() >= SEG_WIDTH && r.len() >= SEG_WIDTH);
            for __k in 0..SEG_ANCHOR_WIDTH {
                cb.connect(l[SEG_LAST_NEW + __k], r[SEG_FIRST_OLD + __k]);
            }
            let count = cb.add(l[SEG_COUNT], r[SEG_COUNT]);
            let mut acc_inputs = Vec::with_capacity(2 * SEG_DIGEST_WIDTH);
            acc_inputs.extend_from_slice(&l[SEG_DIGEST_FIRST..SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
            acc_inputs.extend_from_slice(&r[SEG_DIGEST_FIRST..SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
            let acc = seg_poseidon_commit(cb, &acc_inputs);
            let mut parent = Vec::with_capacity(SEG_WIDTH);
            parent.extend_from_slice(&l[SEG_FIRST_OLD..SEG_FIRST_OLD + SEG_ANCHOR_WIDTH]);
            parent.extend_from_slice(&r[SEG_LAST_NEW..SEG_LAST_NEW + SEG_ANCHOR_WIDTH]);
            parent.push(count);
            parent.extend_from_slice(&acc);
            cb.expose_as_public_output(&parent);
        };
        let left = leaves[0].into_recursion_input_pinned::<BatchOnly>(foreign_left);
        let right = leaves[1].into_recursion_input_pinned::<BatchOnly>(right_commit);
        let res = build_and_prove_aggregation_layer_with_expose::<
            DreggRecursionConfig,
            BatchOnly,
            BatchOnly,
            _,
            D,
        >(
            &left,
            &right,
            &config,
            &backend,
            &params,
            None,
            Some(&expose),
        );
        assert!(
            res.is_err(),
            "FORK FOLLOW-UP (a) CLOSED: a child pinned to a FOREIGN preprocessed commitment \
             (a different-circuit leaf identity) MUST be refused in-band (UNSAT), got Ok"
        );
    }
}

// SKIPPED tooth (vs the deleted in-lib module): `broken_order_unsat_in_circuit`,
// `ungated_prover_with_stub_leaf_cannot_produce_a_root`, and
// `recursive_layer_rejects_forged_leaf_public_inputs` are NOT re-expressed here.
// They depended on lib-internal items that are NOT publicly exported for an
// integration test — `generate_chain_trace_unchecked` / `TurnChainBindingAir` /
// `trace_to_matrix` / `verify_inner_for_air` (the in-circuit binding-trace tooth), and
// the v1 `prove_descriptor_leaf` + `RecursionInput::UniStark` + `EffectVmDescriptorAir`
// wrap (which the rotated cutover DELETED — the v1 leaf no longer exists). The
// surviving forged-PI tooth (`ungated_prover_with_forged_post_commit_cannot_produce_a_root`,
// above) carries the SAME load-bearing assertion — a forged commitment has no
// satisfying in-circuit leaf — through the rotated path; the in-circuit-wrap variant is
// covered by the lib's own `rotation_batchstark_leaf_smoke.rs`.
