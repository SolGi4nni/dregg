//! # `whole_history_demo` — the aggregate-then-light-verify demo (real output).
//!
//! This is the working demonstration the GOLD-tier history-compression story claims: take a chain of
//! several REAL finalized turns (each a genuine Lean-descriptor EffectVM proof with Poseidon2 state
//! commitments, whose full constraint set is re-proven and verified IN-CIRCUIT as the fold's leaf),
//! fold them — via the existing prover, read-only — into ONE constant-size aggregate
//! (`WholeChainProof`), and then have the light client verify the WHOLE history from just that
//! aggregate, re-witnessing NOTHING: no re-execution of any turn, no re-hashing of any state, no walk
//! of the blocklace.
//!
//! It is the executable embodiment of the Lean theorem
//! `Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history` — and the three-leg
//! `FinalizedLightClient.light_client_accepts_finalized_history`.
//!
//! Run: `cargo run -p dregg-lightclient --bin whole_history_demo`.

#![cfg(feature = "prover")]
#![forbid(unsafe_code)]

use std::time::Instant;

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::FinalizedTurn;
use dregg_circuit_prove::joint_turn_aggregation::{DescriptorParticipant, RotatedParticipantLeg};
use dregg_turn::rotation_witness::mint_rotated_participant_leg;

use dregg_lightclient::{
    FinalityCert, SignedVote, finality_signing_message, fold_and_attest, verify_finalized_history,
    verify_history,
};
use ed25519_dalek::{Signer, SigningKey};

/// A genuine signed ratification vote for validator `i` over `(root, participant_count)` — the demo's
/// validators sign the finalized root, so the light client's signature-bound quorum check (the
/// `CertValid` binding leg) accepts them.
fn demo_signed_vote(
    i: u8,
    root: dregg_circuit::field::BabyBear,
    participant_count: usize,
) -> SignedVote {
    let mut seed = [0u8; 32];
    seed[0] = i;
    seed[31] = 0xA5;
    let sk = SigningKey::from_bytes(&seed);
    let msg = finality_signing_message(root, participant_count);
    let sig = sk.sign(&msg);
    // The POST-QUANTUM half: an ML-DSA-65 signature over the SAME message, bound to the shared hybrid
    // context, so the light client's hybrid quorum check (BOTH halves) accepts the demo's votes.
    let mut xi = [0u8; 32];
    xi[0] = i;
    xi[31] = 0xD5;
    let ml_key = dregg_pq::MlDsaKey::from_ed25519_seed(&xi);
    let pq_signature = ml_key
        .try_sign(dregg_lightclient::HYBRID_PQ_CTX, &msg)
        .expect("ml-dsa-65 sign cannot fail on a valid key");
    SignedVote {
        validator: sk.verifying_key().to_bytes(),
        signature: sig.to_bytes(),
        ml_dsa_pubkey: ml_key.public_bytes(),
        pq_signature,
    }
}

/// The TRUSTED committee for a demo group of `n` validators — the verifying-key bytes of validators
/// `0..n`, exactly the genesis/epoch-distributed set the light client holds. The committee-anchored
/// `verify_finalized_history` counts ONLY votes by these keys (red-team LC-2).
fn demo_committee(n: u8) -> Vec<[u8; 32]> {
    (0..n)
        .map(|i| {
            let mut seed = [0u8; 32];
            seed[0] = i;
            seed[31] = 0xA5;
            SigningKey::from_bytes(&seed).verifying_key().to_bytes()
        })
        .collect()
}

/// The TRUSTED, genesis-ENROLLED ML-DSA-65 roster for the demo's validators `0..n`,
/// aligned index-for-index with [`demo_committee`] — the post-quantum anchor
/// `verify_finalized_history` pins each counted vote's carried ML-DSA key to.
fn demo_ml_dsa_committee(n: u8) -> Vec<Vec<u8>> {
    (0..n)
        .map(|i| {
            let mut xi = [0u8; 32];
            xi[0] = i;
            xi[31] = 0xD5;
            dregg_pq::MlDsaKey::from_ed25519_seed(&xi).public_bytes()
        })
        .collect()
}

/// OPEN permissions so the rotated producer-witness path admits the actor cell without auth gating
/// (mirrors `circuit/tests/rotation_batchstark_leaf_smoke.rs`).
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

/// The transfer actor cell at `(balance, nonce)` with open permissions — the before/after `Cell`
/// the rotated mint runs `rotation_witness::produce` over.
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

/// Build ONE real finalized turn on the PRODUCTION descriptor path. **Bucket-F (PATH-PRESERVE
/// Phase 5a):** the finalized turn carries the MANDATORY ROTATED leg — the rotated multi-table
/// `Ir2BatchProof` minted by `mint_rotated_participant_leg` from the live producer witnesses over
/// the before/after actor cells (the v1 `EffectVmP3Proof` leg is dropped). Returns the turn + its
/// REAL ROTATED `(old_root, new_root)` Poseidon2 state commitments (PI 34/35 — the rotated
/// before/after `state_commit`, bound by the descriptor's hash sites, not fabricated).
fn make_turn(balance: u64, nonce: u32, amount: u64) -> (FinalizedTurn, BabyBear, BabyBear) {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    // The rotated transfer DEBIT keeps the nonce and decreases the balance by `amount`.
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
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
    // H0 DEPLOYED-WIDE: the deployed leg is WIDE-anchored — the single-felt rotated roots (PI 42/43)
    // are RETIRED to zero; the chain genesis/final/continuity bind the GENUINE 8-felt (~124-bit) wide
    // anchors. Report their HEAD felt (lane 0) as the scalar root the demo prints / chains on.
    let old_root = leg.wide_old_root8().expect("deployed leg is wide-anchored")[0];
    let new_root = leg.wide_new_root8().expect("deployed leg is wide-anchored")[0];
    (
        FinalizedTurn::new(DescriptorParticipant::rotated(leg)),
        old_root,
        new_root,
    )
}

/// A continuous chain of `k` REAL finalized turns: each turn debits `step` and the next turn starts
/// from the post-state, so turn i's real `new_root` IS turn i+1's real `old_root` (the temporal
/// tooth holds by construction). The rotated trace welds balance/nonce from the v1 sub-trace, which
/// BUMPS the nonce by 1 per Transfer row — so turn i's after-state `(balance - step, nonce + 1)` is
/// the next turn's before-state, and both balance and nonce advance per turn. Returns the turns +
/// genesis/final roots.
fn make_chain(
    start_balance: u64,
    start_nonce: u32,
    step: u64,
    k: usize,
) -> (Vec<FinalizedTurn>, BabyBear, BabyBear) {
    let mut turns = Vec::with_capacity(k);
    let mut balance = start_balance;
    // The rotated trace welds balance/nonce from the v1 sub-trace, which BUMPS the nonce by 1 per
    // Transfer row — turn i's after-state is `(balance - step, nonce + 1)`. Advance BOTH balance
    // and nonce per turn so the rotated state-commit roots link (`old_root[i+1] == new_root[i]`).
    let mut genesis = BabyBear::ZERO;
    let mut final_root = BabyBear::ZERO;
    for i in 0..k {
        // turn i's nonce is start_nonce + i (the v1 sub-trace bumps the nonce by 1 per Transfer row).
        let nonce = start_nonce + i as u32;
        let (turn, old_root, new_root) = make_turn(balance, nonce, step);
        if i == 0 {
            genesis = old_root;
        } else {
            assert_eq!(
                old_root, final_root,
                "real chain: turn {i} continues the previous"
            );
        }
        final_root = new_root;
        turns.push(turn);
        balance -= step;
    }
    (turns, genesis, final_root)
}

fn rule(title: &str) {
    println!("\n────────────────────────────────────────────────────────────────");
    println!(" {title}");
    println!("────────────────────────────────────────────────────────────────");
}

fn main() {
    println!("dregg whole-history compression demo");
    println!("  GOLD tier: N turns of history compressed to ONE constant-size aggregate,");
    println!("  light-verified in time independent of N — re-witnessing nothing.\n");

    // --- 1. A real chain of finalized turns -----------------------------------------------------
    const K: usize = 3;
    rule(&format!(
        "1. EXECUTE — {K} real finalized turns (genuine Lean-descriptor EffectVM proofs)"
    ));
    let build_t0 = Instant::now();
    let (turns, genesis, final_root) = make_chain(1_000, 0, 7, K);
    println!(
        "  produced {} finalized turns in {:?}",
        turns.len(),
        build_t0.elapsed()
    );
    println!("  genesis state root : {}", genesis.as_u32());
    print!("  per-turn root chain: {}", genesis.as_u32());
    for t in &turns {
        // H0 DEPLOYED-WIDE: the genuine 8-felt wide AFTER-anchor (head lane); the single felt is 0.
        print!(
            " -> {}",
            t.participant.rotated.wide_new_root8().expect("wide")[0].as_u32()
        );
    }
    println!();
    println!("  final state root   : {}", final_root.as_u32());
    println!("  (each turn's new_root IS the next turn's old_root — the temporal tooth)");

    // --- 2. Fold to ONE constant-size aggregate (the existing prover, read-only) -----------------
    rule("2. PROVE/FOLD — recurse the whole chain into ONE succinct aggregate");
    let fold_t0 = Instant::now();
    let (agg, _att) = fold_and_attest(&turns).expect("a continuous chain folds + light-verifies");
    let fold_elapsed = fold_t0.elapsed();
    println!("  WholeChainProof folded in {fold_elapsed:?} (the EXPENSIVE step — done ONCE)");
    println!("  aggregate is ONE root recursion proof + 4 public commitments:");
    let lanes =
        |a: &[dregg_circuit::field::BabyBear]| a.iter().map(|d| d.as_u32()).collect::<Vec<_>>();
    println!(
        "    genesis_root : {:?} (8-felt faithful anchor)",
        lanes(&agg.genesis_root)
    );
    println!(
        "    final_root   : {:?} (8-felt faithful anchor)",
        lanes(&agg.final_root)
    );
    println!(
        "    chain_digest : {:?}",
        agg.chain_digest
            .iter()
            .map(|d| d.as_u32())
            .collect::<Vec<_>>()
    );
    println!("    num_turns    : {}", agg.num_turns);

    // --- 3. The light client verifies the WHOLE history from the aggregate alone -----------------
    rule("3. LIGHT-VERIFY — trust ALL the history from the aggregate (re-witnessing NOTHING)");
    // The trust anchor: the honest setup extracts the root circuit's verifier-key fingerprint ONCE
    // from its own fold and distributes it with the client (like any SNARK VK). The verifier then
    // refuses any root whose recomputed fingerprint differs — the from-scratch-prover tooth.
    let vk_anchor = agg.root_vk_fingerprint();
    let v_t0 = Instant::now();
    let attested =
        verify_history(&agg, &vk_anchor).expect("the light client verifies the aggregate");
    let v_elapsed = v_t0.elapsed();
    println!(
        "  verify_history ran the VK pin + binding attestation + ONE recursive-STARK check in {v_elapsed:?}"
    );
    println!("  the light client re-executed 0 turns, re-hashed 0 states, walked 0 of the lace.");
    println!("  it now holds AttestedHistory — meaning, PROVED (under the named engine-soundness");
    println!(
        "  hypotheses) by Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history:"
    );
    println!(
        "    * all {} turns executed correctly per the verified executor,",
        attested.num_turns
    );
    println!("    * the chain is correctly ordered (no reorder / drop / insert),");
    println!(
        "    * final_root {} is the genuine fold of the whole history (head felt; full 8-felt anchor above).",
        attested.final_root[0].as_u32()
    );
    assert_eq!(attested.num_turns, K);
    assert_eq!(attested.genesis_root[0], genesis);
    assert_eq!(attested.final_root[0], final_root);

    // --- 4. O(1): verify cost is independent of history length -----------------------------------
    rule("4. O(1) — verification cost is INDEPENDENT of history length N");
    let (turns2, _g2, _f2) = make_chain(2_000, 0, 3, 2); // a SHORTER chain (N=2)
    let (agg2, _a2) = fold_and_attest(&turns2).expect("the N=2 chain folds");
    let vk_anchor2 = agg2.root_vk_fingerprint(); // the anchor is per accepted window shape
    let v2_t0 = Instant::now();
    verify_history(&agg2, &vk_anchor2).expect("N=2 aggregate verifies");
    let v2_elapsed = v2_t0.elapsed();
    println!("  history of N={K} turns : light-verify took {v_elapsed:?}");
    println!("  history of N=2 turns : light-verify took {v2_elapsed:?}");
    println!("  both check ONE constant-size root proof — the verifier never sees N turns.");
    println!(
        "  (this is the compression property: O(1) verify in history length, soundness kept.)"
    );

    // --- 5. The THREE tamper teeth — a forged / dropped / reordered history is REJECTED ----------
    // This is `lightclient_unfoolable` made REAL over arbitrary histories: an adversary who FORGES a
    // turn's outcome, DROPS a turn, or REORDERS turns cannot obtain a whole-history attestation. Each
    // forgery is refused BEFORE the expensive fold — by the leaf tooth (host re-verifies every turn's
    // rotated proof) or the temporal tooth (`new_root[i] == old_root[i+1]`), so the teeth are cheap.
    rule("5. THE TAMPER TEETH — forged / dropped / reordered histories are REJECTED");

    // (A) FORGED TURN — a malicious prover LIES about a turn's resulting state. Forge the LAST turn's
    //     claimed post-state root (rotated NEW commit, PI 35): the execution witness is honest, only
    //     the CLAIM is forged. Because it is the last turn there is no successor to break continuity —
    //     ONLY the leaf tooth (host re-verifies the rotated proof against its claimed PI) can catch
    //     it. The forged PI no longer satisfies the rotated descriptor, so host admission REJECTS.
    let (mut forged_chain, _gf, real_final) = make_chain(1_000, 0, 7, 3);
    let last = forged_chain.len() - 1;
    let DescriptorParticipant { rotated } = forged_chain.remove(last).participant;
    let RotatedParticipantLeg {
        proof,
        descriptor,
        mut public_inputs,
        carrier_witness,
    } = rotated;
    // H0 DEPLOYED-WIDE: forge the GENUINE 8-felt wide AFTER-commit (PI tail `[n-8 .. n)`), not the
    // RETIRED single-felt rotated NEW-commit (PI 43, now zero / unbound). The proof's bound wide
    // carrier disagrees with the tampered PI ⇒ the leaf re-verify is UNSAT.
    let pi_wide_new = public_inputs.len() - 8;
    let lie = public_inputs[pi_wide_new] + BabyBear::ONE;
    public_inputs[pi_wide_new] = lie; // claim a post-state the turn never produced
    forged_chain.push(FinalizedTurn::new(DescriptorParticipant::rotated(
        RotatedParticipantLeg {
            proof,
            descriptor,
            public_inputs,
            carrier_witness,
        },
    )));
    assert_ne!(lie, real_final, "the forged final root must differ");
    match fold_and_attest(&forged_chain) {
        Ok(_) => panic!("a forged turn outcome must NOT yield a whole-history attestation"),
        Err(e) => println!("  (A) FORGED turn (lied post-state) REFUSED: {e}"),
    }

    // (B) DROPPED TURN — an adversary OMITS a turn from the middle of the history (hoping the verifier
    //     never notices the gap). Remove turn 1 from a real 3-turn chain: turn 2's old_root no longer
    //     equals turn 0's new_root, so the temporal tooth breaks → ChainBreak. REJECTED.
    let (mut dropped_chain, _gd, _fd) = make_chain(1_000, 0, 7, 3);
    // H0 DEPLOYED-WIDE: continuity binds the genuine 8-felt wide anchors (head lane shown).
    let prev_new = dropped_chain[0]
        .participant
        .rotated
        .wide_new_root8()
        .expect("wide")[0];
    let next_old = dropped_chain[2]
        .participant
        .rotated
        .wide_old_root8()
        .expect("wide")[0];
    assert_ne!(
        next_old, prev_new,
        "after the drop the surviving turns must NOT be continuous (that is the gap)"
    );
    dropped_chain.remove(1); // omit the middle turn
    match fold_and_attest(&dropped_chain) {
        Ok(_) => panic!("a dropped turn must NOT yield a whole-history attestation"),
        Err(e) => println!("  (B) DROPPED turn (omitted middle) REFUSED: {e}"),
    }

    // (C) REORDERED TURN — an adversary PERMUTES the finalized order. Swap turns 1 and 2 of a real
    //     3-turn chain: the turn now at position 1 consumes turn 2's old_root, which is not turn 0's
    //     new_root, so continuity breaks → ChainBreak. REJECTED.
    let (mut reordered_chain, _gr, _fr) = make_chain(1_000, 0, 7, 3);
    reordered_chain.swap(1, 2);
    match fold_and_attest(&reordered_chain) {
        Ok(_) => panic!("a reordered history must NOT yield a whole-history attestation"),
        Err(e) => println!("  (C) REORDERED turns (swapped 1<->2) REFUSED: {e}"),
    }
    println!(
        "  (mirrors Lean tampered_aggregate_cannot_bind / leaf_pairing_defeats_swap: forged,\n   dropped, and reordered histories each have NO valid binding — the light client is unfoolable)"
    );

    // --- 6. The THIRD leg — finality (a correct history must also be FINALIZED) ------------------
    rule("6. FINALITY LEG — the trusted root was QUORUM-finalized (three-leg client)");
    // n=4 participants ⇒ supermajority threshold 2*4/3 + 1 = 3. A genuine 3-of-4 quorum.
    let cert = FinalityCert {
        votes: (0..3u8)
            .map(|i| demo_signed_vote(i, final_root, 4))
            .collect(),
        participant_count: 4,
        finalized_root: final_root,
    };
    // The client also holds its trusted GENESIS anchor (like the VK + committee anchors) and pins the
    // aggregate's genesis to it — the exact dual of the final-root seam, closing the whole-history
    // prefix gap (TIER3 LANE 2c): a prover that folds from a fabricated/midpoint genesis is refused.
    let finalized = verify_finalized_history(
        &agg,
        &vk_anchor,
        final_root,
        &cert,
        &demo_committee(4),
        &demo_ml_dsa_committee(4),
        Some(agg.genesis_root),
    )
    .expect("aggregate + root-seam + genesis-anchor + 3-of-4 quorum cert all hold");
    println!(
        "  four legs hold: aggregate verifies, root seam binds, GENESIS anchored, {} of 4 distinct signers ratify.",
        finalized.quorum_signers
    );
    println!(
        "  FinalizedAttestation: the trusted root {} is the genuine fold of {} correct turns",
        finalized.finalized_root.as_u32(),
        finalized.history.num_turns
    );
    println!(
        "  AND was finalized by a BFT supermajority — re-witnessing nothing, never seeing the lace."
    );

    // Sub-quorum is refused (the fork-attack defense).
    let weak = FinalityCert {
        votes: (0..2u8)
            .map(|i| demo_signed_vote(i, final_root, 4))
            .collect(), // 2 of 4 — below the threshold of 3
        participant_count: 4,
        finalized_root: final_root,
    };
    match verify_finalized_history(
        &agg,
        &vk_anchor,
        final_root,
        &weak,
        &demo_committee(4),
        &demo_ml_dsa_committee(4),
        None,
    ) {
        Ok(_) => panic!("a sub-quorum cert must be refused"),
        Err(e) => println!("  sub-quorum finality cert REFUSED: {e}"),
    }

    // A fabricated genesis is refused — the prefix-hiding forge cannot pass the genesis anchor.
    let mut fabricated_genesis = agg.genesis_root;
    fabricated_genesis[0] += BabyBear::ONE;
    match verify_finalized_history(
        &agg,
        &vk_anchor,
        final_root,
        &cert,
        &demo_committee(4),
        &demo_ml_dsa_committee(4),
        Some(fabricated_genesis),
    ) {
        Ok(_) => panic!("a fabricated genesis anchor must be refused"),
        Err(e) => println!("  fabricated-genesis (hidden-prefix) history REFUSED: {e}"),
    }

    // A wrong trust anchor is refused too — the VK pin (item: a root proof of a DIFFERENT circuit
    // can no longer be laundered through the chain verifier).
    let mut wrong_anchor = vk_anchor;
    wrong_anchor.0[0] ^= 0xFF;
    match verify_history(&agg, &wrong_anchor) {
        Ok(_) => panic!("a mismatched VK anchor must be refused"),
        Err(e) => println!("  mismatched VK anchor REFUSED: {e}"),
    }

    rule("DONE — N turns of history, trusted from ONE constant-size aggregate");
    println!("  The light client trusted {K} turns of finalized history without re-executing any.");
    println!("  Proofs are additive attestation: verifying the succinct aggregate IS the trust.");
}
