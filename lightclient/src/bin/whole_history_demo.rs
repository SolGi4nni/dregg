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
use dregg_circuit::ivc_turn_chain::FinalizedTurn;
use dregg_circuit::joint_turn_aggregation::DescriptorParticipant;
use dregg_turn::rotation_witness::mint_rotated_participant_leg;

use dregg_lightclient::{FinalityCert, fold_and_attest, verify_finalized_history, verify_history};

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
        print!(" -> {}", t.new_root().as_u32());
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
    println!("    genesis_root : {}", agg.genesis_root.as_u32());
    println!("    final_root   : {}", agg.final_root.as_u32());
    println!("    chain_digest : {}", agg.chain_digest.as_u32());
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
        "    * final_root {} is the genuine fold of the whole history.",
        attested.final_root.as_u32()
    );
    assert_eq!(attested.num_turns, K);
    assert_eq!(attested.genesis_root, genesis);
    assert_eq!(attested.final_root, final_root);

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

    // --- 5. The rejection tooth — a broken order is REFUSED --------------------------------------
    rule("5. ANTI-GHOST TOOTH — a tampered / reordered history is REJECTED");
    let (mut tampered, _gt, _ft) = make_chain(1_000, 0, 7, 3);
    // Splice an out-of-sequence turn from an UNRELATED chain into the middle — its real old_root does
    // not continue the previous turn's new_root, so the temporal tooth breaks.
    let (foreign, foreign_old, _fn) = make_turn(500, 50, 3);
    let prev_new = tampered[0].new_root();
    assert_ne!(
        foreign_old, prev_new,
        "the foreign turn must NOT continue the chain"
    );
    tampered[1] = foreign;
    match fold_and_attest(&tampered) {
        Ok(_) => panic!("a broken order must NOT yield a whole-history attestation"),
        Err(e) => println!("  reordered chain REFUSED: {e}"),
    }
    println!(
        "  (mirrors Lean tampered_aggregate_cannot_bind: a reordered chain has no valid binding)"
    );

    // --- 6. The THIRD leg — finality (a correct history must also be FINALIZED) ------------------
    rule("6. FINALITY LEG — the trusted root was QUORUM-finalized (three-leg client)");
    // n=4 participants ⇒ supermajority threshold 2*4/3 + 1 = 3. A genuine 3-of-4 quorum.
    let signers: Vec<[u8; 32]> = (0..3u8)
        .map(|i| {
            let mut id = [0u8; 32];
            id[0] = i;
            id
        })
        .collect();
    let cert = FinalityCert {
        signers,
        participant_count: 4,
        finalized_root: final_root,
    };
    let finalized = verify_finalized_history(&agg, &vk_anchor, final_root, &cert)
        .expect("aggregate + root-seam + 3-of-4 quorum cert all hold");
    println!(
        "  three legs hold: aggregate verifies, root seam binds, {} of 4 distinct signers ratify.",
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
        signers: vec![[1u8; 32], [2u8; 32]], // 2 of 4 — below the threshold of 3
        participant_count: 4,
        finalized_root: final_root,
    };
    match verify_finalized_history(&agg, &vk_anchor, final_root, &weak) {
        Ok(_) => panic!("a sub-quorum cert must be refused"),
        Err(e) => println!("  sub-quorum finality cert REFUSED: {e}"),
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
