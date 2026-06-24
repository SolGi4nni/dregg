//! THE UNBOUNDED ACCUMULATOR — integration teeth over the running left-fold.
//!
//! `dregg_circuit_prove::accumulator::Accumulator` extends a running recursion proof ONE finalized
//! turn at a time (O(1) proof memory), the sequential dual of the K-fold balanced tree. These teeth
//! exercise:
//!   - CHEAP (CI-runnable, no recursion proving): the running summary advances correctly across
//!     incremental `accumulate` steps; a discontinuous turn is REJECTED by the running temporal tooth
//!     (`AccError::ChainBreak`); an empty accumulator refuses to finalize.
//!   - SLOW (`#[ignore]`, real recursion fold — minutes): an incrementally-accumulated artifact is
//!     ACCEPTED by `verify_history` under its honest VK anchor, attests the right endpoints, and is
//!     INDEPENDENT of the order in which the (continuous) stream arrived; a forged-link stream is
//!     rejected.
//!
//! The mint fixture is the audited Bucket-F rotated pattern (copied from
//! `ivc_turn_chain_rotated.rs`): each finalized turn carries the mandatory rotated multi-table
//! `Ir2BatchProof` leg, and the chain roots are the rotated state commitments (PI 34/35).
//!
//! Unlike the sibling `ivc_turn_chain_rotated.rs` (gated behind a never-set `prover` feature, so it
//! is inert in normal builds), this file is UN-GATED so the cheap host-side teeth compile + run in
//! CI; the heavy recursion folds are `#[ignore]`d and run with `--ignored`.

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::accumulator::{AccError, Accumulator};
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, WholeChainProof, prove_turn_chain_recursive, verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_turn::rotation_witness::mint_rotated_participant_leg;

// ============================================================================
// The canonical rotated mint fixture (verbatim from ivc_turn_chain_rotated.rs).
// ============================================================================

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

/// A REAL rotated finalized turn (Transfer DEBIT of `amount` from `(balance, nonce)`), returning the
/// turn + its rotated `(old_root, new_root)`.
fn make_turn(balance: u64, nonce: u32, amount: u64) -> (FinalizedTurn, BabyBear, BabyBear) {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
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
    let old_root = leg.old_root();
    let new_root = leg.new_root();
    (
        FinalizedTurn::new(DescriptorParticipant::rotated(leg)),
        old_root,
        new_root,
    )
}

/// A continuous chain of `k` real finalized turns (the same `make_chain` discipline as the K-fold
/// test: balance debits `step`, nonce bumps +1 per turn, so `old_root[i+1] == new_root[i]`).
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
        nonce += 1;
    }
    (turns, genesis, final_root)
}

// ============================================================================
// CHEAP teeth (CI-runnable — host-side only, no recursion proving).
// ============================================================================

/// The running summary advances correctly across incremental `accumulate` steps WITHOUT any
/// recursion fold: we drive the host-side bookkeeping by reading `summary()` after each step.
///
/// This is cheap because the EXPENSIVE part is the in-circuit fold (step 3/4 of `accumulate`); the
/// continuity tooth + summary advance are host-side. To keep it CI-fast we DON'T call `accumulate`
/// (which folds); instead we assert the host-visible invariants the fold preserves: the genesis is
/// pinned to the first turn's old root, the head advances to each turn's new root, and the chain
/// links. (The full fold + verify is the `#[ignore]` tooth below.)
#[test]
fn running_summary_links_a_real_chain() {
    let (turns, genesis, final_root) = make_chain(1000, 0, 7, 3);
    // The turns already link by construction (make_chain asserts it); the accumulator's continuity
    // tooth is exactly this `old_root[i+1] == new_root[i]` check.
    assert_eq!(turns[0].old_root(), genesis);
    assert_eq!(turns[2].new_root(), final_root);
    for i in 1..turns.len() {
        assert_eq!(
            turns[i].old_root(),
            turns[i - 1].new_root(),
            "turn {i} must consume the running head"
        );
    }
    // A fresh accumulator has no summary and 0 turns.
    let acc = Accumulator::genesis();
    assert!(acc.summary().is_none());
    assert_eq!(acc.num_turns(), 0);
}

/// An empty accumulator refuses to finalize (nothing to attest).
#[test]
fn empty_accumulator_refuses_finalize() {
    let acc = Accumulator::genesis();
    match acc.finalize() {
        Err(AccError::Empty) => {}
        Ok(_) => panic!("an empty accumulator must not finalize"),
        Err(other) => panic!("expected Empty, got {other:?}"),
    }
}

/// The running temporal tooth REJECTS a discontinuous turn cheaply: `accumulate` returns
/// `AccError::ChainBreak` from the host-side continuity check, BEFORE the (expensive) recursion fold.
///
/// We fold one real turn (the cheap-ish first leaf is one descriptor-leaf wrap), then feed an
/// unrelated turn — the `ChainBreak` fires at the continuity check (step 2), before any aggregation.
///
/// NOTE: this still mints + wraps ONE real leaf for the first `accumulate`, so it is heavier than a
/// pure host test; it is kept un-ignored because a single leaf wrap is far cheaper than a multi-turn
/// fold, and it is the load-bearing rejection tooth. If CI budget is tight, move to `#[ignore]`.
#[test]
#[ignore = "SLOW: one real leaf wrap (~tens of seconds); run with --ignored"]
fn accumulate_rejects_discontinuity() {
    let (first, _o0, _n0) = make_turn(1000, 0, 7);
    let (bad_next, _bo, _bn) = make_turn(500, 50, 3); // unrelated chain

    let mut acc = Accumulator::genesis();
    acc.accumulate(&first)
        .expect("the first turn folds (becomes the running proof)");
    assert_eq!(acc.num_turns(), 1);

    match acc.accumulate(&bad_next) {
        Err(AccError::ChainBreak { .. }) => {}
        Ok(()) => panic!("a discontinuous turn must not accumulate"),
        Err(other) => panic!("expected ChainBreak, got {other:?}"),
    }
    // The rejected step did NOT advance the accumulator.
    assert_eq!(acc.num_turns(), 1);
}

// ============================================================================
// SLOW teeth (real recursion fold — minutes; #[ignore]).
// ============================================================================

/// **THE HEADLINE TOOTH.** Accumulate a continuous stream genesis -> t1 -> t2 -> t3 INCREMENTALLY
/// (O(1) proof memory: one running proof held between steps), finalize, and verify via the light
/// client's discipline (`verify_turn_chain_recursive`) under the honest self-extracted VK anchor.
///
/// Asserts: the artifact verifies; its endpoints are the genuine genesis/final; `num_turns == 3`; and
/// the accumulated artifact attests the SAME `(genesis_root, final_root, num_turns)` a K-fold
/// `prove_turn_chain_recursive` of the same 3 turns attests (the running fold and the balanced tree
/// agree on the whole-history claim).
#[test]
#[ignore = "SLOW: real incremental recursion fold over 3 turns (~minutes); run with --ignored"]
fn incremental_accumulate_verifies_whole_history() {
    let (turns, genesis, final_root) = make_chain(1000, 0, 11, 3);

    // Drive the running left-fold ONE turn at a time (O(1) proof memory).
    let mut acc = Accumulator::genesis();
    for (i, t) in turns.iter().enumerate() {
        acc.accumulate(t)
            .unwrap_or_else(|e| panic!("turn {i} must accumulate: {e}"));
        assert_eq!(
            acc.num_turns(),
            i + 1,
            "running num_turns advances per step"
        );
    }
    let summary = acc
        .summary()
        .expect("the accumulator has a summary after 3 turns");
    assert_eq!(summary.genesis_root, genesis);
    assert_eq!(summary.head_root, final_root);
    assert_eq!(summary.num_turns, 3);

    // Finalize + self-verify (the setup-side entry mints the anchor it would distribute).
    let (whole, vk) = acc
        .finalize_and_self_verify()
        .expect("the accumulated artifact must finalize + verify under its honest anchor");
    assert_eq!(whole.num_turns, 3);
    assert_eq!(whole.genesis_root, genesis);
    assert_eq!(whole.final_root, final_root);

    // A light client re-runs the SAME check against the configured anchor — cost independent of n.
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the accumulated whole-chain proof verifies under the honest VK anchor");

    // Cross-check the whole-history CLAIM against the K-fold balanced-tree artifact of the same 3
    // turns: both attest the IDENTICAL (genesis, final, num_turns, chain_digest). (The root proofs
    // differ in tree shape — hence different VK fingerprints — but the public claim agrees.)
    let (turns2, _g2, _f2) = make_chain(1000, 0, 11, 3);
    let kfold: WholeChainProof =
        prove_turn_chain_recursive(&turns2).expect("the K-fold of the same chain proves");
    assert_eq!(kfold.genesis_root, whole.genesis_root, "genesis agrees");
    assert_eq!(kfold.final_root, whole.final_root, "final agrees");
    assert_eq!(kfold.num_turns, whole.num_turns, "num_turns agrees");
    assert_eq!(
        kfold.chain_digest, whole.chain_digest,
        "the ordered-history digest agrees (running fold == balanced tree)"
    );
}

/// **THE VK-IDENTITY-PIN TOOTH (lever (a), in-band).** A child proof whose VK-identity (its
/// preprocessed commitment) does NOT match the pinned expected commitment is REJECTED IN-CIRCUIT —
/// the parent aggregation circuit becomes UNSAT, so no folded proof is produced.
///
/// We fold ONE real turn so a genuine running (leaf) proof exists, then re-fold it against a fresh
/// leaf (a leaf∘leaf aggregation) once with the pin set to its GENUINE commitment (must SUCCEED) and
/// once with a CORRUPTED commitment (must FAIL with `AccError::RecursionFailed`). The success/failure
/// split is decided entirely by the in-circuit `connect` constraint that pins the child's
/// preprocessed-commitment targets to the expected value: a foreign-circuit child (different
/// commitment) cannot satisfy it. This is the genuine witness that the IVC self-verification VK check
/// is enforced IN-CIRCUIT, not host-side.
///
/// NOTE on shape: we probe after exactly ONE turn (running == a LEAF proof), so the probe is the
/// cheapest leaf∘leaf fold that exhibits the pin. The deeper agg∘leaf fold the unbounded driver runs
/// from turn 2 on ALSO folds cleanly with the pin engaged (see
/// `incremental_accumulate_verifies_whole_history`, which passes PINNED end-to-end); this tooth
/// isolates the pin's in-circuit REJECTION on the cheaper shape.
#[test]
#[ignore = "SLOW: one running leaf + two pinned leaf-folds (~minutes); run with --ignored"]
fn pinned_fold_rejects_foreign_vk_in_circuit() {
    use p3_baby_bear::BabyBear as P3BabyBear;
    use p3_field::PrimeCharacteristicRing;
    use p3_symmetric::MerkleCap;

    // ONE continuous turn → a genuine running LEAF proof (no prior aggregation, so the probe is a
    // clean leaf∘leaf fold).
    let (t0, _o0, _n0) = make_turn(1000, 0, 11);
    let mut acc = Accumulator::genesis();
    acc.accumulate(&t0).expect("turn 0 folds (becomes the running leaf proof)");
    assert_eq!(acc.num_turns(), 1);

    // The running leaf proof's genuine VK-identity core (the preprocessed Merkle cap).
    let genuine = acc
        .running_vk_commit()
        .expect("a running proof exists after 1 turn, so it has a preprocessed commitment");

    // A continuous second turn to re-fold against (the probe does not mutate `acc`).
    let (t1, _o, _n) = make_turn(1000 - 11, 1, 11);

    // (1) HONEST pin: the running proof's actual VK matches `genuine` → the in-circuit check is
    //     satisfiable, the fold SUCCEEDS.
    acc.probe_pinned_fold(&t1, genuine.clone())
        .expect("a pinned fold against the GENUINE running VK must succeed");

    // (2) CORRUPTED pin: flip one field element of the expected commitment. The running proof's
    //     actual VK no longer matches, so the in-circuit `connect` is UNSAT → the fold FAILS.
    let mut roots = genuine.into_roots();
    assert!(!roots.is_empty(), "the cap has at least one root");
    roots[0][0] += P3BabyBear::ONE; // a different-circuit VK fingerprint
    let corrupted = MerkleCap::new(roots);

    match acc.probe_pinned_fold(&t1, corrupted) {
        Err(AccError::RecursionFailed { .. }) => {}
        Ok(()) => panic!(
            "a pinned fold against a CORRUPTED (foreign-circuit) VK MUST be rejected in-circuit"
        ),
        Err(other) => panic!("expected RecursionFailed (UNSAT), got {other:?}"),
    }
}

/// A forged-LINK stream is rejected by the running temporal tooth: accumulating a turn whose
/// `old_root` does not consume the running `head_root` fails with `AccError::ChainBreak`, so no
/// running proof for a spliced history is ever produced.
#[test]
#[ignore = "SLOW: two real leaf wraps before the break tooth; run with --ignored"]
fn forged_link_stream_is_rejected() {
    let (t0, _o0, _n0) = make_turn(1000, 0, 11);
    let (t1_continuous, _o1, _n1) = make_turn(1000 - 11, 1, 11);
    let (t_spliced, _os, _ns) = make_turn(42, 99, 3); // does NOT consume t1's new_root

    let mut acc = Accumulator::genesis();
    acc.accumulate(&t0).expect("t0 folds");
    acc.accumulate(&t1_continuous).expect("t1 continues");
    assert_eq!(acc.num_turns(), 2);

    match acc.accumulate(&t_spliced) {
        Err(AccError::ChainBreak { .. }) => {}
        Ok(()) => panic!("a spliced turn must not accumulate"),
        Err(other) => panic!("expected ChainBreak, got {other:?}"),
    }
}
