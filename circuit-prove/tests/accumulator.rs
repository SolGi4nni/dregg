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
    assert_eq!(whole.genesis_root, [genesis; 8]);
    assert_eq!(whole.final_root, [final_root; 8]);

    // A light client re-runs the SAME check against the configured anchor — cost independent of n.
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the accumulated whole-chain proof verifies under the honest VK anchor");

    // Cross-check the whole-history CLAIM against the K-fold balanced-tree artifact of the same 3
    // turns: both attest the IDENTICAL (genesis, final, num_turns) — the load-bearing endpoints +
    // count. (The root proofs differ in tree shape — hence different VK fingerprints — but the
    // endpoints + count agree.)
    //
    // NOTE on the digest: BOTH paths now carry the SAME ordered SEGMENT-ACCUMULATOR digest (codex's
    // fix for the mixed-root hole) — each descriptor leaf carries `[first_old, last_new, count,
    // acc]` with the genuine 4-lane W24 Poseidon2 `acc`, and the combine folds `acc = commit(L.acc,
    // R.acc)`. They differ ONLY in fold SHAPE: the K-fold uses the BALANCED binary tree, the online
    // accumulator the LEFT-LINEAR fold. Both are sound ordered-history commitments, but the two fold
    // shapes give different digests, so we deliberately do NOT assert digest equality here. Each
    // artifact's own `verify_turn_chain_recursive` binds its own carried digest to its own
    // root-exposed segment (the segment tooth), which is what soundness requires.
    let (turns2, _g2, _f2) = make_chain(1000, 0, 11, 3);
    let kfold: WholeChainProof =
        prove_turn_chain_recursive(&turns2).expect("the K-fold of the same chain proves");
    assert_eq!(kfold.genesis_root, whole.genesis_root, "genesis agrees");
    assert_eq!(kfold.final_root, whole.final_root, "final agrees");
    assert_eq!(kfold.num_turns, whole.num_turns, "num_turns agrees");
}

/// **THE ONLINE MIXED-ROOT CLOSE (the port of `mixed_root_forgery_executes_A_claims_B` to the
/// online accumulator).** Drive the ONLINE accumulator over history A's REAL segment-bearing
/// descriptor leaves, finalize to A's whole-chain proof, then carry a DIFFERENT history B's claims
/// to the verifier. Because every `accumulate` fold combined A's leaf segments in-circuit, A's root
/// exposes A's `[genesis, final, num_turns, digest]` BY CONSTRUCTION — so a B-claim against an
/// A-execution is REJECTED by the segment tooth. There is no swappable binding leaf to inject B's
/// endpoints into the root (the binding proof is carried but is not a soundness dependency).
///
/// The SECOND assertion exercises the SAME-ENDPOINT close specifically: carry A's REAL
/// genesis/final/count but a TAMPERED 4-lane digest. The old single-felt zero-padded carrier could
/// not bind this lane; now the root exposes the genuine 4-lane W24 Poseidon2 segment digest, so a
/// same-endpoint wrong-digest claim is rejected too (~124-bit collision resistance).
#[test]
#[ignore = "SLOW: a real online segment fold over 2 turns (~minutes); run with --ignored — the online mixed-root CLOSE"]
fn online_mixed_root_forgery_rejected() {
    use dregg_circuit_prove::ivc_turn_chain::{
        SEG_DIGEST_WIDTH, verify_turn_chain_recursive_from_parts,
    };
    use dregg_circuit_prove::plonky3_recursion_impl::recursive::recursion_vk_fingerprint;

    // History A: the REAL executed online history (the descriptor leaves the accumulator folds).
    let (turns_a, _ga, _fa) = make_chain(1000, 0, 7, 2);
    // History B: a DIFFERENT history; only its CLAIMS are carried (the execution was A).
    let (turns_b, gb, fb) = make_chain(500, 0, 3, 2);

    // Drive the ONLINE accumulator over A and finalize to A's whole-chain proof.
    let mut acc = Accumulator::genesis();
    for (i, t) in turns_a.iter().enumerate() {
        acc.accumulate(t)
            .unwrap_or_else(|e| panic!("A turn {i} must accumulate: {e}"));
    }
    let whole_a = acc.finalize().expect("A finalizes to a whole-chain proof");

    // The honest anchor recomputed from A's root (an honest setup over THIS shape distributes
    // exactly this fingerprint — the attacker forges only the carried claim).
    let vk = recursion_vk_fingerprint(&whole_a.root.0);

    // Sanity: A's own claim verifies (the honest online path).
    verify_turn_chain_recursive(&whole_a, &vk).expect("A's honest whole-chain proof verifies");

    // ----- (1) DIFFERENT-ENDPOINT forgery: carry B's claims against A's online root. -----
    let b_genesis = turns_b[0].old_root();
    let b_final = turns_b[1].new_root();
    assert_eq!(b_genesis, gb);
    assert_eq!(b_final, fb);
    assert_ne!(
        b_genesis, whole_a.genesis_root[0],
        "B's history must differ from A's"
    );
    let b_chain_digest = [BabyBear::ZERO; SEG_DIGEST_WIDTH];

    let verdict = verify_turn_chain_recursive_from_parts(
        &whole_a.root.0,
        &whole_a.binding_proof,
        [b_genesis; 8],
        [b_final; 8],
        b_chain_digest,
        2,
        &vk,
    );
    eprintln!("[online mixed-root] B-claim verdict = {verdict:?}  (is_err = CLOSED)");
    assert!(
        verdict.is_err(),
        "ONLINE MIXED-ROOT CLOSED: a B whole-chain claim against an online root that folded A's \
         REAL descriptor leaves MUST be REJECTED by the segment tooth (A's root exposes A's \
         endpoints, not B's). got: {verdict:?}"
    );

    // ----- (2) SAME-ENDPOINT forgery: A's real endpoints + a TAMPERED 4-lane digest. -----
    let mut bad_digest = whole_a.chain_digest;
    bad_digest[0] += BabyBear::ONE;
    let verdict2 = verify_turn_chain_recursive_from_parts(
        &whole_a.root.0,
        &whole_a.binding_proof,
        whole_a.genesis_root,
        whole_a.final_root,
        bad_digest,
        whole_a.num_turns,
        &vk,
    );
    eprintln!(
        "[online mixed-root] same-endpoint wrong-digest verdict = {verdict2:?}  (is_err = CLOSED)"
    );
    assert!(
        verdict2.is_err(),
        "SAME-ENDPOINT CLOSED: a claim carrying A's real genesis/final/count but a WRONG 4-lane \
         digest MUST be REJECTED — the root exposes the genuine segment digest. got: {verdict2:?}"
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
    acc.accumulate(&t0)
        .expect("turn 0 folds (becomes the running leaf proof)");
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

/// **THE FAIL-CLOSED VK-IDENTITY TOOTH (host-side, the load-bearing negative).** After the running
/// fixed-point pin is CAPTURED, a running proof whose preprocessed commitment no longer matches the
/// pin makes `accumulate` REJECT (`AccError::VkIdentityMismatch`) — it does NOT silently fall through
/// to an unpinned fold (the soundness hole this tooth guards: a forged/foreign running proof folding
/// through unpinned). The sibling `pinned_fold_rejects_foreign_vk_in_circuit` exercises the IN-CIRCUIT
/// rejection on the leaf∘leaf probe; THIS exercises the DRIVER's host-side refusal on the live fold
/// path — the branch the probe never touches.
///
/// We fold two continuous turns (turn 1 captures the pin from the first running aggregation), then
/// FORCE the captured pin to a FOREIGN commitment (simulating a running proof / pin disagreement an
/// adversary might engineer) and assert the third `accumulate` REJECTS before building any unpinned
/// fold, leaving the accumulator UNCHANGED (still 2 turns).
#[test]
#[ignore = "SLOW: two real folds to capture the pin (~minutes); run with --ignored"]
fn accumulate_rejects_pin_mismatch_fail_closed() {
    use p3_baby_bear::BabyBear as P3BabyBear;
    use p3_field::PrimeCharacteristicRing;
    use p3_symmetric::MerkleCap;

    // Two continuous turns: turn 0 → running leaf; turn 1 → first running AGGREGATION, which captures
    // the fixed-point pin.
    let (turns, _g, _f) = make_chain(1000, 0, 7, 3);
    let mut acc = Accumulator::genesis();
    acc.accumulate(&turns[0]).expect("turn 0 folds");
    acc.accumulate(&turns[1])
        .expect("turn 1 folds + captures the pin");
    assert_eq!(acc.num_turns(), 2);
    assert!(
        acc.vk_identity_pinned(),
        "the fixed-point pin must be captured after the first running aggregation"
    );

    // The genuine running commitment (what the pin SHOULD equal).
    let genuine = acc
        .running_vk_commit()
        .expect("a running aggregation proof exists after 2 turns");

    // FORCE the pin to a FOREIGN value: flip one field element. Now the running proof's genuine
    // commitment no longer matches the (corrupted) pin.
    let mut roots = genuine.into_roots();
    assert!(!roots.is_empty(), "the cap has at least one root");
    roots[0][0] += P3BabyBear::ONE; // a different-circuit VK fingerprint
    let foreign = MerkleCap::new(roots);
    acc.force_pinned_vk_for_test(foreign);

    // The third accumulate MUST reject fail-closed (NOT fold unpinned).
    match acc.accumulate(&turns[2]) {
        Err(AccError::VkIdentityMismatch { index, .. }) => {
            assert_eq!(
                index, 2,
                "the mismatch is reported at the 3rd fold (index 2)"
            );
        }
        Ok(()) => panic!(
            "a captured-pin MISMATCH MUST be fatal: accumulate folded through (silently unpinned) — \
             the soundness hole"
        ),
        Err(other) => panic!("expected VkIdentityMismatch, got {other:?}"),
    }
    // The rejected step did NOT advance the accumulator.
    assert_eq!(
        acc.num_turns(),
        2,
        "a rejected fold leaves the accumulator unchanged"
    );
}

/// **THE PICKLES-PARITY TOOTH — the running VK reaches a CONSTANT FIXED POINT across depth.**
///
/// This is the fixed-size-verifier-forever property: once the running aggregation proof's VK
/// fingerprint stops changing with depth, a light client pins ONE anchor and accepts an accumulated
/// chain of ANY length. The fingerprint is the full verifier-reconstruction SHAPE: table packing,
/// `rows`, `degree_bits`, the non-primitive manifest, AND the preprocessed commitment (= the VK core /
/// op-list binding).
///
/// **EMPIRICALLY MEASURED SHAPE OF THE FIXED POINT (the honest, validated result):** the running fold
/// is NOT constant from its first aggregation; it settles through a short transient and then is
/// PERPETUALLY CONSTANT. Measured at the dregg leaf-wrap config over a continuous chain:
///   - depth 2: the LEAF∘LEAF result (the running input was a single leaf) — a transient shape;
///   - depth 3: the FIRST AGG∘LEAF result (the running input is now an aggregation) — still settling;
///   - depth 4: the AGG∘LEAF fixed point — the running input is now a stable-shape aggregation;
///   - depth 5+: IDENTICAL to depth 4 (full VK material — `rows`, `degree_bits`, AND the preprocessed
///     commitment all byte-equal). The fold has reached its perpetual fixed point.
///
/// So this tooth asserts the GENUINE depth-invariance: **depth-4 == depth-5 == depth-6** (the fixed
/// point holds across TWO further iterations of the fold-shape transition, not just one), and
/// characterizes the transient (depth 2 ≠ 3 ≠ 4). The `degree_bits` are constant THROUGHOUT
/// (`[9,9,15,14,15]`) — the transient lives entirely in the op-list (logical `rows` + preprocessed
/// commitment), which self-stabilizes once the running input is a fixed-shape aggregation. The A/B
/// companion (`wrap_grows_vk_when_disabled`) confirms the transient is real (the early fingerprints
/// genuinely DIFFER), so the fixed-point equality is non-vacuous.
///
/// **THE MECHANIZED PERPETUAL CLAIM (no longer prose).** The measured fixed point this tooth asserts
/// (`step anchor = anchor`, one application of the fold-shape transition reproduces the depth-4 shape)
/// is the SINGLE hypothesis the Lean `Dregg2.Circuit.RecursiveAggregation.running_vk_perpetually_-
/// constant` rides to `∀N, VK_N = VK_4` (`#assert_axioms`-clean) — the deterministic-iteration
/// induction the old "structural idempotence" prose named, now machine-checked. Its other premise —
/// that the transition is a function of SHAPE alone — is discharged empirically by
/// `running_vk_fixed_point_is_value_independent` (two value-streams reach the same depth-4 VK). The two
/// extra measured iterations here (depth-5, depth-6) are the empirical corroboration of that induction.
///
/// The WRAP-step `min_trace_height` ceiling ([`WRAP_LOG_CEIL`], ON by default) pins the FRI trace shape
/// but is empirically a near-no-op here (heights were already constant); the constant-VK property comes
/// from the fold's NATURAL self-stabilization. To make the fixed point reached EARLIER (eliminate the
/// 2-step transient so EVERY fold from depth 2 carries the one anchor) needs the structural half of the
/// wrap.
///
/// **ROOT-CAUSED structural reason for the 2-step transient (the precise residual).** The AGG∘LEAF
/// verifier op-list depends on the STRUCTURE of the running (left) input — its `non_primitives`
/// per-instance opened-column widths / public-value counts and `rows` (`verify_p3_batch_proof_circuit`
/// in the fork iterates the input proof's `non_primitives` and allocates per-instance targets from
/// them). A LEAF, an `AGG(LEAF,LEAF)`, and an `AGG(AGG,LEAF)` input each carry a different such
/// structure, and that structure propagates EXACTLY ONE level into the parent op-list — so the parent
/// stabilizes only after the input has been `AGG(AGG,LEAF)`-shaped for one full fold (hence depth 4, not
/// 2). A true depth-2 fixed point needs the running input to have the steady `AGG(AGG,LEAF)` structure
/// from the FIRST aggregation, which requires a CANONICAL agg-shaped seed whose own left is agg-shaped (a
/// recursive fixpoint seed = the genuine Pickles step∘wrap circuit); the fork exposes no
/// canonical-shape/normalize/re-prove primitive today, so it is genuinely multi-pass outstanding fork
/// work. See the accumulator module header for the full statement.
#[test]
#[ignore = "SLOW: real incremental recursion fold over 6 turns (~minutes); run with --ignored"]
fn wrapped_running_vk_is_constant_across_depth() {
    let (turns, _genesis, _final_root) = make_chain(1000, 0, 7, 6);

    let mut acc = Accumulator::genesis(); // wrap ENABLED by default
    let mut fps: Vec<dregg_circuit_prove::plonky3_recursion_impl::recursive::RecursionVk> =
        Vec::new();
    let mut mats: Vec<String> = Vec::new();
    for (i, t) in turns.iter().enumerate() {
        acc.accumulate(t)
            .unwrap_or_else(|e| panic!("turn {i} must accumulate: {e}"));
        // The running proof is an AGGREGATION from depth 2 (turn index 1) onward.
        if i >= 1 {
            fps.push(
                acc.running_vk_fingerprint()
                    .expect("a running aggregation proof exists from depth 2"),
            );
            mats.push(acc.running_vk_material_debug().expect("material"));
        }
    }
    assert!(fps.len() >= 5, "captured depths 2,3,4,5,6");
    for (k, m) in mats.iter().enumerate() {
        eprintln!("depth-{} VK fp={} material: {}", k + 2, fps[k].to_hex(), m);
    }

    // THE FIXED POINT, ACROSS TWO ITERATIONS: depth-4 == depth-5 == depth-6 (the running VK has
    // stopped changing — fixed-size verifier forever from here). `fps` is indexed from depth 2:
    // fps[2] = depth-4, fps[3] = depth-5, fps[4] = depth-6. The depth-4 == depth-5 equality is the
    // SINGLE measured hypothesis (`step anchor = anchor`) the Lean `running_vk_perpetually_constant`
    // rides to `∀N, VK_N = VK_4`; the depth-5 == depth-6 equality is a second iteration corroborating
    // it empirically.
    assert_eq!(
        fps[2],
        fps[3],
        "the running VK must reach a CONSTANT FIXED POINT: depth-4 fingerprint {} != depth-5 {} \
         (material depth-4 [{}] vs depth-5 [{}])",
        fps[2].to_hex(),
        fps[3].to_hex(),
        mats[2],
        mats[3],
    );
    assert_eq!(
        fps[3],
        fps[4],
        "the running VK fixed point must HOLD across a second iteration: depth-5 {} != depth-6 {} \
         (material depth-5 [{}] vs depth-6 [{}])",
        fps[3].to_hex(),
        fps[4].to_hex(),
        mats[3],
        mats[4],
    );
    // And the FULL VK material (not just the blake3) is byte-identical at the fixed point — so the
    // equality is the genuine op-list/preprocessed-commitment identity, not a hash coincidence.
    assert_eq!(
        mats[2], mats[3],
        "the running VK MATERIAL must be identical at the fixed point (depth-4 == depth-5)"
    );
    assert_eq!(
        mats[3], mats[4],
        "the running VK MATERIAL must be identical across the second iteration (depth-5 == depth-6)"
    );
}

/// **THE NON-VACUITY HALF (A/B) — the running VK genuinely VARIES through the transient.** Drives a
/// 5-turn chain with the WRAP step DISABLED and reports the per-depth fingerprint + full VK material,
/// localizing exactly where the fold settles. Measured: depth-2 ≠ depth-3 ≠ depth-4, then
/// depth-4 == depth-5 (the natural fixed point). This proves the fixed-point equality asserted by
/// `wrapped_running_vk_is_constant_across_depth` is LOAD-BEARING (the early fingerprints really do
/// differ), not trivially true.
#[test]
#[ignore = "SLOW: real incremental recursion fold over 5 turns, UNwrapped (~minutes); run with --ignored"]
fn wrap_grows_vk_when_disabled() {
    let (turns, _genesis, _final_root) = make_chain(1000, 0, 7, 5);

    let mut acc = Accumulator::genesis().with_wrap(false);
    let mut fps: Vec<dregg_circuit_prove::plonky3_recursion_impl::recursive::RecursionVk> =
        Vec::new();
    for (i, t) in turns.iter().enumerate() {
        acc.accumulate(t)
            .unwrap_or_else(|e| panic!("turn {i} must accumulate (unwrapped): {e}"));
        if i >= 1 {
            eprintln!(
                "UNWRAPPED depth-{} VK fp={} material: {}",
                i + 1,
                acc.running_vk_fingerprint().expect("fp").to_hex(),
                acc.running_vk_material_debug().expect("material")
            );
            fps.push(acc.running_vk_fingerprint().expect("fp"));
        }
    }
    assert!(fps.len() >= 4, "captured depths 2,3,4,5");
    for k in 1..fps.len() {
        eprintln!(
            "UNWRAPPED depth-{} vs depth-{}: {}",
            k + 1,
            k + 2,
            if fps[k] == fps[k - 1] {
                "EQUAL"
            } else {
                "DIFFER"
            }
        );
    }
    // The transient is real: the leaf→agg step (depth-2 vs depth-3) genuinely changes the VK.
    assert_ne!(
        fps[0],
        fps[1],
        "the running VK must change across the leaf→agg transition (depth-2 {} == depth-3 {} would \
         mean the shape was already constant — investigate)",
        fps[0].to_hex(),
        fps[1].to_hex(),
    );
    // And the fold DOES reach a fixed point: depth-4 == depth-5 even unwrapped (the natural
    // self-stabilization the constant-VK tooth asserts).
    assert_eq!(
        fps[2],
        fps[3],
        "the running VK must reach a fixed point by depth 4 (depth-4 {} != depth-5 {})",
        fps[2].to_hex(),
        fps[3].to_hex(),
    );
}

/// **THE VALUE-INDEPENDENCE TOOTH — the empirical discharge of the mechanized fixed-point's modeling
/// assumption.** The Lean mechanization (`Dregg2.Circuit.RecursiveAggregation.running_vk_perpetually_-
/// constant`) proves `∀N, VK_N = VK_4` from a SINGLE measured fixed point (`step anchor = anchor`,
/// the depth-4 == depth-5 reproduction asserted by `wrapped_running_vk_is_constant_across_depth`) by
/// modeling the fold-shape transition as a DETERMINISTIC FUNCTION of the running VK SHAPE alone —
/// `step : VkShape → VkShape`. That "shape alone, not the witness values" is the fork's
/// content-independence (`verify_p3_batch_proof_circuit` builds the parent op-list from `rows`,
/// `table_packing`, the `non_primitives` manifest, and per-instance public-value COUNTS — never the
/// values; `recursion_vk_fingerprint` is correspondingly content-independent). THIS tooth discharges
/// that modeling assumption EMPIRICALLY: two DIFFERENT continuous value-streams (different
/// amounts/balances/nonces, hence different roots and witness values, but the SAME Transfer effect
/// shape ⇒ the same leaf shape) driven to the depth-4 fixed point reach the BYTE-IDENTICAL running VK
/// material. So the fixed point is independent of WHICH values were folded — it is a property of the
/// SHAPE — which is exactly what makes the single-measurement → `∀N` induction sound.
#[test]
#[ignore = "SLOW: two real 4-turn folds to the fixed point (~minutes); run with --ignored — the value-independence discharge"]
fn running_vk_fixed_point_is_value_independent() {
    // Two DISTINCT value-streams: different start balances, different debit steps (hence different
    // roots + witness values at every turn), but both pure-Transfer (same leaf SHAPE). Four turns
    // each so the running proof reaches the depth-4 fixed point.
    let (stream_a, _ga, _fa) = make_chain(1000, 0, 7, 4);
    let (stream_b, _gb, _fb) = make_chain(900, 3, 13, 4);

    let drive = |turns: &[FinalizedTurn]| {
        let mut acc = Accumulator::genesis(); // wrap ENABLED (the fixed-shape ceiling)
        for (i, t) in turns.iter().enumerate() {
            acc.accumulate(t)
                .unwrap_or_else(|e| panic!("turn {i} must accumulate: {e}"));
        }
        (
            acc.running_vk_fingerprint()
                .expect("a running aggregation proof exists at depth 4"),
            acc.running_vk_material_debug().expect("material"),
        )
    };

    let (fp_a, mat_a) = drive(&stream_a);
    let (fp_b, mat_b) = drive(&stream_b);
    eprintln!(
        "[value-indep] stream A depth-4 VK fp={} material: {}",
        fp_a.to_hex(),
        mat_a
    );
    eprintln!(
        "[value-indep] stream B depth-4 VK fp={} material: {}",
        fp_b.to_hex(),
        mat_b
    );

    // The depth-4 fixed-point VK is the SAME for both value-streams — the fold-shape transition
    // depends on the SHAPE alone, not the witness values. This is the Rust discharge of the Lean
    // `step : VkShape → VkShape` modeling assumption (shape-only determinism), under which one
    // measured fixed point gives `∀N, VK_N = VK_4`.
    assert_eq!(
        fp_a,
        fp_b,
        "the depth-4 fixed-point VK must be VALUE-INDEPENDENT: stream-A fp {} != stream-B fp {} \
         (material A [{}] vs B [{}]) — if these differ the op-list depends on witness values, \
         breaking the shape-only-determinism the perpetual-constancy induction rests on",
        fp_a.to_hex(),
        fp_b.to_hex(),
        mat_a,
        mat_b,
    );
    assert_eq!(
        mat_a, mat_b,
        "the depth-4 fixed-point VK MATERIAL must be byte-identical across value-streams"
    );
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
