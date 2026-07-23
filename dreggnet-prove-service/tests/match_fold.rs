//! The match-fold service driven on the REAL fold backend.
//!
//! FAST (normal suite): a forged match settles `Failed` off the fold (its teeth
//! bite at lowering, before any proving); the GPU-dispatch probe is wired.
//!
//! SLOW (`--ignored`, minutes-to-hours — the deployed recursive fold): a played
//! match ENQUEUES, folds on a background worker to `Done{proof}`, and the proof
//! VERIFIES via the O(1) light client, correctness-identical to the FOREGROUND
//! fold; a tampered proof is REJECTED.
//!
//! Run the slow lane:
//!   ssh persvati 'cd .../breadstuffs && cargo test -p dreggnet-prove-service \
//!     --test match_fold -- --ignored --nocapture'

use dregg_automatafl::reference::{ATT, AUTO, Board, VAC};
use dregg_circuit_prove::ivc_turn_chain::WholeChainProofBytes;
use dregg_lightclient::verify_history_bytes;
use dreggnet_prove_service::{
    AutomataflMatch, JobStatus, MatchProof, PlayedMatch, ProveService, TugMatch, TugWin, gpu,
    match_prove_service,
};
use std::sync::Arc;

fn tug_hand() -> Vec<(u64, u64)> {
    vec![
        (0, 1001),
        (1, 1002),
        (3, 1003),
        (7, 1004),
        (12, 1005),
        (18, 1006),
    ]
}

/// The driven 5x5 automatafl board (matches the game-board crate's own gate).
fn demo_board() -> Board {
    let n = 5usize;
    let mut cells = vec![VAC; n * n];
    cells[4 * n + 2] = ATT;
    cells[2 * n + 2] = AUTO;
    Board {
        n,
        cells,
        auto: (2, 2),
        col_rule: true,
    }
}

fn assert_correctness_identical(async_proof: &MatchProof, foreground: &MatchProof) {
    // Both self-verify against their own vk (the shipped envelope IS what verifies).
    verify_history_bytes(&async_proof.proof_bytes, &async_proof.vk)
        .expect("the async-folded proof verifies");
    verify_history_bytes(&foreground.proof_bytes, &foreground.vk)
        .expect("the foreground proof verifies");
    // Correctness identity: same trust anchor, same attested history endpoints.
    assert_eq!(
        async_proof.vk.0, foreground.vk.0,
        "same root VK fingerprint"
    );
    assert_eq!(
        async_proof.attested.genesis_root, foreground.attested.genesis_root,
        "same genesis anchor"
    );
    assert_eq!(
        async_proof.attested.final_root, foreground.attested.final_root,
        "same final (WIN) anchor"
    );
    assert_eq!(
        async_proof.attested.num_turns, foreground.attested.num_turns,
        "same attested turn count"
    );
}

// ───────────────────────────────────────────────────────────────────────────
// FAST — always run.
// ───────────────────────────────────────────────────────────────────────────

/// NON-VACUOUS forged-match rejection, off the fold: a card never dealt has no
/// membership leaf, so the match cannot lower — the backend returns `Err` and the
/// job settles `Failed` fast, WITHOUT ever entering the (slow) fold. This is the
/// forgery tooth biting on the async service's own path.
#[test]
fn a_forged_match_settles_failed_off_the_fold() {
    let svc = match_prove_service();
    let forged = PlayedMatch::Tug(TugMatch {
        hand: tug_hand(),
        plays: vec![0, 20], // 20 was never dealt
        win: None,
    });
    let job = svc.enqueue(forged).expect("accepted into the queue");
    let outcome = svc.wait(job);
    assert!(
        outcome.is_err(),
        "a forged match must NOT fold to a proof; got {outcome:?}"
    );
    let err = outcome.unwrap_err();
    assert!(
        err.contains("not under the current hand root") || err.to_lowercase().contains("card"),
        "the failure names the forgery tooth: {err}"
    );
    assert!(matches!(svc.status(job), JobStatus::Failed(_)));
    let m = svc.metrics();
    assert_eq!(m.failed, 1);
    assert_eq!(m.completed, 0);
    eprintln!("forged match rejected off the fold: {err}");
}

/// The GPU dispatch is wired on the fold path and runtime-probed: `gpu::available`
/// reflects adapter presence (CPU fallback on a CPU box — the correctness gate;
/// the GPU path where an adapter exists — the speed win).
///
/// `--ignored`: the probe enumerates a real `wgpu` adapter, which segfaults inside
/// the driver on a HEADLESS box (no display/GPU). Run it on a box with a GPU (or a
/// working software adapter) — where the speedup is realized anyway. The fold
/// itself never touches `wgpu` on a CPU box: it routes through the CPU recursion
/// config (`create_recursion_backend`), so the CPU correctness gate stands
/// independent of this probe.
#[test]
#[ignore = "enumerates a real wgpu adapter (segfaults on a headless box); run on a GPU box"]
fn the_gpu_dispatch_probe_is_wired() {
    let available = gpu::available();
    let desc = gpu::describe();
    assert!(!desc.is_empty());
    // Consistency: a named adapter iff available.
    assert_eq!(available, gpu::adapter_name().is_some());
    eprintln!("fold-path GPU dispatch: {desc} (available={available})");
}

// ───────────────────────────────────────────────────────────────────────────
// SLOW — `--ignored`: the real deployed fold.
// ───────────────────────────────────────────────────────────────────────────

/// HARD GATE (multiway-tug): a played match ENQUEUES, folds on a background worker
/// to `Done{proof}`, and the proof VERIFIES — correctness-identical to the
/// foreground fold. The play path never waited on the fold.
#[test]
#[ignore = "SLOW: the real deployed recursion fold over a played match (minutes-to-hours); run with --ignored"]
fn tug_match_folds_off_path_to_a_verifying_proof() {
    let m = TugMatch {
        hand: tug_hand(),
        plays: vec![0, 1],
        win: Some(TugWin {
            charm: 13,
            winner: 1,
        }),
    };
    let n_turns = m.plays.len() + m.win.is_some() as usize;

    // ── The service: enqueue returns immediately; the fold runs off-path. ──
    let svc = match_prove_service();
    let job = svc
        .enqueue(PlayedMatch::Tug(m.clone()))
        .expect("enqueued (the play is over)");
    // Poll shows it is proving in the background, not blocking us.
    assert!(matches!(
        svc.status(job),
        JobStatus::Queued | JobStatus::Proving
    ));
    eprintln!("enqueued a {n_turns}-turn tug match; folding in the background…");

    let async_proof = svc.wait(job).expect("the honest match folds to ONE proof");
    assert_eq!(
        async_proof.turns(),
        n_turns,
        "every played turn is attested"
    );
    assert!(matches!(svc.status(job), JobStatus::Done(_)));
    assert_eq!(svc.metrics().completed, 1);

    // ── Correctness identity vs the FOREGROUND fold (the same proof). ──
    let foreground = dreggnet_game_board::prove_tug_match(&m).expect("foreground fold");
    assert_correctness_identical(&async_proof, &foreground);

    eprintln!(
        "TUG: play → enqueue → [background fold, {n_turns} turns] → Done{{proof}} that VERIFIES, \
         correctness-identical to the foreground fold. The hand was never revealed."
    );
}

/// HARD GATE (automatafl): the D1 board-transition chain folds off-path to a
/// verifying proof, correctness-identical to the foreground fold.
#[test]
#[ignore = "SLOW: the real deployed recursion fold over the D1 board-transition chain; run with --ignored"]
fn automatafl_match_folds_off_path_to_a_verifying_proof() {
    let m = AutomataflMatch::automaton_only(demo_board(), 2);
    let svc = match_prove_service();
    let job = svc
        .enqueue(PlayedMatch::Automatafl(m.clone()))
        .expect("enqueued");
    let async_proof = svc.wait(job).expect("the honest match folds to ONE proof");
    assert_eq!(async_proof.turns(), m.turns);

    let foreground = dreggnet_game_board::prove_automatafl_match(&m).expect("foreground fold");
    assert_correctness_identical(&async_proof, &foreground);
    eprintln!(
        "AUTOMATAFL: play → enqueue → [background fold] → Done{{proof}} that VERIFIES. \
         The moves were never posted."
    );
}

/// NON-VACUOUS: a tampered proof (a relabeled final root) from an otherwise-valid
/// background fold is REJECTED by the light client — the async path ships no free
/// wins.
#[test]
#[ignore = "SLOW: folds a real match, then tampers; run with --ignored"]
fn a_tampered_folded_proof_is_rejected() {
    let m = TugMatch {
        hand: tug_hand(),
        plays: vec![0, 1],
        win: Some(TugWin {
            charm: 13,
            winner: 1,
        }),
    };
    let svc = match_prove_service();
    let job = svc.enqueue(PlayedMatch::Tug(m)).expect("enqueued");
    let proof = svc.wait(job).expect("folds");

    // The honest envelope verifies.
    verify_history_bytes(&proof.proof_bytes, &proof.vk).expect("honest proof verifies");

    // Relabel the attested final root — a forged "win".
    let mut env = WholeChainProofBytes::from_postcard(&proof.proof_bytes).expect("envelope");
    env.final_root[0] = env.final_root[0].wrapping_add(1);
    let tampered = env.to_postcard();
    assert!(
        verify_history_bytes(&tampered, &proof.vk).is_err(),
        "a relabeled final root must be REJECTED by the light client"
    );
    eprintln!("tampered fold proof REJECTED on verify (non-vacuous).");
}

/// Two concurrent matches fold on separate workers and both reach `Done` — the
/// bounded pool serves parallel matches, not one-at-a-time.
#[test]
#[ignore = "SLOW: folds TWO real matches concurrently; run with --ignored"]
fn two_matches_fold_concurrently() {
    // Force 2 workers regardless of the env default.
    let svc: dreggnet_prove_service::MatchProveService =
        ProveService::spawn_with(Arc::new(dreggnet_prove_service::fold_played_match), 2, 8);
    let tug = PlayedMatch::Tug(TugMatch {
        hand: tug_hand(),
        plays: vec![0, 1],
        win: Some(TugWin {
            charm: 13,
            winner: 1,
        }),
    });
    let afl = PlayedMatch::Automatafl(AutomataflMatch::automaton_only(demo_board(), 2));
    let j1 = svc.enqueue(tug).expect("enqueued");
    let j2 = svc.enqueue(afl).expect("enqueued");
    let p1 = svc.wait(j1).expect("tug folds");
    let p2 = svc.wait(j2).expect("afl folds");
    verify_history_bytes(&p1.proof_bytes, &p1.vk).expect("tug verifies");
    verify_history_bytes(&p2.proof_bytes, &p2.vk).expect("afl verifies");
    assert_eq!(svc.metrics().completed, 2);
    eprintln!("two matches folded concurrently; both Done{{proof}} verify.");
}
