//! # THE ZK-LEADERBOARD ACCEPT-PATH, DRIVEN end-to-end (not named).
//!
//! `ugc-dregg` accepts a SUCCINCT FOLD PROOF of a win — verified by the whole-history
//! light client in O(1) — INSTEAD of a replayed [`Playthrough`], and a proof-backed
//! entry stores NO moves. This test DRIVES the real path against a REAL proof:
//!
//!   * a proof-backed universe accepts a real fold proof
//!     (`dregg_lightclient::verify_history_bytes`) and RANKS it on the board — WITHOUT
//!     the playthrough stored (the moves are not posted);
//!   * a FORGED proof (a relabeled `final_root`) is REJECTED by the light client — the
//!     honest one having just been accepted (non-vacuous);
//!   * the win-predicate + genesis + result bindings each bite (a wrong win root / a
//!     wrong genesis / a lied turn count are refused);
//!   * a replay-only universe refuses a proof submission;
//!   * `reverify_entry` re-verifies a proof entry via the O(1) light client (not replay).
//!
//! ## The proof source (honest scope — see the crate docs)
//!
//! The proof driven here is a REAL, previously-folded whole-history proof — the deployed
//! browser light-client's baked artifact (`site/light-client/history.json`, a genuine
//! 3-turn recursive fold), vendored as [`PROOF_BYTES`]. `verify_history_bytes` ACCEPTS it
//! in-tree, so the accept-path is exercised against a GENUINE proof (not a stub).
//!
//! Why a baked artifact and not a live fold: the live in-tree fold (`fold_and_attest` over
//! `mint_rotated_participant_leg`) is currently Lane-D-blocked — the rotated prover's
//! wide/refuse-weld geometry is mid-flag-day inconsistent (the same class as
//! `WIDE_NUM_CARRIERS`; `game-turn-slice`'s tripwire tracks it). The SUCCINCT VERIFY
//! accept-path this test drives is independent of that block and is the deliverable.
//!
//! What is REAL: the succinct proof-verify accept-path (the light client's own verifier,
//! consumed verbatim) + the *moves-not-posted* practical privacy. NAMED FRONTIERS: a real
//! multi-turn Descent RUN → per-turn leaves → fold (the run→leaves→fold glue, Lane-D
//! geometry-blocked), and true crypto-ZK (the deployed STARK is *succinct*, not *hiding* —
//! "moves not posted" is data-availability, NOT cryptographic hiding).

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{RecursionVk, WholeChainProofBytes};
use dregg_lightclient::verify_history_bytes;

use ugc_dregg::{
    ProofAnchor, ProofCompletion, Registry, RejectReason, Universe, WinCondition,
    verify_proof_completion,
};

/// A REAL whole-history proof envelope (`WholeChainProof::to_bytes()`) — the deployed
/// light-client's baked 3-turn recursive fold. `verify_history_bytes` accepts it in-tree.
const PROOF_BYTES: &[u8] = include_bytes!("fixtures/whole_history_proof.bin");
/// The trust anchor (root-circuit VK fingerprint) for [`PROOF_BYTES`], 64 hex chars.
const ANCHOR_HEX: &str = include_str!("fixtures/whole_history_anchor.hex");

fn parse_hex32(s: &str) -> [u8; 32] {
    let s = s.trim();
    assert_eq!(s.len(), 64, "anchor must be 32 bytes (64 hex chars)");
    core::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).expect("hex"))
}

fn anchor_vk() -> RecursionVk {
    RecursionVk(parse_hex32(ANCHOR_HEX))
}

/// A minimal, valid, publishable universe carrying a proof anchor (its scene/win are
/// irrelevant to the proof path — the proof path never replays).
const PROOF_SCENE: &str = "---\nid: proof-board\ntitle: Proof Board\nweight: 1\n---\n\n=== start\n\n* [Leave]\n  -> END\n";

fn proof_universe(name: &str, anchor: ProofAnchor) -> Universe {
    Universe::authored(name, "prover", PROOF_SCENE, WinCondition::ended())
        .expect("valid proof-board universe")
        .with_proof_anchor(anchor)
}

fn bump0(mut a: [BabyBear; 8]) -> [BabyBear; 8] {
    a[0] = a[0] + BabyBear::ONE;
    a
}

#[test]
fn zk_leaderboard_accepts_a_fold_proof_and_drops_the_playthrough() {
    let vk = anchor_vk();
    let proof_bytes = PROOF_BYTES.to_vec();

    // The O(1) light client accepts the real proof and reads off the attested publics.
    // (This is the same call the board's accept-path makes; here it also gives us the
    // genuine genesis/final roots the board owner PINS as this universe's genesis + win.)
    let att = verify_history_bytes(&proof_bytes, &vk)
        .expect("the real baked whole-history proof must verify in-tree");
    assert_eq!(att.num_turns, 3, "the baked fold covers 3 turns");

    // The board owner pins the anchor as CONFIG: the VK + this universe's genesis + the
    // final state that encodes the WIN (here, the fold's genuine endpoints).
    let anchor = ProofAnchor::new(vk, att.genesis_root, att.final_root);
    let u = proof_universe("The Descent — Proof Board", anchor);
    let id = u.id();
    let mut reg = Registry::new();
    reg.publish(u);

    // ── ACCEPT + RANK, in O(1), WITHOUT posting the moves ──
    let accepted = reg
        .submit_proof(ProofCompletion {
            universe: id,
            player: "ada".into(),
            proof_bytes: proof_bytes.clone(),
            claimed_turns: att.num_turns,
        })
        .expect("the light client must ACCEPT the honest fold proof and rank it");
    assert_eq!(accepted.turns, 3);
    assert_eq!(accepted.rank, 1, "the sole entry ranks first");

    // THE PRIVACY: the accepted entry stores NO moves — only the proof + attested publics.
    let board = reg.leaderboard(id);
    assert_eq!(board.len(), 1);
    let entry = board[0];
    assert!(entry.is_proof_backed(), "entry is proof-backed");
    assert!(
        !entry.has_moves(),
        "a proof entry stores NO moves (the privacy)"
    );
    assert!(
        entry.playthrough().is_none(),
        "no playthrough is recoverable from a proof entry — the moves are not posted"
    );
    assert!(
        entry.proof_bytes().is_some(),
        "the proof envelope IS stored"
    );
    assert_eq!(
        entry.attested().expect("attested publics stored").num_turns,
        3
    );

    // reverify_entry re-runs the O(1) LIGHT CLIENT (not a replay).
    let t = reg
        .reverify_entry(id, &accepted.completion_id)
        .expect("a proof entry re-verifies via the light client");
    assert_eq!(t, 3);

    // ── FORGERY (non-vacuous — the honest one was just accepted): relabel final_root ──
    let mut env = WholeChainProofBytes::from_postcard(&proof_bytes).expect("envelope decodes");
    env.final_root[0] = env.final_root[0].wrapping_add(1); // a spliced final root
    let tampered = env.to_postcard();
    let verdict = reg.submit_proof(ProofCompletion {
        universe: id,
        player: "mallory".into(),
        proof_bytes: tampered,
        claimed_turns: att.num_turns,
    });
    assert!(
        matches!(verdict, Err(RejectReason::ProofRejected(_))),
        "a relabeled final_root must be REJECTED by the light client; got {verdict:?}"
    );
    assert_eq!(
        reg.leaderboard(id).len(),
        1,
        "the forged submission added nothing to the board"
    );

    // ── the WIN-PREDICATE binding bites: an honest proof whose final root is not the
    //    universe's declared WIN anchor is refused (the proof-path DidNotWin). ──
    let wrong_win = proof_universe(
        "Wrong Win Anchor",
        ProofAnchor::new(vk, att.genesis_root, bump0(att.final_root)),
    );
    let vw = verify_proof_completion(
        &wrong_win,
        &ProofCompletion {
            universe: wrong_win.id(),
            player: "ada".into(),
            proof_bytes: proof_bytes.clone(),
            claimed_turns: att.num_turns,
        },
    );
    assert!(
        matches!(vw, Err(RejectReason::WinNotProven)),
        "a proof that does not reach the declared win root must be refused; got {vw:?}"
    );

    // ── the GENESIS binding bites: a proof attesting a different universe's genesis. ──
    let wrong_gen = proof_universe(
        "Wrong Genesis Anchor",
        ProofAnchor::new(vk, bump0(att.genesis_root), att.final_root),
    );
    let vg = verify_proof_completion(
        &wrong_gen,
        &ProofCompletion {
            universe: wrong_gen.id(),
            player: "ada".into(),
            proof_bytes: proof_bytes.clone(),
            claimed_turns: att.num_turns,
        },
    );
    assert!(
        matches!(vg, Err(RejectReason::GenesisMismatch)),
        "a proof attesting a different genesis must be refused; got {vg:?}"
    );

    // ── the RESULT binding bites: a lied turn count on an otherwise-honest proof. ──
    let honest = proof_universe(
        "Honest Result Board",
        ProofAnchor::new(vk, att.genesis_root, att.final_root),
    );
    let vr = verify_proof_completion(
        &honest,
        &ProofCompletion {
            universe: honest.id(),
            player: "ada".into(),
            proof_bytes: proof_bytes.clone(),
            claimed_turns: att.num_turns + 1, // a lie
        },
    );
    assert!(
        matches!(vr, Err(RejectReason::ResultMismatch { .. })),
        "a lied turn count must be refused; got {vr:?}"
    );

    // ── a REPLAY-ONLY universe (no anchor) refuses a proof submission. ──
    let mut reg2 = Registry::new();
    let replay_only =
        Universe::authored("Replay Only", "author", PROOF_SCENE, WinCondition::ended())
            .expect("valid replay-only universe");
    let rid = replay_only.id();
    reg2.publish(replay_only);
    let vn = reg2.submit_proof(ProofCompletion {
        universe: rid,
        player: "ada".into(),
        proof_bytes: proof_bytes.clone(),
        claimed_turns: att.num_turns,
    });
    assert!(
        matches!(vn, Err(RejectReason::NotProofBacked)),
        "a universe without a proof anchor must refuse a proof completion; got {vn:?}"
    );

    eprintln!(
        "ZK-LEADERBOARD ACCEPT: verify_history_bytes(real 3-turn fold) OK; ranked #{} with \
         NO moves stored; relabeled proof REJECTED; win/genesis/result bindings all bite.",
        accepted.rank
    );
}
