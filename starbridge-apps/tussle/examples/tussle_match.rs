//! A runnable headless TUSSLE match — `cargo run -p starbridge-tussle --example tussle_match`.
//!
//! Plays a short SCRIPTED match, printing each frame's commit → reveal → deterministic resolution,
//! the running score (read from the VERIFIED ledger), and the verified outcome. Then re-runs the
//! exact script to witness REPRODUCIBILITY (same moves → same outcome). Every frame's score move is
//! a 2-party JOINT TURN folded through the verified per-asset executor (atomic + conserving + linked
//! to the real Lean export leg-by-leg).

use starbridge_tussle::resolution::SCORE_BANK;
use starbridge_tussle::{
    Figure, JointState, JointVector, Match, MatchEnd, MoveCommit, REST_POSE, SCORE_ASSET,
};

const P0: u8 = 10; // "Blue"
const P1: u8 = 11; // "Red"

/// A pose with `k` Contract joints (push), the rest Relax.
fn push(k: usize) -> JointVector {
    let mut v = REST_POSE;
    for slot in v.iter_mut().take(k) {
        *slot = JointState::Contract;
    }
    v
}

/// A defensive pose: `h` Hold joints (brace), the rest Contract (counter-push).
fn guard(h: usize) -> JointVector {
    let mut v = [JointState::Contract; 4];
    for slot in v.iter_mut().take(h) {
        *slot = JointState::Hold;
    }
    v
}

/// Pretty-print one joint vector as the figure's stance.
fn show_pose(v: &JointVector) -> String {
    v.iter()
        .map(|j| match j {
            JointState::Relax => "·",
            JointState::Contract => ">",
            JointState::Hold => "#",
            JointState::Extend => "<",
        })
        .collect::<Vec<_>>()
        .join("")
}

fn label(id: u8) -> &'static str {
    if id == P0 { "Blue" } else { "Red " }
}

/// Play and narrate a scripted match. Returns the final `(score0, score1, frames)` for the
/// reproducibility check.
fn play_and_narrate(script: &[(JointVector, JointVector)], announce: bool) -> (i128, i128, usize) {
    // Target 5 points, frame cap 12, figures spawn 2 apart.
    let mut m = Match::new(P0, P1, 2, 5, 12);

    if announce {
        println!("═══════════════════════════════════════════════════════════════");
        println!(" TUSSLE — a Toribash-style verified joint-combat match");
        println!("   Blue (cell {P0}) vs Red (cell {P1})   ·   first to 5 points");
        println!("   joints: · Relax  > Contract(pull)  # Hold(brace)  < Extend(push)");
        println!("   each frame: COMMIT (sealed) → REVEAL → resolve = a verified joint turn");
        println!("═══════════════════════════════════════════════════════════════");
        println!(
            "   score asset column 0x{:02x}.. · neutral score-bank = cell 0x{SCORE_BANK:02x}",
            SCORE_ASSET[0]
        );
        println!(
            "   start: Blue@{}  Red@{}   bank holds {} pts",
            m.f0.position(),
            m.f1.position(),
            m.ledger.get(SCORE_BANK, &SCORE_ASSET),
        );
        println!();
    }

    for (i, (a, b)) in script.iter().enumerate() {
        if m.outcome().is_some() {
            break;
        }
        // Each player builds a SEALED move (a fresh nonce blinds the joints — fog-of-war).
        let nonce0 = 0x1000 + i as u64;
        let nonce1 = 0x2000 + i as u64;
        let m0 = MoveCommit::new(P0, *a, nonce0);
        let m1 = MoveCommit::new(P1, *b, nonce1);

        if announce {
            // COMMIT phase: the opponent sees only the 32-byte seal — the joints are fog.
            let s0 = m0.seal();
            let s1 = m1.seal();
            println!("── Frame {i} ──────────────────────────────────────────────────");
            println!(
                "  COMMIT  Blue seal {:02x}{:02x}{:02x}{:02x}…   Red seal {:02x}{:02x}{:02x}{:02x}…  (joints hidden)",
                s0[0], s0[1], s0[2], s0[3], s1[0], s1[1], s1[2], s1[3],
            );
        }

        // RESOLVE the frame — the verified 2-party joint turn.
        match m.play_frame(m0, m1) {
            Ok(res) => {
                if announce {
                    println!(
                        "  REVEAL  Blue {} (drive {})   Red {} (drive {})",
                        show_pose(a),
                        starbridge_tussle::resolution::forward_drive(a),
                        show_pose(b),
                        starbridge_tussle::resolution::forward_drive(b),
                    );
                    match res.contact {
                        Some(c) => println!(
                            "  RESOLVE contact! {} strikes {} for {} pt(s)   → positions Blue@{} Red@{}",
                            label(c.striker).trim(),
                            label(c.struck).trim(),
                            c.points,
                            res.new_positions.0,
                            res.new_positions.1,
                        ),
                        None => println!(
                            "  RESOLVE no decisive contact (clash cancels / out of range)   → positions Blue@{} Red@{}",
                            res.new_positions.0, res.new_positions.1
                        ),
                    }
                    println!(
                        "  SCORE   Blue {} — Red {}   (verified ledger; supply conserved at {})",
                        m.score0(),
                        m.score1(),
                        m.ledger.total_asset(&SCORE_ASSET),
                    );
                    println!();
                }
            }
            Err(e) => {
                eprintln!("  frame {i} rejected by the verified executor: {e}");
                break;
            }
        }
    }

    if announce {
        match m.outcome() {
            Some(MatchEnd::TargetReached(w)) => {
                println!("🏆 KNOCKOUT — {} reaches the target. Final {} — {}.", label(w).trim(), m.score0(), m.score1());
            }
            Some(MatchEnd::FrameCap(Some(w))) => {
                println!("⏱  frame cap — {} leads. Final {} — {}.", label(w).trim(), m.score0(), m.score1());
            }
            Some(MatchEnd::FrameCap(None)) => {
                println!("⏱  frame cap — a draw at {} — {}.", m.score0(), m.score1());
            }
            None => println!("(match still in progress — script exhausted)"),
        }
        println!(
            "   point supply conserved across the whole match: {} (never minted/burned).",
            m.ledger.total_asset(&SCORE_ASSET)
        );
    }

    (m.score0(), m.score1(), m.log.len())
}

fn main() {
    // A scripted bout: Blue presses, Red defends then counters, a cancelled clash, a finisher.
    let script: [(JointVector, JointVector); 8] = [
        (push(3), guard(2)),  // Blue pushes 3, Red braces 2 + counters 2 → Red's brace blunts Blue
        (push(3), push(1)),   // Blue out-pushes → Blue scores
        (push(2), push(2)),   // even clash — cancels, no score
        (push(3), guard(1)),  // Blue pushes 3, Red braces 1 + pushes 3 → Red counters
        (push(4), push(1)),   // Blue all-in push → Blue scores big
        (push(3), push(1)),   // Blue presses → Blue scores
        (push(1), push(3)),   // Red surges → Red scores
        (push(4), push(0)),   // Blue finisher
    ];

    let (s0, s1, frames) = play_and_narrate(&script, true);

    // ── Reproducibility: replay the EXACT script; the outcome must be byte-identical. ──
    println!();
    println!("── reproducibility check ─────────────────────────────────────");
    let replay = play_and_narrate(&script, false);
    let same = replay == (s0, s1, frames);
    println!(
        "  run 1: score {s0}—{s1} over {frames} frames   run 2: score {}—{} over {} frames",
        replay.0, replay.1, replay.2
    );
    println!(
        "  same moves → same outcome: {}",
        if same { "YES ✓ (deterministic + reproducible)" } else { "NO ✗" }
    );
    assert!(same, "the deterministic resolution was not reproducible");

    // ── A spot-check that the typed-`sym` enum tooth + fog-of-war are real, printed for the demo. ──
    println!();
    println!("── teeth (spot-check) ────────────────────────────────────────");
    // Enum tooth: a figure's joint program refuses an out-of-enum joint slot.
    {
        use dregg_cell::field_from_u64;
        let old = Figure::spawn(P0, 0).cell;
        let mut bad = old.clone();
        bad.set_field(0, field_from_u64(7)); // sym 7 ∉ {Relax,Contract,Hold,Extend}
        let refused = Figure::joint_program().evaluate(&bad, Some(&old), None).is_err();
        println!(
            "  typed-sym enum tooth: out-of-enum joint (sym 7) refused by the cell program: {}",
            if refused { "YES ✓" } else { "NO ✗" }
        );
        assert!(refused);
    }
    // Fog-of-war: the seal of a different guess does not match the true seal.
    {
        let truth = MoveCommit::new(P1, push(3), 0xC0FFEE);
        let seal = truth.seal();
        let wrong = MoveCommit::new(P1, push(2), 0xC0FFEE).seal(); // changed joints
        println!(
            "  fog-of-war: a different joint guess yields a different seal (move unreadable): {}",
            if wrong != seal { "YES ✓" } else { "NO ✗" }
        );
        assert_ne!(wrong, seal);
    }
    println!();
    println!("done — every score move above settled through the verified per-asset executor.");
}
