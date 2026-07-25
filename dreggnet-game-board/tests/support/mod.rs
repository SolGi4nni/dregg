//! Shared test support: a REAL folded whole-history proof + its true VK anchor.
//!
//! The fast board tests exercise the board's O(1) accept-path, its forgery refusal, and its
//! anchor binding. Those are properties of the PROOF-CARRYING BOARD and need a genuine
//! `WholeChainProof` — but folding one is minutes-to-hours, so the fast lane never folds.
//!
//! Source order (both are REAL artifacts of the deployed prover; neither is a stub):
//!
//! 1. `tests/fixtures/<game>_match_proof.bin` (+ `.hex`) — a proof BAKED BY THIS CRATE'S
//!    slow end-to-end lane (`--ignored`): a real PLAYED multiway-tug / automatafl match,
//!    folded. When present, the fast lane's board tests run against the game's OWN match
//!    proof.
//! 2. `../ugc-dregg/tests/fixtures/whole_history_proof.bin` (+ anchor) — the in-tree real
//!    3-turn recursive fold the proof-carrying board's own test suite drives. Used when the
//!    game fixture has not been baked on this machine. It is a genuine artifact of the same
//!    prover and the same envelope format; what it is NOT is a *game match*, which is exactly
//!    why the game-match fold is driven end-to-end in the slow lane.

#![allow(dead_code)] // each test binary uses a subset of these helpers

use std::path::{Path, PathBuf};

use dregg_circuit_prove::ivc_turn_chain::{RecursionVk, WholeChainProofBytes};
use dreggnet_game_board::Game;

/// A real proof envelope + the anchor VK it verifies under, and where it came from.
pub struct RealProof {
    pub bytes: Vec<u8>,
    pub vk: RecursionVk,
    pub source: String,
}

fn parse_hex32(s: &str) -> [u8; 32] {
    let s = s.trim();
    assert_eq!(s.len(), 64, "anchor must be 32 bytes (64 hex chars)");
    core::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).expect("hex"))
}

pub fn hex32(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn manifest() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// The path a baked game-match fixture lives at.
pub fn fixture_paths(game: Game) -> (PathBuf, PathBuf) {
    let dir = manifest().join("tests/fixtures");
    (
        dir.join(format!("{}_match_proof.bin", game.slug())),
        dir.join(format!("{}_match_anchor.hex", game.slug())),
    )
}

fn load(bin: &Path, hex: &Path, source: &str) -> Option<RealProof> {
    let bytes = std::fs::read(bin).ok()?;
    let anchor = std::fs::read_to_string(hex).ok()?;
    // The fixture FILE exists, so it must decode under HEAD's `WholeChainProof` envelope. A
    // present-but-stale fixture (baked under an older envelope layout — e.g. before the v5
    // board-window / v3 8-felt-anchor bumps) is a LOUD, actionable failure with the exact
    // re-bake command — never the confusing mid-test `EnvelopeDecode{"Hit the end of buffer"}`
    // panic that reads like an anti-forgery/anchor-binding regression and silently disables the
    // light-client security teeth these tests carry.
    if let Err(e) = WholeChainProofBytes::from_postcard(&bytes) {
        panic!(
            "STALE FIXTURE: {} does not decode under HEAD's WholeChainProof envelope ({e}). \
             Re-bake it (the envelope format evolved): \
             `DREGG_ALLOW_UNAUDITED_PQ=1 cargo run --release -p dregg-lightclient \
             --bin produce_history_envelope --features prover -- 3 7`, then base64-decode the \
             emitted `proof_bytes_b64` into {} and write `anchor_hex` (no trailing newline) to {}.",
            bin.display(),
            bin.display(),
            hex.display(),
        );
    }
    Some(RealProof {
        bytes,
        vk: RecursionVk(parse_hex32(&anchor)),
        source: source.to_string(),
    })
}

/// A REAL proof for `game`: the baked game-match fold if it exists, else the in-tree real
/// whole-history fold artifact. Panics if neither is available (the board tests are not
/// runnable without a genuine proof — we never substitute a stub).
pub fn real_proof(game: Game) -> RealProof {
    let (bin, hex) = fixture_paths(game);
    if let Some(p) = load(&bin, &hex, &format!("BAKED {} MATCH FOLD", game.slug())) {
        return p;
    }
    let ugc = manifest().join("../ugc-dregg/tests/fixtures");
    load(
        &ugc.join("whole_history_proof.bin"),
        &ugc.join("whole_history_anchor.hex"),
        "in-tree real 3-turn whole-history fold (ugc-dregg fixture)",
    )
    .expect("a real WholeChainProof artifact must be available to drive the board")
}
