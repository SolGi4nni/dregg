//! **The one seat every driven surface sits in.**
//!
//! Deliberately small and deliberately NOT a renderer: each impl reaches its platform's OWN
//! projection and its OWN router. There is no shared "render a ViewNode" here, because a shared
//! renderer is exactly the mirror that would make every finding a finding about this crate.

use crate::out::{Control, Frame};

/// A driven surface: a real session, a real projection, one command at a time.
pub trait DrivenSurface {
    /// A one-line account of WHAT IS REAL here and what is not — printed at startup and
    /// re-printed by `where`. This is where a surface admits an unreachable inch.
    fn provenance(&self) -> String;

    /// Open (or join) the offering in this surface's slot.
    fn open(&mut self) -> Frame;

    /// **Re-request the surface** without acting — "show it to me again". On a chat surface this
    /// is the invocation that discovers whether a re-present REPOSTS or EDITS.
    fn again(&mut self) -> Frame;

    /// Press the `index`th control of the CURRENT frame.
    fn press(&mut self, index: usize) -> Frame;

    /// Press the `index`th control of the PREVIOUS frame — a control still on the user's screen
    /// but no longer the current one. A stale press must be legibly refused or legibly land;
    /// an illegible refusal is a defect and can only be found by trying.
    fn press_stale(&mut self, index: usize) -> Frame;

    /// Fire a raw `(turn, arg)` — precision, and the way to drive a payload the surface never
    /// offered (an out-of-range arg, a verb from another phase).
    fn act(&mut self, turn: &str, arg: i64) -> Frame;

    /// Free text / a slash command. Chat surfaces route it; others say they have no such channel.
    fn send(&mut self, text: &str) -> Frame;

    /// **Switch who is looking, WITHOUT resetting state.** Does not re-request — the caller
    /// re-requests and diffs, so the fog comparison is explicit.
    fn become_viewer(&mut self, who: &str) -> Frame;

    /// **Rebuild the host from the durable store**, exactly as a redeploy would: in-memory
    /// indices are gone, the durable move-log is not, and whatever was already on the user's
    /// screen is still on the user's screen.
    fn restart(&mut self) -> Frame;

    /// Re-verify the committed chain through this surface's own verify path.
    fn verify(&mut self) -> Frame;

    /// The controls of the current frame (for the fog diff, without re-issuing a command).
    fn controls(&self) -> Vec<Control>;

    /// Who is looking, by the name the driver knows them as.
    fn viewer(&self) -> String;
}

/// A deterministic 64-bit handle for a viewer NAME — a stable synthetic Telegram user id, so
/// `--as alice` is the same person on every run and across a restart. FNV-1a, offset into a
/// plausible id range. Deterministic identity is the point; cryptographic quality is not.
pub fn uid_of(name: &str) -> u64 {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in name.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100_0000_01b3);
    }
    1_000_000 + (hash % 900_000_000)
}
