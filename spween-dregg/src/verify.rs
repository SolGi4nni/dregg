//! # Playthrough re-verification — the un-retconnable receipt chain
//!
//! A [`Playthrough`] is a *provable* record of which choices were made, in order. Two
//! independent teeth make it un-retconnable:
//!
//! 1. **Chain linkage** ([`verify_chain_linkage`]) — the recorded receipts form a
//!    hash chain: each turn's `pre_state_hash` equals its predecessor's
//!    `post_state_hash`, every `turn_hash` is real and distinct. Splicing, dropping,
//!    reordering, or tampering a receipt breaks the link. Pure — no re-execution.
//!
//! 2. **Replay** ([`verify_by_replay`]) — re-drive a *fresh, identically-seeded*
//!    world-cell through the recorded choice sequence and confirm it reproduces the
//!    exact committed slot state at every step, in passage order. A forged choice (an
//!    ineligible pick) is *refused by the real executor* on replay; an altered record
//!    diverges from the reproduced state. Because the world identity is deterministic
//!    in the scene id + seed, the reproduction is exact and timestamp-independent.
//!
//! [`verify`] runs both. A tampered or forged playthrough fails.

use spween::Scene;

use crate::world::{Driver, Playthrough, WorldCell};

/// A specific way a playthrough failed verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyBreak {
    /// Receipt `index` does not link to its predecessor (`pre != prev.post`).
    LinkageBroken { index: usize },
    /// A receipt carries a zero (absent) turn hash — not a genuine committed turn.
    ZeroTurnHash { index: usize },
    /// Two receipts share a turn hash (a replayed/duplicated turn).
    DuplicateTurnHash { index: usize },
    /// On replay, the scene ended before all recorded steps were consumed.
    RanShort { at_step: usize },
    /// A recorded step's passage does not match where the replay actually is (a
    /// reordered / spliced record).
    PassageOutOfOrder {
        step: usize,
        recorded: String,
        actual: String,
    },
    /// The real executor REFUSED the recorded choice on replay (a forged/ineligible
    /// pick that never could have committed).
    RefusedOnReplay { step: usize, why: String },
    /// The reproduced world-cell state diverges from the recorded state at a step
    /// (`genesis` = the genesis snapshot).
    StateMismatch { step: StepPos },
}

/// Which snapshot mismatched.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StepPos {
    /// The genesis snapshot.
    Genesis,
    /// Choice-step `index`.
    Step(usize),
}

impl std::fmt::Display for VerifyBreak {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VerifyBreak::LinkageBroken { index } => {
                write!(
                    f,
                    "receipt chain broken at index {index} (pre != prev.post)"
                )
            }
            VerifyBreak::ZeroTurnHash { index } => {
                write!(f, "receipt {index} has a zero turn hash")
            }
            VerifyBreak::DuplicateTurnHash { index } => {
                write!(f, "receipt {index} duplicates an earlier turn hash")
            }
            VerifyBreak::RanShort { at_step } => {
                write!(f, "scene ended on replay before step {at_step}")
            }
            VerifyBreak::PassageOutOfOrder {
                step,
                recorded,
                actual,
            } => write!(
                f,
                "step {step} recorded at `{recorded}` but replay is at `{actual}`"
            ),
            VerifyBreak::RefusedOnReplay { step, why } => {
                write!(f, "step {step} refused on replay: {why}")
            }
            VerifyBreak::StateMismatch { step } => {
                write!(f, "reproduced state diverges at {step:?}")
            }
        }
    }
}

impl std::error::Error for VerifyBreak {}

/// **Chain-linkage tooth.** The recorded receipts must form an unbroken hash chain
/// and each name a genuine, distinct committed turn.
pub fn verify_chain_linkage(playthrough: &Playthrough) -> Result<(), VerifyBreak> {
    let receipts = playthrough.receipts();
    let mut seen: Vec<[u8; 32]> = Vec::new();
    for (i, r) in receipts.iter().enumerate() {
        if r.turn_hash == [0u8; 32] {
            return Err(VerifyBreak::ZeroTurnHash { index: i });
        }
        if seen.contains(&r.turn_hash) {
            return Err(VerifyBreak::DuplicateTurnHash { index: i });
        }
        seen.push(r.turn_hash);
        if i > 0 && r.pre_state_hash != receipts[i - 1].post_state_hash {
            return Err(VerifyBreak::LinkageBroken { index: i });
        }
    }
    Ok(())
}

/// **Replay tooth.** Re-drive `fresh_world` (a freshly-deployed, identically-seeded
/// world-cell) through the recorded choice sequence and confirm every step reproduces
/// the recorded committed state in passage order. `fresh_world` must be deployed from
/// the same `scene` and seed (and seeded with the same pre-play vars) as the original.
pub fn verify_by_replay(
    fresh_world: WorldCell,
    scene: &Scene,
    playthrough: &Playthrough,
) -> Result<(), VerifyBreak> {
    let mut driver =
        Driver::start(fresh_world, scene).map_err(|e| VerifyBreak::RefusedOnReplay {
            step: 0,
            why: e.to_string(),
        })?;

    // Genesis must reproduce.
    if driver.world().snapshot() != playthrough.genesis_state {
        return Err(VerifyBreak::StateMismatch {
            step: StepPos::Genesis,
        });
    }

    for (i, step) in playthrough.steps.iter().enumerate() {
        // Causal order: replay must be at the recorded passage before advancing.
        match driver.current_passage() {
            None => return Err(VerifyBreak::RanShort { at_step: i }),
            Some(actual) if actual != step.passage => {
                return Err(VerifyBreak::PassageOutOfOrder {
                    step: i,
                    recorded: step.passage.clone(),
                    actual,
                });
            }
            Some(_) => {}
        }
        // Advance by the recorded choice — a forged/ineligible pick is refused here.
        let advanced =
            driver
                .advance(step.choice_index)
                .map_err(|e| VerifyBreak::RefusedOnReplay {
                    step: i,
                    why: e.to_string(),
                })?;
        if advanced.state != step.state {
            return Err(VerifyBreak::StateMismatch {
                step: StepPos::Step(i),
            });
        }
    }
    Ok(())
}

/// **Full verification** — both teeth. Returns `Ok(())` iff the playthrough is
/// authentic: an un-retconnable receipt chain that reproduces exactly on replay.
pub fn verify(
    fresh_world: WorldCell,
    scene: &Scene,
    playthrough: &Playthrough,
) -> Result<(), VerifyBreak> {
    verify_chain_linkage(playthrough)?;
    verify_by_replay(fresh_world, scene, playthrough)
}
