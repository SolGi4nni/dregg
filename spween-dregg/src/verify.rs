//! # Playthrough re-verification — the un-retconnable receipt chain
//!
//! A [`Playthrough`] is a *provable* record of which choices were made, in order. Three
//! independent teeth make it un-retconnable:
//!
//! 1. **Chain linkage** ([`verify_chain_linkage`]) — the recorded receipts form a
//!    hash chain: each turn's `pre_state_hash` equals its predecessor's
//!    `post_state_hash`, every `turn_hash` is real and distinct. Splicing, dropping,
//!    reordering, or tampering a receipt breaks the link. Pure — no re-execution.
//!
//! 2. **Receipt hash** ([`verify_receipt_hash_chain`]) — each receipt's recorded
//!    `previous_receipt_hash` must equal the RECOMPUTED
//!    [`dregg_app_framework::TurnReceipt::receipt_hash`] of
//!    its predecessor. This is the only tooth here that reads a receipt's *whole* body:
//!    `receipt_hash` (domain `dregg-receipt-v5`) folds in `effects_hash`,
//!    `emitted_events`, `computrons_used`, `consumed_capabilities`, and the rest. Teeth
//!    1 and 3 both look only at the two state hashes, so a **state-passthrough** field —
//!    an [`Effect::EmitEvent`](dregg_app_framework::Effect) mutates no cell field, hence
//!    moves neither state hash — is invisible to them. Editing an emitted event is
//!    exactly that kind of edit, and it is what this tooth sees.
//!
//! 3. **Replay** ([`verify_by_replay`]) — re-drive a *fresh, identically-seeded*
//!    world-cell through the recorded choice sequence and confirm it reproduces the
//!    exact committed slot state at every step, in passage order. A forged choice (an
//!    ineligible pick) is *refused by the real executor* on replay; an altered record
//!    diverges from the reproduced state. Because the world identity is deterministic
//!    in the scene id + seed, the reproduction is exact and timestamp-independent.
//!
//! [`verify`] runs all three. A tampered or forged playthrough fails.
//!
//! ## What tooth 2 does NOT cover — the head receipt
//!
//! `previous_receipt_hash` is a BACKWARD link, so receipt `n-1` (the head) has nothing
//! after it to commit to its body. An edit confined to the last receipt's events, with
//! its state hashes left alone, passes all three teeth. Closing that needs an anchor
//! *outside* the record: [`verify_receipts_anchored`] looks every receipt up in the
//! issuing executor's own chain by recomputed hash, which covers the head as well —
//! but it needs the live world, so it is a separate entry point rather than part of
//! [`verify`] (which is deliberately callable against a fresh replay-only world).

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
    /// Receipt `index` records no `previous_receipt_hash`, so its predecessor's body is
    /// uncommitted — the chain is severed even though the state hashes may still line up.
    ReceiptHashAbsent { index: usize },
    /// Receipt `index`'s recorded `previous_receipt_hash` does not equal the RECOMPUTED
    /// `receipt_hash()` of receipt `index - 1`: some field of that predecessor (its
    /// emitted events, effects hash, computron count, …) has been altered since it was
    /// issued.
    ReceiptHashMismatch { index: usize },
    /// Receipt `index` is not in the issuing executor's own chain under its recomputed
    /// `receipt_hash()` — the executor never issued this exact receipt body.
    ReceiptUnanchored { index: usize },
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
            VerifyBreak::ReceiptHashAbsent { index } => {
                write!(
                    f,
                    "receipt {index} records no previous_receipt_hash: its predecessor's body is uncommitted"
                )
            }
            VerifyBreak::ReceiptHashMismatch { index } => {
                write!(
                    f,
                    "receipt {index} does not commit to the recomputed receipt_hash of receipt {}: that receipt's body was altered after issue",
                    index.saturating_sub(1)
                )
            }
            VerifyBreak::ReceiptUnanchored { index } => {
                write!(
                    f,
                    "receipt {index} is not in the executor's own chain under its recomputed receipt_hash"
                )
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
    // Dedup turn hashes through a `HashSet` (O(n)) rather than a `Vec::contains` scan
    // (O(n²)). `insert` returns `false` on a duplicate — the same first-duplicate detection,
    // and the linkage/zero-hash checks stay in receipt order.
    let mut seen: std::collections::HashSet<[u8; 32]> = std::collections::HashSet::new();
    for (i, r) in receipts.iter().enumerate() {
        if r.turn_hash == [0u8; 32] {
            return Err(VerifyBreak::ZeroTurnHash { index: i });
        }
        if !seen.insert(r.turn_hash) {
            return Err(VerifyBreak::DuplicateTurnHash { index: i });
        }
        if i > 0 && r.pre_state_hash != receipts[i - 1].post_state_hash {
            return Err(VerifyBreak::LinkageBroken { index: i });
        }
    }
    Ok(())
}

/// **Receipt-hash tooth.** Recompute every receipt's
/// [`receipt_hash`](dregg_app_framework::TurnReceipt::receipt_hash) and check that its successor's recorded
/// `previous_receipt_hash` is exactly that value.
///
/// This is the tooth that reads a receipt's WHOLE body. [`verify_chain_linkage`] and
/// [`verify_by_replay`] both compare only state: the pre/post state hashes and the
/// reproduced slot vector. A field that carries no state — the canonical case being
/// `emitted_events`, produced by `Effect::EmitEvent`, which mutates no cap-gated cell
/// field — moves neither state hash, so both of those teeth are blind to it by
/// construction. `receipt_hash` (domain `dregg-receipt-v5`) folds in `emitted_events`
/// (prefix-free, felt-counted), `effects_hash`, `computrons_used`, `action_count`,
/// `consumed_capabilities`, `derivation_records`, `was_encrypted`, `was_burn`, and the
/// rest, so any edit to any of them breaks the link recorded by the NEXT receipt.
///
/// ## Honest scope
///
/// * The link is BACKWARD. Receipt `n-1` (the head) has no successor committing to it,
///   so an edit confined to the head's non-state fields survives this tooth. Use
///   [`verify_receipts_anchored`] against the issuing world to cover it.
/// * `previous_receipt_hash` is itself a recorded field, so this is INTERNAL
///   consistency of the record — it catches an edit, not a wholesale re-forge by
///   someone able to recompute every downstream hash. What makes a re-forge fail is the
///   other two teeth (the executor refuses an ineligible choice on replay; the state
///   chain must reproduce), plus, where available, the executor anchor.
/// * Receipt 0 (genesis) is not checked here: its `previous_receipt_hash` points at the
///   world's deploy turn, which is not part of the [`Playthrough`].
pub fn verify_receipt_hash_chain(playthrough: &Playthrough) -> Result<(), VerifyBreak> {
    let receipts = playthrough.receipts();
    for i in 1..receipts.len() {
        let Some(recorded) = receipts[i].previous_receipt_hash else {
            return Err(VerifyBreak::ReceiptHashAbsent { index: i });
        };
        if recorded != receipts[i - 1].receipt_hash() {
            return Err(VerifyBreak::ReceiptHashMismatch { index: i });
        }
    }
    Ok(())
}

/// **Executor-anchor tooth.** Every recorded receipt — the head included — must be
/// present in `issuing_world`'s own authoritative receipt chain under its RECOMPUTED
/// [`receipt_hash`](dregg_app_framework::TurnReceipt::receipt_hash).
///
/// [`verify_receipt_hash_chain`] can only ever check receipts against each other, which
/// leaves the head's body uncommitted. This resolves that against something outside the
/// record: the executor's immutable chain (`WorldCell::receipt_by_hash`). A record whose
/// last receipt had its emitted events edited hashes to a value the executor never
/// issued, so the lookup misses.
///
/// `issuing_world` must be the LIVE world that produced the record, not the fresh
/// replay-only world [`verify_by_replay`] deploys — a fresh executor has issued none of
/// these receipts and every lookup would miss. That is why this is not folded into
/// [`verify`], which is deliberately usable with nothing but a seed and a scene.
///
/// ## Honest scope — this anchors a RECORD, not a HOST
///
/// The chain it consults is the in-process executor's own. That makes it a real check on a
/// record that was serialized, transmitted, and handed back edited — the case
/// [`crate::Playthrough`] exists for — and no check at all on a host that controls the
/// executor, which controls both sides of the comparison. Anchoring against a party that
/// cannot be the forger needs an external commitment (a federation node's receipt, an
/// executor signature verified under a pinned key); this is the in-process floor beneath
/// that, not a substitute for it.
pub fn verify_receipts_anchored(
    issuing_world: &WorldCell,
    playthrough: &Playthrough,
) -> Result<(), VerifyBreak> {
    for (i, receipt) in playthrough.receipts().iter().enumerate() {
        if issuing_world
            .receipt_by_hash(receipt.receipt_hash())
            .is_none()
        {
            return Err(VerifyBreak::ReceiptUnanchored { index: i });
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
        // Advance by the recorded choice — a forged/ineligible pick is refused here. A
        // collective step re-pins its recorded certified-decision commitment in the SAME
        // turn (so the reproduced state, including DECISION_EXT_KEY, matches the record);
        // the certified-winner tooth (`verify_collective_certified`) checks that
        // commitment against the round's certified winner separately.
        let advanced = match step.decision_commitment {
            Some(commitment) => driver.advance_certified(step.choice_index, commitment),
            None => driver.advance(step.choice_index),
        }
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

/// **Full verification** — all three record-only teeth. Returns `Ok(())` iff the
/// playthrough is authentic: an un-retconnable receipt chain, whose receipt bodies are
/// the ones the chain committed to, that reproduces exactly on replay.
///
/// Add [`verify_receipts_anchored`] when the issuing world is in hand; it is the only
/// tooth that covers the head receipt's body.
pub fn verify(
    fresh_world: WorldCell,
    scene: &Scene,
    playthrough: &Playthrough,
) -> Result<(), VerifyBreak> {
    verify_chain_linkage(playthrough)?;
    verify_receipt_hash_chain(playthrough)?;
    verify_by_replay(fresh_world, scene, playthrough)
}
