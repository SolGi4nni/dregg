//! THE PROOF-ATTACH + STARK VERIFICATION-STATUS VIEW.
//!
//! Every committed turn carries a verification posture. This module surfaces it
//! as an actionable view: for each turn in the provenance log, *what is the proof
//! status, and what can be attached/verified?* It extends
//! [`crate::reflect::reflect_proof_status`] (which projects a single receipt's
//! attestation surface) into the panel's WORKFLOW model: the verification tier, a
//! legible verdict, and the attach point.
//!
//! ## The three verification tiers (honest)
//!
//! A committed turn sits at one of three verification tiers, each REAL and
//! distinguished honestly (never inflated):
//!
//!   1. **Verified-by-construction** — the default in the embedded single-custody
//!      world. The producer IS this process, and `commit_turn` runs the REAL
//!      verified executor (`TurnExecutor::execute`), which enforces EVERY whole-
//!      turn guarantee (value conservation, no capability amplification, receipt-
//!      chain integrity, lifecycle invariants) inline. A turn that would violate a
//!      guarantee does not commit — so the receipt's EXISTENCE is the proof that
//!      the guarantees held. This is a real assurance, not a placeholder: it is
//!      exactly the assurance the federation's authoritative producer carries.
//!
//!   2. **Executor-signed (producer-attested)** — when a receipt carries the
//!      executor's Ed25519 signature over its hash (`executor_signature`), it is
//!      cryptographically bound to a known producer: a verifier can check the
//!      signature without re-executing, the federation-exit attestation surface.
//!
//!   3. **STARK-attached** — when a turn additionally carries an explicit
//!      `execution_proof` (a succinct STARK over the whole-turn statement), a
//!      light client can verify the turn's correctness with NO trust in the
//!      producer at all — the strongest tier. Producing one is the federated
//!      `dregg_sdk::full_turn_proof` lane (real `prove_full_turn`/
//!      `verify_full_turn`); it is HEAVY (succinct-proof generation), so it is a
//!      node/background act, NOT a per-turn cost in the embedded world. This view
//!      surfaces whether a turn carries such a proof + the attach point — it does
//!      NOT mint a multi-second STARK inside a panel build (that would be a UI
//!      mistake; the honest stance is to show the tier + the route to the next).
//!
//! The pale-ghost question (§5) for proofs: *can a light client be fooled about
//! whether a turn was verified?* The tiers answer it honestly — tier 1 binds the
//! operator's own re-execution, tier 2 binds a known producer's signature, tier 3
//! binds nothing but the math. The view never claims a higher tier than the
//! receipt actually carries.
//!
//! gpui-free + `cargo test`-able: built from the [`World`]'s receipt log; the
//! cockpit maps [`ProofBoard`] onto the OBJECTS panel's proof column + an
//! attach/verify affordance.

use dregg_turn::turn::{Finality, TurnReceipt};

use crate::reflect::{reflect_proof_status, Inspectable};
use crate::world::World;

/// The verification tier a committed turn sits at — honest, never inflated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerificationTier {
    /// The embedded verified executor enforced every guarantee inline; the
    /// receipt's existence is the proof (the federation-producer assurance).
    VerifiedByConstruction,
    /// The producer signed the receipt hash (Ed25519) — a known producer is
    /// cryptographically bound; a verifier checks the signature, not the re-exec.
    ExecutorSigned,
    /// An explicit STARK over the whole-turn statement rides the turn — a light
    /// client verifies with NO trust in the producer (the strongest tier).
    StarkAttached,
}

impl VerificationTier {
    /// A short operator-legible label.
    pub fn label(self) -> &'static str {
        match self {
            VerificationTier::VerifiedByConstruction => "verified-by-construction",
            VerificationTier::ExecutorSigned => "executor-signed",
            VerificationTier::StarkAttached => "STARK-attached",
        }
    }

    /// The tier's ordinal strength (higher = binds less trust in the producer).
    pub fn strength(self) -> u8 {
        match self {
            VerificationTier::VerifiedByConstruction => 1,
            VerificationTier::ExecutorSigned => 2,
            VerificationTier::StarkAttached => 3,
        }
    }

    /// The NEXT tier up, and the route to reach it (the honest "designed-pending"
    /// path) — `None` at the top tier.
    pub fn next_route(self) -> Option<&'static str> {
        match self {
            VerificationTier::VerifiedByConstruction => Some(
                "attach the executor's signature (producer attestation) — a known producer \
                 is bound; or attach a STARK for producer-free verification",
            ),
            VerificationTier::ExecutorSigned => Some(
                "attach a STARK (dregg_sdk::full_turn_proof::prove_full_turn, the federated \
                 lane) — a light client then verifies with NO trust in the producer",
            ),
            VerificationTier::StarkAttached => None,
        }
    }
}

/// The attach/verify status of a turn's proof — what is present and what a
/// verifier can do with it RIGHT NOW.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AttachStatus {
    /// No explicit proof attached; the assurance is the executor's inline
    /// enforcement (tier 1) and/or the producer signature (tier 2). A verifier
    /// re-executes (tier 1) or checks the signature (tier 2).
    NoExplicitProof,
    /// An `execution_proof` (STARK) is attached and ready to verify — a light
    /// client can check it against the turn's pre/post state commitment.
    StarkReadyToVerify,
}

impl AttachStatus {
    pub fn label(self) -> &'static str {
        match self {
            AttachStatus::NoExplicitProof => "no explicit proof (re-exec / signature)",
            AttachStatus::StarkReadyToVerify => "STARK attached — ready to verify",
        }
    }
}

/// One turn's proof status in the proof board — the actionable verification view.
#[derive(Clone, Debug)]
pub struct ProofEntry {
    /// The local chain height of this turn.
    pub height: u64,
    /// The turn's receipt hash (the provenance-chain link), short-form.
    pub receipt_short: String,
    /// The full receipt hash.
    pub receipt_hash: [u8; 32],
    /// The verification tier this turn sits at.
    pub tier: VerificationTier,
    /// The attach/verify status (what is present, what a verifier can do).
    pub attach: AttachStatus,
    /// The turn's finality (final / tentative).
    pub finality: Finality,
    /// The pre-state commitment (what the turn started from), short-form.
    pub pre_state_short: String,
    /// The post-state commitment (what the turn produced) — the STARK binds this.
    pub post_state_short: String,
    /// In-band disclosures bound into the receipt hash (a verifier sees these
    /// without learning the content): `was_burn`, `was_encrypted`.
    pub burn_disclosed: bool,
    pub encrypted: bool,
    /// The full reflective proof-status object (for the inspector drill-down).
    pub inspectable: Inspectable,
}

impl ProofEntry {
    /// A one-line operator summary of the proof posture.
    pub fn summary(&self) -> String {
        format!(
            "h{} · {} · {} · pre {} → post {}",
            self.height,
            self.tier.label(),
            self.attach.label(),
            self.pre_state_short,
            self.post_state_short,
        )
    }

    /// The route to the next-stronger tier (the honest "what can I attach next"),
    /// or `None` at the top.
    pub fn upgrade_route(&self) -> Option<&'static str> {
        self.tier.next_route()
    }
}

/// THE PROOF BOARD — the verification status of every committed turn, as an
/// actionable attach/verify view. Built from the [`World`]'s receipt log; the
/// cockpit maps it onto the OBJECTS panel's proof column.
#[derive(Clone, Debug)]
pub struct ProofBoard {
    /// One entry per committed turn (most-recent-first).
    pub entries: Vec<ProofEntry>,
    /// How many turns are verified-by-construction only (tier 1).
    pub by_construction: usize,
    /// How many turns carry a producer signature (tier 2+).
    pub signed: usize,
    /// How many turns carry an explicit STARK (tier 3).
    pub stark_attached: usize,
}

impl ProofBoard {
    /// Build the proof board from the live world: classify every committed turn's
    /// verification tier + attach status. `max` bounds how many recent turns to
    /// surface (most-recent-first); pass `usize::MAX` for all.
    pub fn build(world: &World, max: usize) -> Self {
        // Pair each receipt with its commit height via the dynamics stream.
        let events = world.dynamics().all();
        let mut entries: Vec<ProofEntry> = Vec::new();
        for r in world.receipts() {
            let height = height_of(events, r.receipt_hash()).unwrap_or(0);
            entries.push(classify(r, height));
        }
        // Most-recent-first.
        entries.reverse();

        let by_construction = entries
            .iter()
            .filter(|e| e.tier == VerificationTier::VerifiedByConstruction)
            .count();
        let signed = entries
            .iter()
            .filter(|e| e.tier.strength() >= VerificationTier::ExecutorSigned.strength())
            .count();
        let stark_attached = entries
            .iter()
            .filter(|e| e.tier == VerificationTier::StarkAttached)
            .count();

        entries.truncate(max);
        ProofBoard {
            entries,
            by_construction,
            signed,
            stark_attached,
        }
    }

    /// The number of turns on the board.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the board is empty (no committed turns yet).
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// Classify a receipt's verification tier + attach status (the honest tiering).
fn classify(r: &TurnReceipt, height: u64) -> ProofEntry {
    // Tier: STARK > signed > by-construction. The STARK rides the TURN (not the
    // receipt); a receipt produced from a turn carrying an `execution_proof` is
    // detectable here only via the producer-attested surface the receipt exposes.
    // In the embedded world the explicit STARK is the federated lane, so a
    // committed embedded turn is tier 1 (or tier 2 if the producer signed it).
    let signed = r.executor_signature.is_some();
    let stark = false; // the embedded receipt carries no inline STARK (federated lane)
    let tier = if stark {
        VerificationTier::StarkAttached
    } else if signed {
        VerificationTier::ExecutorSigned
    } else {
        VerificationTier::VerifiedByConstruction
    };
    let attach = if stark {
        AttachStatus::StarkReadyToVerify
    } else {
        AttachStatus::NoExplicitProof
    };
    ProofEntry {
        height,
        receipt_short: crate::reflect::short_hex(&r.receipt_hash()),
        receipt_hash: r.receipt_hash(),
        tier,
        attach,
        finality: r.finality,
        pre_state_short: crate::reflect::short_hex(&r.pre_state_hash),
        post_state_short: crate::reflect::short_hex(&r.post_state_hash),
        burn_disclosed: r.was_burn,
        encrypted: r.was_encrypted,
        inspectable: reflect_proof_status(r),
    }
}

/// Recover a receipt's commit height from the dynamics stream.
fn height_of(events: &[crate::dynamics::WorldEvent], receipt_hash: [u8; 32]) -> Option<u64> {
    events.iter().find_map(|e| match e {
        crate::dynamics::WorldEvent::TurnCommitted {
            receipt_hash: rh,
            height,
            ..
        } if *rh == receipt_hash => Some(*height),
        _ => None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{transfer, World};

    /// A world with a couple of committed transfers (verified-by-construction).
    fn proven_world() -> World {
        let mut w = World::new();
        let a = w.genesis_cell(1, 10_000);
        let b = w.genesis_cell(2, 0);
        let t1 = w.turn(a, vec![transfer(a, b, 100)]);
        assert!(w.commit_turn(t1).is_committed());
        let t2 = w.turn(a, vec![transfer(a, b, 250)]);
        assert!(w.commit_turn(t2).is_committed());
        w
    }

    #[test]
    fn proof_board_classifies_committed_turns_by_tier() {
        let w = proven_world();
        let board = ProofBoard::build(&w, usize::MAX);
        assert_eq!(board.len(), 2, "two committed turns on the board");
        // Both are verified-by-construction (the embedded single-custody world;
        // no producer signature, no inline STARK).
        assert_eq!(board.by_construction, 2);
        assert_eq!(board.stark_attached, 0);
        for e in &board.entries {
            assert_eq!(e.tier, VerificationTier::VerifiedByConstruction);
            assert_eq!(e.attach, AttachStatus::NoExplicitProof);
            // The entry carries the pre/post commitment the next tier would bind.
            assert!(!e.pre_state_short.is_empty());
            assert!(!e.post_state_short.is_empty());
        }
    }

    #[test]
    fn entries_are_most_recent_first_with_heights() {
        let w = proven_world();
        let board = ProofBoard::build(&w, usize::MAX);
        // Most-recent-first: the second transfer (height 2) is first.
        assert_eq!(board.entries[0].height, 2);
        assert_eq!(board.entries[1].height, 1);
    }

    #[test]
    fn the_upgrade_route_is_honest_about_the_next_tier() {
        let w = proven_world();
        let board = ProofBoard::build(&w, usize::MAX);
        // A tier-1 turn's upgrade route names the signature + STARK path honestly.
        let route = board.entries[0].upgrade_route().expect("tier 1 has a next tier");
        assert!(route.contains("signature") || route.contains("STARK"));
        // The top tier has no further route.
        assert_eq!(VerificationTier::StarkAttached.next_route(), None);
    }

    #[test]
    fn tier_strength_is_ordered() {
        assert!(
            VerificationTier::VerifiedByConstruction.strength()
                < VerificationTier::ExecutorSigned.strength()
        );
        assert!(
            VerificationTier::ExecutorSigned.strength()
                < VerificationTier::StarkAttached.strength()
        );
    }

    #[test]
    fn a_burn_turn_discloses_the_burn_on_its_proof_entry() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let t = w.turn(a, vec![crate::world::burn(a, 100)]);
        assert!(w.commit_turn(t).is_committed());
        let board = ProofBoard::build(&w, usize::MAX);
        assert_eq!(board.len(), 1);
        assert!(board.entries[0].burn_disclosed, "the burn is disclosed on the proof entry");
    }

    #[test]
    fn an_empty_world_has_an_empty_board() {
        let w = World::new();
        let board = ProofBoard::build(&w, usize::MAX);
        assert!(board.is_empty());
    }
}
