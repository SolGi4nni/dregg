//! **Weighted `/council`** — standing-weighted ballots on the VERIFIED weighted vote
//! engine (backlog 2026-07-17 #22).
//!
//! `/council open weighted:true` builds the same cryptographic electorate as a plain
//! council, but each member arrives with a **granted ballot weight**, and the offering
//! is [`CouncilOffering::new_weighted`] — so every PROPOSE opens its poll via
//! `collective_choice::open_poll_weighted_gated` and every APPROVE/REJECT press lands
//! through `collective_choice::cast_weighted` (the member's whole weight rides ONE
//! nullifier; a zero-weight cast is refused fail-closed before the ballot is
//! consumed). Before this module, `/council` only ever reached the plain `cast`.
//!
//! ## Where the weight comes from — honestly
//!
//! Weight here is **`1 + the member's run-credit balance at open`**, read from the
//! bot's paid-credit ledger (`pay_credits` — the same sqlite rows real `$DREGG`
//! payments credit through `dregg_pay`). That is *bot-recorded standing*, NOT a
//! consensus-proven on-chain holding: the proof-of-holdings path (light-client-proven
//! balance → Lean-verified `grantWeightCore` → weight) lives in
//! `dregg_governance::holding_weight` and needs a chain proof the bot does not collect
//! at `/council open`. The surface says exactly this ([`WEIGHT_SOURCE_NOTE`]), so a
//! member knows what the number measures. The `1 +` floor keeps every member a voter
//! (a credit-less friend still casts a weight-1 ballot) while credits add standing.
//!
//! What the ENGINE guarantees (regardless of the weight's provenance): the weight is
//! cast as one verified weighted turn, the tally is a light-client-recomputable weight
//! sum, quorum is a weight threshold with the distinct-approver floor, and a double
//! cast at any weight is the same nullifier refusal as ever.

use dreggnet_council::{CandidateProposal, CouncilOffering};

use crate::BotState;

/// The honest weight-source line the `/council open weighted:true` surface carries.
pub const WEIGHT_SOURCE_NOTE: &str = "⚖ Weighted ballots: weight = 1 + run-credits at open \
     (the bot's paid-credit ledger — bot-recorded standing, NOT a consensus-proven on-chain \
     holding). Each vote lands on the verified weighted engine: one nullifier carries the \
     member's whole weight, and quorum is a WEIGHT threshold.";

/// The granted ballot weight of one member: `1 + run-credit balance` (see the module
/// docs for why the floor is 1 and what the credits measure).
pub async fn standing_weight_of(state: &BotState, discord_user_id: u64) -> u64 {
    let credits = state
        .db
        .pay_credit_balance(&discord_user_id.to_string())
        .await
        .unwrap_or(0);
    1u64.saturating_add(credits)
}

/// The granted weights of a whole electorate, in `discord_ids` order.
pub async fn standing_weights(state: &BotState, discord_ids: &[u64]) -> Vec<u64> {
    let mut out = Vec::with_capacity(discord_ids.len());
    for id in discord_ids {
        out.push(standing_weight_of(state, *id).await);
    }
    out
}

/// The default WEIGHT quorum when the opener names none: a simple majority of the
/// total granted weight (the weighted analog of `/council`'s member majority).
pub fn default_weight_quorum(weights: &[u64]) -> u64 {
    let total: u64 = weights.iter().fold(0u64, |a, w| a.saturating_add(*w));
    (total / 2) + 1
}

/// Build the council offering — weighted onto [`CouncilOffering::new_weighted`] (the
/// verified `cast_weighted` path) when `weights` is `Some`, the classic
/// one-member-one-vote [`CouncilOffering::new`] otherwise. `weights` is parallel to
/// `members`.
pub fn make_council(
    members: Vec<[u8; 32]>,
    weights: Option<Vec<u64>>,
    catalog: Vec<CandidateProposal>,
    quorum: u64,
) -> CouncilOffering {
    match weights {
        Some(ws) => {
            CouncilOffering::new_weighted(members.into_iter().zip(ws).collect(), catalog, quorum)
        }
        None => CouncilOffering::new(members, catalog, quorum),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the weighted factory + quorum arithmetic, and the weighted offering
// driven at the logic level (the same shape a live press takes).
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_council::{TURN_APPROVE, TURN_ENACT, TURN_PROPOSE};
    use dreggnet_offerings::{Action, Offering, Outcome, SessionConfig};

    fn catalog() -> Vec<CandidateProposal> {
        vec![CandidateProposal::new("Fund the commons treasury", 1)]
    }

    #[test]
    fn the_weight_quorum_defaults_to_a_majority_of_total_weight() {
        assert_eq!(default_weight_quorum(&[1, 1, 1]), 2);
        assert_eq!(default_weight_quorum(&[5, 2, 1]), 5, "8 total → majority 5");
        assert_eq!(
            default_weight_quorum(&[]),
            1,
            "an empty roster still needs a vote"
        );
        // Saturation, not wrap, on absurd grants.
        assert_eq!(default_weight_quorum(&[u64::MAX, 2]), u64::MAX / 2 + 1);
    }

    /// `make_council(weights: Some(..))` reaches the VERIFIED weighted engine: a
    /// member's single APPROVE bumps the tally by their whole granted weight and
    /// alone clears a weight quorum their weight covers — the exact behavior the
    /// plain `cast` path cannot produce.
    #[test]
    fn the_weighted_factory_casts_on_the_weighted_engine() {
        let members: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
        let weights = vec![4u64, 1];
        let quorum = default_weight_quorum(&weights); // 3
        let offering = make_council(members.clone(), Some(weights), catalog(), quorum);
        let mut session = offering
            .open(SessionConfig::with_seed(80_001))
            .expect("deploys");
        assert!(session.is_weighted());
        assert_eq!(session.member_weight(&members[0]), 4);

        let who = CouncilOffering::member_identity(&members[0]);
        let press = |s: &mut _, turn: &str| {
            offering.advance(s, Action::new("", turn, 0, true), who.clone())
        };
        assert!(matches!(
            press(&mut session, TURN_PROPOSE),
            Outcome::Landed { .. }
        ));
        assert!(matches!(
            press(&mut session, TURN_APPROVE),
            Outcome::Landed { .. }
        ));
        assert_eq!(
            session.tally_of(0),
            Some((0, 4)),
            "ONE ballot, weight 4 — the plain cast path would read 1 here"
        );
        assert!(matches!(
            press(&mut session, TURN_ENACT),
            Outcome::Landed { .. }
        ));
        assert!(offering.verify(&session).verified);
    }

    /// `make_council(weights: None)` is byte-for-byte the classic council.
    #[test]
    fn the_unweighted_factory_is_the_classic_council() {
        let offering = make_council(vec![[3u8; 32]], None, catalog(), 1);
        let session = offering
            .open(SessionConfig::with_seed(80_002))
            .expect("deploys");
        assert!(!session.is_weighted());
        assert_eq!(session.member_weight(&[3u8; 32]), 1);
    }
}
