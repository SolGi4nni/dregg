//! THE NARRATION-VS-TRUTH PANEL — the pale ghost caught at the glass (N6).
//!
//! This is the sharpest ADOS tooth: a headless model that puts a swarm member's
//! **own CLAIMED action** (what its loop SAYS it did, supplied alongside the turn)
//! next to the **executor's RECEIPT** — or the **ABSENCE** of one — and flags
//! every divergence. The operator does not read the summary the agent wrote; they
//! read what the swarm *actually did* (the grounded [`Swarm::action_log`] +
//! the [`WorldEvent`] dynamics), and the panel surfaces the gap.
//!
//! `docs/ADOS-DEEPENING.md` §3.5 is the spec; the four divergences it names:
//!
//! | the agent CLAIMS…        | the receipt chain SHOWS…          | the divergence flagged   |
//! |--------------------------|-----------------------------------|--------------------------|
//! | "I did X"                | no committed turn for X           | a **fabricated action**  |
//! | "I was authorized to X"  | a refused (red) outcome for X     | a **claimed-but-refused**|
//! | "I only did A and B"     | a third committed turn C          | a **concealed side-effect**|
//! | "I stayed in budget"     | a `BudgetExhausted` refusal       | a **claimed-but-bounded**|
//!
//! The last two are the pale ghost: an agent that *did more than it said* or
//! *failed at what it claimed* is exposed because the turns (and the refusals) are
//! in the grounded action log whether or not the agent mentions them.
//!
//! # The honest boundary — the R1 claim-to-turn correlation seam
//!
//! This panel ships NOW as **pure UI over data that already exists**
//! ([`Swarm::action_log`] + the dynamics). It correlates a claim to its member's
//! outcomes at the **feed level** — *did this member, in this window of the log,
//! actually commit / get refused / breach its budget, as it claimed?* That is a
//! real, non-fakeable check (the action log is the executor's record, not the
//! agent's self-report).
//!
//! What it does NOT do — and **must not pretend to** — is correlate a *specific
//! narrated claim* ("I transferred 500 to worker-b") to the *specific turn* that
//! claim should have produced. That needs the **tool-call → effect compiler**
//! (`FRONTIER-ROADMAP.md` R1 / `docs/ADOS-DEEPENING.md` §3.9): an adapter that
//! turns a provider's tool-call schema into the typed effects [`Swarm::run`]
//! executes, emitting a stable correlation id the panel can join on. Until that
//! lands, a [`ClaimedAction`] carries an OPTIONAL `expected` posture (the member's
//! claim about WHETHER it committed / was in budget) and the panel checks THAT
//! against the ground truth — the feed-level divergence. The claim-to-turn join is
//! the named compiler-gated deepening, surfaced as [`Correlation::FeedLevelOnly`]
//! so the operator is never told the panel proved more than it did.
//!
//! gpui-free + `cargo test`-able: built from a [`Swarm`] (its action log) + the
//! [`World`] (the dynamics). The cockpit maps [`NarrationPanel`] onto the
//! narration-vs-truth panel beside the activity feed.

use dregg_cell::CellId;

use crate::swarm::{Swarm, SwarmActionOutcome};
use crate::world::World;

/// What a member's loop CLAIMS about an action — supplied by the loop alongside
/// the turn (the reflection/log line the agent wrote about itself). This is the
/// NARRATION half; the panel puts it next to the executor's RECEIPT.
///
/// The `expected` posture is the claim's checkable content at the feed level: did
/// the member claim the action COMMITTED (it "did X"), or that it stayed WITHIN
/// BUDGET? The SPECIFIC effects the claim describes (the `description`) are
/// operator-legible text — joining them to a specific turn is the R1 compiler seam
/// (`correlation_id`, populated only when a compiler supplies it).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimedAction {
    /// The member whose loop made this claim (the narrator).
    pub member: CellId,
    /// The human-legible claim the loop wrote (e.g. "transferred 500 to worker-b").
    /// This is the narration the operator would otherwise have to trust.
    pub description: String,
    /// The claim's checkable POSTURE — what the loop asserts about the action's
    /// fate (committed / authorized / in-budget). The panel checks THIS against
    /// the grounded action log.
    pub expected: ClaimPosture,
    /// An OPTIONAL correlation id the R1 tool-call → effect compiler would emit so
    /// this specific claim joins to its specific turn. `None` today (the compiler
    /// is the named frontier) — the panel correlates at the feed level when absent.
    pub correlation_id: Option<[u8; 32]>,
}

/// The posture a claim asserts about its action's fate — the feed-level-checkable
/// content of the narration.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClaimPosture {
    /// "I did X" / "I committed an action" — the loop claims a turn COMMITTED.
    Committed,
    /// "I was authorized to do X" — the loop claims the action was permitted (so
    /// it should appear as a COMMITTED outcome, not a refusal).
    Authorized,
    /// "I stayed within budget" — the loop claims no budget breach.
    WithinBudget,
}

impl ClaimPosture {
    pub fn label(self) -> &'static str {
        match self {
            ClaimPosture::Committed => "claims: committed an action",
            ClaimPosture::Authorized => "claims: was authorized",
            ClaimPosture::WithinBudget => "claims: stayed within budget",
        }
    }
}

/// The kind of divergence the panel found between a claim and the ground truth —
/// the four pale-ghost flags from `docs/ADOS-DEEPENING.md` §3.5, plus the honest
/// "no divergence" verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Divergence {
    /// The claim agrees with the ground truth (claimed committed AND a real
    /// committed outcome exists; or claimed in-budget AND no breach) — no ghost.
    None,
    /// **FABRICATED ACTION** — the loop claims it "did X" but the grounded log
    /// holds NO committed turn for this member in the window. The pale ghost: an
    /// action narrated but never performed.
    FabricatedAction,
    /// **CLAIMED-BUT-REFUSED** — the loop claims it was authorized, but the
    /// member's outcome in the window is a REFUSAL (out-of-mandate / executor-
    /// rejected). It said it was allowed; the executor said no.
    ClaimedButRefused,
    /// **CONCEALED SIDE-EFFECT** — the loop claims it "only did A and B" (a
    /// bounded set), but the grounded log holds MORE committed turns for this
    /// member than the claim accounted for. It did more than it said.
    ConcealedSideEffect,
    /// **CLAIMED-BUT-BOUNDED** — the loop claims it stayed within budget, but the
    /// member's window holds a `BudgetExhausted` refusal. It said it was fine; the
    /// budget gate fired.
    ClaimedButBounded,
}

impl Divergence {
    /// Whether this is a genuine divergence (a ghost caught), vs. agreement.
    pub fn is_divergent(self) -> bool {
        !matches!(self, Divergence::None)
    }

    /// A short operator-legible label (red in the panel when divergent).
    pub fn label(self) -> &'static str {
        match self {
            Divergence::None => "✓ matches the receipt",
            Divergence::FabricatedAction => "⚠ FABRICATED — claimed but no committed turn",
            Divergence::ClaimedButRefused => "⚠ CLAIMED-BUT-REFUSED — the executor refused it",
            Divergence::ConcealedSideEffect => "⚠ CONCEALED SIDE-EFFECT — did more than it said",
            Divergence::ClaimedButBounded => "⚠ CLAIMED-BUT-BOUNDED — budget exhausted",
        }
    }
}

/// How tightly the panel could correlate this claim to the ground truth — the
/// honest assurance label (never overstated). Today every row is
/// [`Correlation::FeedLevelOnly`]; the [`Correlation::ByCorrelationId`] tier lands
/// with the R1 compiler.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Correlation {
    /// The claim was checked at the FEED LEVEL — against this member's outcomes in
    /// the action-log window, not joined to a specific turn. The honest default
    /// (the R1 compiler is the named seam to a tighter join).
    FeedLevelOnly,
    /// The claim carried a correlation id (from the R1 tool-call → effect
    /// compiler) and was joined to its SPECIFIC turn. Not reachable until the
    /// compiler lands — present so the model already names the stronger tier.
    ByCorrelationId,
}

impl Correlation {
    pub fn label(self) -> &'static str {
        match self {
            Correlation::FeedLevelOnly => {
                "feed-level (claim-to-specific-turn join needs the R1 tool-call→effect compiler)"
            }
            Correlation::ByCorrelationId => "joined to its turn by correlation id (R1)",
        }
    }
}

/// One row of the narration-vs-truth panel: a member's CLAIM next to the
/// executor's RECEIPT (or its absence), with the divergence verdict.
#[derive(Clone, Debug)]
pub struct NarrationRow {
    /// The claim the member's loop made (the narration).
    pub claim: ClaimedAction,
    /// A short id for the claiming member.
    pub member_short: String,
    /// The receipt of the member's matching committed outcome in the window, if
    /// one exists (the GROUND TRUTH the claim is checked against), short-form.
    pub receipt_short: Option<String>,
    /// How many committed turns this member actually has in the window (the
    /// grounded count — the concealed-side-effect check compares the claim's
    /// accounted set against this).
    pub committed_in_window: usize,
    /// Whether the member's window holds a refusal (out-of-mandate / executor /
    /// budget) — the claimed-but-refused / claimed-but-bounded evidence.
    pub refused_in_window: bool,
    /// Whether the member's window holds a `BudgetExhausted` refusal specifically.
    pub budget_breached_in_window: bool,
    /// The divergence verdict (the pale-ghost flag, or agreement).
    pub divergence: Divergence,
    /// How tightly the claim could be correlated (the honest R1 boundary label).
    pub correlation: Correlation,
}

impl NarrationRow {
    /// Whether this row is a caught ghost (a genuine divergence).
    pub fn is_divergent(&self) -> bool {
        self.divergence.is_divergent()
    }
}

/// THE NARRATION-VS-TRUTH PANEL — every claim a swarm's members made, each next to
/// the executor's grounded record, with the divergences flagged. Built from the
/// [`Swarm`]'s action log + the [`World`]'s dynamics; gpui-free.
#[derive(Clone, Debug)]
pub struct NarrationPanel {
    /// One row per claim (claim order).
    pub rows: Vec<NarrationRow>,
    /// How many rows are genuine divergences (caught ghosts) — the headline count.
    pub divergences: usize,
}

impl NarrationPanel {
    /// **Build the panel** by correlating each claim against the grounded action
    /// log over the WINDOW `[from_log_index .. ]` — the slice of the log that
    /// covers the claims being checked (the caller passes the log length captured
    /// BEFORE the members ran, so the window is exactly the actions taken since).
    ///
    /// Each claim is matched (feed-level) against its member's outcomes in that
    /// window: a `Committed`/`Authorized` claim diverges if the member has NO
    /// committed outcome (fabricated) or a refusal (claimed-but-refused); a
    /// `WithinBudget` claim diverges if the member's window holds a budget breach;
    /// a `claimed_action_count` (how many actions the claim accounts for) below the
    /// member's grounded committed count is a concealed side-effect.
    ///
    /// `claimed_action_count` is an OPTIONAL per-member map of how many distinct
    /// actions each member's narration accounts for (the "I only did A and B" =
    /// 2). When a member's grounded committed count EXCEEDS its claimed count, the
    /// extra turns are a concealed side-effect. Pass `&[]` to skip that check.
    pub fn build(
        swarm: &Swarm,
        _world: &World,
        claims: &[ClaimedAction],
        from_log_index: usize,
        claimed_action_count: &[(CellId, usize)],
    ) -> Self {
        let log = swarm.action_log();
        let window: &[SwarmActionOutcome] = if from_log_index <= log.len() {
            &log[from_log_index..]
        } else {
            &[]
        };

        let mut rows: Vec<NarrationRow> = Vec::new();
        for claim in claims {
            let member = claim.member;
            // The member's outcomes in the window (the GROUND TRUTH).
            let mine: Vec<&SwarmActionOutcome> =
                window.iter().filter(|o| o.member == member).collect();
            let committed: Vec<&&SwarmActionOutcome> =
                mine.iter().filter(|o| o.committed).collect();
            let committed_in_window = committed.len();
            let refused_in_window = mine.iter().any(|o| !o.committed);
            // A budget breach is a refusal whose summary names the budget gate
            // (the `Swarm::run` budget refusal stamps "BUDGET EXHAUSTED").
            let budget_breached_in_window = mine
                .iter()
                .any(|o| !o.committed && o.summary.contains("BUDGET EXHAUSTED"));
            // The first committed receipt is the matching ground-truth record.
            let receipt_short = committed
                .first()
                .and_then(|o| o.receipt_hash)
                .map(|h| crate::reflect::short_hex(&h));

            // The claimed action count for this member, if supplied.
            let claimed_count = claimed_action_count
                .iter()
                .find(|(m, _)| *m == member)
                .map(|(_, n)| *n);

            let divergence = diagnose(
                claim.expected,
                committed_in_window,
                refused_in_window,
                budget_breached_in_window,
                claimed_count,
            );

            rows.push(NarrationRow {
                claim: claim.clone(),
                member_short: crate::reflect::short_hex(member.as_bytes()),
                receipt_short,
                committed_in_window,
                refused_in_window,
                budget_breached_in_window,
                divergence,
                // The honest correlation tier: feed-level unless an R1 correlation
                // id was supplied (not reachable until the compiler lands).
                correlation: if claim.correlation_id.is_some() {
                    Correlation::ByCorrelationId
                } else {
                    Correlation::FeedLevelOnly
                },
            });
        }

        let divergences = rows.iter().filter(|r| r.is_divergent()).count();
        NarrationPanel { rows, divergences }
    }

    /// The rows that are genuine divergences (the caught ghosts) — what the
    /// operator's eye goes to first.
    pub fn ghosts(&self) -> Vec<&NarrationRow> {
        self.rows.iter().filter(|r| r.is_divergent()).collect()
    }

    /// Whether the panel caught any divergence at all.
    pub fn any_divergence(&self) -> bool {
        self.divergences > 0
    }
}

/// Diagnose the divergence between a claim's posture and the grounded record.
///
/// The order of checks matters: a budget breach is the most specific refusal, so a
/// `WithinBudget` claim is checked against it first; an `Authorized`/`Committed`
/// claim is fabricated if there is NO committed turn, claimed-but-refused if there
/// IS a refusal, and a concealed-side-effect if the grounded committed count
/// exceeds the claim's accounted count.
fn diagnose(
    expected: ClaimPosture,
    committed_in_window: usize,
    refused_in_window: bool,
    budget_breached: bool,
    claimed_count: Option<usize>,
) -> Divergence {
    match expected {
        ClaimPosture::WithinBudget => {
            if budget_breached {
                Divergence::ClaimedButBounded
            } else {
                Divergence::None
            }
        }
        ClaimPosture::Committed | ClaimPosture::Authorized => {
            if committed_in_window == 0 {
                // The loop claimed it did/was-authorized-to-do something, but the
                // grounded log holds no committed turn for it.
                if refused_in_window {
                    // There IS a record — a refusal — so the claim is not merely
                    // fabricated; it is a claimed-but-refused (it said it was
                    // authorized; the executor refused it).
                    Divergence::ClaimedButRefused
                } else {
                    // No committed turn AND no refusal: the action was narrated but
                    // never performed at all — a fabrication.
                    Divergence::FabricatedAction
                }
            } else if refused_in_window && matches!(expected, ClaimPosture::Authorized) {
                // It DID commit something, but ALSO has a refusal in the window —
                // an authorized-claim that includes a refused attempt is a
                // claimed-but-refused (it overstated its authority somewhere).
                Divergence::ClaimedButRefused
            } else if let Some(claimed) = claimed_count {
                if committed_in_window > claimed {
                    // It committed MORE turns than the claim accounted for — the
                    // extra turns are a concealed side-effect.
                    Divergence::ConcealedSideEffect
                } else {
                    Divergence::None
                }
            } else {
                Divergence::None
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::swarm::Swarm;
    use crate::world::{emit_event, make_open_cell, transfer, World};

    /// A three-member swarm (coordinator with caps to both workers, worker-a,
    /// worker-b) over a fresh world — the same mandate graph the swarm tests use.
    fn swarm_world() -> (World, Swarm, CellId, CellId, CellId) {
        let mut world = World::new();
        let worker_a = world.genesis_cell(0xA0, 5_000);
        let worker_b = world.genesis_cell(0xB0, 5_000);
        let mut coord_cell = make_open_cell(0xC0, 10_000);
        coord_cell
            .capabilities
            .grant(worker_a, dregg_cell::AuthRequired::None)
            .expect("free slot");
        coord_cell
            .capabilities
            .grant(worker_b, dregg_cell::AuthRequired::None)
            .expect("free slot");
        let coord = world.genesis_install(coord_cell);
        let swarm = Swarm::new(
            &world,
            [(coord, "coordinator"), (worker_a, "worker-a"), (worker_b, "worker-b")],
        );
        (world, swarm, coord, worker_a, worker_b)
    }

    #[test]
    fn an_honest_claim_matches_the_receipt_no_divergence() {
        // POLARITY (agreement): the coordinator claims it committed an action, and
        // it really did — the panel finds NO divergence and links the receipt.
        let (mut world, mut swarm, coord, worker_a, _) = swarm_world();
        let log0 = swarm.action_log().len();
        let outcome = swarm
            .run(&mut world, coord, vec![transfer(coord, worker_a, 100)])
            .expect("the action commits");
        let claim = ClaimedAction {
            member: coord,
            description: "transferred 100 to worker-a".to_string(),
            expected: ClaimPosture::Committed,
            correlation_id: None,
        };
        let panel = NarrationPanel::build(&swarm, &world, &[claim], log0, &[]);
        assert_eq!(panel.rows.len(), 1);
        assert!(!panel.any_divergence(), "an honest claim does not diverge");
        assert_eq!(panel.rows[0].divergence, Divergence::None);
        // The ground-truth receipt is linked.
        assert_eq!(
            panel.rows[0].receipt_short,
            Some(crate::reflect::short_hex(&outcome.receipt_hash.unwrap()))
        );
        // The honest correlation label names the R1 boundary.
        assert_eq!(panel.rows[0].correlation, Correlation::FeedLevelOnly);
    }

    #[test]
    fn a_fabricated_action_is_caught_no_committed_turn() {
        // THE PALE GHOST (fabrication): the coordinator claims it "did X" but never
        // ran ANY turn — the panel flags FabricatedAction (no committed turn, no
        // refusal). The narration said more than the receipts hold.
        let (world, swarm, coord, _wa, _wb) = swarm_world();
        let log0 = swarm.action_log().len();
        // No action is run — the claim is pure narration.
        let claim = ClaimedAction {
            member: coord,
            description: "transferred 500 to worker-b (but I didn't, really)".to_string(),
            expected: ClaimPosture::Committed,
            correlation_id: None,
        };
        let panel = NarrationPanel::build(&swarm, &world, &[claim], log0, &[]);
        assert!(panel.any_divergence(), "a fabricated action must be caught");
        assert_eq!(panel.rows[0].divergence, Divergence::FabricatedAction);
        assert_eq!(panel.rows[0].committed_in_window, 0);
        assert!(panel.rows[0].receipt_short.is_none(), "no receipt — it never happened");
        assert_eq!(panel.ghosts().len(), 1);
    }

    #[test]
    fn a_claimed_but_refused_action_is_caught() {
        // THE PALE GHOST (claimed-but-refused): the coordinator claims it was
        // AUTHORIZED to move 1,000,000 to worker-a, but it holds nowhere near that
        // balance — the real executor REJECTED the overspend (recorded as a refused
        // outcome in the log). The panel puts the "I was authorized" claim next to
        // the red refusal and flags it. (We use an executor rejection, which logs a
        // refused outcome; an out-of-mandate cap-gate pre-check returns early
        // without logging, so it would not exercise this feed-level branch.)
        let (mut world, mut swarm, coord, worker_a, _wb) = swarm_world();
        let log0 = swarm.action_log().len();
        let r = swarm.run(&mut world, coord, vec![transfer(coord, worker_a, 1_000_000)]);
        assert!(matches!(r, Err(crate::swarm::SwarmError::ExecutorRejected { .. })));
        let claim = ClaimedAction {
            member: coord,
            description: "I was authorized to transfer 1,000,000 to worker-a".to_string(),
            expected: ClaimPosture::Authorized,
            correlation_id: None,
        };
        let panel = NarrationPanel::build(&swarm, &world, &[claim], log0, &[]);
        assert!(panel.any_divergence(), "a claimed-but-refused action must be caught");
        assert_eq!(panel.rows[0].divergence, Divergence::ClaimedButRefused);
        assert!(panel.rows[0].refused_in_window);
    }

    #[test]
    fn a_concealed_side_effect_is_caught_more_turns_than_claimed() {
        // THE PALE GHOST (concealed side-effect): the coordinator claims it "only
        // did 1 action" but actually committed THREE — the panel flags the extra
        // turns. It did more than it said.
        let (mut world, mut swarm, coord, worker_a, worker_b) = swarm_world();
        let log0 = swarm.action_log().len();
        // Three real committed actions.
        swarm.run(&mut world, coord, vec![transfer(coord, worker_a, 100)]).unwrap();
        swarm.run(&mut world, coord, vec![transfer(coord, worker_b, 100)]).unwrap();
        swarm.run(&mut world, coord, vec![emit_event(worker_a, "task/go", vec![])]).unwrap();
        let claim = ClaimedAction {
            member: coord,
            description: "I only did 1 action (a single transfer)".to_string(),
            expected: ClaimPosture::Committed,
            correlation_id: None,
        };
        // The claim accounts for only 1 action; the grounded log holds 3.
        let panel = NarrationPanel::build(&swarm, &world, &[claim], log0, &[(coord, 1)]);
        assert!(panel.any_divergence(), "a concealed side-effect must be caught");
        assert_eq!(panel.rows[0].divergence, Divergence::ConcealedSideEffect);
        assert_eq!(panel.rows[0].committed_in_window, 3, "three turns actually committed");
    }

    #[test]
    fn an_accurate_action_count_does_not_flag_concealment() {
        // The dual: when the claimed count MATCHES the grounded committed count,
        // there is no concealed side-effect (the claim is honest about its breadth).
        let (mut world, mut swarm, coord, worker_a, worker_b) = swarm_world();
        let log0 = swarm.action_log().len();
        swarm.run(&mut world, coord, vec![transfer(coord, worker_a, 100)]).unwrap();
        swarm.run(&mut world, coord, vec![transfer(coord, worker_b, 100)]).unwrap();
        let claim = ClaimedAction {
            member: coord,
            description: "I did 2 transfers".to_string(),
            expected: ClaimPosture::Committed,
            correlation_id: None,
        };
        let panel = NarrationPanel::build(&swarm, &world, &[claim], log0, &[(coord, 2)]);
        assert!(!panel.any_divergence(), "an accurate count does not flag concealment");
        assert_eq!(panel.rows[0].divergence, Divergence::None);
    }

    #[test]
    fn a_claimed_but_bounded_overspend_is_caught() {
        // THE PALE GHOST (claimed-but-bounded): the coordinator claims it "stayed
        // within budget", but the metered world refused a dispatch with
        // BudgetExhausted — the panel flags the contradiction.
        use dregg_turn::ComputronCosts;
        let mut world =
            World::with_costs(ComputronCosts::default_costs()).with_turn_fee(1_000);
        let worker_a = world.genesis_cell(0xA0, 5_000);
        let mut coord_cell = make_open_cell(0xC0, 100_000_000);
        coord_cell
            .capabilities
            .grant(worker_a, dregg_cell::AuthRequired::None)
            .expect("free slot");
        let coord = world.genesis_install(coord_cell);
        let mut swarm = Swarm::new(&world, [(coord, "coordinator"), (worker_a, "worker-a")]);
        // Spend once, then cap at that spend so the next dispatch breaches.
        let o1 = swarm.run(&mut world, coord, vec![transfer(coord, worker_a, 100)]).unwrap();
        swarm.set_ceiling(&coord, Some(o1.computrons));
        let log0 = swarm.action_log().len();
        let r = swarm.run(&mut world, coord, vec![transfer(coord, worker_a, 100)]);
        assert!(matches!(r, Err(crate::swarm::SwarmError::BudgetExhausted { .. })));
        let claim = ClaimedAction {
            member: coord,
            description: "I stayed within budget".to_string(),
            expected: ClaimPosture::WithinBudget,
            correlation_id: None,
        };
        let panel = NarrationPanel::build(&swarm, &world, &[claim], log0, &[]);
        assert!(panel.any_divergence(), "a claimed-but-bounded overspend must be caught");
        assert_eq!(panel.rows[0].divergence, Divergence::ClaimedButBounded);
        assert!(panel.rows[0].budget_breached_in_window);
    }

    #[test]
    fn a_within_budget_claim_with_no_breach_does_not_diverge() {
        // The dual: a WithinBudget claim when there was no breach is honest.
        let (mut world, mut swarm, coord, worker_a, _) = swarm_world();
        let log0 = swarm.action_log().len();
        swarm.run(&mut world, coord, vec![transfer(coord, worker_a, 100)]).unwrap();
        let claim = ClaimedAction {
            member: coord,
            description: "I stayed within budget".to_string(),
            expected: ClaimPosture::WithinBudget,
            correlation_id: None,
        };
        let panel = NarrationPanel::build(&swarm, &world, &[claim], log0, &[]);
        assert!(!panel.any_divergence());
        assert_eq!(panel.rows[0].divergence, Divergence::None);
    }

    #[test]
    fn the_correlation_tier_names_the_r1_boundary_honestly() {
        // The honest R1 boundary: with no correlation id, the row is FeedLevelOnly
        // and its label names the tool-call→effect compiler as the seam to a
        // tighter join. With an id supplied (the compiler's artifact), it would be
        // ByCorrelationId — the model already names the stronger tier without
        // faking it.
        let (mut world, mut swarm, coord, worker_a, _) = swarm_world();
        let log0 = swarm.action_log().len();
        swarm.run(&mut world, coord, vec![transfer(coord, worker_a, 100)]).unwrap();
        let feed_claim = ClaimedAction {
            member: coord,
            description: "did a transfer".to_string(),
            expected: ClaimPosture::Committed,
            correlation_id: None,
        };
        let joined_claim = ClaimedAction {
            member: coord,
            description: "did a transfer".to_string(),
            expected: ClaimPosture::Committed,
            correlation_id: Some([0x11; 32]),
        };
        let panel =
            NarrationPanel::build(&swarm, &world, &[feed_claim, joined_claim], log0, &[]);
        assert_eq!(panel.rows[0].correlation, Correlation::FeedLevelOnly);
        assert!(panel.rows[0].correlation.label().contains("R1"));
        assert_eq!(panel.rows[1].correlation, Correlation::ByCorrelationId);
    }
}
