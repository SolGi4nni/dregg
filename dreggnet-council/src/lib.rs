//! # dreggnet-council — a COLLECTIVE-GOVERNANCE offering (propose → vote → enact).
//!
//! The fourth DreggNet [`Offering`], beyond the game (`dungeon`), the agent
//! (hosted-Hermes), and the grain (Sandstorm). Its per-session thing is a
//! **council over a real cell**: the SAME `open / actions / advance / verify /
//! render / price` shape that hosts a dungeon playthrough here hosts a governance
//! flow. That is the point — the [`Offering`] abstraction is not narrative-shaped;
//! it carries any confined, verifiable, per-session thing whose moves are real
//! executor turns. A council is that thing for collective decisions.
//!
//! ## The model — three affordances over one substrate
//!
//! An [`advance`](Offering::advance) is one of three governance moves, keyed by the
//! [`Action::turn`] verb:
//!
//! - **PROPOSE** (`turn = "propose"`, `arg` = a catalog index) — a council member
//!   opens a proposal: a per-option-gated `reject / approve` poll on the real
//!   [`collective_choice`] engine (gated on APPROVE, at the council quorum `M`), and
//!   a committed council-cell turn recording the opening. Lands a real
//!   [`TurnReceipt`].
//! - **VOTE** (`turn = "approve"` / `"reject"`, `arg` = a proposal index) — a member
//!   casts a **single-use, write-once ballot**. The ballot's `WriteOnce(VOTE)` + the
//!   engine nullifier make a second vote a real refusal; a non-member holds no ballot
//!   cap and is refused ([`collective_choice::VoteError::Ineligible`]). A cast lands a
//!   real [`TurnReceipt`]; a double-vote / non-member is [`Outcome::Refused`].
//! - **ENACT** (`turn = "enact"`, `arg` = a proposal index) — attempts the decision.
//!   The quorum **`AffineLe` gate inside the engine is the real referee**: below quorum
//!   the engine refuses the decision-turn ([`collective_choice::VoteEngine::resolve`]
//!   yields `None`) and ENACT is [`Outcome::Refused`] — **nothing is applied**. At
//!   quorum with APPROVE the winner, the proposal's **real effect** (a `WriteOnce`
//!   policy-slot write on the council cell) commits as one executor-refereed turn →
//!   [`Outcome::Landed`]. A second enact of the same proposal is refused (already
//!   enacted / the executor's `WriteOnce`).
//!
//! The executor is the SOURCE OF TRUTH on both substrates: the vote board is a
//! monotone tally of real ballot turns (a light client recomputes it), and the
//! enactment is a real committed cell-state change. A jailbroken narration cannot
//! move the treasury; only a passed vote can.
//!
//! ## Honest scope
//!
//! The effect an enacted proposal applies here is a **cell-state change**: it writes
//! the proposal's `value` into a per-catalog `WriteOnce` policy slot on the council
//! cell (a policy flag / a treasury parameter / an authorization bit). That is a real,
//! executor-refereed, verifiable effect. A *fuller* governance offering would let a
//! proposal carry a richer effect — a capability **grant** to a named cell, a fund
//! **transfer**, a cross-cell program install, or a parameterized method call — and
//! would add proposal lifecycle (amend / withdraw / expire), delegated ballots (the
//! engine already supports non-amplifying delegation), and a constitutional amendment
//! path. The abstraction is unchanged; only the enacted [`Effect`] set widens.
//!
//! ## Weighted councils
//!
//! [`CouncilOffering::new_weighted`] opens the SAME three affordances over the
//! engine's **weighted** primitives instead of the plain ones — nothing here
//! hand-rolls a weight tally:
//!
//! - PROPOSE opens the poll with [`collective_choice::VoteEngine::open_poll_weighted_gated`],
//!   so `quorum_m` becomes a **WEIGHT** threshold on APPROVE (`M·RESOLVED −
//!   TALLY_approve ≤ 0` over weight-bumped tallies) and the `CountGe` floor drops to
//!   one genuine distinct approver — a member whose grant alone clears `M` is a
//!   legitimate quorum, while a forged tally jump with no real voter still cannot arm
//!   `RESOLVED`.
//! - VOTE casts with [`collective_choice::VoteEngine::cast_weighted`], so the member's
//!   whole granted weight rides **ONE** nullifier (never `W` weight-1 ballots — that
//!   is the amplification the delegation lattice forbids). A second cast at any weight
//!   is the same [`VoteError::DoubleVote`] refusal as the classic council.
//! - A **zero-weight** member is refused fail-closed by the engine's
//!   [`VoteError::ZeroWeight`] floor *before* the ballot turn, so a worthless cast
//!   never consumes their single-use ballot.
//!
//! The electorate of a weighted poll is dynamic at the ENGINE layer (eligibility is
//! meant to be the caller's verified grant), so the council keeps its own membership
//! gate: an actor outside [`CouncilSession::members`] is refused in
//! [`advance`](Offering::advance) before any ballot is minted.
//!
//! The weight itself is **granted upstream** — this crate consumes it, it does not
//! prove it. Where the number comes from (a proven on-chain holding, a bot-recorded
//! standing, a charter) is the caller's claim to make honestly.
//!
//! An unweighted council is unchanged in every respect: it opens `open_poll_gated`,
//! casts plain `cast`, and [`CouncilSession::member_weight`] reads a uniform `1`.

#![forbid(unsafe_code)]

use std::collections::HashMap;

use collective_choice::{
    BallotCap, CollectiveChoice, Decision, PollId, PollSpec, VoteEngine, VoteError,
};
use deos_view::{MenuItem, ViewNode};
use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellProgram, Effect, EmbeddedExecutor,
    Event, FieldElement, StateConstraint, TurnReceipt, field_from_u64, symbol,
};
use dregg_cell::Cell;

use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

// ── the poll option layout (matches dregg-pay's LiquidityGovernance) ──────────

/// The `REJECT` ballot option (index 0).
pub const REJECT_OPTION: usize = 0;
/// The `APPROVE` ballot option (index 1). Every council poll is per-option-gated on
/// THIS option, so the decision-turn commits only once APPROVE itself reaches quorum
/// — `M` reject/other ballots never arm the enactment.
pub const APPROVE_OPTION: usize = 1;

// ── council-cell slot layout ──────────────────────────────────────────────────

/// A monotone counter of proposals opened — bumped by each PROPOSE turn, so a
/// propose is a real committed council-cell turn (not a bookkeeping no-op).
const PROPOSALS_OPENED_SLOT: usize = 2;
/// The first per-catalog **policy slot**. Catalog item `i` enacts into
/// `POLICY_BASE + i`, a `WriteOnce` slot: the enacted `value` is written exactly once
/// (a second enactment of the same proposal is a real executor refusal), and an
/// unenacted proposal leaves its slot `0` (the "below-quorum does not enact" tooth).
const POLICY_BASE: usize = 8;
/// The structural ceiling on catalog items (the council cell's 16-slot layout).
pub const MAX_CATALOG: usize = 8;

// ── the affordance verbs ──────────────────────────────────────────────────────

/// PROPOSE verb — open a proposal for the catalog item named by [`Action::arg`].
pub const TURN_PROPOSE: &str = "propose";
/// APPROVE-vote verb — cast an APPROVE ballot on the proposal named by [`Action::arg`].
pub const TURN_APPROVE: &str = "approve";
/// REJECT-vote verb — cast a REJECT ballot on the proposal named by [`Action::arg`].
pub const TURN_REJECT: &str = "reject";
/// ENACT verb — attempt to apply the proposal named by [`Action::arg`] (quorum-gated).
pub const TURN_ENACT: &str = "enact";

/// **A candidate proposal** the council can open, vote on, and enact — a named,
/// pre-declared effect on the council cell. Enacting catalog item `i` writes `value`
/// into the `WriteOnce` policy slot `POLICY_BASE + i` (a policy flag / treasury
/// parameter / authorization bit set by a passed vote, and only a passed vote).
#[derive(Clone, Debug)]
pub struct CandidateProposal {
    /// The human title (the affordance label / the proposal's question).
    pub title: String,
    /// The value a passed proposal writes into its policy slot. Non-zero (a `WriteOnce`
    /// slot treats `0` as "unset", so `0` would be indistinguishable from unenacted).
    pub value: u64,
}

impl CandidateProposal {
    /// A candidate that, when enacted, sets its policy slot to `value` (`value` is
    /// clamped to at least `1`, since a `WriteOnce` slot reads `0` as unenacted).
    pub fn new(title: impl Into<String>, value: u64) -> Self {
        CandidateProposal {
            title: title.into(),
            value: value.max(1),
        }
    }
}

/// The live state of one opened proposal — its poll, the votes cast (for render/audit),
/// and its enactment record (`None` until a passing ENACT applies the effect).
struct ProposalState {
    /// Which catalog item this proposal is for (indexes the council-cell policy slot).
    catalog_index: usize,
    /// The `collective-choice` poll (reject/approve, gated on APPROVE) this proposal votes in.
    poll: PollId,
    /// The ballots issued per voter (deterministic; re-issue is idempotent). Kept so a
    /// re-vote reuses the SAME ballot cell — the double-vote refusal bites at the nullifier.
    ballots: HashMap<[u8; 32], BallotCap>,
    /// The votes cast so far — `(voter, option)`, for the rendered "votes cast" panel.
    votes: Vec<(DreggIdentity, usize)>,
    /// The enactment receipt, once a passing ENACT applied the effect (`None` while pending).
    enacted: Option<TurnReceipt>,
    /// The certified decision behind the enactment (`None` while pending).
    decision: Option<Decision>,
}

/// **A live council session** — the confined per-session thing. Owns the real
/// [`collective_choice`] engine (the vote substrate), a real [`EmbeddedExecutor`]
/// hosting the **council cell** (the enactment substrate), and the opened proposals.
pub struct CouncilSession {
    /// The quorum engine — every poll, ballot, and tally is a verified turn here.
    engine: CollectiveChoice,
    /// The council-cell operator identity (authors the propose/enact turns).
    clerk: AppCipherclerk,
    /// The executor hosting the council cell (the enactment substrate).
    exec: EmbeddedExecutor,
    /// The council cell — the real cell an enacted proposal's effect writes.
    council_cell: CellId,
    /// The electorate: council-member public keys (the poll electorate). A vote from
    /// an identity not derived from one of these is a non-member and is refused.
    members: Vec<[u8; 32]>,
    /// The quorum threshold `M` — APPROVE must reach this for a proposal to enact.
    /// In a **weighted** session this is a WEIGHT threshold, not a headcount.
    quorum_m: u64,
    /// The granted ballot weights, `Some` iff this council was opened weighted (see
    /// [`CouncilOffering::new_weighted`]). `None` is the classic one-member-one-vote
    /// council, whose every member weighs exactly `1`.
    weights: Option<HashMap<[u8; 32], u64>>,
    /// The catalog of candidate proposals (the enactable effects).
    catalog: Vec<CandidateProposal>,
    /// `DreggIdentity` → member public key. Built from `members` at open; the reverse
    /// derivation of [`CouncilOffering::member_identity`]. An actor absent here is a
    /// non-member.
    member_pk: HashMap<DreggIdentity, [u8; 32]>,
    /// The proposals opened so far, in order (`Action::arg` for a vote/enact indexes this).
    proposals: Vec<ProposalState>,
    /// Every committed governance turn (propose + vote + enact), for the verified-turn count.
    receipts: Vec<TurnReceipt>,
}

impl CouncilSession {
    /// The number of proposals opened.
    pub fn proposal_count(&self) -> usize {
        self.proposals.len()
    }

    /// Whether this council was opened **weighted** ([`CouncilOffering::new_weighted`]):
    /// every poll rides `open_poll_weighted_gated`, every vote rides `cast_weighted`,
    /// and [`quorum`](Self::quorum) is a WEIGHT threshold rather than a headcount.
    pub fn is_weighted(&self) -> bool {
        self.weights.is_some()
    }

    /// The granted ballot weight one member's single vote is worth.
    ///
    /// In a **weighted** council this is the grant recorded at open — `0` for anyone
    /// not granted (a stranger weighs nothing, and a granted `0` is a real zero-weight
    /// member whose cast the engine refuses fail-closed). In the classic council every
    /// member weighs exactly `1` — one member, one vote.
    pub fn member_weight(&self, member: &[u8; 32]) -> u64 {
        match &self.weights {
            Some(w) => w.get(member).copied().unwrap_or(0),
            None => 1,
        }
    }

    /// The quorum threshold `M` — a WEIGHT threshold on APPROVE when
    /// [`is_weighted`](Self::is_weighted), a distinct-member count otherwise.
    pub fn quorum(&self) -> u64 {
        self.quorum_m
    }

    /// The total granted weight of the electorate (the denominator a weight quorum is
    /// read against). The member count for an unweighted council.
    pub fn total_weight(&self) -> u64 {
        self.members
            .iter()
            .fold(0u64, |a, pk| a.saturating_add(self.member_weight(pk)))
    }

    /// The live `(reject, approve)` tally for proposal `i` (a monotone board a light
    /// client recomputes). `None` for an out-of-range index.
    pub fn tally_of(&self, i: usize) -> Option<(u64, u64)> {
        let p = self.proposals.get(i)?;
        let t = self.engine.tally(p.poll).ok()?;
        let reject = *t.per_option.get(REJECT_OPTION).unwrap_or(&0);
        let approve = *t.per_option.get(APPROVE_OPTION).unwrap_or(&0);
        Some((reject, approve))
    }

    /// Whether proposal `i` has been enacted (its effect committed).
    pub fn is_enacted(&self, i: usize) -> bool {
        self.proposals
            .get(i)
            .map(|p| p.enacted.is_some())
            .unwrap_or(false)
    }

    /// The committed value of catalog item `i`'s policy slot on the council cell —
    /// the proposal's `value` once enacted, `0` while unenacted. The real, verifiable
    /// effect a passed proposal applied (read straight off the committed cell state).
    pub fn policy_value(&self, catalog_index: usize) -> u64 {
        self.read_slot(POLICY_BASE + catalog_index)
    }

    /// The number of real committed governance turns so far (propose + vote + enact).
    pub fn committed_turns(&self) -> usize {
        self.receipts.len()
    }

    fn read_slot(&self, slot: usize) -> u64 {
        self.exec
            .cell_state(self.council_cell)
            .and_then(|s| s.fields.get(slot).map(field_to_u64))
            .unwrap_or(0)
    }
}

/// **The council offering** — a stateless factory over an electorate + a proposal
/// catalog + a quorum threshold. Each [`open`](Offering::open) deploys a fresh
/// [`CouncilSession`] (its own engine + council cell). Analogous to
/// `DungeonOffering`: the factory carries the session-shaping config, `open` births
/// the confined thing.
pub struct CouncilOffering {
    members: Vec<[u8; 32]>,
    weights: Option<HashMap<[u8; 32], u64>>,
    catalog: Vec<CandidateProposal>,
    quorum_m: u64,
}

impl CouncilOffering {
    /// The council surface, painted for `viewer` (`None` = the public render).
    fn render_as(&self, session: &CouncilSession, viewer: Option<&DreggIdentity>) -> Surface {
        // ── THE STATUS PLAQUE. The council had the best scoreboard of any offering and said
        //    NOTHING about where the turn stood: no phase, no whose-move, not even "you have not
        //    voted on this". The tallies were there; the reader had to be the state machine.
        let open = session
            .proposals
            .iter()
            .filter(|p| p.enacted.is_none())
            .count();
        let passed = session
            .proposals
            .iter()
            .enumerate()
            .filter(|(pi, p)| {
                p.enacted.is_none() && session.tally_of(*pi).unwrap_or((0, 0)).1 >= session.quorum_m
            })
            .count();
        let enacted = session
            .proposals
            .iter()
            .filter(|p| p.enacted.is_some())
            .count();
        let unproposed = self.catalog.len().saturating_sub(session.proposals.len());
        let voted_here = |pi: usize| -> Option<bool> {
            let v = viewer?;
            session
                .proposals
                .get(pi)?
                .votes
                .iter()
                .find_map(|(who, opt)| (who == v).then_some(*opt == APPROVE_OPTION))
        };

        // The ONE SENTENCE, in the order a council actually blocks: enact what has passed, then
        // vote on what is open, then open something.
        let directive = if passed > 0 {
            format!(
                "{passed} proposal{} already at quorum and waiting. ENACT one — enacting is what \
                 writes the policy value onto the council cell; a passing tally on its own changes \
                 nothing.",
                if passed == 1 { " is" } else { "s are" }
            )
        } else if open > 0 {
            let mine_left = (0..session.proposals.len())
                .filter(|pi| session.proposals[*pi].enacted.is_none() && voted_here(*pi).is_none())
                .count();
            if viewer.is_some() && mine_left > 0 {
                format!(
                    "{open} proposal{} open and you have not voted on {mine_left} of them. Approve \
                     or reject — each ballot is one cap-gated executor turn and you get one per \
                     proposal.",
                    if open == 1 { " is" } else { "s are" }
                )
            } else if viewer.is_some() {
                format!(
                    "You have voted on every open proposal. {open} still short of quorum — nothing \
                     enacts until approvals reach {}.",
                    session.quorum_m
                )
            } else {
                format!(
                    "{open} proposal{} open, none yet at quorum ({} approvals needed).",
                    if open == 1 { " is" } else { "s are" },
                    session.quorum_m
                )
            }
        } else if unproposed > 0 {
            format!(
                "Nothing is on the floor. Propose one of the {unproposed} candidate{} — a proposal \
                 opens a per-option-gated poll and is itself a verified turn.",
                if unproposed == 1 { "" } else { "s" }
            )
        } else {
            "Every candidate in the catalog has been decided. There is nothing left to put on the \
             floor."
                .to_string()
        };

        let pill = |text: String, tag: &str| ViewNode::Pill {
            text,
            tag: tag.to_string(),
            slot: None,
            cases: Vec::new(),
        };
        let mut standing = vec![
            ViewNode::Row(vec![
                pill(
                    format!("{open} open"),
                    if open > 0 { "accent" } else { "muted" },
                ),
                pill(
                    format!("{passed} at quorum"),
                    if passed > 0 { "good" } else { "muted" },
                ),
                pill(
                    format!("{enacted} enacted"),
                    if enacted > 0 { "good" } else { "muted" },
                ),
                pill(format!("{unproposed} not yet proposed"), "muted"),
            ]),
            ViewNode::Text(directive),
        ];
        standing.push(ViewNode::Text(match viewer {
            Some(_) => format!(
                "A ballot needs {} approval{} to pass{}. Your vote is attributed to your identity \
                 and published — this is a council, not a secret ballot.",
                session.quorum_m,
                if session.quorum_m == 1 { "" } else { "s" },
                if session.is_weighted() {
                    format!(" (by WEIGHT, of {} granted)", session.total_weight())
                } else {
                    String::new()
                }
            ),
            None => format!(
                "{} member{} · a ballot needs {} approval{} to pass{}. Every vote here is public.",
                session.members.len(),
                if session.members.len() == 1 { "" } else { "s" },
                session.quorum_m,
                if session.quorum_m == 1 { "" } else { "s" },
                if session.is_weighted() {
                    format!(" (by WEIGHT, of {} granted)", session.total_weight())
                } else {
                    String::new()
                }
            ),
        }));
        standing.push(ViewNode::Text(format!(
            "{} member{} · {} verified turn{} committed.",
            session.members.len(),
            if session.members.len() == 1 { "" } else { "s" },
            session.committed_turns(),
            if session.committed_turns() == 1 {
                ""
            } else {
                "s"
            }
        )));

        let mut children = vec![ViewNode::Section {
            title: "Where the council stands".to_string(),
            tag: "accent".to_string(),
            children: standing,
        }];

        // ── THE DOMAIN PLAQUE — what a vote here IS. Invisible on any tally: that the ballot is a
        //    real cap-gated turn, that the gate (not this page) is what stops a stranger or a second
        //    vote, and that enactment is a separate write.
        children.push(ViewNode::Section {
            title: "What a vote here actually is".to_string(),
            tag: "accent".to_string(),
            children: vec![
                ViewNode::Text(
                    "Each ballot is ONE cap-gated executor turn against the council cell, not a \
                     row in a database this page keeps. A vote from an identity holding no council \
                     capability is REFUSED by the substrate with nothing committed, and so is a \
                     second vote from an identity that has already cast one — the page dims those \
                     buttons as a courtesy, but the executor is what enforces it."
                        .to_string(),
                ),
                ViewNode::Text(format!(
                    "Passing and ENACTING are two different events. A proposal passes the moment \
                     approvals reach {}, and that changes nothing on its own; enacting is the turn \
                     that writes the candidate's value into the council's policy slot, and the \
                     replay verifier refuses a record where a policy slot moved without a passing \
                     decision behind it.",
                    session.quorum_m
                )),
            ],
        });

        for (pi, p) in session.proposals.iter().enumerate() {
            let cand = &self.catalog[p.catalog_index];
            let (reject, approve) = session.tally_of(pi).unwrap_or((0, 0));
            let (status, status_tag) = if p.enacted.is_some() {
                (
                    format!("ENACTED — the policy slot now reads {}", cand.value),
                    "good",
                )
            } else if approve >= session.quorum_m {
                (
                    "AT QUORUM — it passes, and waits for someone to enact it".to_string(),
                    "warn",
                )
            } else {
                (
                    format!(
                        "OPEN — {} more approval{} carries it",
                        session.quorum_m - approve,
                        if session.quorum_m - approve == 1 {
                            ""
                        } else {
                            "s"
                        }
                    ),
                    "accent",
                )
            };
            let cast = p
                .votes
                .iter()
                .map(|(who, opt)| {
                    let short: String = who.as_str().chars().take(8).collect();
                    let label = if *opt == APPROVE_OPTION {
                        "approve"
                    } else {
                        "reject"
                    };
                    let mine = viewer.is_some_and(|v| v == who);
                    ViewNode::Text(format!(
                        "{short}…{} voted {label}",
                        if mine { " (you)" } else { "" }
                    ))
                })
                .collect::<Vec<_>>();
            let mut kids = vec![
                ViewNode::Row(vec![pill(status, status_tag)]),
                // The tally as a real bar against the bar it has to clear — a count next to a
                // quorum is arithmetic the reader was left to do.
                ViewNode::Progress {
                    value: approve,
                    max: session.quorum_m.max(1),
                    label: "approvals".to_string(),
                },
                ViewNode::Text(format!(
                    "approve {approve} · reject {reject} — {}",
                    if session.is_weighted() {
                        "tallied by granted WEIGHT, on the verified cast_weighted path"
                    } else {
                        "one member, one vote"
                    }
                )),
            ];
            if viewer.is_some() {
                kids.push(ViewNode::Text(match voted_here(pi) {
                    Some(true) => "You voted APPROVE on this. You cannot vote again — a second \
                                   ballot from you is refused with nothing committed."
                        .to_string(),
                    Some(false) => "You voted REJECT on this. You cannot vote again — a second \
                                    ballot from you is refused with nothing committed."
                        .to_string(),
                    None if p.enacted.is_some() => {
                        "You never voted on this one, and it is already enacted.".to_string()
                    }
                    None => "You have NOT voted on this yet.".to_string(),
                }));
            }
            kids.push(ViewNode::Section {
                title: "Votes cast".to_string(),
                tag: "muted".to_string(),
                children: cast,
            });
            children.push(ViewNode::Section {
                title: format!("Proposal {pi}: {}", cand.title),
                tag: "accent".to_string(),
                children: kids,
            });
        }

        let items = self
            .actions(session)
            .into_iter()
            .map(|a| MenuItem {
                label: a.label,
                turn: a.turn,
                arg: a.arg,
                enabled: a.enabled,
            })
            .collect();
        children.push(ViewNode::Section {
            title: "Affordances".to_string(),
            tag: "accent".to_string(),
            children: vec![ViewNode::Menu { items }],
        });

        Surface(ViewNode::Section {
            title: "DreggNet Council".to_string(),
            tag: "accent".to_string(),
            children,
        })
    }

    /// A council over `members` (the electorate), able to open/vote/enact the given
    /// `catalog` of candidate proposals, at quorum `quorum_m` (APPROVE must reach this
    /// for a proposal to enact). `catalog` is truncated to [`MAX_CATALOG`].
    pub fn new(members: Vec<[u8; 32]>, catalog: Vec<CandidateProposal>, quorum_m: u64) -> Self {
        let mut catalog = catalog;
        catalog.truncate(MAX_CATALOG);
        CouncilOffering {
            members,
            weights: None,
            catalog,
            quorum_m: quorum_m.max(1),
        }
    }

    /// **A weighted council** — the same three affordances over the engine's weighted
    /// primitives: each `(member, weight)` grant makes that member's single ballot
    /// worth `weight` on `collective_choice::cast_weighted` (one nullifier carries the
    /// whole grant), every PROPOSE opens its poll with `open_poll_weighted_gated`, and
    /// `quorum_m` is a **WEIGHT** threshold on APPROVE — so a member whose grant alone
    /// clears it is a legitimate quorum, and `M` weight-1 ballots are no longer the
    /// only way there.
    ///
    /// The weights are **granted upstream and consumed here** (this crate proves no
    /// standing); a member granted `0` is a real zero-weight voter whose cast the
    /// engine refuses fail-closed without burning their ballot. A repeated member key
    /// keeps its LAST grant, and the electorate is the grant order.
    ///
    /// `catalog` is truncated to [`MAX_CATALOG`] and `quorum_m` is clamped to at least
    /// `1`, exactly as in [`new`](Self::new).
    pub fn new_weighted(
        grants: Vec<([u8; 32], u64)>,
        catalog: Vec<CandidateProposal>,
        quorum_m: u64,
    ) -> Self {
        let mut catalog = catalog;
        catalog.truncate(MAX_CATALOG);
        let mut members: Vec<[u8; 32]> = Vec::with_capacity(grants.len());
        let mut weights: HashMap<[u8; 32], u64> = HashMap::with_capacity(grants.len());
        for (pk, w) in grants {
            if weights.insert(pk, w).is_none() {
                members.push(pk);
            }
        }
        CouncilOffering {
            members,
            weights: Some(weights),
            catalog,
            quorum_m: quorum_m.max(1),
        }
    }

    /// The [`DreggIdentity`] a council member holds — the lowercase-hex of their public
    /// key. A [`Frontend`](dreggnet_offerings::Frontend) derives the SAME identity for
    /// the same member; an [`advance`](Offering::advance) whose `actor` is not one of
    /// these is a non-member (refused on VOTE/PROPOSE/ENACT).
    pub fn member_identity(pk: &[u8; 32]) -> DreggIdentity {
        DreggIdentity(hex(pk))
    }

    /// The catalog of candidate proposals this council can enact.
    pub fn catalog(&self) -> &[CandidateProposal] {
        &self.catalog
    }

    fn resolve_member(&self, session: &CouncilSession, actor: &DreggIdentity) -> Option<[u8; 32]> {
        session.member_pk.get(actor).copied()
    }
}

impl Offering for CouncilOffering {
    type Session = CouncilSession;

    /// Deploy a fresh council: a `collective-choice` engine + a real executor hosting a
    /// freshly-seeded **council cell** (a `WriteOnce` policy slot per catalog item + a
    /// monotone proposals-opened counter), funded so it can author governance turns. The
    /// seed in `cfg` pins the federation/cell identity (a re-open under the same seed is
    /// the same council).
    fn open(&self, cfg: SessionConfig) -> Result<CouncilSession, OfferingError> {
        let seed = cfg.seed.unwrap_or(1);
        let fed = federation_id_from_seed(seed);

        // The vote substrate.
        let engine = CollectiveChoice::new(fed);

        // The enactment substrate: a dedicated operator + executor hosting the council cell.
        let clerk = AppCipherclerk::new(AgentCipherclerk::new(), fed);
        let exec = EmbeddedExecutor::new(&clerk, "default");
        let operator = clerk.public_key().0;

        // Fund the operator so it can pay the propose/enact turn fees.
        let operator_cell = clerk.cell_id();
        exec.with_ledger_mut(|ledger| {
            if let Some(cell) = ledger.get_mut(&operator_cell) {
                cell.state.set_balance(1_000_000_000);
            }
        });

        // Seed the council cell: install the program so the executor re-enforces
        // WriteOnce(policy_i) / Monotonic(proposals_opened) on every touching turn, then
        // pin the genesis state (all zero).
        let token = *blake3::hash(&[b"dreggnet-council".as_slice(), &seed.to_be_bytes()].concat())
            .as_bytes();
        let council_cell = CellId::derive_raw(&operator, &token);
        let program = Self::council_program(self.catalog.len());
        let mut cell = Cell::new(operator, token);
        cell.program = program.clone();
        cell.state
            .set_field(PROPOSALS_OPENED_SLOT, field_from_u64(0));
        for i in 0..self.catalog.len() {
            cell.state.set_field(POLICY_BASE + i, field_from_u64(0));
        }
        exec.ensure_cell(cell)
            .map_err(|e| OfferingError::Deploy(e.to_string()))?;
        exec.install_program(council_cell, program);

        // Grant the operator a cap reaching the council cell so propose/enact turns author against it.
        exec.with_ledger_mut(|ledger| {
            if let Some(agent) = ledger.get_mut(&operator_cell) {
                agent
                    .capabilities
                    .grant(council_cell, AuthRequired::Signature);
            }
        });

        let member_pk = self
            .members
            .iter()
            .map(|pk| (CouncilOffering::member_identity(pk), *pk))
            .collect();

        Ok(CouncilSession {
            engine,
            clerk,
            exec,
            council_cell,
            members: self.members.clone(),
            quorum_m: self.quorum_m,
            weights: self.weights.clone(),
            catalog: self.catalog.clone(),
            member_pk,
            proposals: Vec::new(),
            receipts: Vec::new(),
        })
    }

    /// The council's current cap-gated affordances: a PROPOSE for every catalog item not
    /// yet proposed, plus APPROVE / REJECT / ENACT for every open proposal. `enabled` is a
    /// decoration (ENACT shows enabled once APPROVE has reached quorum) — the executor is
    /// the sole referee on `advance`.
    fn actions(&self, session: &CouncilSession) -> Vec<Action> {
        let mut out = Vec::new();
        let proposed: Vec<usize> = session.proposals.iter().map(|p| p.catalog_index).collect();
        for (i, cand) in self.catalog.iter().enumerate() {
            if !proposed.contains(&i) {
                out.push(Action::new(
                    format!("Propose: {}", cand.title),
                    TURN_PROPOSE,
                    i as i64,
                    true,
                ));
            }
        }
        for (pi, p) in session.proposals.iter().enumerate() {
            let title = &self.catalog[p.catalog_index].title;
            let (_, approve) = session.tally_of(pi).unwrap_or((0, 0));
            out.push(Action::new(
                format!("Approve: {title}"),
                TURN_APPROVE,
                pi as i64,
                p.enacted.is_none(),
            ));
            out.push(Action::new(
                format!("Reject: {title}"),
                TURN_REJECT,
                pi as i64,
                p.enacted.is_none(),
            ));
            out.push(Action::new(
                format!("Enact: {title}"),
                TURN_ENACT,
                pi as i64,
                p.enacted.is_none() && approve >= session.quorum_m,
            ));
        }
        out
    }

    /// **Resolve one governance move as a real turn.** PROPOSE opens a poll + commits a
    /// council-cell turn; APPROVE/REJECT cast a write-once ballot; ENACT applies the
    /// proposal's effect iff the engine's quorum gate admits the decision. A member drives
    /// each; a non-member (`actor` not in the electorate) is refused. Illegal / double /
    /// below-quorum moves are real [`Outcome::Refused`] that commit nothing (anti-ghost).
    fn advance(
        &self,
        session: &mut CouncilSession,
        input: Action,
        actor: DreggIdentity,
    ) -> Outcome {
        let Some(voter_pk) = self.resolve_member(session, &actor) else {
            return Outcome::Refused("not a council member".to_string());
        };
        match input.turn.as_str() {
            TURN_PROPOSE => self.do_propose(session, input.arg),
            TURN_APPROVE => self.do_vote(session, input.arg, voter_pk, actor, APPROVE_OPTION),
            TURN_REJECT => self.do_vote(session, input.arg, voter_pk, actor, REJECT_OPTION),
            TURN_ENACT => self.do_enact(session, input.arg),
            other => Outcome::Refused(format!("unknown affordance: {other}")),
        }
    }

    /// **Re-verify the decision chain** — read-only, over both committed substrates:
    /// (1) for every poll, the executor's stored monotone tally equals the light-client
    /// recompute (nobody stuffed a board); (2) every ENACTED proposal has its policy slot
    /// committed to the catalog value AND a passing decision (APPROVE at quorum); (3) every
    /// UNENACTED proposal leaves its policy slot `0` (the below-quorum tooth). Any break —
    /// a forged board, an enacted effect that does not match its decision, or a phantom
    /// effect with no passing vote — fails.
    fn verify(&self, session: &CouncilSession) -> VerifyReport {
        // `VerifyReport::turns` is the cross-offering "genesis + committed steps" count (its
        // own doc, and how every substrate-backed sibling reports it — the dungeon's
        // `receipts_len` is `1 + steps`). The council cell is seeded with its genesis state at
        // `open` (the `WriteOnce`/`Monotonic` program + the all-zero slots), so the verified
        // chain is that genesis turn plus each committed governance turn. `committed_turns`
        // stays the governance-only tally (propose + vote + enact); the genesis is the `+ 1`.
        let turns = 1 + session.committed_turns();
        for (pi, p) in session.proposals.iter().enumerate() {
            // (1) board integrity: the stored monotone tally == the light-client recompute.
            let stored = match session.engine.tally(p.poll) {
                Ok(t) => t,
                Err(e) => return VerifyReport::broken(turns, format!("proposal {pi} tally: {e}")),
            };
            let lc = match session.engine.light_client_tally(p.poll) {
                Ok(t) => t,
                Err(e) => {
                    return VerifyReport::broken(turns, format!("proposal {pi} light-client: {e}"));
                }
            };
            if stored != lc {
                return VerifyReport::broken(
                    turns,
                    format!("proposal {pi}: stored tally diverges from the light-client recompute"),
                );
            }

            // (2)/(3) enactment consistency against the committed council cell.
            let slot_val = session.policy_value(p.catalog_index);
            let expected = self.catalog[p.catalog_index].value;
            match &p.enacted {
                Some(_) => {
                    if slot_val != expected {
                        return VerifyReport::broken(
                            turns,
                            format!("proposal {pi}: enacted policy slot {slot_val} != {expected}"),
                        );
                    }
                    match &p.decision {
                        Some(d)
                            if d.winner == APPROVE_OPTION && d.winner_tally >= session.quorum_m => {
                        }
                        _ => {
                            return VerifyReport::broken(
                                turns,
                                format!("proposal {pi}: enacted without a passing decision"),
                            );
                        }
                    }
                }
                None => {
                    if slot_val != 0 {
                        return VerifyReport::broken(
                            turns,
                            format!("proposal {pi}: unenacted, yet its policy slot is {slot_val}"),
                        );
                    }
                }
            }
        }
        VerifyReport::ok(turns)
    }

    /// Render the council as a deos affordance [`Surface`]: the quorum, each proposal with
    /// its live `(reject, approve)` tally + enactment state, and the cap-gated affordances.
    fn render(&self, session: &CouncilSession) -> Surface {
        self.render_as(session, None)
    }

    /// **The council as `viewer` stands in it.** Nothing here is secret — every ballot is published
    /// with the identity that cast it, which is the point of a council — but "have I voted, and can
    /// I" was previously answerable only by scanning a list of truncated hashes for your own. The
    /// per-viewer render answers it in a sentence.
    fn render_for(&self, session: &CouncilSession, viewer: &DreggIdentity) -> Surface {
        self.render_as(session, Some(viewer))
    }

    /// **The governance affordances AS `viewer` may fire them** — every row of
    /// [`actions`](Offering::actions), with each one DIMMED for a viewer who is not in the
    /// electorate.
    ///
    /// ⚑ Without this override the trait default falls back to the anonymous, fully-enabled
    /// [`actions`](Offering::actions), so a visitor holding no seat on this council was served
    /// live, undimmed Propose / Approve / Reject / Enact controls, every one of which `advance`
    /// answers "not a council member" — the whole page was dead affordances, and the only way to
    /// learn it was to press. The cap tooth is SHOWN, not hidden: the rows keep their turn and
    /// `arg` (so a frontend validating a POST against this list still reaches the executor and
    /// gets ITS refusal), and the executor stays the sole referee — `enabled` is decoration.
    fn actions_for(&self, session: &CouncilSession, viewer: &DreggIdentity) -> Vec<Action> {
        let mut all = self.actions(session);
        if self.resolve_member(session, viewer).is_none() {
            for action in &mut all {
                action.enabled = false;
            }
        }
        all
    }

    /// Governance turns are free + verifiable (the substrate turn itself always is). A
    /// fuller offering could price a confined deliberation overlay; here every move is free.
    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

impl CouncilOffering {
    /// PROPOSE: open a per-option-gated `reject/approve` poll for catalog item `arg` and
    /// commit a council-cell turn recording the opening. Refused if `arg` is out of range or
    /// the catalog item already has an open proposal (one live proposal per catalog item).
    fn do_propose(&self, session: &mut CouncilSession, arg: i64) -> Outcome {
        if arg < 0 || arg as usize >= session.catalog.len() {
            return Outcome::Refused("no such catalog item".to_string());
        }
        let catalog_index = arg as usize;
        if session
            .proposals
            .iter()
            .any(|p| p.catalog_index == catalog_index)
        {
            return Outcome::Refused("that item already has an open proposal".to_string());
        }

        // Open the poll on the real engine (reject/approve, gated on APPROVE at quorum M).
        let spec = PollSpec {
            question: session.catalog[catalog_index].title.clone(),
            options: vec!["reject".to_string(), "approve".to_string()],
            electorate: session.members.clone(),
            quorum_m: session.quorum_m,
        };
        // A weighted council opens the WEIGHTED gated poll: `quorum_m` becomes a weight
        // threshold on APPROVE and the tallies are the ones `cast_weighted` bumps by a
        // member's whole grant. Unweighted opens exactly the poll it always did.
        let opened = if session.is_weighted() {
            session
                .engine
                .open_poll_weighted_gated(spec, APPROVE_OPTION)
        } else {
            session.engine.open_poll_gated(spec, APPROVE_OPTION)
        };
        let poll = match opened {
            Ok(p) => p,
            Err(e) => return Outcome::Refused(format!("poll open refused: {e}")),
        };

        // Commit a real council-cell turn recording the opening (bump the monotone counter).
        let live = session.read_slot(PROPOSALS_OPENED_SLOT);
        let effects = vec![
            Effect::SetField {
                cell: session.council_cell,
                index: PROPOSALS_OPENED_SLOT as u64,
                value: field_from_u64(live + 1),
            },
            Effect::EmitEvent {
                cell: session.council_cell,
                event: Event::new(
                    symbol("council-proposal-opened"),
                    vec![field_from_u64(catalog_index as u64)],
                ),
            },
        ];
        let action = session
            .clerk
            .make_action(session.council_cell, "open_proposal", effects);
        let receipt = match session.exec.submit_action(&session.clerk, action) {
            Ok(r) => r,
            Err(e) => return Outcome::Refused(format!("executor refused the proposal turn: {e}")),
        };

        session.proposals.push(ProposalState {
            catalog_index,
            poll,
            ballots: HashMap::new(),
            votes: Vec::new(),
            enacted: None,
            decision: None,
        });
        session.receipts.push(receipt.clone());
        Outcome::Landed {
            receipt,
            ended: false,
        }
    }

    /// VOTE: cast a single-use ballot for `voter_pk` on proposal `arg`. The engine's
    /// `WriteOnce(VOTE)` + nullifier make a second vote a real [`Outcome::Refused`]; a
    /// non-electorate voter holds no cap (Ineligible → Refused). A cast lands a real receipt.
    /// In a weighted council the cast rides `cast_weighted` at the member's granted
    /// weight, and a zero-weight member is refused before the ballot is consumed.
    fn do_vote(
        &self,
        session: &mut CouncilSession,
        arg: i64,
        voter_pk: [u8; 32],
        actor: DreggIdentity,
        option: usize,
    ) -> Outcome {
        if arg < 0 || arg as usize >= session.proposals.len() {
            return Outcome::Refused("no such proposal".to_string());
        }
        let pi = arg as usize;
        if session.proposals[pi].enacted.is_some() {
            return Outcome::Refused("that proposal is already enacted".to_string());
        }
        let poll = session.proposals[pi].poll;

        // The weighted floor, checked BEFORE the ballot is minted or consumed: the
        // engine refuses a zero-weight cast (`VoteError::ZeroWeight`) precisely so a
        // worthless cast never burns the member's single ballot — refusing here keeps
        // that promise one step earlier, with the same effect (nothing committed).
        let weight = session.member_weight(&voter_pk);
        if session.is_weighted() && weight == 0 {
            return Outcome::Refused(
                "that member's granted ballot weight is 0 — the cast is refused \
                 fail-closed and their single-use ballot is NOT consumed"
                    .to_string(),
            );
        }

        // Issue (idempotent) the voter's single-use ballot cap. Ineligible → non-member → refused.
        let existing = session.proposals[pi].ballots.get(&voter_pk).cloned();
        let cap = match existing {
            Some(c) => c,
            None => {
                let c = match session.engine.issue_ballot(poll, voter_pk) {
                    Ok(c) => c,
                    Err(VoteError::Ineligible) => {
                        return Outcome::Refused(
                            "voter is not in the council electorate".to_string(),
                        );
                    }
                    Err(e) => return Outcome::Refused(format!("ballot issue refused: {e}")),
                };
                session.proposals[pi].ballots.insert(voter_pk, c.clone());
                c
            }
        };

        // Cast: the ballot turn is refereed by the executor (WriteOnce + monotone tally).
        // A weighted council rides `cast_weighted`, so the member's WHOLE grant lands on
        // ONE nullifier — never `weight` separate weight-1 ballots, which is exactly the
        // amplification the delegation lattice forbids. Unweighted rides plain `cast`.
        let cast = if session.is_weighted() {
            session.engine.cast_weighted(poll, &cap, option, weight)
        } else {
            session.engine.cast(poll, &cap, option)
        };
        match cast {
            Ok(receipt) => {
                session.proposals[pi].votes.push((actor, option));
                session.receipts.push(receipt.clone());
                Outcome::Landed {
                    receipt,
                    ended: false,
                }
            }
            Err(VoteError::DoubleVote) => {
                Outcome::Refused("that member has already voted on this proposal".to_string())
            }
            Err(VoteError::ZeroWeight) => Outcome::Refused(
                "that member's granted ballot weight is 0 — the cast is refused \
                 fail-closed and their single-use ballot is NOT consumed"
                    .to_string(),
            ),
            Err(e) => Outcome::Refused(format!("vote refused: {e}")),
        }
    }

    /// ENACT: attempt proposal `arg`. The engine's quorum `AffineLe` gate is the real
    /// referee — `resolve` yields `None` below quorum, so ENACT is refused and NOTHING is
    /// applied. At quorum with APPROVE winning, the proposal's effect (a `WriteOnce` policy
    /// write) commits as one executor-refereed turn → [`Outcome::Landed`].
    fn do_enact(&self, session: &mut CouncilSession, arg: i64) -> Outcome {
        if arg < 0 || arg as usize >= session.proposals.len() {
            return Outcome::Refused("no such proposal".to_string());
        }
        let pi = arg as usize;
        if session.proposals[pi].enacted.is_some() {
            return Outcome::Refused("that proposal is already enacted".to_string());
        }
        let poll = session.proposals[pi].poll;

        // THE QUORUM GATE (executor-refereed inside the engine): resolve the decision-turn.
        // Below quorum the AffineLe (`M·RESOLVED − TALLY_approve ≤ 0`) refuses it → None.
        let decision = match session.engine.resolve(poll) {
            Ok(Some(d)) => d,
            Ok(None) => {
                return Outcome::Refused(
                    "below quorum: the proposal has not passed — nothing enacted".to_string(),
                );
            }
            Err(e) => return Outcome::Refused(format!("resolve refused: {e}")),
        };
        // A contested board (APPROVE reached M but did not win) is not a mandate to enact.
        if decision.winner != APPROVE_OPTION || decision.winner_tally < session.quorum_m {
            return Outcome::Refused(
                "the proposal was not approved at quorum — nothing enacted".to_string(),
            );
        }

        // Apply the REAL effect: write the proposal's value into its WriteOnce policy slot
        // as one committed executor-refereed turn. A double-enact is refused (WriteOnce).
        let catalog_index = session.proposals[pi].catalog_index;
        let value = session.catalog[catalog_index].value;
        let effects = vec![
            Effect::SetField {
                cell: session.council_cell,
                index: u64::try_from(POLICY_BASE + catalog_index)
                    .expect("council policy slot fits the stable u64 wire format"),
                value: field_from_u64(value),
            },
            Effect::EmitEvent {
                cell: session.council_cell,
                event: Event::new(
                    symbol("council-proposal-enacted"),
                    vec![field_from_u64(catalog_index as u64), field_from_u64(value)],
                ),
            },
        ];
        let action = session
            .clerk
            .make_action(session.council_cell, "enact_proposal", effects);
        let receipt = match session.exec.submit_action(&session.clerk, action) {
            Ok(r) => r,
            Err(e) => return Outcome::Refused(format!("executor refused the enactment: {e}")),
        };

        session.proposals[pi].enacted = Some(receipt.clone());
        session.proposals[pi].decision = Some(decision);
        session.receipts.push(receipt.clone());
        Outcome::Landed {
            receipt,
            ended: false,
        }
    }

    /// The council cell's program: `WriteOnce` on every policy slot (so an enacted effect
    /// commits exactly once) + `Monotonic` on the proposals-opened counter.
    fn council_program(catalog_len: usize) -> CellProgram {
        let mut cs = vec![StateConstraint::Monotonic {
            index: PROPOSALS_OPENED_SLOT as u8,
        }];
        for i in 0..catalog_len {
            cs.push(StateConstraint::WriteOnce {
                index: (POLICY_BASE + i) as u8,
            });
        }
        CellProgram::always(cs)
    }
}

// ── small helpers ─────────────────────────────────────────────────────────────

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// [`field_from_u64`], matching the executor's `affine_sum` decode).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// Lowercase-hex of a 32-byte public key (a member's stable [`DreggIdentity`]).
fn hex(pk: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for &b in pk {
        s.push(char::from_digit((b >> 4) as u32, 16).unwrap());
        s.push(char::from_digit((b & 0xf) as u32, 16).unwrap());
    }
    s
}

/// Derive a stable federation id from a session seed.
fn federation_id_from_seed(seed: u64) -> [u8; 32] {
    *blake3::hash(&[b"dreggnet-council-fed".as_slice(), &seed.to_be_bytes()].concat()).as_bytes()
}
