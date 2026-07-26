//! # Phase 5 — the **Offering** + the per-player HIDDEN-HAND surface.
//!
//! [`TugOffering`] hosts a multiway-tug round as a [`dreggnet_offerings::Offering`]: the
//! same `open`/`actions`/`advance`/`verify`/`render`/`price` shape every dreggnet frontend
//! (Discord / Telegram / WeChat / web) already drives. A play is a REAL executor turn (the
//! [`crate::game::MultiwayTug`] driver commits the [`crate::reference::Engine`]'s projection
//! under the action method — a legal move lands a [`dreggnet_offerings::Outcome::Landed`]
//! receipt, an out-of-turn / illegal one is a [`dreggnet_offerings::Outcome::Refused`] that
//! commits nothing).
//!
//! **The differentiated bit — the per-player fog plus live admission.** [`Offering::render`] paints ONE public
//! surface (both hands are FOG — a count + the committed hand root). [`Offering::render_for`]
//! paints the surface *as a specific viewer sees it*: the viewer's OWN hand is revealed (the
//! exact distinct card ids held by the reference engine and committed by the
//! [`crate::hidden_hand`] [`HandTree`]), while
//! the opponent stays fog. So player A's card ids appear in A's view and NOT in B's view of
//! the same table — the hidden-hand fog, in the UI.
//!
//! The guild-lane table + coordinate-grid hand + affordance menu are the deos affordance
//! surface. On advance, every exact 4/3/2/1-card consumption carries its private inventory
//! membership witness into the executor. The Lean-authored rules action and the witnessed
//! hidden action share one atomic turn, so either both cells land or neither does.
//!
//! ## ⚑ THE SEAT DECIDES — the `{turn, arg}` encoding
//!
//! There is no schedule to fire: [`TugSession::legal_decisions`] is the seat's full choice
//! space (which action-kind, which favors, which PAIRING, and — answering — which side), and
//! an [`Offering::advance`] input names one of them by INDEX (`arg`) plus that decision's
//! dispatch method (`turn`). [`Offering::actions`] presents a manageable slice of it: while an
//! offer stands, the response sides and nothing else; otherwise one row per unused
//! action-kind aimed at one concrete cut. A frontend that wants to choose the cut reads
//! `legal_decisions()` and posts that index.
//!
//! A RESPONSE carries no membership witness (its cards left the hand when the offer was cut),
//! so it is the rules projection alone, dispatched under the Lean-emitted `respond_gift` /
//! `respond_comp` case.
//!
//! HONEST RESIDUAL: duplicate-card consumption is an exact host ratchet checked again by
//! fresh-seed replay, not a protocol-native dynamic-root/nullifier tooth.

use deos_view::{CoordCell, MenuItem, PillCase, ViewNode};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

use crate::hidden_hand::{HandTree, HiddenHandLedger, deck_guild};
use crate::reference::{
    ActionKind, Decision, Engine, INFLUENCE, N_GUILDS, PendingOffer, Player, Projection,
    ROUND_TURNS, decision_method,
};

/// The default round seed when a [`SessionConfig`] pins none.
const DEFAULT_SEED: u64 = 0xD2E9;

/// The number of favor cards each player is dealt into the committed hidden hand (the standard
/// six-card opening). Distinct card ids `0..21` (see [`crate::hidden_hand`]) — seat A gets the
/// first six, seat B the next six.
const HAND_SIZE: usize = 6;

/// **The multiway-tug Offering** — hosts one round as a dreggnet [`Offering`] with a per-player
/// hidden-hand surface. Stateless; the live round lives in [`TugSession`].
pub struct TugOffering;

impl TugOffering {
    /// The deterministic seat identity for a player (the two seats a frontend maps its two
    /// players onto). A frontend that knows which of its users holds seat A passes THIS identity
    /// to [`Offering::render_for`] to serve A's private hand.
    pub fn seat_identity(p: Player) -> DreggIdentity {
        match p {
            Player::A => DreggIdentity("multiway-tug:seat-A".to_string()),
            Player::B => DreggIdentity("multiway-tug:seat-B".to_string()),
        }
    }

    /// Which seat an identity holds (`None` = a spectator: they see both hands as fog).
    fn seat_of(viewer: &DreggIdentity) -> Option<Player> {
        if *viewer == Self::seat_identity(Player::A) {
            Some(Player::A)
        } else if *viewer == Self::seat_identity(Player::B) {
            Some(Player::B)
        } else {
            None
        }
    }
}

/// A live multiway-tug round: the REAL executor game, the reference mover, and each player's
/// committed hidden hand (the source of the per-viewer reveal + the opponent fog).
pub struct TugSession {
    /// Deterministic deployment/deal seed. Replay verification opens a fresh
    /// confined game from this exact seed and re-drives every accepted input.
    seed: u64,
    /// One embedded executor containing both the Lean-authored rules cell and the witnessed
    /// hidden-hand cell. Every Offering advance is an atomic multi-action turn over both.
    runtime: HiddenHandLedger,
    /// The reference mover — card identities + the next projection each play commits.
    engine: Engine,
    /// Each seat's CURRENT committed hidden hand. It is rebuilt from the engine's exact distinct
    /// card ids after every draw-and-play; there is no independently invented UI deal.
    hands: [HandTree; 2],
    /// Whether the round has ended (the round completed).
    ended: bool,
    /// THE PRIVATE FOLD RECORD: all ten distinct cards entrusted to each player during this
    /// deterministic round (opening six + four draws), committed with stable per-card blinds.
    /// This is deliberately separate from `hands`, whose root tracks only the CURRENT hand.
    fold_inventory: [Vec<(u64, u64)>; 2],
    /// Each seat's full-round inventory with already-consumed cards removed. Its root is the
    /// hidden ledger's dynamic remaining-inventory commitment; unlike `hands`, it includes future
    /// draws and is therefore never rendered or exposed while the round is live.
    proof_hands: [HandTree; 2],
    /// The ordered card ids each seat actually PLAYED (all cards consumed by an action, rather
    /// than one arbitrary representative). Every id belongs to that seat's `fold_inventory`.
    plays: [Vec<u64>; 2],
    /// Accepted player inputs, in order. Refusals never enter this log. This is
    /// deliberately action-level rather than a trusted projection snapshot:
    /// [`Offering::verify`] replays it through a fresh engine and executor.
    history: Vec<LandedInput>,
}

/// The terminal owner-only material handed to the post-match fold. It is unavailable while a
/// round is live, so the precomputed four future draws cannot leak through the public session API.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TugPrivateMatchRecord {
    pub hand: Vec<(u64, u64)>,
    pub plays: Vec<u64>,
}

/// An accepted player input, recorded in FULL so [`Offering::verify`]'s fresh-seat replay is
/// faithful: the seat plus the exact [`Decision`] it made (which cards, which cut, which pick),
/// not merely which action-kind it spent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LandedInput {
    Play { seat: Player, decision: Decision },
    Score { seat: Player },
}

impl TugSession {
    /// The seat to move next — to ACT, or (while an offer stands) to ANSWER.
    pub fn to_move(&self) -> Player {
        self.engine.current_player()
    }

    /// **Every legal decision for the seat to move.** THE `arg` ENCODING: an
    /// [`Offering::advance`] input names its decision by INDEX into exactly this vector,
    /// with `turn` set to that decision's dispatch method
    /// ([`crate::reference::decision_method`]). The vector is a deterministic function of the
    /// committed state, so the same index means the same decision on a fresh replay.
    pub fn legal_decisions(&self) -> Vec<Decision> {
        self.engine.legal_decisions()
    }

    /// The offer on the table, if any — who cut, and what they presented.
    pub fn pending_offer(&self) -> Option<PendingOffer> {
        self.engine.pending_offer()
    }

    /// Whether the round has ended.
    pub fn ended(&self) -> bool {
        self.ended || self.engine.projection().scored == 1
    }

    /// THE MATCH-RECORD SEAM — after SCORE only, return the seat's private full-round inventory
    /// (opening hand + later draws) and actual played-card order. While the match is live this is
    /// `None`: a frontend cannot use the fold accessor to peek at future draws. The fold's public
    /// inputs never contain these card ids.
    pub fn terminal_match_record(&self, seat: Player) -> Option<TugPrivateMatchRecord> {
        if !self.ended() {
            return None;
        }
        Some(TugPrivateMatchRecord {
            hand: self.fold_inventory[seat.idx()].clone(),
            plays: self.plays[seat.idx()].clone(),
        })
    }

    /// The terminal WIN facts once the round has scored: `(winner, charm)` where `winner` is
    /// `1` (seat A) / `2` (seat B) and `charm` is the winner's total influence — exactly the two
    /// bound public inputs of the whole-match fold's win leaf. `None` while the round runs, or on
    /// a genuine DRAW — which since the terminal rule reached the deployed teeth means an EXACT
    /// dead heat on both influence and rows held (`roundWinner_draw_iff`), not merely "nobody
    /// cleared 11".
    pub fn win_facts(&self) -> Option<(u64, u64)> {
        let proj = self.projection();
        match proj.winner {
            1 => Some((1, proj.charm[0])),
            2 => Some((2, proj.charm[1])),
            _ => None,
        }
    }

    /// The committed public projection (both hands appear as counts here — the fog datum).
    fn projection(&self) -> Projection {
        self.runtime.read_projection()
    }

    /// The guild-lane table: one row per guild — its influence WEIGHT as a [`ViewNode::Pill`],
    /// the two placement counters (A / B), and a control [`ViewNode::Icon`] (who leads the lane).
    /// ⚑ One `ViewNode::Table` and no more: `surface/tests.rs::guild_lanes_and_action_menu_render`
    /// counts EVERY table in the tree and expects exactly [`N_GUILDS`] rows, so any other tabular
    /// block on this surface is a [`ViewNode::List`] of [`ViewNode::Row`]s instead.
    fn guild_lanes(&self, proj: &Projection) -> ViewNode {
        let mut rows = Vec::with_capacity(N_GUILDS);
        for g in 0..N_GUILDS {
            let a = proj.score[g][0];
            let b = proj.score[g][1];
            let w = INFLUENCE[g] as u64;
            // Control: whoever placed more favors leads the lane (a tie is contested). The lane's
            // STANDING is a word, not a letter — `A` in a column of numbers told a reader nothing
            // about whether the lane was won, and a lane's whole job is to say who holds it.
            let (lead, ctrl_tag) = if a > b {
                (format!("A holds it (+{})", a - b), "good")
            } else if b > a {
                (format!("B holds it (+{})", b - a), "accent")
            } else if a == 0 {
                ("nobody has pulled".to_string(), "muted")
            } else {
                ("contested — dead even".to_string(), "warn")
            };
            let weight_tag = if w >= 4 { "accent" } else { "muted" };
            rows.push(ViewNode::Row(vec![
                // ⚑ THE EQUATION, IN EVERY ROW. `guild` and `lane` were used interchangeably across
                // this surface and never once equated, so a reader met two vocabularies for one
                // object (`docs/reference/UX-QA-SWEEP-2026-07-26.md`). The row now says both names
                // for itself, seven times, and the section prose says it in words above. Redundant
                // on purpose: the redundancy IS the definition.
                ViewNode::Text(format!("Guild {g} · lane {g}")),
                ViewNode::Pill {
                    text: format!("worth {w}"),
                    tag: weight_tag.to_string(),
                    slot: None,
                    cases: Vec::<PillCase>::new(),
                },
                ViewNode::Text(format!("A {a} · B {b}")),
                ViewNode::Pill {
                    text: lead,
                    tag: ctrl_tag.to_string(),
                    slot: None,
                    cases: Vec::<PillCase>::new(),
                },
            ]));
        }
        ViewNode::Table(rows)
    }

    /// ⚑ **WHY THE LANES DID NOT MOVE.** The one sentence a first-time reader needed and did not
    /// get: they pressed a button, every one of the seven lane rows came back byte-identical, and
    /// their verdict was *"I would have concluded the button did nothing"*
    /// (`docs/reference/UX-QA-SWEEP-2026-07-26.md`).
    ///
    /// The page was CORRECT and silent, which is indistinguishable from broken. Only two events ever
    /// move a lane counter, and neither is "you spent an action":
    ///
    /// * a **response** — a Gift or Competition puts its favors in ESCROW, and the split lands on the
    ///   two sides only when the OTHER seat answers the cut;
    /// * the **score** — each face-down Secret turns up onto its owner's side before control is
    ///   counted (Lean `secret_is_scored`).
    ///
    /// A Secret and a Discard therefore move these rows by exactly nothing, forever and by design
    /// (a Discard's two favors leave the round and nobody ever scores them). Said out loud, plus the
    /// live 21-favor accounting from [`Self::favor_accounting`], the still scoreboard becomes a
    /// reading of the game instead of a suspected bug.
    fn lane_movement_rule(&self) -> String {
        let pending = match self.engine.pending_offer() {
            Some(offer) => format!(
                " Right now seat {:?}'s {:?} is sitting in escrow: those favors have left their hand \
                 and reached NO lane — seat {:?}'s answer is what places them.",
                offer.proposer,
                offer.kind(),
                offer.responder(),
            ),
            None => String::new(),
        };
        format!(
            "⚑ SPENDING AN ACTION DOES NOT MOVE THESE ROWS. Two things do, and only two: the other \
             seat ANSWERING your Gift or Competition (which is what actually places the favors on \
             the two sides), and the final REVEAL & SCORE (where every face-down Secret turns up \
             onto its owner's side). A Secret changes these numbers by nothing until scoring, and a \
             Discard's two favors leave the round for good — so a still scoreboard right after your \
             move is the rules working, not a stuck page. The tally below is what moved.{pending}"
        )
    }

    /// **Where all 21 favors are, right now** — the line that MOVES when the lanes cannot.
    ///
    /// Every favor is in exactly one of five places and the executor's conservation tooth pins the
    /// total at [`crate::reference::DECK_SIZE`] every turn ([`Projection::conservation_sum`]), so this
    /// is a complete account rather than a selection. It is also the honest home of the escrow: the
    /// projection folds a pending offer's cards into the PROPOSER's hand entry (mirroring the Lean's
    /// `pendingCards`), so the count is named as "held or in escrow" instead of quietly reading as
    /// "still in hand".
    fn favor_accounting(&self, proj: &Projection) -> String {
        let held = proj.hand[0] + proj.hand[1];
        let secrets = proj.secret_count[0] + proj.secret_count[1];
        let placed = proj.board[0] + proj.board[1];
        format!(
            "All {total} favors, right now: {held} held or in escrow ({a_hand} · {b_hand}) · \
             {secrets} face down as Secrets ({a_secret} · {b_secret}), which score at the reveal · \
             {burnt} burnt by Discards, which nobody will ever score · {placed} placed on the lanes \
             above ({a_board} · {b_board}) · {deck} still in the deck.",
            total = crate::reference::DECK_SIZE,
            held = held,
            a_hand = proj.hand[0],
            b_hand = proj.hand[1],
            secrets = secrets,
            a_secret = proj.secret_count[0],
            b_secret = proj.secret_count[1],
            burnt = proj.oop,
            placed = placed,
            a_board = proj.board[0],
            b_board = proj.board[1],
            deck = proj.deck,
        )
    }

    /// **The one sentence that says what to do right now** — the automatafl `next_step_line`
    /// convention, which the renderer promotes to a lead inside an `accent` plaque. A tug player's
    /// standing question is never "what are the rules", it is "is it me, and for what".
    ///
    /// `claimant` is the seat a SEATLESS viewer would take on their first landed press (`None` for a
    /// true spectator, both seats held). It exists because the two seatless states are genuinely
    /// different — one has live controls, the other has none — and telling both of them the same
    /// thing is what made the "every control is inert" line false.
    fn next_step_line(&self, viewer: Option<Player>, claimant: Option<Player>) -> String {
        let proj = self.projection();
        if proj.scored == 1 {
            return match proj.winner {
                1 => "The round is over — seat A took it. Nothing further can be committed.",
                2 => "The round is over — seat B took it. Nothing further can be committed.",
                _ => {
                    "The round is over — an exact dead heat on influence AND on lanes held, \
                      which is the only draw the rules admit."
                }
            }
            .to_string();
        }
        if self.engine.round_complete() {
            return "Every favor is placed. Press Reveal secrets & score — each seat's face-down \
                    Secret turns up onto its own side BEFORE control is counted, and the proven \
                    rule names the winner."
                .to_string();
        }
        let mover = if proj.current == 0 {
            Player::A
        } else {
            Player::B
        };
        let yours = viewer == Some(mover);
        if let Some(offer) = self.engine.pending_offer() {
            let answering = offer.responder();
            return if viewer == Some(answering) {
                format!(
                    "Seat {:?} has cut a {:?} and it is FACE UP. Choose the side you take — what \
                     you leave goes to them, and you cannot un-choose.",
                    offer.proposer,
                    offer.kind()
                )
            } else if viewer == Some(offer.proposer) {
                format!(
                    "You cut a {:?}. Seat {:?} now chooses which side they take; whatever they \
                     leave lands on YOUR side of those lanes. Nothing to press.",
                    offer.kind(),
                    answering
                )
            } else {
                format!(
                    "Seat {:?}'s {:?} is on the table face up; seat {:?} is choosing which side to \
                     take.",
                    offer.proposer,
                    offer.kind(),
                    answering
                )
            };
        }
        if yours {
            "Your move. Spend ONE of your four actions — each is once per round, and the heavier \
             ones commit more favors, so the order is the game."
                .to_string()
        } else if viewer.is_some() {
            format!(
                "Waiting on seat {mover:?}. They are choosing which of their unspent actions to \
                 commit; your hand is untouched until it is your move again."
            )
        } else if let Some(claim) = claimant {
            // ⚑ NOT "every control is inert". This viewer holds no seat AND a seat is free, so the
            // buttons below are LIVE and the first press that lands takes that seat. Saying they
            // were inert while serving working controls was the exact falsehood the QA sweep
            // proved from a before/after pair (finding 2).
            format!(
                "Seat {mover:?} is to move. You hold no seat YET — the controls below are LIVE, and \
                 the first move you land CLAIMS seat {claim:?}. Both hands stay fog to you until \
                 then."
            )
        } else {
            format!(
                "Seat {mover:?} is to move. Both seats are held, so you are watching: both hands \
                 are fog to you, and a move from an actor holding no seat is REFUSED with nothing \
                 committed."
            )
        }
    }

    /// **"Where the round stands"** — the status plaque. Which actions each seat has burned (the
    /// tug's phase: there are four, once each, and which are gone is the shape of the endgame), the
    /// one sentence above, the two standings, and who the viewer is.
    fn round_standing(&self, viewer: Option<Player>, claimant: Option<Player>) -> ViewNode {
        let proj = self.projection();
        let mover = if proj.current == 0 {
            Player::A
        } else {
            Player::B
        };
        let seat_row = |s: Player| {
            let i = s.idx();
            let whose = match viewer {
                Some(v) if v == s => " (you)",
                Some(_) => " (them)",
                None => "",
            };
            // Nobody is "to move" once every favor is placed — the only press left is the score,
            // and lighting a seat as on-move there would be the surface asserting a turn that does
            // not exist.
            let live = !self.ended() && !self.engine.round_complete();
            let on_move = if !live {
                ""
            } else if s == mover {
                " · to move"
            } else {
                " · waiting"
            };
            let mut cells = vec![ViewNode::Pill {
                text: format!("seat {s:?}{whose}{on_move}"),
                tag: if live && s == mover { "good" } else { "muted" }.to_string(),
                slot: None,
                cases: Vec::<PillCase>::new(),
            }];
            for kind in [
                ActionKind::Secret,
                ActionKind::Discard,
                ActionKind::Gift,
                ActionKind::Competition,
            ] {
                let spent = self.engine.used_flag(s, kind);
                cells.push(ViewNode::Pill {
                    text: format!("{kind:?}{}", if spent { " spent" } else { "" }),
                    tag: if spent { "muted" } else { "accent" }.to_string(),
                    slot: None,
                    cases: Vec::<PillCase>::new(),
                });
            }
            cells.push(ViewNode::Text(format!(
                "{} influence · {} lane{}",
                proj.charm[i],
                proj.guilds_controlled[i],
                if proj.guilds_controlled[i] == 1 {
                    ""
                } else {
                    "s"
                }
            )));
            ViewNode::Row(cells)
        };
        // ⚑ THE SEATLESS LINE SPLITS IN TWO, because the two seatless states are not the same
        // state. A CLAIMANT (a free seat exists) is handed working controls; a SPECTATOR (both
        // seats held) is handed none and would be refused anyway. The old single sentence told
        // both of them "every control is inert" — true of the spectator, provably false of the
        // claimant, whose press changed their seat, their hand and the turn counter.
        let who = match (viewer, claimant) {
            (Some(s), _) => format!(
                "You hold seat {s:?}. Your six favors are rendered to you and to nobody else; the \
                 other house sees only how many you hold and the committed root of the set."
            ),
            (None, Some(claim)) => format!(
                "You hold no seat at this table: BOTH hands are the fog form — a count and a \
                 committed root. The controls below are NOT inert. They are seat {claim:?}'s own \
                 controls, and the first move you land takes that seat; only then are its favors \
                 rendered to you."
            ),
            // ⚑ NOT "every control is inert" even here. This same surface is posted as the SHARED
            // board on Discord, where the host attaches `Offering::actions` as real buttons
            // (`commands::offering::surface_of`) — so "inert" is a claim about the CONTROLS that a
            // host can falsify. The claim that holds on every host is about the EXECUTOR: it refuses
            // an advance from an actor holding no seat ("actor holds no seat in this round") and
            // commits nothing.
            (None, None) => "You are watching this table: BOTH hands are the fog form — a count \
                             and a committed root. Both seats are held, so nothing you press can \
                             move this round: the executor refuses a move from an actor holding no \
                             seat, and commits nothing."
                .to_string(),
        };
        ViewNode::Section {
            title: "Where the round stands".to_string(),
            tag: "accent".to_string(),
            children: vec![
                ViewNode::Text(self.next_step_line(viewer, claimant)),
                ViewNode::List(vec![seat_row(Player::A), seat_row(Player::B)]),
                ViewNode::Text(format!(
                    "Turn {}/{ROUND_TURNS} of the round.",
                    proj.round_actions
                )),
                ViewNode::Text(who),
            ],
        }
    }

    /// **"How this round is decided"** — the tug's analogue of automatafl's automaton plaque: the
    /// thing a player cannot read off the lanes and must understand anyway.
    ///
    /// Two facts, both invisible on the board. **The bars are the DEPLOYED ones** — read out of the
    /// program the executor actually runs ([`crate::program_loader::PROGRAM_JSON`]), not retyped
    /// here, so a threshold edited in the Lean source moves this page. **The precedence** is what
    /// makes a losing-looking board still winnable: short of a bar the round is decided on total
    /// influence, then on lanes held, and only an exact dead heat on both is a draw.
    fn decision_plaque(&self) -> ViewNode {
        let proj = self.projection();
        let total: u64 = INFLUENCE.iter().map(|w| u64::from(*w)).sum();
        let mut kids = vec![ViewNode::Text(format!(
            "Nobody wins a lane by holding it — a lane you lead pays you its whole WEIGHT when \
             control is counted, and the seven lanes are worth {total} influence in all. Placing a \
             favor is the only way to pull one."
        ))];
        match (deployed_bar("a_charm"), deployed_bar("a_guilds")) {
            (Some(charm_bar), Some(guild_bar)) => {
                kids.push(ViewNode::Text(format!(
                    "It ends the moment a seat reaches {charm_bar} influence OR leads \
                     {guild_bar} lanes. Short of that the round is still DECIDED at turn \
                     {ROUND_TURNS}: on total influence first, then on lanes held, and only an exact \
                     dead heat on BOTH is a draw."
                )));
                let gap = |s: Player| {
                    let i = s.idx();
                    let dc = charm_bar.saturating_sub(proj.charm[i]);
                    let dg = guild_bar.saturating_sub(proj.guilds_controlled[i]);
                    let tag = if dc == 0 || dg == 0 {
                        "bad"
                    } else if dc <= 3 || dg <= 1 {
                        "warn"
                    } else {
                        ""
                    };
                    ViewNode::Pill {
                        text: if dc == 0 || dg == 0 {
                            format!("seat {s:?} · AT THE BAR")
                        } else {
                            format!("seat {s:?} · {dc} influence or {dg} lanes short")
                        },
                        tag: tag.to_string(),
                        slot: None,
                        cases: Vec::<PillCase>::new(),
                    }
                };
                kids.push(ViewNode::Row(vec![gap(Player::A), gap(Player::B)]));
            }
            _ => kids.push(ViewNode::Text(
                "⚠ The deployed win bars could not be read out of the program this table runs, so \
                 they are not stated here rather than guessed."
                    .to_string(),
            )),
        }
        // THE CUT — live, and the only arithmetic a player genuinely cannot do by looking.
        if let Some(offer) = self.engine.pending_offer() {
            let mut lines = Vec::new();
            for pick in 0..offer.picks() {
                if let Some((taker, cutter)) = offer.split(pick) {
                    lines.push(ViewNode::Text(format!(
                        "Side {pick}: seat {:?} takes {} — which leaves {} to seat {:?}.",
                        offer.responder(),
                        favor_list(&taker),
                        favor_list(&cutter),
                        offer.proposer,
                    )));
                }
            }
            kids.push(ViewNode::Section {
                title: format!("The {:?} on the table", offer.kind()),
                tag: String::new(),
                children: {
                    let mut c = vec![ViewNode::Text(format!(
                        "Seat {:?} cut it and cannot answer their own cut. Every side reassembles \
                         the whole offer, so nothing is destroyed — the only question is which half \
                         of the influence lands on whose side.",
                        offer.proposer
                    ))];
                    c.extend(lines);
                    c
                },
            });
        }
        ViewNode::Section {
            title: "How this round is decided".to_string(),
            tag: "accent".to_string(),
            children: kids,
        }
    }

    /// **The affordance rows for `seat`** — the real choices, in the `{turn, arg}` wire shape.
    ///
    /// * While an OFFER stands, the only affordances are the RESPONSES, one per side, each
    ///   labelled with the favors that side contains. They are live only for the seat that
    ///   did NOT cut (the anti-self-deal tooth, shown dimmed rather than hidden).
    /// * Otherwise there is one row per once-per-round action-kind, dimmed by its used-flag.
    ///   A kind row is aimed at the FIRST legal decision of that kind — one concrete cut. A
    ///   frontend that wants to choose the cut itself reads [`TugSession::legal_decisions`]
    ///   and posts that index directly; `advance` accepts any index in range.
    ///
    /// Every row is dimmed when it is not `seat`'s turn. Dimming is decoration: the executor
    /// is still the referee on [`Offering::advance`].
    fn affordances(&self, seat: Player) -> Vec<Action> {
        self.affordances_showing_cuts(seat, true)
    }

    /// [`Self::affordances`], but able to WITHHOLD the cut a row is aimed at.
    ///
    /// ⚑ **A REAL FOG HOLE, closed.** An action row's label is `"{kind} · {the exact favors this
    /// press would present}"`, and that cut is read off the seat's own committed hand. That is
    /// correct for the seat holding it and a DISCLOSURE to anybody else — and
    /// [`TugSession::surface_claim`] served exactly that menu to any viewer holding no seat. On a
    /// seat-locked table, `/tug/watch/{id}` (and the opponent, who is welcome to open it) therefore
    /// read the unclaimed seat's hand out of the button text before that seat had ever acted: the
    /// hidden-hand fog was intact in the hand sections and leaking through the controls.
    ///
    /// `show_cuts = false` keeps every row — same turn name, same `arg`, same `enabled`, so the
    /// controls a prospective claimant is handed still work and the executor is still the referee —
    /// and drops only the card text. A RESPONSE keeps its full label either way: the cut on the
    /// table is face-up by the rules, and hiding it would be a lie about the game.
    fn affordances_showing_cuts(&self, seat: Player, show_cuts: bool) -> Vec<Action> {
        if self.ended() {
            return Vec::new();
        }
        if self.engine.round_complete() {
            return vec![Action::new("Reveal secrets & score", "score", 4, true)];
        }
        let to_move = self.engine.current_player() == seat;
        if let Some(offer) = self.engine.pending_offer() {
            let live = to_move && offer.responder() == seat;
            return (0..offer.picks())
                .map(|pick| {
                    let decision = Decision::Respond { pick };
                    let arg = if live {
                        self.engine
                            .legal_decisions()
                            .iter()
                            .position(|d| *d == decision)
                            .map(|i| i as i64)
                            .unwrap_or(-1)
                    } else {
                        -1
                    };
                    Action::new(
                        respond_label(&offer, pick),
                        offer.respond_method(),
                        arg,
                        live && arg >= 0,
                    )
                })
                .collect();
        }
        let decisions = self.engine.legal_decisions();
        [
            ActionKind::Secret,
            ActionKind::Discard,
            ActionKind::Gift,
            ActionKind::Competition,
        ]
        .into_iter()
        .map(|kind| {
            let spent = self.engine.used_flag(seat, kind);
            let aimed = if to_move && !spent {
                decisions.iter().position(|d| d.kind() == Some(kind))
            } else {
                None
            };
            // ⚑ EVERY ROW NOW STATES ITS EFFECT AND NAMES ITS LANES, not just its price.
            //
            // The four rows used to read `Secret — put up #4(guild 3·w3) (1 card)`: a COST, with no
            // word on what the favor DOES, and nothing tying it to a lane — which is what the whole
            // win condition is about (`docs/reference/UX-QA-SWEEP-2026-07-26.md`, the tug section).
            // A player could not tell from the buttons that a Secret reaches no lane until scoring,
            // that a Discard reaches none ever, or that a Gift's leftovers land on THEIR side.
            //
            // The FOGGED variant (`show_cuts = false`, the claimant's menu) states the same effect
            // with no card and no lane — an effect is a rule, and rules are public; only the
            // specific favors are the hidden thing. It must not print `(guild ` in any form:
            // `surface::tests::the_claim_surface_leaks_no_favor_through_a_button_label` reads that
            // token in both directions.
            let label = match aimed {
                Some(i) if show_cuts => format!(
                    "{kind:?} — {} · {}",
                    kind_effect(kind),
                    cut_label(&decisions[i]),
                ),
                Some(_) => format!(
                    "{kind:?} — {} · {} favor{}, not named until you hold the seat",
                    kind_effect(kind),
                    kind.card_count(),
                    if kind.card_count() == 1 { "" } else { "s" }
                ),
                None => format!("{kind:?} — {}", kind_effect(kind)),
            };
            Action::new(
                label,
                kind.method(),
                aimed.map(|i| i as i64).unwrap_or(-1),
                aimed.is_some(),
            )
        })
        .collect()
    }

    /// The affordance rows as a deos [`ViewNode::Menu`]. `show_cuts` is the fog switch documented
    /// on [`Self::affordances_showing_cuts`] — false for a viewer who does not hold the seat.
    fn action_menu(&self, seat: Player, show_cuts: bool) -> ViewNode {
        let items = self
            .affordances_showing_cuts(seat, show_cuts)
            .into_iter()
            .map(|a| MenuItem {
                label: a.label,
                turn: a.turn,
                arg: a.arg,
                enabled: a.enabled,
            })
            .collect();
        ViewNode::Menu { items }
    }

    /// The viewer's OWN CURRENT hand — the exact engine cards (their ids + guild), as a text list AND a
    /// [`ViewNode::CoordGrid`] board (the coordinate-grid node) with the whole hand highlighted
    /// (the viewer's active set). The card ids are read off the committed [`HandTree`] — the
    /// hidden-hand source, revealed only to its owner.
    fn own_hand(&self, seat: Player) -> ViewNode {
        let ids = self.hands[seat.idx()].card_ids();
        debug_assert_eq!(
            ids,
            self.engine
                .hand(seat)
                .iter()
                .copied()
                .map(u64::from)
                .collect::<Vec<_>>(),
            "the rendered committed hand must be the engine hand"
        );
        // ⚑ THE TWO WORD-PAIRS, EQUATED, where a player first meets both. `favor`/`card` and
        // `guild`/`lane` were each used for one object and never once defined against each other.
        let mut lines = vec![ViewNode::Text(format!(
            "{} favors — a favor IS a card, these are the cards you hold, and the other house sees \
             none of them (only the count and the committed root below). Each favor belongs to one \
             GUILD, and a guild IS a LANE: that is the lane the favor pulls, and its pay is what \
             that lane hands whoever ends up leading it.",
            ids.len()
        ))];
        let mut cells = Vec::with_capacity(ids.len());
        for id in &ids {
            let g = deck_guild(*id);
            let w = if (g as usize) < N_GUILDS {
                INFLUENCE[g as usize]
            } else {
                0
            };
            // The card id is revealed in the prose — the reveal the fog denies the opponent. ⚑ The
            // `card #{id} ·` token is what `surface::tests::viewer_sees_own_hand_only` searches for
            // in BOTH directions (present in the owner's view, absent from the other's); it is the
            // fog's assertion handle, so keep the shape if this line is ever reworded.
            lines.push(ViewNode::Text(format!(
                "  card #{id} · guild {g} (lane {g}) · pays {w}"
            )));
            cells.push(CoordCell {
                // A card FACE, not a bare row index: `#4 lane3/3` says which favor it is, which lane
                // it pulls and what that lane pays — the three things a hand is read for. It was
                // `#4 g3w3`, two undefined single-letter columns; the legend below names the shape.
                // The renderer paints a multi-character glyph as a small mono chip.
                glyph: format!("#{id} lane{g}/{w}"),
                tag: if w >= 4 {
                    "accent".into()
                } else {
                    "muted".into()
                },
                turn: String::new(), // display cells (a play fires through the action menu)
                arg: *id as i64,
                highlight: true, // the viewer's own cards — the active set
            });
        }
        lines.push(ViewNode::Text(
            "Each chip below reads `#card lane/pays`.".to_string(),
        ));
        lines.push(ViewNode::CoordGrid {
            cols: HAND_SIZE,
            cells,
        });
        ViewNode::Section {
            title: "Your hand".to_string(),
            tag: String::new(),
            children: lines,
        }
    }

    /// The OPPONENT (or, for a spectator, a player's) hand as FOG — only a count + the committed
    /// hand root. NEVER the card ids: the root hides which favors are held (Poseidon2 blinding),
    /// so a viewer learns nothing of the other hand beyond how many cards + the binding commitment.
    fn hand_fog(&self, who: Player, label: &str) -> ViewNode {
        let count = self.hands[who.idx()].card_ids().len();
        let root = self.hands[who.idx()].root_bytes();
        // A short hex of the committed root (the public fog datum).
        let root_hex: String = root[0..4].iter().map(|b| format!("{b:02x}")).collect();
        ViewNode::Section {
            title: label.to_string(),
            tag: String::new(),
            children: vec![
                ViewNode::Text(format!(
                    "{count} cards · committed root {root_hex}… (hidden)"
                )),
                // WHAT THE FOG IS, on the surface that shows it. A count and a root is not "the UI
                // declining to draw the cards": the root BINDS the set, so the cards that come out
                // of that hand later have to be the ones that were in it.
                // ⚑ Exact about WHICH commitment does what. The root printed above is
                // `hands[..]` — the CURRENT hand. The membership witness a spend carries rides the
                // hidden ledger's own remaining-inventory commitment (`proof_hands`), which
                // includes future draws and is deliberately never rendered while the round is live.
                // So: this root commits the set, and the executor checks membership in the same
                // turn — but do not claim the witness is against THIS root.
                ViewNode::Text(
                    "That root is a Poseidon2 commitment to the exact set they hold right now. It \
                     hides which favors those are and it binds them: every favor this seat spends \
                     is checked for membership by the executor in the SAME turn as the rules move, \
                     so a card that was never entrusted to them cannot be played out of that hand."
                        .to_string(),
                ),
            ],
        }
    }

    /// Build the surface for `viewer` (`None` = a spectator: both hands are fog).
    fn surface_for(&self, viewer: Option<Player>) -> Surface {
        self.surface_as(viewer, None)
    }

    /// [`Self::surface_for`], told which seat a SEATLESS viewer would claim.
    ///
    /// ⚑ The parameter exists because the two seatless states are not the same state, and the
    /// surface was describing them identically. `claimant: Some(seat)` is a viewer who will be
    /// handed working controls (their first landed press takes that seat); `None` is a viewer at a
    /// table where both seats are held, who gets no menu at all and would be refused if they forged
    /// one. Only [`Self::surface_claim`] passes `Some`, which is exactly the surface that appends the
    /// live menu — so the copy can no longer disagree with the controls it ships beside.
    fn surface_as(&self, viewer: Option<Player>, claimant: Option<Player>) -> Surface {
        let proj = self.projection();
        let to_move = if proj.current == 0 { "A" } else { "B" };
        let status = match (proj.scored, proj.winner) {
            (1, 1) => "ROUND COMPLETE · WINNER: A".to_string(),
            (1, 2) => "ROUND COMPLETE · WINNER: B".to_string(),
            // A DRAW is now an EXACT DEAD HEAT on both tallies (`roundWinner_draw_iff`), not
            // "nobody cleared 11" — the word is kept so the surfaces' terminal-status checks
            // still bite, and the parenthetical is what actually changed for a player.
            (1, _) => "ROUND COMPLETE · DRAW (an exact dead heat)".to_string(),
            (_, _) if self.engine.round_complete() => {
                "All favors placed · awaiting reveal and score".to_string()
            }
            _ => format!(
                "turn {}/{ROUND_TURNS} · to move: {to_move}",
                proj.round_actions
            ),
        };
        let mut kids = vec![
            ViewNode::Text(format!("Multiway-Tug — {status}")),
            // `guilds A:2` became `lanes led A:2` — same number, and it now uses the same noun the
            // seat rows, the decision plaque and the lane table all use.
            ViewNode::Text(format!(
                "Influence A:{} / B:{} · lanes led A:{} / B:{}",
                proj.charm[0], proj.charm[1], proj.guilds_controlled[0], proj.guilds_controlled[1]
            )),
            // THE TWO PLAQUES, the automatafl convention: where the turn stands (with the ONE
            // SENTENCE saying what to do now), then the thing the board cannot show — here, how the
            // round actually gets decided and what each side of a live cut is worth.
            self.round_standing(viewer, claimant),
            self.decision_plaque(),
        ];
        // The cut on the table is PUBLIC — the presented favors are face-up, and everyone can
        // see which seat must now choose.
        if let Some(offer) = self.engine.pending_offer() {
            kids.push(ViewNode::Text(format!(
                "ON THE TABLE — seat {:?} cut a {:?}: {} · seat {:?} chooses",
                offer.proposer,
                offer.kind(),
                cut_label_for_offer(&offer),
                offer.responder(),
            )));
        }
        kids.push(ViewNode::Section {
            title: "The seven lanes".to_string(),
            tag: String::new(),
            children: vec![
                // THE EQUATION, in words, before the table that uses both nouns.
                ViewNode::Text(
                    "The seven contested GUILDS are the seven LANES — guild 3 is lane 3, and the \
                     two words name one thing on this page. Each row: the lane · what leading it \
                     pays · favors placed (A · B) · who holds it now."
                        .to_string(),
                ),
                // ⚑ WHY THE ROWS MAY NOT HAVE MOVED, said BEFORE the reader concludes the button
                // did nothing, and the live tally that did move.
                ViewNode::Text(self.lane_movement_rule()),
                ViewNode::Text(self.favor_accounting(&proj)),
                self.guild_lanes(&proj),
            ],
        });

        match viewer {
            Some(seat) => {
                // The viewer's own hand revealed; the opponent stays fog.
                kids.push(self.own_hand(seat));
                kids.push(self.hand_fog(seat.other(), "Opponent (hidden hand)"));
                // The viewer's affordances (dimmed off-turn and by the used-flags).
                let rows = self.affordances(seat);
                if !rows.is_empty() {
                    kids.push(ViewNode::Menu {
                        items: rows
                            .into_iter()
                            .map(|a| MenuItem {
                                label: a.label,
                                turn: a.turn,
                                arg: a.arg,
                                enabled: a.enabled,
                            })
                            .collect(),
                    });
                }
            }
            None => {
                // A spectator: BOTH hands are fog (no reveal to a non-seat).
                kids.push(self.hand_fog(Player::A, "Seat A (hidden hand)"));
                kids.push(self.hand_fog(Player::B, "Seat B (hidden hand)"));
            }
        }

        Surface(ViewNode::VStack(kids))
    }

    /// The OPENING-CLAIM surface for a not-yet-seated web viewer — the public fog (both hidden
    /// hands stay hidden, exactly what a spectator sees) PLUS the action menu for `claimant`, the
    /// seat this viewer will CLAIM the instant they act. It hands a fresh visitor real opening
    /// controls without leaking either committed hand before a seat is actually claimed. No menu
    /// once the round is complete. The executor stays the referee on `advance` (an out-of-turn or
    /// spent-action POST is still refused).
    pub fn surface_claim(&self, claimant: Player) -> Surface {
        // ⚑ `surface_as(None, Some(claimant))`, not `surface_for(None)`. The fog branch used to tell
        // this viewer "every control is inert" and then this function appended a LIVE menu below it
        // — the page contradicting its own buttons. Naming the claimant makes the standing plaque
        // describe the surface that is actually being built.
        let Surface(ViewNode::VStack(mut kids)) = self.surface_as(None, Some(claimant)) else {
            return self.surface_as(None, Some(claimant));
        };
        if !self.ended() {
            // ⚑ `show_cuts: false` IS THE FIX, not a caution. The doc above always promised
            // "without leaking either committed hand", and this menu broke that promise: an
            // action row's label names the exact favors the press would put up, read off the
            // claimant seat's own hand, and this surface is served to every viewer holding no
            // seat. On a seat-locked table that means `/tug/watch/{id}` — which the OPPONENT is
            // free to open — printed the unclaimed seat's cards in the button text before that
            // seat had acted once. The rows stay (same turn, same `arg`, same `enabled`, so the
            // controls a prospective claimant is handed still work); only the card text goes.
            //
            // This line no longer CORRECTS the plaque above (which now says the right thing for a
            // claimant); it says the one extra thing only this surface knows — that the buttons
            // below are deliberately card-less.
            kids.push(ViewNode::Text(format!(
                "These are seat {claimant:?}'s controls and they are live: the first move you land \
                 CLAIMS that seat, and only then are its favors rendered to you. Until it lands, \
                 each button states what the action DOES and never which cards it would spend — \
                 that would read the unclaimed hand out to anybody watching."
            )));
            kids.push(self.action_menu(claimant, false));
        }
        Surface(ViewNode::VStack(kids))
    }
}

/// A compact rendering of a set of favors: `#id(guild G · pays N)` each.
///
/// The GUILD is here because it is the whole decision — a favor's only effect is to pull the lane
/// it belongs to, and a label reading `#4(w3)` told a player the price of a card without telling
/// them what it buys. `w3` became `pays 3` for the same reason: `w` is a column name, and what the
/// number means is what that lane pays whoever ends up leading it.
///
/// ⚑ `(guild ` is the fog assertion handle
/// (`surface::tests::the_claim_surface_leaks_no_favor_through_a_button_label` and
/// `dreggnet-web/tests/tug_table.rs`'s `FAVOR` read it in BOTH directions — present wherever a
/// concrete cut is disclosed, absent from every surface that must not disclose one). Keep the token
/// if this is ever reworded.
fn favor_list(cards: &[u8]) -> String {
    cards
        .iter()
        .map(|&c| {
            let g = deck_guild(u64::from(c));
            let w = if (g as usize) < N_GUILDS {
                INFLUENCE[g as usize]
            } else {
                0
            };
            format!("#{c}(guild {g} · pays {w})")
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// **What each action DOES** — the effect, tied to a lane, in a player's words.
///
/// The four affordance rows stated only a COST (`put up 3 cards`). This is the other half, and it is
/// the half that decides whether a still scoreboard reads as a rule or as a bug: a Secret reaches no
/// lane until scoring, a Discard reaches none ever, and a Gift/Competition reaches one only when the
/// other seat answers. All four sentences are RULES, so they are public — the fogged claimant menu
/// prints them too, and only the specific favors are withheld.
fn kind_effect(kind: ActionKind) -> &'static str {
    match kind {
        ActionKind::Secret => {
            "hide 1 favor face down; it joins YOUR side of its lane at the reveal, and moves no \
             lane before then"
        }
        ActionKind::Discard => {
            "burn 2 favors out of the round; they reach no lane and nobody ever scores them"
        }
        ActionKind::Gift => {
            "offer 3 favors; they take ONE onto their side of its lane and the other two land on \
             yours — lanes move when they answer, not now"
        }
        ActionKind::Competition => {
            "offer 2 pairs; they take ONE PAIR onto their side and the other pair lands on yours — \
             lanes move when they answer, not now"
        }
    }
}

/// **A win bar, read off the DEPLOYED program** — the `fieldGte` guard on register `reg` in
/// [`crate::program_loader::PROGRAM_JSON`], which is the cell program the executor admits scoring
/// turns under.
///
/// The point is that the number a player is shown is not a second copy of the rule. The bars live in
/// the Lean (`roundWinner`'s absolute clauses) and reach Rust only as this compiled program, so
/// raising the influence bar in the metatheory moves the plaque with no edit here; a retyped `11`
/// would silently disagree the day it changed. `None` when no such guard exists — the caller says
/// so rather than substituting a guess, and `surface::tests` pins that both bars are found.
fn deployed_bar(reg: &str) -> Option<u64> {
    let needle = format!("\"fieldGte\",\"reg\":\"{reg}\",\"value\":");
    let json = crate::program_loader::PROGRAM_JSON;
    // The compiled JSON is emitted without spaces; accept both shapes rather than depend on that.
    let spaced = format!("\"fieldGte\", \"reg\": \"{reg}\", \"value\": ");
    let rest = json
        .split_once(&needle)
        .or_else(|| json.split_once(&spaced))?
        .1;
    let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
    digits.parse().ok()
}

/// What a decision PRESENTS or SPENDS, for an affordance label.
fn cut_label(d: &Decision) -> String {
    match d {
        Decision::Competition { pairs } => format!(
            "{} | {}",
            favor_list(&pairs[0][..]),
            favor_list(&pairs[1][..])
        ),
        Decision::Respond { pick } => format!("take side {pick}"),
        other => favor_list(&other.cards()),
    }
}

/// What is on the table, for the public status line.
fn cut_label_for_offer(offer: &PendingOffer) -> String {
    match offer.shape {
        crate::reference::OfferShape::Gift(present) => favor_list(&present[..]),
        crate::reference::OfferShape::Competition(pairs) => format!(
            "{} | {}",
            favor_list(&pairs[0][..]),
            favor_list(&pairs[1][..])
        ),
    }
}

/// A response affordance's label — what the responder TAKES and what that leaves the cutter.
fn respond_label(offer: &PendingOffer, pick: u8) -> String {
    match offer.split(pick) {
        Some((taker, cutter)) => format!(
            "Take {} · leaves {} to seat {:?}",
            favor_list(&taker),
            favor_list(&cutter),
            offer.proposer
        ),
        None => format!("(no side {pick})"),
    }
}

/// Stable per-card blind. A card keeps the same opening while it moves from deck to hand; only
/// the set committed under the current-hand root changes.
fn nonce_of(seed: u64, card: u64) -> u64 {
    let mut z = seed
        .wrapping_add(card.wrapping_mul(0x9E37_79B9_7F4A_7C15))
        .wrapping_add(0xA5A5_5A5A_1234_9876);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z ^ (z >> 27)
}

fn openings_for(seed: u64, cards: impl IntoIterator<Item = u8>) -> Vec<(u64, u64)> {
    cards
        .into_iter()
        .map(|card| {
            let card = u64::from(card);
            (card, nonce_of(seed, card))
        })
        .collect()
}

/// Commit the engine's ACTUAL current hands. Draws enter this root and every card consumed by
/// an action leaves it; the UI and the mover therefore have one deal, not peer copies.
fn commit_engine_hands(engine: &Engine, seed: u64) -> [HandTree; 2] {
    [Player::A, Player::B]
        .map(|seat| HandTree::commit(openings_for(seed, engine.hand(seat).iter().copied())))
}

/// Each seat's private full-round inventory for the whole-match fold: the ten distinct cards
/// that seat is entrusted with — its opening six plus its four draws.
///
/// This comes straight off the DEAL ([`Engine::round_inventory`]), not off a scripted
/// playthrough. It has to: with the seats now DECIDING, there is no canonical round to script,
/// and the old "play a round and collect what it happened to play" would have pinned the fold
/// to one agent's choices. The deal suffices because the draw assignment is choice-independent
/// — action-turns strictly alternate A, B, A, B and only they draw — so seat A always takes
/// draw slots 0, 2, 4, 6 and seat B slots 1, 3, 5, 7 whatever either seat decides.
fn fold_inventory(seed: u64) -> [Vec<(u64, u64)>; 2] {
    let engine = Engine::new(seed);
    [Player::A, Player::B]
        .map(|seat| openings_for(seed, engine.round_inventory(seat).iter().copied()))
}

impl Offering for TugOffering {
    type Session = TugSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        let seed = cfg.seed.unwrap_or(DEFAULT_SEED);
        let engine = Engine::new(seed);
        let hands = commit_engine_hands(&engine, seed);
        let fold_inventory = fold_inventory(seed);
        let proof_hands = fold_inventory.clone().map(HandTree::commit);
        let mut runtime = HiddenHandLedger::deploy(seed as u8)
            .map_err(|e| OfferingError::Deploy(e.to_string()))?;
        // One genesis receipt seeds the Lean rules cell and pins both private inventory roots.
        runtime
            .start_round(
                &engine.projection(),
                proof_hands[Player::A.idx()].root(),
                proof_hands[Player::B.idx()].root(),
            )
            .map_err(|e| OfferingError::Deploy(e.to_string()))?;
        Ok(TugSession {
            seed,
            runtime,
            engine,
            hands,
            ended: false,
            fold_inventory,
            proof_hands,
            plays: [Vec::new(), Vec::new()],
            history: Vec::new(),
        })
    }

    /// The affordances for the seat TO MOVE. While an offer stands these are the response
    /// sides and nothing else; otherwise one row per once-per-round action-kind. See
    /// [`TugSession::affordances`] for the `{turn, arg}` encoding and
    /// [`TugSession::legal_decisions`] for the full choice space.
    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        session.affordances(session.engine.current_player())
    }

    /// **THE AFFORDANCE HALF OF THE FOG — and it was open.**
    ///
    /// [`Offering::actions_for`]'s default is [`Offering::actions`], which is the seat TO MOVE, whose
    /// row labels name the exact favors that press would put up, read off that seat's own committed
    /// hand. So every viewer who was not that seat — the OPPONENT most of all, and any spectator —
    /// read the live cut out of the button text. This is the identical hole
    /// [`TugSession::surface_claim`] closed on the claim SURFACE, at the other door: the surface path
    /// asks `affordances(viewer_seat)` (whose cut is `None` off-turn) while this one asked for the
    /// mover's rows and handed them to whoever was looking. It reaches every frontend that paints
    /// this seam rather than the rendered [`Surface`] — the Discord/Telegram affordance lists, and
    /// `dreggnet-catalog`'s seat adapter, which only dimmed `enabled` and left the labels intact.
    ///
    /// A seat gets ITS OWN rows, exactly as [`TugSession::surface_for`] serves them. Anyone else gets
    /// the mover's rows with the card text withheld and every control inert — the turn names, `arg`s
    /// and row count are unchanged, so a transport validating a POST against this list still reaches
    /// the executor and still gets ITS refusal. A face-up RESPONSE keeps its full label either way:
    /// the cut on the table is public by the rules, and hiding it would be a lie about the game.
    fn actions_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Vec<Action> {
        match TugOffering::seat_of(viewer) {
            Some(seat) => session.affordances(seat),
            None => session
                .affordances_showing_cuts(session.engine.current_player(), false)
                .into_iter()
                .map(|action| Action {
                    enabled: false,
                    ..action
                })
                .collect(),
        }
    }

    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        // The actor must hold a seat.
        let Some(seat) = TugOffering::seat_of(&actor) else {
            return Outcome::Refused("actor holds no seat in this round".to_string());
        };
        if session.ended() {
            return Outcome::Refused("the round is already complete".to_string());
        }
        if session.engine.round_complete() {
            if input.turn != "score" || input.arg != 4 {
                return Outcome::Refused(
                    "all action turns are complete; reveal and score the round".to_string(),
                );
            }
            let mut scored = session.engine.clone();
            // The verdict is the PROVEN Lean's (`rules::adjudicate`); an oracle that cannot answer
            // refuses the turn rather than reporting a winner nothing decided.
            if let Err(e) = scored.score() {
                return Outcome::Refused(format!("the round cannot be adjudicated: {e}"));
            }
            return match session.runtime.score_projection(&scored.projection()) {
                Ok(receipt) => {
                    session.engine = scored;
                    session.ended = true;
                    session.history.push(LandedInput::Score { seat });
                    Outcome::Landed {
                        receipt,
                        ended: true,
                    }
                }
                Err(error) => Outcome::Refused(error.to_string()),
            };
        }
        // THE DECISION. `arg` indexes the seat's `legal_decisions()`; `turn` names that
        // decision's dispatch method, and both must agree (a transport cannot splice a method
        // onto someone else's decision). The executor is still the referee — this only keeps
        // an out-of-turn / out-of-range fire from committing anything at all (anti-ghost).
        if seat != session.engine.current_player() {
            return Outcome::Refused("not your turn".to_string());
        }
        let decisions = session.engine.legal_decisions();
        if input.arg < 0 || input.arg as usize >= decisions.len() {
            return Outcome::Refused(format!(
                "decision index {} is out of range (this seat has {} legal decisions)",
                input.arg,
                decisions.len()
            ));
        }
        let decision = decisions[input.arg as usize];
        let pending = session.engine.pending_offer();
        let expected = decision_method(&decision, pending.as_ref());
        if input.turn != expected {
            return Outcome::Refused(format!(
                "method `{}` does not name decision {} ({decision:?}, which dispatches under `{expected}`)",
                input.turn, input.arg
            ));
        }

        // A RESPONSE places the escrow onto the two boards and consumes nothing from any hand,
        // so it carries no membership witness — the whole move is the rules projection.
        if matches!(decision, Decision::Respond { .. }) {
            let mut next_engine = session.engine.clone();
            let mv = match next_engine.apply(seat, decision) {
                Ok(mv) => mv,
                Err(err) => return Outcome::Refused(err.to_string()),
            };
            let proj = next_engine.projection();
            return match session.runtime.respond_projection(mv.method(), &proj) {
                Ok(receipt) => {
                    session.engine = next_engine;
                    session.hands = commit_engine_hands(&session.engine, session.seed);
                    session.history.push(LandedInput::Play { seat, decision });
                    Outcome::Landed {
                        receipt,
                        ended: false,
                    }
                }
                Err(error) => Outcome::Refused(error.to_string()),
            };
        }

        // An ACTION: apply it on the mover, then commit its projection as ONE real executor
        // turn under the action method. A legal projection lands a receipt; the teeth would refuse
        // an illegal one.
        let mut next_engine = session.engine.clone();
        let mv = match next_engine.apply(seat, decision) {
            Ok(mv) => mv,
            Err(err) => return Outcome::Refused(err.to_string()),
        };
        let proj = next_engine.projection();
        let played_cards: Vec<u64> = mv.played_cards().into_iter().map(u64::from).collect();
        // Every action card is opened against the DEAL-pinned full inventory root. A separate
        // private remaining tree ratchets the committed remaining root and supplies the host-side
        // no-replay check. Neither tree is exposed to the frontend before SCORE.
        let full_inventory = HandTree::commit(session.fold_inventory[seat.idx()].clone());
        let mut next_proof_hand = session.proof_hands[seat.idx()].clone();
        let mut proofs = Vec::with_capacity(played_cards.len());
        for &card in &played_cards {
            if next_proof_hand.opening(card).is_none() {
                return Outcome::Refused(format!(
                    "card {card} is absent from the remaining private inventory"
                ));
            }
            let Some(proof) = full_inventory.prove_play(card) else {
                return Outcome::Refused(format!(
                    "card {card} is absent from the DEAL-pinned private inventory"
                ));
            };
            proofs.push(proof);
            next_proof_hand = next_proof_hand.without(card);
        }
        match session.runtime.play_projection(
            seat,
            &played_cards,
            &proofs,
            next_proof_hand.root(),
            mv.action(),
            &proj,
        ) {
            Ok(action_receipt) => {
                // Record every exact action card, then rebuild the UI commitment from the mover's
                // exact post-draw/post-play hand. This handles the 4/3/2/1-card actions and later
                // draws without inventing a "first surviving card" as the play.
                session.plays[seat.idx()].extend(played_cards);
                session.proof_hands[seat.idx()] = next_proof_hand;
                session.engine = next_engine;
                session.hands = commit_engine_hands(&session.engine, session.seed);
                session.history.push(LandedInput::Play { seat, decision });

                // SCORE is deliberately a separate affordance/advance. The
                // Offering contract says one accepted action yields one real
                // executor turn and one receipt; silently committing SCORE here
                // would make the last press perform two turns while exposing
                // only the second receipt. The terminal surface now presents
                // the exact `score(4)` turn explicitly.
                Outcome::Landed {
                    receipt: action_receipt,
                    ended: false,
                }
            }
            Err(e) => Outcome::Refused(e.to_string()),
        }
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        let proj = session.projection();
        let turns = 1 + proj.round_actions as usize + proj.scored as usize;
        if proj != session.engine.projection() {
            return VerifyReport::broken(
                turns,
                "executor projection differs from the reference engine",
            );
        }
        if proj.conservation_sum() != 21 {
            return VerifyReport::broken(
                turns,
                format!("conservation broke: sum = {}", proj.conservation_sum()),
            );
        }

        let mut replay = match self.open(SessionConfig::with_seed(session.seed)) {
            Ok(replay) => replay,
            Err(error) => return VerifyReport::broken(0, error.to_string()),
        };
        for (index, input) in session.history.iter().copied().enumerate() {
            let (seat, action) = match input {
                LandedInput::Play { seat, decision } => {
                    // Re-derive the index the recorded DECISION sits at in the replay's own
                    // legal set. A recorded decision the replay does not offer gets `-1`,
                    // which `advance` refuses — so a tampered log cannot replay.
                    let arg = replay
                        .engine
                        .legal_decisions()
                        .iter()
                        .position(|d| *d == decision)
                        .map(|i| i as i64)
                        .unwrap_or(-1);
                    let method = decision_method(&decision, replay.engine.pending_offer().as_ref());
                    (seat, Action::new("", method, arg, true))
                }
                LandedInput::Score { seat } => (
                    seat,
                    Action::new("Reveal secrets & score", "score", 4, true),
                ),
            };
            let outcome = self.advance(&mut replay, action, TugOffering::seat_identity(seat));
            if !outcome.landed() {
                return VerifyReport::broken(
                    index + 1,
                    format!("accepted tug input {index} refused during replay: {outcome:?}"),
                );
            }
        }
        let same_hands = [Player::A, Player::B].into_iter().all(|seat| {
            replay.hands[seat.idx()].root_bytes() == session.hands[seat.idx()].root_bytes()
                && replay.hands[seat.idx()].card_ids() == session.hands[seat.idx()].card_ids()
        });
        let same_proof_hands = [Player::A, Player::B].into_iter().all(|seat| {
            replay.proof_hands[seat.idx()].root_bytes()
                == session.proof_hands[seat.idx()].root_bytes()
                && replay.proof_hands[seat.idx()].card_ids()
                    == session.proof_hands[seat.idx()].card_ids()
        });
        if replay.projection() != proj
            || replay.engine.projection() != session.engine.projection()
            || !same_hands
            || !same_proof_hands
            || replay.runtime.state() != session.runtime.state()
            || replay.fold_inventory != session.fold_inventory
            || replay.plays != session.plays
            || replay.ended != session.ended
            || replay.history != session.history
        {
            return VerifyReport::broken(
                turns,
                "fresh-seed replay differs from the live projection, hidden-hand roots, or match record",
            );
        }
        let mut report = VerifyReport::ok(turns);
        report.detail = format!(
            "replayed {} accepted player input(s) through a fresh executor; {} atomic rules+witness turn(s) including genesis{}",
            session.history.len(),
            turns,
            if proj.scored == 1 { " and scoring" } else { "" }
        );
        report
    }

    /// The PUBLIC surface — both hands are fog (no viewer to reveal to).
    fn render(&self, session: &Self::Session) -> Surface {
        session.surface_for(None)
    }

    /// The per-VIEWER surface — the viewer's own hand revealed, the opponent fog.
    fn render_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Surface {
        session.surface_for(TugOffering::seat_of(viewer))
    }

    /// **Hidden information: YES.** `render_for` reveals the viewer's own card ids — the whole
    /// point of the hand. A frontend must never paint that projection onto a surface more than
    /// one person reads (a group chat's shared message); it serves [`render`] there, or hosts the
    /// game somewhere private.
    fn hidden_information(&self) -> bool {
        true
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

#[cfg(test)]
mod tests;
