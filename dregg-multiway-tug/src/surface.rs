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
//! **The differentiated bit — the per-player fog.** [`Offering::render`] paints ONE public
//! surface (both hands are FOG — a count + the committed hand root). [`Offering::render_for`]
//! paints the surface *as a specific viewer sees it*: the viewer's OWN hand is revealed (the
//! card ids they hold, sourced from the [`crate::hidden_hand`] committed [`HandTree`]), while
//! the opponent stays fog. So player A's card ids appear in A's view and NOT in B's view of
//! the same table — the hidden-hand fog, in the UI.
//!
//! HONEST SCOPE: this is the hidden hand **in the UI** (what a frontend paints for a viewer) —
//! DISTINCT from the hidden hand **in the proof** (the committed Merkle fold the executor gates
//! on, [`crate::hidden_hand`]). The two agree (the surface reveals what the viewer legitimately
//! holds under their committed root) but are separate seams. The guild-lane table + the
//! coordinate-grid hand + the action menu are the deos affordance surface; the play wiring is a
//! real [`crate::game::MultiwayTug`] turn. NAMED NEXT: an `AutomataflOffering` over the same
//! coordinate-grid board node.

use deos_view::{CoordCell, MenuItem, PillCase, ViewNode};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

use crate::game::MultiwayTug;
use crate::hidden_hand::{HandTree, deck_guild};
use crate::reference::{ActionKind, Engine, INFLUENCE, N_GUILDS, Player, Projection};

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
    /// The deployed executor game — a play commits its projection as one real verified turn.
    game: MultiwayTug,
    /// The reference mover — card identities + the next projection each play commits.
    engine: Engine,
    /// Each seat's committed hidden hand (the [`crate::hidden_hand`] Merkle-committed hand). The
    /// viewer's own hand is read off theirs; the opponent's is fog (a count + the committed root).
    hands: [HandTree; 2],
    /// Whether the round has ended (the round completed).
    ended: bool,
}

impl TugSession {
    /// The seat to move next (whose turn it is).
    pub fn to_move(&self) -> Player {
        self.engine.current_player()
    }

    /// The action the seat-to-move would play next (their scheduled once-per-round action), or
    /// `None` if the round is complete. A frontend fires exactly this method through
    /// [`Offering::advance`]; anything else is refused as out-of-order.
    pub fn scheduled_action(&self) -> Option<ActionKind> {
        self.engine.peek_next_action()
    }

    /// Whether the round has ended.
    pub fn ended(&self) -> bool {
        self.ended || self.engine.round_complete()
    }

    /// The committed public projection (both hands appear as counts here — the fog datum).
    fn projection(&self) -> Projection {
        self.game.read_projection()
    }

    /// The guild-lane table: one row per guild — its influence WEIGHT as a [`ViewNode::Pill`],
    /// the two placement counters (A / B), and a control [`ViewNode::Icon`] (who leads the lane).
    fn guild_lanes(&self, proj: &Projection) -> ViewNode {
        let mut rows = Vec::with_capacity(N_GUILDS);
        for g in 0..N_GUILDS {
            let a = proj.score[g][0];
            let b = proj.score[g][1];
            let w = INFLUENCE[g] as u64;
            // Control: whoever placed more favors leads the lane (a tie is contested).
            let (glyph, ctrl_tag) = if a > b {
                ("A", "good")
            } else if b > a {
                ("B", "accent")
            } else {
                ("·", "muted")
            };
            let weight_tag = if w >= 4 { "accent" } else { "muted" };
            rows.push(ViewNode::Row(vec![
                ViewNode::Text(format!("Guild {g}")),
                ViewNode::Pill {
                    text: format!("w{w}"),
                    tag: weight_tag.to_string(),
                    slot: None,
                    cases: Vec::<PillCase>::new(),
                },
                ViewNode::Text(format!("A:{a}")),
                ViewNode::Text(format!("B:{b}")),
                ViewNode::Icon {
                    glyph: glyph.to_string(),
                    tag: ctrl_tag.to_string(),
                },
            ]));
        }
        ViewNode::Table(rows)
    }

    /// The action MENU for `seat` — the four once-per-round actions, each a `{turn=method, arg}`
    /// row GREYED (`enabled=false`) once its used-flag is set. A [`ViewNode::Menu`] so the cap
    /// tooth is SHOWN dimmed, never hidden (the executor is still the referee on `advance`).
    fn action_menu(&self, seat: Player) -> ViewNode {
        let items = [
            ActionKind::Secret,
            ActionKind::Discard,
            ActionKind::Gift,
            ActionKind::Competition,
        ]
        .into_iter()
        .map(|a| MenuItem {
            label: format!("{a:?}"),
            turn: a.method().to_string(),
            arg: a.idx() as i64,
            // Greyed by the used-flag (the once-per-round tooth, shown).
            enabled: !self.engine.used_flag(seat, a),
        })
        .collect();
        ViewNode::Menu { items }
    }

    /// The viewer's OWN hand — the revealed cards (their ids + guild), as a text list AND a
    /// [`ViewNode::CoordGrid`] board (the coordinate-grid node) with the whole hand highlighted
    /// (the viewer's active set). The card ids are read off the committed [`HandTree`] — the
    /// hidden-hand source, revealed only to its owner.
    fn own_hand(&self, seat: Player) -> ViewNode {
        let ids = self.hands[seat.idx()].card_ids();
        let mut lines = vec![ViewNode::Text(format!("Your hand ({} cards):", ids.len()))];
        let mut cells = Vec::with_capacity(ids.len());
        for id in &ids {
            let g = deck_guild(*id);
            let w = if (g as usize) < N_GUILDS {
                INFLUENCE[g as usize]
            } else {
                0
            };
            // The card id is revealed in the prose — the reveal the fog denies the opponent.
            lines.push(ViewNode::Text(format!("  card #{id} · guild {g} · w{w}")));
            cells.push(CoordCell {
                glyph: format!("#{id}"),
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
            children: vec![ViewNode::Text(format!(
                "{count} cards · committed root {root_hex}… (hidden)"
            ))],
        }
    }

    /// Build the surface for `viewer` (`None` = a spectator: both hands are fog).
    fn surface_for(&self, viewer: Option<Player>) -> Surface {
        let proj = self.projection();
        let to_move = if proj.current == 0 { "A" } else { "B" };
        let winner = match proj.winner {
            1 => " · WINNER: A",
            2 => " · WINNER: B",
            _ => "",
        };
        let mut kids = vec![
            ViewNode::Text(format!(
                "Multiway-Tug — action {}/8 · to move: {to_move}{winner}",
                proj.round_actions
            )),
            ViewNode::Section {
                title: "Guilds".to_string(),
                tag: String::new(),
                children: vec![self.guild_lanes(&proj)],
            },
        ];

        match viewer {
            Some(seat) => {
                // The viewer's own hand revealed; the opponent stays fog.
                kids.push(self.own_hand(seat));
                kids.push(self.hand_fog(seat.other(), "Opponent (hidden hand)"));
                // The viewer's action menu (greyed by used-flags).
                kids.push(self.action_menu(seat));
            }
            None => {
                // A spectator: BOTH hands are fog (no reveal to a non-seat).
                kids.push(self.hand_fog(Player::A, "Seat A (hidden hand)"));
                kids.push(self.hand_fog(Player::B, "Seat B (hidden hand)"));
            }
        }

        Surface(ViewNode::VStack(kids))
    }
}

/// Deal the two committed hidden hands from `seed` — distinct card ids `0..12`, seat A the first
/// six, seat B the next six, each blinded by a deterministic per-card nonce. The remaining ids
/// fund the (out-of-scope-here) draw. The committed roots are the fog the opponent sees.
fn deal_hidden_hands(seed: u64) -> [HandTree; 2] {
    let nonce_of = |card: u64| -> u64 {
        // A tiny deterministic blind per card (splitmix-flavored).
        let mut z = seed
            .wrapping_add(card.wrapping_mul(0x9E37_79B9_7F4A_7C15))
            .wrapping_add(0xA5A5_5A5A_1234_9876);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z ^ (z >> 27)
    };
    let hand_for = |base: u64| -> HandTree {
        let cards: Vec<(u64, u64)> = (0..HAND_SIZE as u64)
            .map(|i| {
                let card = base + i;
                (card, nonce_of(card))
            })
            .collect();
        HandTree::commit(cards)
    };
    [hand_for(0), hand_for(HAND_SIZE as u64)]
}

impl Offering for TugOffering {
    type Session = TugSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        let seed = cfg.seed.unwrap_or(DEFAULT_SEED);
        let engine = Engine::new(seed);
        let game =
            MultiwayTug::deploy(seed as u8).map_err(|e| OfferingError::Deploy(e.to_string()))?;
        // Seed the executor genesis from the reference initial projection.
        game.seed(&engine.projection())
            .map_err(|e| OfferingError::Deploy(e.to_string()))?;
        Ok(TugSession {
            game,
            engine,
            hands: deal_hidden_hands(seed),
            ended: false,
        })
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        if session.ended || session.engine.round_complete() {
            return Vec::new();
        }
        let seat = session.engine.current_player();
        [
            ActionKind::Secret,
            ActionKind::Discard,
            ActionKind::Gift,
            ActionKind::Competition,
        ]
        .into_iter()
        .map(|a| {
            Action::new(
                format!("{a:?}"),
                a.method(),
                a.idx() as i64,
                !session.engine.used_flag(seat, a),
            )
        })
        .collect()
    }

    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        // The actor must hold a seat.
        let Some(seat) = TugOffering::seat_of(&actor) else {
            return Outcome::Refused("actor holds no seat in this round".to_string());
        };
        if session.ended || session.engine.round_complete() {
            return Outcome::Refused("the round is already complete".to_string());
        }
        // The fired action.
        let action = match input.turn.as_str() {
            "secret" => ActionKind::Secret,
            "discard" => ActionKind::Discard,
            "gift" => ActionKind::Gift,
            "comp" => ActionKind::Competition,
            other => return Outcome::Refused(format!("unknown action method `{other}`")),
        };
        // The executor is the referee, but the offering first checks the turn order + the
        // once-per-round schedule (an out-of-turn / out-of-order fire commits nothing — anti-ghost).
        if seat != session.engine.current_player() {
            return Outcome::Refused("not your turn".to_string());
        }
        if session.engine.peek_next_action() != Some(action) {
            return Outcome::Refused(format!(
                "action `{}` is out of order this turn",
                action.method()
            ));
        }
        // Play the scheduled move on the mover, then commit its projection as ONE real executor
        // turn under the action method. A legal projection lands a receipt; the teeth would refuse
        // an illegal one.
        let mv = session.engine.play_next();
        let proj = session.engine.projection();
        match session.game.commit_projection(mv.action().method(), &proj) {
            Ok(receipt) => {
                // Advance the acting seat's hidden hand: remove a played card so the remaining-hand
                // root moves (the hidden-hand fold update — a replay of that card now fails
                // membership under the new root).
                let ids = session.hands[seat.idx()].card_ids();
                if let Some(&played) = ids.first() {
                    session.hands[seat.idx()] = session.hands[seat.idx()].without(played);
                }
                let ended = session.engine.round_complete();
                session.ended = ended;
                Outcome::Landed { receipt, ended }
            }
            Err(e) => Outcome::Refused(e.to_string()),
        }
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        let proj = session.projection();
        let turns = proj.round_actions as usize + 1; // genesis + committed actions
        if proj.conservation_sum() == 21 {
            VerifyReport::ok(turns)
        } else {
            VerifyReport::broken(
                turns,
                format!("conservation broke: sum = {}", proj.conservation_sum()),
            )
        }
    }

    /// The PUBLIC surface — both hands are fog (no viewer to reveal to).
    fn render(&self, session: &Self::Session) -> Surface {
        session.surface_for(None)
    }

    /// The per-VIEWER surface — the viewer's own hand revealed, the opponent fog.
    fn render_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Surface {
        session.surface_for(TugOffering::seat_of(viewer))
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

#[cfg(test)]
mod tests;
