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
//! The guild-lane table + coordinate-grid hand + action menu are the deos affordance surface.
//! On advance, every exact 4/3/2/1-card consumption carries its private inventory membership
//! witness into the executor. The Lean-authored rules action and the witnessed hidden action share
//! one atomic turn, so either both cells land or neither does. HONEST RESIDUAL: duplicate-card
//! consumption is an exact host ratchet checked again by fresh-seed replay; a protocol-native
//! dynamic-root/nullifier tooth is not yet installed.

use deos_view::{CoordCell, MenuItem, PillCase, ViewNode};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

use crate::hidden_hand::{HandTree, HiddenHandLedger, deck_guild};
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LandedInput {
    Play { seat: Player, action: ActionKind },
    Score { seat: Player },
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
    /// bound public inputs of the whole-match fold's win leaf. `None` while the round runs (or
    /// if it ended with no winner).
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
        let status = match (proj.scored, proj.winner) {
            (1, 1) => "ROUND COMPLETE · WINNER: A".to_string(),
            (1, 2) => "ROUND COMPLETE · WINNER: B".to_string(),
            (1, _) => "ROUND COMPLETE · DRAW".to_string(),
            (_, _) if self.engine.round_complete() => {
                "All favors placed · awaiting reveal and score".to_string()
            }
            _ => format!("action {}/8 · to move: {to_move}", proj.round_actions),
        };
        let mut kids = vec![
            ViewNode::Text(format!("Multiway-Tug — {status}")),
            ViewNode::Text(format!(
                "Influence A:{} / B:{} · guilds A:{} / B:{}",
                proj.charm[0], proj.charm[1], proj.guilds_controlled[0], proj.guilds_controlled[1]
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
                if !self.engine.round_complete() {
                    kids.push(self.action_menu(seat));
                } else if proj.scored == 0 {
                    kids.push(ViewNode::Menu {
                        items: vec![MenuItem {
                            label: "Reveal secrets & score".to_string(),
                            turn: "score".to_string(),
                            arg: 4,
                            enabled: true,
                        }],
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
        let Surface(ViewNode::VStack(mut kids)) = self.surface_for(None) else {
            return self.surface_for(None);
        };
        if !self.ended() {
            if self.engine.round_complete() {
                kids.push(ViewNode::Menu {
                    items: vec![MenuItem {
                        label: "Reveal secrets & score".to_string(),
                        turn: "score".to_string(),
                        arg: 4,
                        enabled: true,
                    }],
                });
            } else {
                kids.push(self.action_menu(claimant));
            }
        }
        Surface(ViewNode::VStack(kids))
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

/// Precompute each seat's private full-round inventory for the whole-match fold. The deterministic
/// engine assigns every distinct card exactly once; this record contains all ten cards each seat
/// consumes, while the live `hands` roots expose only current-hand commitments.
fn fold_inventory(seed: u64) -> [Vec<(u64, u64)>; 2] {
    let mut engine = Engine::new(seed);
    let mut cards = [Vec::new(), Vec::new()];
    while !engine.round_complete() {
        let mv = engine.play_next();
        cards[mv.player().idx()].extend(mv.played_cards());
    }
    cards.map(|cards| openings_for(seed, cards))
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

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        if session.ended() {
            return Vec::new();
        }
        if session.engine.round_complete() {
            return vec![Action::new("Reveal secrets & score", "score", 4, true)];
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
            let _ = scored.score();
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
        // The fired action.
        let action = match input.turn.as_str() {
            "secret" => ActionKind::Secret,
            "discard" => ActionKind::Discard,
            "gift" => ActionKind::Gift,
            "comp" => ActionKind::Competition,
            other => return Outcome::Refused(format!("unknown action method `{other}`")),
        };
        if input.arg != action.idx() as i64 {
            return Outcome::Refused(format!(
                "action method `{}` requires argument {}, got {}",
                action.method(),
                action.idx(),
                input.arg
            ));
        }
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
        let mut next_engine = session.engine.clone();
        let mv = next_engine.play_next();
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
                session.history.push(LandedInput::Play { seat, action });

                // SCORE is deliberately a separate affordance/advance. The
                // Offering contract says one accepted action yields one real
                // executor turn and one receipt; silently committing SCORE here
                // would make the eighth press perform two turns while exposing
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
                LandedInput::Play { seat, action } => (
                    seat,
                    Action::new("", action.method(), action.idx() as i64, true),
                ),
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
