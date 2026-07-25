//! # The deterministic reference engine — the game's oracle.
//!
//! A faithful, pure Rust model of the multiway-tug round used to DRIVE and CHECK the
//! executor deployment (`crate::game`). The executor tracks card COUNTS + per-guild
//! placement scores + win state; this engine tracks the actual card identities.
//!
//! Mechanics derived from Hanamikoji (designer Kota Nakayama); shipped as the original
//! re-theming "multiway-tug". Seven **guilds** with **influence** `[2,2,2,3,3,4,5]` (21
//! total), a 21-card **favor** deck whose cards have distinct ids, a hidden 6-card hand,
//! four once-per-round actions (Secret / Discard / Gift / Competition), win at `>= 11`
//! influence OR `>= 4` guilds — and short of that the round is still ADJUDICATED, on total
//! influence then on rows held, with only an exact dead heat a draw.
//!
//! ## ⚑ THE TERMINAL RULE IS NOT DECIDED HERE
//!
//! [`Engine::score`] calls the proven Lean (`crate::rules`), which is where row control, both
//! tallies, the winner and the deciding CLAUSE come from. The Rust `winner_of` that used to end
//! that function is DELETED: it was the model's `roundWinner` truncated to its two
//! absolute-threshold branches, so it answered "no winner" on every round the ruleset
//! adjudicates — a measured 78.5% played draw rate against the model's 5.1%.
//!
//! ## ⚑ THE ENGINE IS `I-CUT-YOU-CHOOSE`, AND THE CALLER DECIDES
//!
//! The RULES are authored in Lean — `metatheory/Dregg2/Games/MultiwayTug.lean`. This module
//! is the Rust expression of the decisions that model permits; it invents no rule. The three
//! decisions, each a theorem there:
//!
//! 1. **WHICH action, WHEN.** [`Engine::apply`] only requires the kind UNUSED — there is no
//!    fixed order. (Lean `every_action_order_is_feasible`: all 24 orderings are card-feasible,
//!    so the hardcoded descending `[Competition, Gift, Discard, Secret]` this engine used to
//!    run for BOTH seats was one arbitrary point in a fully-available space.)
//! 2. **THE CUT.** A [`Decision::Gift`] PRESENTS three favors and a [`Decision::Competition`]
//!    PRESENTS two pairs the cutter chose. The cards land in ESCROW; the split is not the
//!    actor's to make. (Lean `comp_balanced_cut_dominates` / `gift_modest_cut_dominates`.)
//! 3. **THE CHOICE.** The OTHER seat answers with [`Decision::Respond`], and that answer
//!    decides who gets what. (Lean `respond_decides_the_round`.)
//!
//! The interlock the Lean model proves and this engine enforces identically: while an offer
//! is pending NOTHING but a response is legal ([`MoveError::OfferPending`]), a response needs
//! a pending offer ([`MoveError::NoOfferPending`]), and **the proposer can never answer their
//! own cut** ([`MoveError::CannotAnswerOwnOffer`] — Lean `respond_not_by_proposer`).
//!
//! ## The turn stamp
//!
//! `round_actions` counts EVERY committed turn, actions AND responses. Each player takes
//! exactly four action-turns and makes exactly one Gift and one Competition offer, so a full
//! round is **8 actions + 4 responses = 12 turns** ([`Engine::round_complete`]).
//!
//! ## The draw
//!
//! Each ACTION-turn draws one card first (`6 + 4 = 10 = 1+2+3+4`); a RESPONSE draws nothing.
//! The draw is EAGER: whenever the engine settles into "seat `p` is to act", `p` has already
//! drawn, so [`Engine::hand`] is the exact set of favors that seat may spend right now and
//! [`Engine::legal_decisions`] is COMPLETE over it. Action-turns strictly alternate A, B, A,
//! B, …, so the eight draws are assigned to the seats independently of every choice made —
//! see [`Engine::round_inventory`].
//!
//! ## The Secret card is scored
//!
//! [`Engine::score`] reveals each player's secret onto their own side before control is
//! computed (Lean `secret_is_scored`).

/// Number of contested guilds.
pub const N_GUILDS: usize = 7;
/// Per-guild influence weight; sums to 21 (the deck size and total contestable charm).
pub const INFLUENCE: [u8; N_GUILDS] = [2, 2, 2, 3, 3, 4, 5];
/// The full deck size (== total influence == the conservation constant).
pub const DECK_SIZE: u8 = 21;

/// The number of committed turns in a full round: 8 action-turns + 4 responses (each seat
/// makes exactly one Gift and one Competition offer, and every offer must be answered before
/// play continues). Mirrors the Lean `#guard (8 + 4 : ℕ) = 12`.
pub const ROUND_TURNS: u64 = 12;

/// The guild carried by a distinct card id (`0..DECK_SIZE`). Guild `g` owns
/// `INFLUENCE[g]` consecutive cards, so duplicate favors remain distinct Merkle leaves while
/// projecting to the same seven guild lanes.
pub fn deck_guild(card_id: u64) -> u8 {
    let mut id = card_id as usize;
    for (guild, &copies) in INFLUENCE.iter().enumerate() {
        let copies = copies as usize;
        if id < copies {
            return guild as u8;
        }
        id -= copies;
    }
    N_GUILDS as u8
}

/// The influence a card carries (its guild's weight).
fn card_influence(card: u8) -> u64 {
    let g = deck_guild(card as u64) as usize;
    if g < N_GUILDS { INFLUENCE[g] as u64 } else { 0 }
}

/// The total influence of a set of favors.
fn influence_of(cards: &[u8]) -> u64 {
    cards.iter().copied().map(card_influence).sum()
}

/// A player.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Player {
    A,
    B,
}

impl Player {
    pub fn idx(self) -> usize {
        match self {
            Player::A => 0,
            Player::B => 1,
        }
    }
    pub fn other(self) -> Player {
        match self {
            Player::A => Player::B,
            Player::B => Player::A,
        }
    }
}

/// One of the four once-per-round actions. A RESPONSE is deliberately NOT one of these:
/// answering the opponent's cut consumes no used-flag (Lean `used_applyResponse`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ActionKind {
    Secret,
    Discard,
    Gift,
    Competition,
}

impl ActionKind {
    /// The stable 0..4 index used for the per-player used-flag heap keys.
    pub fn idx(self) -> usize {
        match self {
            ActionKind::Secret => 0,
            ActionKind::Discard => 1,
            ActionKind::Gift => 2,
            ActionKind::Competition => 3,
        }
    }
    /// The executor dispatch method this action commits under.
    pub fn method(self) -> &'static str {
        match self {
            ActionKind::Secret => "secret",
            ActionKind::Discard => "discard",
            ActionKind::Gift => "gift",
            ActionKind::Competition => "comp",
        }
    }

    /// The exact number of distinct cards this action consumes after its draw. For Gift and
    /// Competition these are the cards PRESENTED into escrow — the whole 3 / 4, since the
    /// split is not decided until the other seat answers.
    pub fn card_count(self) -> usize {
        match self {
            ActionKind::Secret => 1,
            ActionKind::Discard => 2,
            ActionKind::Gift => 3,
            ActionKind::Competition => 4,
        }
    }
}

/// What a seat may do. [`Engine::apply`] is the ONLY mover.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Decision {
    Secret {
        card: u8,
    },
    Discard {
        cards: [u8; 2],
    },
    /// PRESENT three favors; the opponent will take one.
    Gift {
        present: [u8; 3],
    },
    /// PRESENT two pairs; the opponent will take one pair.
    Competition {
        pairs: [[u8; 2]; 2],
    },
    /// Answer the pending offer: take side `pick` (0..3 for gift, 0..2 for comp).
    Respond {
        pick: u8,
    },
}

impl Decision {
    /// The once-per-round action-kind this decision spends, or `None` for a response.
    pub fn kind(&self) -> Option<ActionKind> {
        match self {
            Decision::Secret { .. } => Some(ActionKind::Secret),
            Decision::Discard { .. } => Some(ActionKind::Discard),
            Decision::Gift { .. } => Some(ActionKind::Gift),
            Decision::Competition { .. } => Some(ActionKind::Competition),
            Decision::Respond { .. } => None,
        }
    }

    /// The exact cards this decision takes out of the acting seat's hand. A response takes
    /// NONE: its cards were already spent into escrow when the offer was cut.
    pub fn cards(&self) -> Vec<u8> {
        match self {
            Decision::Secret { card } => vec![*card],
            Decision::Discard { cards } => cards.to_vec(),
            Decision::Gift { present } => present.to_vec(),
            Decision::Competition { pairs } => {
                vec![pairs[0][0], pairs[0][1], pairs[1][0], pairs[1][1]]
            }
            Decision::Respond { .. } => Vec::new(),
        }
    }
}

/// Why a decision was refused. These are exactly the `legalB` / `legalRespB` conjuncts of
/// `metatheory/Dregg2/Games/MultiwayTug.lean`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MoveError {
    NotYourTurn,
    OfferPending,
    NoOfferPending,
    CannotAnswerOwnOffer,
    ActionAlreadyUsed,
    CardNotInHand,
    BadPick,
    RoundComplete,
}

impl std::fmt::Display for MoveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            MoveError::NotYourTurn => "it is not that seat's turn",
            MoveError::OfferPending => "an offer is on the table; it must be answered first",
            MoveError::NoOfferPending => "there is no offer to answer",
            MoveError::CannotAnswerOwnOffer => "the proposer cannot answer their own cut",
            MoveError::ActionAlreadyUsed => "that action is already spent this round",
            MoveError::CardNotInHand => "those favors are not in that seat's hand",
            MoveError::BadPick => "that pick does not exist on the pending offer",
            MoveError::RoundComplete => "the round is complete",
        };
        f.write_str(s)
    }
}

/// The presented cards of a pending offer (mirrors the Lean `Offer` payload).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum OfferShape {
    /// Three favors presented; the responder takes exactly ONE (`pick` in `0..3`).
    Gift([u8; 3]),
    /// Two pairs presented; the responder takes exactly ONE PAIR (`pick` in `0..2`).
    Competition([[u8; 2]; 2]),
}

/// **A pending offer** — favors revealed on the table, awaiting the other seat's choice. It
/// records WHO cut, so [`MoveError::CannotAnswerOwnOffer`] can refuse a self-deal (the Lean
/// `respond_not_by_proposer` tooth).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct PendingOffer {
    /// Who CUT. They can never be the seat who chooses.
    pub proposer: Player,
    /// What is on the table.
    pub shape: OfferShape,
}

impl PendingOffer {
    /// The action-kind that opened this offer.
    pub fn kind(&self) -> ActionKind {
        match self.shape {
            OfferShape::Gift(_) => ActionKind::Gift,
            OfferShape::Competition(_) => ActionKind::Competition,
        }
    }

    /// The seat who must answer.
    pub fn responder(&self) -> Player {
        self.proposer.other()
    }

    /// How many picks the responder is choosing between (3 for a gift, 2 for a competition).
    pub fn picks(&self) -> u8 {
        match self.shape {
            OfferShape::Gift(_) => 3,
            OfferShape::Competition(_) => 2,
        }
    }

    /// Every card held in escrow by this offer.
    pub fn presented(&self) -> Vec<u8> {
        match self.shape {
            OfferShape::Gift(c) => c.to_vec(),
            OfferShape::Competition(p) => vec![p[0][0], p[0][1], p[1][0], p[1][1]],
        }
    }

    /// **The split** — `(takerShare, cutterShare)` for `pick`, exactly the Lean table:
    ///
    /// | offer | pick | taker (the RESPONDER) | cutter (the PROPOSER) |
    /// |-------|------|-----------------------|-----------------------|
    /// | gift `c₀ c₁ c₂` | 0 | `{c₀}` | `{c₁, c₂}` |
    /// | gift `c₀ c₁ c₂` | 1 | `{c₁}` | `{c₀, c₂}` |
    /// | gift `c₀ c₁ c₂` | 2 | `{c₂}` | `{c₀, c₁}` |
    /// | comp `a₀a₁ ∣ b₀b₁` | 0 | `{a₀, a₁}` | `{b₀, b₁}` |
    /// | comp `a₀a₁ ∣ b₀b₁` | 1 | `{b₀, b₁}` | `{a₀, a₁}` |
    ///
    /// `None` for a pick that does not exist. The two shares always reassemble the whole
    /// offer (Lean `share_split`), which is why a response conserves the deck.
    pub fn split(&self, pick: u8) -> Option<(Vec<u8>, Vec<u8>)> {
        match (self.shape, pick) {
            (OfferShape::Gift(c), 0) => Some((vec![c[0]], vec![c[1], c[2]])),
            (OfferShape::Gift(c), 1) => Some((vec![c[1]], vec![c[0], c[2]])),
            (OfferShape::Gift(c), 2) => Some((vec![c[2]], vec![c[0], c[1]])),
            (OfferShape::Competition(p), 0) => Some((p[0].to_vec(), p[1].to_vec())),
            (OfferShape::Competition(p), 1) => Some((p[1].to_vec(), p[0].to_vec())),
            _ => None,
        }
    }

    /// The executor dispatch method a response to THIS offer commits under.
    pub fn respond_method(&self) -> &'static str {
        match self.shape {
            OfferShape::Gift(_) => "respond_gift",
            OfferShape::Competition(_) => "respond_comp",
        }
    }
}

/// The executor dispatch method a decision commits under, given the offer (if any) on the
/// table. Responses dispatch under `respond_gift` / `respond_comp`.
pub fn decision_method(d: &Decision, pending: Option<&PendingOffer>) -> &'static str {
    match d {
        Decision::Respond { .. } => pending
            .map(PendingOffer::respond_method)
            .unwrap_or("respond"),
        other => other.kind().expect("a non-response has a kind").method(),
    }
}

/// A resolved move ready to replay on the executor: the acting player and exactly which
/// guild-cards moved. The draw is implicit (deck -> hand) and folded into the action turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolvedMove {
    /// Player secreted `card` from `guild` (revealed + scored at [`Engine::score`]).
    Secret { player: Player, card: u8, guild: u8 },
    /// Player discarded two favors (out of play this round).
    Discard {
        player: Player,
        cards: [u8; 2],
        guilds: [u8; 2],
    },
    /// Player PRESENTED three favors into escrow. Nothing is placed yet — the opponent's
    /// [`ResolvedMove::Respond`] decides the split.
    Gift {
        player: Player,
        present: [u8; 3],
        guilds: [u8; 3],
    },
    /// Player PRESENTED two pairs into escrow. Nothing is placed yet.
    Competition {
        player: Player,
        pairs: [[u8; 2]; 2],
        guilds: [[u8; 2]; 2],
    },
    /// The OTHER seat answered a pending offer: `player` (the responder) took `taker_cards`
    /// onto their own side, the proposer kept `cutter_cards`. Consumes NO cards from any hand
    /// — the escrow was funded at offer time — so [`ResolvedMove::played_cards`] is empty.
    Respond {
        player: Player,
        /// The kind of OFFER this answers (Gift or Competition). A response spends no
        /// used-flag; see [`ResolvedMove::action_kind`].
        answering: ActionKind,
        taker_cards: Vec<u8>,
        cutter_cards: Vec<u8>,
    },
}

impl ResolvedMove {
    pub fn player(&self) -> Player {
        match self {
            ResolvedMove::Secret { player, .. }
            | ResolvedMove::Discard { player, .. }
            | ResolvedMove::Gift { player, .. }
            | ResolvedMove::Competition { player, .. }
            | ResolvedMove::Respond { player, .. } => *player,
        }
    }

    /// The action-kind this move BELONGS TO. For the four actions it is their own kind; for a
    /// [`ResolvedMove::Respond`] it is the kind of the OFFER being answered. A response
    /// consumes no used-flag — use [`ResolvedMove::action_kind`] when that distinction
    /// matters, and [`ResolvedMove::method`] for the executor dispatch method (a response
    /// does NOT dispatch under the offer's method).
    pub fn action(&self) -> ActionKind {
        match self {
            ResolvedMove::Secret { .. } => ActionKind::Secret,
            ResolvedMove::Discard { .. } => ActionKind::Discard,
            ResolvedMove::Gift { .. } => ActionKind::Gift,
            ResolvedMove::Competition { .. } => ActionKind::Competition,
            ResolvedMove::Respond { answering, .. } => *answering,
        }
    }

    /// The once-per-round action-kind this move SPENDS — `None` for a response, which spends
    /// none (Lean `used_applyResponse`).
    pub fn action_kind(&self) -> Option<ActionKind> {
        match self {
            ResolvedMove::Respond { .. } => None,
            other => Some(other.action()),
        }
    }

    /// The executor dispatch method this move commits under.
    pub fn method(&self) -> &'static str {
        match self {
            ResolvedMove::Respond {
                answering: ActionKind::Gift,
                ..
            } => "respond_gift",
            ResolvedMove::Respond { .. } => "respond_comp",
            other => other.action().method(),
        }
    }

    /// The exact distinct card ids this move consumes FROM HAND. This is the bridge from the
    /// guild-count projection back to the committed hidden hand: the surface removes these
    /// cards. A Gift/Competition consumes all 3 / all 4 AT OFFER TIME; a response consumes
    /// NOTHING (its cards left the hand when the offer was cut).
    pub fn played_cards(&self) -> Vec<u8> {
        match self {
            ResolvedMove::Secret { card, .. } => vec![*card],
            ResolvedMove::Discard { cards, .. } => cards.to_vec(),
            ResolvedMove::Gift { present, .. } => present.to_vec(),
            ResolvedMove::Competition { pairs, .. } => {
                vec![pairs[0][0], pairs[0][1], pairs[1][0], pairs[1][1]]
            }
            ResolvedMove::Respond { .. } => Vec::new(),
        }
    }
}

/// A flat projection of the engine state into the executor's slot/heap model — the exact
/// values the driven executor must commit to after replaying the same moves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Projection {
    /// deck, oop, a_hand, b_hand, a_secret, b_secret, a_board, b_board (the 8
    /// conservation counters — they sum to 21).
    pub deck: u64,
    pub oop: u64,
    /// Cards a seat holds. **The escrow of a pending offer is counted in its PROPOSER's
    /// entry** — mirroring the Lean abstraction, where `pendingCards` is folded into the
    /// conserved total — so [`Projection::conservation_sum`] is 21 at EVERY turn, including
    /// while an offer stands on the table.
    pub hand: [u64; 2],
    pub secret_count: [u64; 2],
    pub board: [u64; 2],
    pub charm: [u64; 2],
    pub guilds_controlled: [u64; 2],
    pub winner: u64, // 0 none, 1 = A, 2 = B
    pub current: u64,
    /// The committed turn stamp: actions AND responses (a full round is 12).
    pub round_actions: u64,
    pub scored: u64,
    /// Whether an offer is on the table: 0 none, 1 gift, 2 competition.
    pub pending_kind: u64,
    /// score[guild][player] — cards placed on each side of each guild.
    pub score: [[u64; 2]; N_GUILDS],
    /// used-flag stamp per (player, action); 0 = unused, else the round turn stamp at which
    /// it was used (strictly increasing, so any reuse changes it).
    pub flag: [[u64; 4]; 2],
}

impl Projection {
    /// The conservation sum the `SumEquals` tooth pins to 21.
    pub fn conservation_sum(&self) -> u64 {
        self.deck
            + self.oop
            + self.hand[0]
            + self.hand[1]
            + self.secret_count[0]
            + self.secret_count[1]
            + self.board[0]
            + self.board[1]
    }
}

/// A tiny deterministic splitmix64 PRNG — keeps the reference reproducible with no
/// external `rand` dependency.
struct SplitMix64(u64);
impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// The reference engine: card identities, placements, the escrow, and the decisions each
/// seat may take. It moves ONLY through [`Engine::apply`] — there is no built-in strategy.
#[derive(Clone)]
pub struct Engine {
    deck: Vec<u8>,
    hands: [Vec<u8>; 2],
    secret: [Option<u8>; 2],
    /// score[guild][player].
    score: [[u64; 2]; N_GUILDS],
    used: [[bool; 4]; 2],
    flag: [[u64; 4]; 2],
    charm: [u64; 2],
    guilds_controlled: [u64; 2],
    winner: u64,
    /// The clause of `roundWinner` the ORACLE named for this round (`0..8`); `0` until scored.
    win_branch: u8,
    current: Player,
    /// Committed turns: actions AND responses.
    round_actions: u64,
    scored: bool,
    /// The offer on the table. Its cards are the ESCROW (derived, never a separate zone that
    /// can drift — the Lean `pendingCards`).
    pending: Option<PendingOffer>,
    /// The ten distinct cards each seat is entrusted for the whole round (opening six plus
    /// that seat's four draws), fixed at the deal.
    inventory: [Vec<u8>; 2],
}

impl Engine {
    /// Deal a fresh round from `seed`: build the 21-card deck, shuffle, remove one favor
    /// out of play, deal six to each player. The remaining eight fund the per-turn draws.
    /// The seat to move (A) then takes its first turn's draw immediately, so
    /// [`Engine::hand`] is always the exact set that seat may spend.
    pub fn new(seed: u64) -> Engine {
        // Deal DISTINCT card ids. `deck_guild` is the only projection into the seven guild
        // lanes; dealing guild numbers directly loses which copy a Merkle leaf commits.
        let mut deck: Vec<u8> = (0..DECK_SIZE).collect();
        // Deterministic Fisher-Yates.
        let mut rng = SplitMix64(seed ^ 0xA5A5_5A5A_1234_9876);
        for i in (1..deck.len()).rev() {
            let j = (rng.next() % (i as u64 + 1)) as usize;
            deck.swap(i, j);
        }
        // One favor removed out of play (face down).
        let _removed = deck.pop().expect("deck non-empty");
        let mut hands = [Vec::new(), Vec::new()];
        for _ in 0..6 {
            hands[0].push(deck.pop().unwrap());
        }
        for _ in 0..6 {
            hands[1].push(deck.pop().unwrap());
        }
        // THE DRAW ASSIGNMENT IS CHOICE-INDEPENDENT. Action-turns strictly alternate A, B,
        // A, B (an action passes the seat to the other player; a response hands it straight
        // back to the responder for their OWN action). Each action-turn draws exactly once
        // and a response draws nothing, so of the eight remaining cards seat A takes draw
        // slots 0, 2, 4, 6 and seat B slots 1, 3, 5, 7 — whatever either seat decides.
        let mut inventory = [hands[0].clone(), hands[1].clone()];
        for (slot, &card) in deck.iter().rev().enumerate() {
            inventory[slot % 2].push(card);
        }
        let mut engine = Engine {
            deck,
            hands,
            secret: [None, None],
            score: [[0; 2]; N_GUILDS],
            used: [[false; 4]; 2],
            flag: [[0; 4]; 2],
            charm: [0; 2],
            guilds_controlled: [0; 2],
            winner: 0,
            win_branch: 0,
            current: Player::A,
            round_actions: 0,
            scored: false,
            pending: None,
            inventory,
        };
        // A's first action-turn begins: the draw precedes the action.
        engine.draw_for_action_turn();
        engine
    }

    /// The current flat projection (what the executor must match).
    pub fn projection(&self) -> Projection {
        Projection {
            deck: self.deck.len() as u64,
            oop: self.oop_count(),
            hand: [self.hand_count(Player::A), self.hand_count(Player::B)],
            secret_count: [
                self.secret[0].is_some() as u64,
                self.secret[1].is_some() as u64,
            ],
            board: [self.board_count(Player::A), self.board_count(Player::B)],
            charm: self.charm,
            guilds_controlled: self.guilds_controlled,
            winner: self.winner,
            current: self.current.idx() as u64,
            round_actions: self.round_actions,
            scored: self.scored as u64,
            pending_kind: match self.pending.map(|o| o.kind()) {
                None => 0,
                Some(ActionKind::Gift) => 1,
                Some(ActionKind::Competition) => 2,
                Some(_) => unreachable!("only Gift/Competition open an offer"),
            },
            score: self.score,
            flag: self.flag,
        }
    }

    /// The seat to move — to ACT, or (while an offer stands) to ANSWER.
    pub fn current_player(&self) -> Player {
        self.current
    }

    /// The offer on the table, if any.
    pub fn pending_offer(&self) -> Option<PendingOffer> {
        self.pending
    }

    /// Whether `p` has already spent their once-per-round `action` (the used-flag).
    pub fn used_flag(&self, p: Player, a: ActionKind) -> bool {
        self.used[p.idx()][a.idx()]
    }

    /// The exact distinct card ids currently in `p`'s hand. Cards PRESENTED into a pending
    /// offer are on the table, not in hand, so they are not here (they are still counted in
    /// [`Projection::hand`] — see that field's note).
    pub fn hand(&self, p: Player) -> &[u8] {
        &self.hands[p.idx()]
    }

    /// The ten distinct cards `p` is entrusted for the whole round: the opening six plus the
    /// four that seat will draw. Fixed at the deal and independent of every decision either
    /// seat makes (see [`Engine::new`]).
    pub fn round_inventory(&self, p: Player) -> &[u8] {
        &self.inventory[p.idx()]
    }

    fn board_count(&self, p: Player) -> u64 {
        (0..N_GUILDS).map(|g| self.score[g][p.idx()]).sum()
    }

    /// The cards a pending offer holds in escrow on behalf of `p` (its proposer).
    fn escrow_count(&self, p: Player) -> u64 {
        match self.pending {
            Some(o) if o.proposer == p => o.presented().len() as u64,
            _ => 0,
        }
    }

    /// The card counter the executor commits for `p`: hand PLUS that seat's escrow. Folding
    /// the escrow into the proposer's counter is what keeps the conservation sum at 21 while
    /// an offer stands (the Lean model folds `pendingCards` into `totalCards` the same way).
    fn hand_count(&self, p: Player) -> u64 {
        self.hands[p.idx()].len() as u64 + self.escrow_count(p)
    }

    /// Cards out of play = 21 - (deck + both hands + both secrets + both boards). The
    /// removed favor plus every discarded favor.
    fn oop_count(&self) -> u64 {
        let accounted = self.deck.len() as u64
            + self.hand_count(Player::A)
            + self.hand_count(Player::B)
            + self.secret[0].is_some() as u64
            + self.secret[1].is_some() as u64
            + self.board_count(Player::A)
            + self.board_count(Player::B);
        DECK_SIZE as u64 - accounted
    }

    /// Whether the round's twelve committed turns (8 actions + 4 responses) are all played.
    pub fn round_complete(&self) -> bool {
        self.round_actions >= ROUND_TURNS
    }

    /// Draw for the seat that is about to take an ACTION turn. A response draws nothing, and
    /// no card is drawn once the round is complete — so exactly eight cards leave the deck,
    /// four per seat.
    fn draw_for_action_turn(&mut self) {
        if self.round_complete() || self.pending.is_some() {
            return;
        }
        debug_assert!(
            self.used[self.current.idx()].iter().any(|&u| !u),
            "a seat with no unused action must never be handed an action turn"
        );
        let card = self.deck.pop().expect("deck exhausted before round end");
        self.hands[self.current.idx()].push(card);
    }

    fn take(&mut self, p: Player, card: u8) -> u8 {
        let hand = &mut self.hands[p.idx()];
        let pos = hand
            .iter()
            .position(|&c| c == card)
            .expect("card not in hand");
        hand.remove(pos)
    }

    fn place_card(&mut self, p: Player, card: u8) {
        let guild = deck_guild(card as u64);
        debug_assert!((guild as usize) < N_GUILDS);
        self.score[guild as usize][p.idx()] += 1;
    }

    /// Whether `p` holds every one of `cards`, with no card named twice (the multiset
    /// containment `actionCards a ≤ hand p` — hand ids are distinct, so a repeat is a miss).
    fn holds_all(&self, p: Player, cards: &[u8]) -> bool {
        let hand = &self.hands[p.idx()];
        cards
            .iter()
            .enumerate()
            .all(|(i, c)| hand.contains(c) && !cards[..i].contains(c))
    }

    /// **Every legal decision for the seat to move**, for a UI or a bot to choose among.
    /// Complete: it enumerates every card combination (and, for a Competition, every one of
    /// the three PAIRINGS of a chosen four) that [`Engine::apply`] would admit right now.
    pub fn legal_decisions(&self) -> Vec<Decision> {
        let mut out = Vec::new();
        if self.scored || self.round_complete() {
            return out;
        }
        let p = self.current;
        if let Some(offer) = self.pending {
            // The interlock: only a response is legal, and only from the seat that did not cut.
            if offer.proposer == p {
                return out;
            }
            for pick in 0..offer.picks() {
                out.push(Decision::Respond { pick });
            }
            return out;
        }
        let mut hand = self.hands[p.idx()].clone();
        hand.sort_unstable();
        let n = hand.len();
        if !self.used_flag(p, ActionKind::Secret) {
            for &card in &hand {
                out.push(Decision::Secret { card });
            }
        }
        if !self.used_flag(p, ActionKind::Discard) {
            for i in 0..n {
                for j in (i + 1)..n {
                    out.push(Decision::Discard {
                        cards: [hand[i], hand[j]],
                    });
                }
            }
        }
        if !self.used_flag(p, ActionKind::Gift) {
            for i in 0..n {
                for j in (i + 1)..n {
                    for k in (j + 1)..n {
                        out.push(Decision::Gift {
                            present: [hand[i], hand[j], hand[k]],
                        });
                    }
                }
            }
        }
        if !self.used_flag(p, ActionKind::Competition) {
            for i in 0..n {
                for j in (i + 1)..n {
                    for k in (j + 1)..n {
                        for l in (k + 1)..n {
                            let q = [hand[i], hand[j], hand[k], hand[l]];
                            // The three distinct PAIRINGS of four favors. The pairing IS the
                            // cut (Lean `comp_balanced_cut_dominates`), so it is part of the
                            // decision, not a derived detail.
                            for (a, b, c, d) in [(0, 1, 2, 3), (0, 2, 1, 3), (0, 3, 1, 2)] {
                                out.push(Decision::Competition {
                                    pairs: [[q[a], q[b]], [q[c], q[d]]],
                                });
                            }
                        }
                    }
                }
            }
        }
        out
    }

    /// **THE ONLY MOVER.** Apply `p`'s decision, or refuse it with the exact reason. The
    /// legality conjuncts are the Lean `legalB` / `legalRespB` ones, unchanged.
    pub fn apply(&mut self, p: Player, d: Decision) -> Result<ResolvedMove, MoveError> {
        if self.scored || self.round_complete() {
            return Err(MoveError::RoundComplete);
        }
        match d {
            Decision::Respond { pick } => self.apply_response(p, pick),
            action => self.apply_action(p, action),
        }
    }

    fn apply_response(&mut self, p: Player, pick: u8) -> Result<ResolvedMove, MoveError> {
        let Some(offer) = self.pending else {
            return Err(MoveError::NoOfferPending);
        };
        // The anti-self-deal tooth is reported FIRST because it is the stronger reason: the
        // proposer is never the seat to move on their own offer, so `NotYourTurn` would
        // hide why they can never be.
        if offer.proposer == p {
            return Err(MoveError::CannotAnswerOwnOffer);
        }
        if self.current != p {
            return Err(MoveError::NotYourTurn);
        }
        let (taker, cutter) = offer.split(pick).ok_or(MoveError::BadPick)?;
        for &card in &taker {
            self.place_card(p, card);
        }
        for &card in &cutter {
            self.place_card(offer.proposer, card);
        }
        self.pending = None;
        self.round_actions += 1;
        // The seat STAYS with the responder, who now takes their own action turn — so
        // action-turns still alternate A, B, A, B with responses interjected.
        self.current = p;
        self.draw_for_action_turn();
        Ok(ResolvedMove::Respond {
            player: p,
            answering: offer.kind(),
            taker_cards: taker,
            cutter_cards: cutter,
        })
    }

    fn apply_action(&mut self, p: Player, d: Decision) -> Result<ResolvedMove, MoveError> {
        if self.pending.is_some() {
            return Err(MoveError::OfferPending);
        }
        if self.current != p {
            return Err(MoveError::NotYourTurn);
        }
        let kind = d.kind().expect("a non-response decision has a kind");
        if self.used[p.idx()][kind.idx()] {
            return Err(MoveError::ActionAlreadyUsed);
        }
        let cards = d.cards();
        if !self.holds_all(p, &cards) {
            return Err(MoveError::CardNotInHand);
        }
        for &card in &cards {
            self.take(p, card);
        }
        self.used[p.idx()][kind.idx()] = true;
        self.round_actions += 1;
        self.flag[p.idx()][kind.idx()] = self.round_actions;
        let mv = match d {
            Decision::Secret { card } => {
                self.secret[p.idx()] = Some(card);
                ResolvedMove::Secret {
                    player: p,
                    card,
                    guild: deck_guild(card as u64),
                }
            }
            Decision::Discard { cards } => ResolvedMove::Discard {
                player: p,
                cards,
                guilds: [deck_guild(cards[0] as u64), deck_guild(cards[1] as u64)],
            },
            Decision::Gift { present } => {
                self.pending = Some(PendingOffer {
                    proposer: p,
                    shape: OfferShape::Gift(present),
                });
                ResolvedMove::Gift {
                    player: p,
                    present,
                    guilds: [
                        deck_guild(present[0] as u64),
                        deck_guild(present[1] as u64),
                        deck_guild(present[2] as u64),
                    ],
                }
            }
            Decision::Competition { pairs } => {
                self.pending = Some(PendingOffer {
                    proposer: p,
                    shape: OfferShape::Competition(pairs),
                });
                ResolvedMove::Competition {
                    player: p,
                    pairs,
                    guilds: [
                        [
                            deck_guild(pairs[0][0] as u64),
                            deck_guild(pairs[0][1] as u64),
                        ],
                        [
                            deck_guild(pairs[1][0] as u64),
                            deck_guild(pairs[1][1] as u64),
                        ],
                    ],
                }
            }
            Decision::Respond { .. } => unreachable!("routed to apply_response"),
        };
        // To the responder if this opened an offer, to the next actor otherwise — both are
        // `p.other()` (Lean `applyLegal`).
        self.current = p.other();
        self.draw_for_action_turn();
        Ok(mv)
    }

    /// Reveal the secrets and take the round's verdict FROM THE PROVEN LEAN. The secret card is
    /// placed on its owner's side before the tallies are read (`secret_is_scored`); everything
    /// after that — row control, both tallies, the winner, and WHICH clause of the terminal rule
    /// decided — is [`crate::rules::adjudicate`], i.e. `Dregg2.Games.MultiwayTug`.
    ///
    /// ⚑ This used to end in `winner_of`, a Rust re-expression of `roundWinner` truncated to its
    /// two absolute-threshold branches. It had no charm tie-break and no row tie-break, so on
    /// every round where neither seat cleared the bar it answered "no winner" where the ruleset
    /// names a seat — a **78.5% played draw rate against the model's 5.1%**. It is deleted; this
    /// call is the only remaining answer source, and there is no fallback.
    ///
    /// `Err` iff the archive lacks the export or Lean refused the wire — fail-closed, because the
    /// alternative is answering with the semantics that caused the bug.
    pub fn score(&mut self) -> Result<Option<Player>, String> {
        assert!(
            self.round_complete(),
            "cannot score before the round completes"
        );
        for p in [Player::A, Player::B] {
            if let Some(c) = self.secret[p.idx()].take() {
                self.place_card(p, c);
            }
        }
        let v = crate::rules::adjudicate(&self.score)?;
        self.charm = v.charm;
        self.guilds_controlled = v.guilds;
        self.winner = v.winner_code;
        self.win_branch = v.branch;
        self.scored = true;
        Ok(v.winner())
    }

    /// The clause of the terminal rule that decided this round (`roundWinnerBranch`, `0..8`), as
    /// the oracle answered it. Meaningless before [`Engine::score`]; it is what names the deployed
    /// scoring method (`state::score_method`).
    pub fn win_branch(&self) -> u8 {
        self.win_branch
    }
}

/// **ONE example agent** — a deterministic policy over [`Engine::legal_decisions`], nothing
/// more. It is not the game and it is not optimal:
///
/// * answering, it takes the heaviest share on offer;
/// * acting, it spends the most expensive UNUSED kind first (the descending
///   `[Competition, Gift, Discard, Secret]` order, one of the 24 card-feasible ones),
///   presenting its LOWEST-influence favors and, on a Competition, the most BALANCED cut
///   (which is the side the Lean `comp_balanced_cut_dominates` proves guarantees more).
pub fn greedy_policy(engine: &Engine) -> Decision {
    let options = engine.legal_decisions();
    assert!(
        !options.is_empty(),
        "greedy_policy called with no legal decision (round complete?)"
    );
    options
        .into_iter()
        .min_by_key(|d| greedy_key(engine, d))
        .expect("a non-empty option list has a minimum")
}

/// The ranking [`greedy_policy`] minimises.
fn greedy_key(engine: &Engine, d: &Decision) -> (u8, i64, i64, Vec<u8>) {
    match d {
        Decision::Respond { pick } => {
            let offer = engine
                .pending_offer()
                .expect("a Respond is only legal with an offer on the table");
            let (taker, _) = offer.split(*pick).expect("a legal pick splits");
            (0, -(influence_of(&taker) as i64), 0, vec![*pick])
        }
        other => {
            let kind = other.kind().expect("a non-response has a kind");
            // Competition (4 cards) ranks 0, Secret (1 card) ranks 3.
            let kind_rank = 4 - kind.card_count() as u8;
            let cards = other.cards();
            let imbalance = match other {
                Decision::Competition { pairs } => {
                    (influence_of(&pairs[0]) as i64 - influence_of(&pairs[1]) as i64).abs()
                }
                _ => 0,
            };
            (kind_rank, influence_of(&cards) as i64, imbalance, cards)
        }
    }
}

/// Play a whole round to completion under `policy`, returning the ordered [`ResolvedMove`]s
/// and the (unscored) engine. The policy sees the live engine — its
/// [`Engine::legal_decisions`], [`Engine::pending_offer`] and [`Engine::hand`] — and returns
/// the decision for [`Engine::current_player`]. Panics if the policy returns an illegal one.
pub fn play_round_with<F>(seed: u64, mut policy: F) -> (Engine, Vec<ResolvedMove>)
where
    F: FnMut(&Engine) -> Decision,
{
    let mut e = Engine::new(seed);
    let mut moves = Vec::new();
    while !e.round_complete() {
        let p = e.current_player();
        let d = policy(&e);
        let mv = e
            .apply(p, d)
            .unwrap_or_else(|err| panic!("policy returned an illegal decision {d:?}: {err}"));
        moves.push(mv);
    }
    (e, moves)
}

/// Play a whole round under [`greedy_policy`]. A convenience for callers that just need
/// *some* complete round; it is one agent's play, not "the" play of the deal.
pub fn play_round(seed: u64) -> (Engine, Vec<ResolvedMove>) {
    play_round_with(seed, greedy_policy)
}
