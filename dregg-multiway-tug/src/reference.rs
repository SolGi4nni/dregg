//! # The deterministic reference engine — the game's oracle.
//!
//! A faithful, pure Rust model of the multiway-tug round used to DRIVE and CHECK the
//! executor deployment (`crate::game`). The executor tracks card COUNTS + per-guild
//! placement scores + win state; this engine tracks the actual card identities and is
//! the source of truth the driven playthrough must reproduce (translation-validation:
//! the engine computes the next state, the executor's teeth re-check each rule against
//! it).
//!
//! Mechanics derived from Hanamikoji (designer Kota Nakayama); shipped as the original
//! re-theming "multiway-tug". Seven **guilds** with **influence** `[2,2,2,3,3,4,5]` (21
//! total), a 21-card **favor** deck, a hidden 6-card hand, four once-per-round actions
//! (Secret / Discard / Gift / Competition), win at `>= 11` influence OR `>= 4` guilds.
//!
//! ## The two rule gaps this engine FIXES (vs the vendored reference in
//! `~/dev/multiway-tug/src/mechanics.rs`)
//!
//! 1. **The Secret card is now scored.** `mechanics.rs::update_control_and_score` never
//!    added the secreted card to a guild — here [`Engine::score`] reveals each player's
//!    secret onto their side before control is computed.
//! 2. **The opponent's blind pick is a REAL choice, not pre-folded.** In `mechanics.rs`
//!    the acting player pre-decided the Gift/Competition split (`for_player` /
//!    `for_other`). Here the actor only chooses which cards to PRESENT; the OPPONENT
//!    ([`opponent_gift_pick`] / [`opponent_comp_pick`]) decides who gets what — an
//!    adversarial decision made by the other agent. (The full on-executor
//!    opponent-SIGNED sealed reveal is the Phase-2 sealed-auction shape.)
//!
//! It also models the per-turn **draw** (`mechanics.rs` omitted it, so a 6-card hand
//! could not fund the `1+2+3+4 = 10` cards a full round plays): each of a player's four
//! action-turns draws one card from the deck first (`6 + 4 = 10`; the deck holds exactly
//! the `8` cards two players draw).

/// Number of contested guilds.
pub const N_GUILDS: usize = 7;
/// Per-guild influence weight; sums to 21 (the deck size and total contestable charm).
pub const INFLUENCE: [u8; N_GUILDS] = [2, 2, 2, 3, 3, 4, 5];
/// The full deck size (== total influence == the conservation constant).
pub const DECK_SIZE: u8 = 21;

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

/// One of the four once-per-round actions.
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
}

/// A resolved move ready to replay on the executor: the acting player, the action, and
/// (for the placing actions) exactly which guild-cards landed on which side. The draw is
/// implicit (deck -> hand) and folded into the action turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolvedMove {
    /// Player secreted one favor of `guild` (revealed + scored at [`Engine::score`]).
    Secret { player: Player, guild: u8 },
    /// Player discarded two favors (out of play this round).
    Discard { player: Player, guilds: [u8; 2] },
    /// Player presented three favors; the OPPONENT kept `opp_guild`, the actor kept
    /// `self_guilds` (placed on the actor's side; `opp_guild` on the opponent's).
    Gift {
        player: Player,
        self_guilds: [u8; 2],
        opp_guild: u8,
    },
    /// Player presented two pairs; the OPPONENT kept `opp_guilds`, the actor kept
    /// `self_guilds`.
    Competition {
        player: Player,
        self_guilds: [u8; 2],
        opp_guilds: [u8; 2],
    },
}

impl ResolvedMove {
    pub fn player(&self) -> Player {
        match self {
            ResolvedMove::Secret { player, .. }
            | ResolvedMove::Discard { player, .. }
            | ResolvedMove::Gift { player, .. }
            | ResolvedMove::Competition { player, .. } => *player,
        }
    }
    pub fn action(&self) -> ActionKind {
        match self {
            ResolvedMove::Secret { .. } => ActionKind::Secret,
            ResolvedMove::Discard { .. } => ActionKind::Discard,
            ResolvedMove::Gift { .. } => ActionKind::Gift,
            ResolvedMove::Competition { .. } => ActionKind::Competition,
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
    pub hand: [u64; 2],
    pub secret_count: [u64; 2],
    pub board: [u64; 2],
    pub charm: [u64; 2],
    pub guilds_controlled: [u64; 2],
    pub winner: u64, // 0 none, 1 = A, 2 = B
    pub current: u64,
    pub round_actions: u64,
    pub scored: u64,
    /// score[guild][player] — cards placed on each side of each guild.
    pub score: [[u64; 2]; N_GUILDS],
    /// used-flag stamp per (player, action); 0 = unused, else the round-action sequence
    /// number at which it was used (strictly increasing, so any reuse changes it).
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

/// The reference engine: card identities, placements, and the fixed deterministic
/// strategy that produces a full round of [`ResolvedMove`]s.
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
    current: Player,
    round_actions: u64,
    scored: bool,
    /// The per-player action order (draw-first feasible: 4,3,2,1 cards).
    order: [ActionKind; 4],
    order_pos: [usize; 2],
}

impl Engine {
    /// Deal a fresh round from `seed`: build the 21-card deck, shuffle, remove one favor
    /// out of play, deal six to each player. The remaining eight fund the per-turn draws.
    pub fn new(seed: u64) -> Engine {
        let mut deck: Vec<u8> = Vec::with_capacity(DECK_SIZE as usize);
        for (g, &inf) in INFLUENCE.iter().enumerate() {
            for _ in 0..inf {
                deck.push(g as u8);
            }
        }
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
        Engine {
            deck,
            hands,
            secret: [None, None],
            score: [[0; 2]; N_GUILDS],
            used: [[false; 4]; 2],
            flag: [[0; 4]; 2],
            charm: [0; 2],
            guilds_controlled: [0; 2],
            winner: 0,
            current: Player::A,
            round_actions: 0,
            scored: false,
            order: [
                ActionKind::Competition,
                ActionKind::Gift,
                ActionKind::Discard,
                ActionKind::Secret,
            ],
            order_pos: [0, 0],
        }
    }

    /// The current flat projection (what the executor must match).
    pub fn projection(&self) -> Projection {
        Projection {
            deck: self.deck.len() as u64,
            oop: self.oop_count(),
            hand: [self.hands[0].len() as u64, self.hands[1].len() as u64],
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
            score: self.score,
            flag: self.flag,
        }
    }

    /// The player whose turn it is to act next (the mover of the next [`Engine::play_next`]).
    pub fn current_player(&self) -> Player {
        self.current
    }

    /// The action the current player would play next (their scheduled order), or `None` if the
    /// round is complete. Lets a surface offer the *right* once-per-round action and refuse an
    /// out-of-order fire.
    pub fn peek_next_action(&self) -> Option<ActionKind> {
        if self.round_complete() {
            None
        } else {
            Some(self.order[self.order_pos[self.current.idx()]])
        }
    }

    /// Whether `p` has already spent their once-per-round `action` (the used-flag). A surface
    /// greys a used action.
    pub fn used_flag(&self, p: Player, a: ActionKind) -> bool {
        self.used[p.idx()][a.idx()]
    }

    fn board_count(&self, p: Player) -> u64 {
        (0..N_GUILDS).map(|g| self.score[g][p.idx()]).sum()
    }

    /// Cards out of play = 21 - (deck + both hands + both secrets + both boards). The
    /// removed favor plus every discarded favor.
    fn oop_count(&self) -> u64 {
        let accounted = self.deck.len() as u64
            + self.hands[0].len() as u64
            + self.hands[1].len() as u64
            + self.secret[0].is_some() as u64
            + self.secret[1].is_some() as u64
            + self.board_count(Player::A)
            + self.board_count(Player::B);
        DECK_SIZE as u64 - accounted
    }

    /// Whether the round's eight action-turns are all played.
    pub fn round_complete(&self) -> bool {
        self.round_actions >= 8
    }

    fn draw(&mut self, p: Player) {
        let card = self.deck.pop().expect("deck exhausted before round end");
        self.hands[p.idx()].push(card);
    }

    fn take(&mut self, p: Player, guild: u8) -> u8 {
        let hand = &mut self.hands[p.idx()];
        let pos = hand
            .iter()
            .position(|&c| c == guild)
            .expect("card not in hand");
        hand.remove(pos)
    }

    fn place(&mut self, p: Player, guild: u8) {
        self.score[guild as usize][p.idx()] += 1;
    }

    /// Play the acting player's next scheduled action, resolving any opponent pick, and
    /// return the [`ResolvedMove`]. Panics if the round is complete.
    pub fn play_next(&mut self) -> ResolvedMove {
        assert!(!self.round_complete(), "round already complete");
        let p = self.current;
        self.draw(p);
        let action = self.order[self.order_pos[p.idx()]];
        self.order_pos[p.idx()] += 1;
        self.used[p.idx()][action.idx()] = true;
        self.round_actions += 1;
        self.flag[p.idx()][action.idx()] = self.round_actions;

        let mv = match action {
            ActionKind::Secret => {
                let g = self.pick_lowest(p, 1)[0];
                let c = self.take(p, g);
                self.secret[p.idx()] = Some(c);
                ResolvedMove::Secret {
                    player: p,
                    guild: g,
                }
            }
            ActionKind::Discard => {
                let gs = self.pick_lowest(p, 2);
                self.take(p, gs[0]);
                self.take(p, gs[1]);
                ResolvedMove::Discard {
                    player: p,
                    guilds: [gs[0], gs[1]],
                }
            }
            ActionKind::Gift => {
                // Actor PRESENTS three; the OPPONENT keeps one (their real choice).
                let present = self.pick_highest(p, 3);
                let opp_guild = opponent_gift_pick(&present);
                // Remove the presented cards from the actor's hand.
                for &g in &present {
                    self.take(p, g);
                }
                let mut kept = present.clone();
                let kpos = kept.iter().position(|&g| g == opp_guild).unwrap();
                kept.remove(kpos);
                self.place(p.other(), opp_guild);
                self.place(p, kept[0]);
                self.place(p, kept[1]);
                ResolvedMove::Gift {
                    player: p,
                    self_guilds: [kept[0], kept[1]],
                    opp_guild,
                }
            }
            ActionKind::Competition => {
                // Actor PRESENTS two pairs; the OPPONENT keeps one pair.
                let four = self.pick_highest(p, 4);
                let pair0 = [four[0], four[1]];
                let pair1 = [four[2], four[3]];
                let opp_pair = opponent_comp_pick(pair0, pair1);
                let self_pair = if opp_pair == pair0 { pair1 } else { pair0 };
                for &g in &four {
                    self.take(p, g);
                }
                self.place(p.other(), opp_pair[0]);
                self.place(p.other(), opp_pair[1]);
                self.place(p, self_pair[0]);
                self.place(p, self_pair[1]);
                ResolvedMove::Competition {
                    player: p,
                    self_guilds: self_pair,
                    opp_guilds: opp_pair,
                }
            }
        };
        self.current = self.current.other();
        mv
    }

    /// Pick `k` lowest-influence cards from `p`'s hand (deterministic).
    fn pick_lowest(&self, p: Player, k: usize) -> Vec<u8> {
        let mut hand = self.hands[p.idx()].clone();
        hand.sort_by_key(|&g| (INFLUENCE[g as usize], g));
        hand.truncate(k);
        hand
    }

    /// Pick `k` highest-influence cards from `p`'s hand (deterministic).
    fn pick_highest(&self, p: Player, k: usize) -> Vec<u8> {
        let mut hand = self.hands[p.idx()].clone();
        hand.sort_by_key(|&g| (std::cmp::Reverse(INFLUENCE[g as usize]), g));
        hand.truncate(k);
        hand
    }

    /// Reveal the secrets, compute control / charm / guild counts / winner. Fixes gap #1:
    /// the secret card is placed on its owner's side BEFORE control is computed. Returns
    /// the resolved winner (`None` = no win threshold reached).
    pub fn score(&mut self) -> Option<Player> {
        assert!(
            self.round_complete(),
            "cannot score before the round completes"
        );
        // Gap #1: reveal + score each secret.
        for p in [Player::A, Player::B] {
            if let Some(c) = self.secret[p.idx()].take() {
                self.place(p, c);
            }
        }
        let mut charm = [0u64; 2];
        let mut controlled = [0u64; 2];
        for g in 0..N_GUILDS {
            let a = self.score[g][0];
            let b = self.score[g][1];
            let owner = if a > b {
                Some(0usize)
            } else if b > a {
                Some(1usize)
            } else {
                None
            };
            if let Some(o) = owner {
                charm[o] += INFLUENCE[g] as u64;
                controlled[o] += 1;
            }
        }
        self.charm = charm;
        self.guilds_controlled = controlled;
        self.winner = winner_of(charm, controlled)
            .map(|p| p as u64 + 1)
            .unwrap_or(0);
        self.scored = true;
        match self.winner {
            1 => Some(Player::A),
            2 => Some(Player::B),
            _ => None,
        }
    }
}

/// The win rule: `>= 11` influence wins first, else `>= 4` controlled guilds. Ties on a
/// threshold resolve to whichever player reaches it (A checked first — matching the
/// vendored `mechanics.rs` max-by-key order). Returns the winning player index.
pub fn winner_of(charm: [u64; 2], controlled: [u64; 2]) -> Option<usize> {
    if charm[0] >= 11 && charm[0] >= charm[1] {
        return Some(0);
    }
    if charm[1] >= 11 {
        return Some(1);
    }
    if controlled[0] >= 4 && controlled[0] >= controlled[1] {
        return Some(0);
    }
    if controlled[1] >= 4 {
        return Some(1);
    }
    None
}

/// The opponent's Gift pick (gap #2): faced with three presented favors, the opponent
/// keeps the single highest-influence one for themselves (denying the actor the strongest
/// card). A genuine choice by the OTHER agent — not the actor's pre-folded split.
pub fn opponent_gift_pick(present: &[u8]) -> u8 {
    *present
        .iter()
        .max_by_key(|&&g| (INFLUENCE[g as usize], std::cmp::Reverse(g)))
        .expect("non-empty presentation")
}

/// The opponent's Competition pick (gap #2): faced with two presented pairs, the opponent
/// keeps the higher-total-influence pair for themselves.
pub fn opponent_comp_pick(pair0: [u8; 2], pair1: [u8; 2]) -> [u8; 2] {
    let w = |pair: [u8; 2]| INFLUENCE[pair[0] as usize] as u64 + INFLUENCE[pair[1] as usize] as u64;
    if w(pair1) > w(pair0) { pair1 } else { pair0 }
}

/// Play a whole round to completion, returning the ordered [`ResolvedMove`]s and the
/// scored engine (call [`Engine::score`] result via `.winner`). Convenience for the
/// driver.
pub fn play_round(seed: u64) -> (Engine, Vec<ResolvedMove>) {
    let mut e = Engine::new(seed);
    let mut moves = Vec::new();
    while !e.round_complete() {
        moves.push(e.play_next());
    }
    (e, moves)
}
