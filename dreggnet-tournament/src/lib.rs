//! # `dreggnet-tournament` — a NO-CHEAT verifiable tournament BRACKET
//!
//! A tournament is a **seeded single-elimination bracket** over N competitors in which
//! advancement is structurally un-fakeable. Each ROUND runs on a FRESH, beacon-seeded
//! universe — the SAME universe for every competitor that round, so the field is fair —
//! and a competitor **ADVANCES only on a VERIFIED WIN**: their submission is re-executed
//! to the declared win state through [`ugc_dregg::verify_completion`] (the audited
//! no-cheat leaderboard gate), or, on the succinct path, its fold proof is accepted by
//! [`ugc_dregg::verify_proof_completion`]. A **forged / incomplete / result-tampered /
//! lost** run does NOT advance. The champion is the last verified survivor.
//!
//! So a bracket is un-riggable **by construction**: you cannot move to the next round
//! without a real, independently re-verifiable win. Cheating a tournament is not made
//! *hard* — it is made *impossible*, the same way the no-cheat leaderboard is.
//!
//! ## The bracket
//!
//! Entrants are seeded in entry order and padded to a power of two with **byes**. Each
//! round pairs adjacent surviving slots. For a match:
//!
//! 1. Both competitors submit their run for the round's universe.
//! 2. Each submission passes through the **no-cheat gate** ([`Registry::submit`] =
//!    [`verify_completion`], or [`Registry::submit_proof`] on the succinct path). It
//!    yields either a **verified turns-to-win** or a **rejection** (the exact
//!    [`ugc_dregg::RejectReason`]).
//! 3. The match winner is the verified win with **fewer turns**; ties break by the
//!    **seed index** (deterministic, fixed by the fair seeding). If *neither* competitor
//!    produced a verified win, the slot is left EMPTY — nobody advances without a win.
//!
//! A bye is not a free pass: to occupy any next-round slot a competitor must post a
//! verified win **that round** — the no-cheat property holds uniformly across the whole
//! bracket, byes included.
//!
//! ## Fairness (the beacon seed)
//!
//! Each round's universe is derived from the tournament's base seed and the round index
//! ([`round_epoch`]); the provider turns that epoch into a universe (a procgen world
//! everyone re-derives identically, or an authored fixed world). Every competitor in a
//! round faces the identical universe, and the round seeds are a real, reproducible
//! record.
//!
//! ## Honest scope
//!
//! What is REAL here: the bracket + the verify-gated advancement over ugc-dregg's audited
//! no-cheat verifier (a forged run cannot advance; the champion is a verified survivor;
//! each round is a real ugc leaderboard). Each round accepts BOTH a replay completion and
//! a succinct proof completion (whichever the universe supports).
//!
//! NAMED SEAMS (not built here): live match scheduling / a frontend; **matchmaking &
//! seeding by skill** (seeding is entry order — a fair but skill-blind policy); a
//! **durable bracket store** (the bracket lives in memory; [`Outcome`] is a serial
//! record a store would persist); **richer verified secondary tiebreak metrics** (depth
//! reached) beyond the verified turn count; and **prize / stake settlement** — glory,
//! not yield, over `$DREGG` services only (no P2E).

use blake3::Hasher;
use ugc_dregg::{
    Accepted, Completion, ProofCompletion, Registry, RejectReason, Universe, UniverseId,
    record_playthrough,
};

/// Domain tag for the per-round epoch derivation (a round's universe seed).
const DOMAIN_ROUND_EPOCH: &[u8] = b"dreggnet-tournament/round-epoch/v1";

/// Derive the **epoch commitment** for a round from the tournament's base `seed` and the
/// 0-based `round` index — a domain-separated hash. Every round is therefore a fresh,
/// deterministically-reproducible universe seed that anyone holding the base seed can
/// recompute (and confirm the round universe against).
pub fn round_epoch(seed: &[u8; 32], round: usize) -> [u8; 32] {
    let mut h = Hasher::new();
    h.update(&(DOMAIN_ROUND_EPOCH.len() as u64).to_le_bytes());
    h.update(DOMAIN_ROUND_EPOCH);
    h.update(seed);
    h.update(&(round as u64).to_le_bytes());
    *h.finalize().as_bytes()
}

// ═══════════════════════════════════════════════════════════════════════════════
// Competitors + their submissions.
// ═══════════════════════════════════════════════════════════════════════════════

/// What a competitor submits for a round's universe. The tournament re-verifies every
/// variant through the no-cheat gate; nothing here is trusted.
pub enum Submission {
    /// **An honest run**: play these moves against the round universe. The tournament
    /// records the playthrough and submits it claiming the true move count. Accepted iff
    /// the moves re-execute to the win ([`verify_completion`]).
    Play(Vec<usize>),
    /// **A result-tampered run**: play these (honest) moves but CLAIM a possibly-false
    /// turn count. Rejected as a result mismatch when the claim is a lie.
    PlayClaiming {
        /// The moves actually played.
        moves: Vec<usize>,
        /// The (possibly false) claimed turns-to-win.
        claimed_turns: usize,
    },
    /// **A forged run**: play `base_moves` honestly, then RETCON the recorded receipt at
    /// `tamper_step` to `tamper_choice`. On replay the edited move is refused by the real
    /// executor or diverges from the reproduced state — the forgery is rejected.
    Forged {
        /// The honest base run that is recorded, then tampered.
        base_moves: Vec<usize>,
        /// The receipt step index to retcon.
        tamper_step: usize,
        /// The choice index forged into that step.
        tamper_choice: usize,
    },
    /// **A raw completion** handed over verbatim (for a completion the caller assembles
    /// itself — e.g. a foreign-universe or otherwise hand-crafted submission).
    Raw(Box<Completion>),
    /// **A succinct proof-backed completion** — the ZK accept-path (moves not posted).
    Proof(Box<ProofCompletion>),
    /// **No submission** — a no-show, a disconnect, or a run that was lost. Never advances.
    NoShow,
}

impl Submission {
    /// Convenience: an honest run of `moves`.
    pub fn play(moves: impl Into<Vec<usize>>) -> Submission {
        Submission::Play(moves.into())
    }
}

/// A competitor's per-round strategy: given the round's universe, produce a submission.
/// Boxed so a competitor can be any closure (an honest player, a forger, a no-show).
pub type Strategy = Box<dyn Fn(&Universe) -> Submission>;

/// A registered competitor — a display name + a strategy. The seed index (bracket
/// position) is the order of entry into the [`Tournament`].
pub struct Entrant {
    name: String,
    strategy: Strategy,
}

impl Entrant {
    /// A competitor with `name` playing `strategy` each round.
    pub fn new(name: impl Into<String>, strategy: Strategy) -> Entrant {
        Entrant {
            name: name.into(),
            strategy,
        }
    }

    /// A competitor that plays the SAME fixed moves every round (an honest player of an
    /// authored universe whose winning line is constant). For a procgen world use
    /// [`Entrant::new`] with a strategy that derives the moves from the universe.
    pub fn honest(name: impl Into<String>, moves: impl Into<Vec<usize>>) -> Entrant {
        let moves = moves.into();
        Entrant::new(name, Box::new(move |_u| Submission::Play(moves.clone())))
    }

    /// A competitor that never submits — a no-show. Never advances (the no-cheat gate has
    /// nothing to accept).
    pub fn no_show(name: impl Into<String>) -> Entrant {
        Entrant::new(name, Box::new(|_u| Submission::NoShow))
    }

    /// The competitor's display name.
    pub fn name(&self) -> &str {
        &self.name
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// The round universe provider.
// ═══════════════════════════════════════════════════════════════════════════════

/// Builds a round's universe from the round index and its derived epoch. A procgen
/// provider turns the epoch into a fresh daily world everyone re-derives identically; an
/// authored provider may ignore the epoch and return a fixed world. The provider is
/// invoked ONCE per round, so every competitor that round faces the identical universe.
pub type RoundUniverse = Box<dyn Fn(usize, &[u8; 32]) -> Universe>;

// ═══════════════════════════════════════════════════════════════════════════════
// The bracket record.
// ═══════════════════════════════════════════════════════════════════════════════

/// A reference to a competitor in the bracket record — its display name + seed index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompetitorRef {
    /// The competitor's display name.
    pub name: String,
    /// The competitor's seed index (bracket position / entry order).
    pub seed: usize,
}

/// The verdict on one competitor's submission in a match — always the real result of the
/// no-cheat gate.
#[derive(Clone, Debug)]
pub enum SideOutcome {
    /// The submission passed the no-cheat gate: a verified win in `turns`.
    Verified {
        /// The verified turns-to-win (the deciding rank key — lower is better).
        turns: usize,
    },
    /// The submission was REJECTED by the no-cheat gate — the exact reason (a forged
    /// receipt chain, an incomplete run, a tampered result, a rejected proof, …).
    Rejected {
        /// The rejection message from [`RejectReason`].
        reason: String,
    },
    /// No competitor occupied this side (a bye / an empty slot from an earlier round with
    /// no verified winner).
    Absent,
}

impl SideOutcome {
    /// The verified turns, if this side posted a verified win.
    pub fn verified_turns(&self) -> Option<usize> {
        match self {
            SideOutcome::Verified { turns } => Some(*turns),
            _ => None,
        }
    }
}

/// One match in a round: the two sides, their gate verdicts, and who advanced.
#[derive(Clone, Debug)]
pub struct MatchRecord {
    /// The competitor on side A (or `None` for a bye/empty slot).
    pub a: Option<CompetitorRef>,
    /// The competitor on side B (or `None` for a bye/empty slot).
    pub b: Option<CompetitorRef>,
    /// The no-cheat gate's verdict on A's submission.
    pub a_outcome: SideOutcome,
    /// The no-cheat gate's verdict on B's submission.
    pub b_outcome: SideOutcome,
    /// Who advanced — the verified winner, or `None` if NEITHER side posted a verified
    /// win (the no-cheat gate refused to advance anyone).
    pub advanced: Option<CompetitorRef>,
}

/// The record of one round: its index, the derived epoch + universe, and every match.
#[derive(Clone, Debug)]
pub struct RoundRecord {
    /// The 0-based round index.
    pub round: usize,
    /// The derived epoch commitment this round's universe was seeded from.
    pub epoch: [u8; 32],
    /// The round universe's content id (identical for every competitor that round).
    pub universe_id: UniverseId,
    /// The round universe's display name.
    pub universe_name: String,
    /// The matches played this round.
    pub matches: Vec<MatchRecord>,
}

impl RoundRecord {
    /// The competitors who advanced out of this round (verified winners), in bracket order.
    pub fn advancers(&self) -> Vec<CompetitorRef> {
        self.matches
            .iter()
            .filter_map(|m| m.advanced.clone())
            .collect()
    }
}

/// The outcome of running a tournament to completion.
#[derive(Clone, Debug)]
pub struct Outcome {
    /// The champion — the last verified survivor, or `None` if the final round produced
    /// no verified winner (nobody can be champion without a verified win).
    pub champion: Option<CompetitorRef>,
    /// The full round-by-round record (who advanced, the round seeds, every match).
    pub rounds: Vec<RoundRecord>,
}

// ═══════════════════════════════════════════════════════════════════════════════
// The tournament.
// ═══════════════════════════════════════════════════════════════════════════════

/// A seeded, single-elimination, no-cheat tournament. Enter competitors, then [`run`]
/// the bracket; advancement is gated on a verified win every round.
///
/// [`run`]: Tournament::run
pub struct Tournament {
    seed: [u8; 32],
    round_universe: RoundUniverse,
    entrants: Vec<Entrant>,
}

impl Tournament {
    /// A new tournament seeded from `seed`, whose per-round universe comes from
    /// `round_universe` (invoked once per round with the round index + its derived epoch).
    pub fn new(seed: [u8; 32], round_universe: RoundUniverse) -> Tournament {
        Tournament {
            seed,
            round_universe,
            entrants: Vec::new(),
        }
    }

    /// Register a competitor. Entry order fixes the seed index (bracket position).
    pub fn enter(&mut self, entrant: Entrant) -> &mut Tournament {
        self.entrants.push(entrant);
        self
    }

    /// The number of registered competitors.
    pub fn len(&self) -> usize {
        self.entrants.len()
    }

    /// Whether no competitors are registered.
    pub fn is_empty(&self) -> bool {
        self.entrants.is_empty()
    }

    /// **RUN the bracket.** Rounds proceed until a single slot remains. Every round is a
    /// fresh beacon-seeded universe (fair — the same for all competitors), and every
    /// advancement passes the no-cheat gate. Returns the champion (last verified survivor)
    /// + the full round record.
    pub fn run(self) -> Outcome {
        // Pad to a power of two (min 2 so even a lone entrant must WIN a qualifying round
        // to be champion — no advancement without a verified win, byes included).
        let size = self.entrants.len().next_power_of_two().max(2);
        let mut alive: Vec<Option<usize>> = (0..size)
            .map(|i| (i < self.entrants.len()).then_some(i))
            .collect();

        let mut rounds = Vec::new();
        let mut round = 0;
        while alive.len() > 1 {
            let epoch = round_epoch(&self.seed, round);
            let universe = (self.round_universe)(round, &epoch);
            let universe_id = universe.id();
            let universe_name = universe.name().to_string();

            // Each round IS a real ugc-dregg leaderboard: publish the round universe and
            // submit every competitor's completion through the audited no-cheat gate.
            let mut board = Registry::new();
            board.publish(universe.clone());

            let mut next = Vec::with_capacity(alive.len() / 2);
            let mut matches = Vec::with_capacity(alive.len() / 2);
            let mut chunks = alive.chunks(2);
            while let Some(pair) = chunks.next() {
                let a_seed = pair[0];
                let b_seed = pair.get(1).copied().flatten();

                let (a_ref, a_outcome) = self.play_side(a_seed, &universe, universe_id, &mut board);
                let (b_ref, b_outcome) = self.play_side(b_seed, &universe, universe_id, &mut board);

                let advanced = decide(
                    a_ref.as_ref(),
                    a_outcome.verified_turns(),
                    b_ref.as_ref(),
                    b_outcome.verified_turns(),
                );
                next.push(advanced.as_ref().map(|c| c.seed));
                matches.push(MatchRecord {
                    a: a_ref,
                    b: b_ref,
                    a_outcome,
                    b_outcome,
                    advanced,
                });
            }

            rounds.push(RoundRecord {
                round,
                epoch,
                universe_id,
                universe_name,
                matches,
            });
            alive = next;
            round += 1;
        }

        let champion = alive
            .first()
            .copied()
            .flatten()
            .map(|seed| self.competitor_ref(seed));
        Outcome { champion, rounds }
    }

    /// A `CompetitorRef` for a seed index.
    fn competitor_ref(&self, seed: usize) -> CompetitorRef {
        CompetitorRef {
            name: self.entrants[seed].name.clone(),
            seed,
        }
    }

    /// Evaluate one side of a match: resolve the competitor's submission against the round
    /// universe and run it through the no-cheat gate. Returns the (optional) competitor
    /// reference + the gate verdict.
    fn play_side(
        &self,
        seed: Option<usize>,
        universe: &Universe,
        universe_id: UniverseId,
        board: &mut Registry,
    ) -> (Option<CompetitorRef>, SideOutcome) {
        let Some(seed) = seed else {
            return (None, SideOutcome::Absent);
        };
        let entrant = &self.entrants[seed];
        let submission = (entrant.strategy)(universe);
        let outcome = self.gate(&entrant.name, universe, universe_id, submission, board);
        (Some(self.competitor_ref(seed)), outcome)
    }

    /// THE NO-CHEAT GATE for one submission: build the completion against the round
    /// universe and submit it through the real ugc-dregg verifier. A verified win yields
    /// `Verified { turns }`; anything else yields `Rejected` with the exact reason. This
    /// is the whole guarantee — a forged / incomplete / tampered / lost run cannot pass.
    fn gate(
        &self,
        player: &str,
        universe: &Universe,
        universe_id: UniverseId,
        submission: Submission,
        board: &mut Registry,
    ) -> SideOutcome {
        match submission {
            Submission::NoShow => SideOutcome::Absent,

            Submission::Play(moves) => self.submit_recorded(
                player,
                universe,
                universe_id,
                &moves,
                moves.len(),
                None,
                board,
            ),

            Submission::PlayClaiming {
                moves,
                claimed_turns,
            } => self.submit_recorded(
                player,
                universe,
                universe_id,
                &moves,
                claimed_turns,
                None,
                board,
            ),

            Submission::Forged {
                base_moves,
                tamper_step,
                tamper_choice,
            } => self.submit_recorded(
                player,
                universe,
                universe_id,
                &base_moves,
                base_moves.len(),
                Some((tamper_step, tamper_choice)),
                board,
            ),

            Submission::Raw(c) => submit_verdict(board.submit(*c)),

            Submission::Proof(pc) => submit_verdict(board.submit_proof(*pc)),
        }
    }

    /// Record a base run against the round universe, optionally retcon a receipt step (a
    /// forgery), then submit with the given claimed turns. A move the executor refuses
    /// while recording (an ineligible pick — a lost run) is itself a real rejection.
    fn submit_recorded(
        &self,
        player: &str,
        universe: &Universe,
        universe_id: UniverseId,
        moves: &[usize],
        claimed_turns: usize,
        tamper: Option<(usize, usize)>,
        board: &mut Registry,
    ) -> SideOutcome {
        let mut play = match record_playthrough(universe, moves) {
            Ok(play) => play,
            // The real executor refused a move while recording — the run never happened.
            Err(e) => {
                return SideOutcome::Rejected {
                    reason: format!("run refused by the executor while recording: {e}"),
                };
            }
        };
        if let Some((step, choice)) = tamper {
            if let Some(s) = play.steps.get_mut(step) {
                s.choice_index = choice;
            }
        }
        let completion = Completion {
            universe: universe_id,
            player: player.to_string(),
            play,
            claimed_turns,
        };
        // The audited no-cheat gate.
        submit_verdict(board.submit(completion))
    }
}

/// Turn a `Registry::submit` / `submit_proof` result into a side verdict.
fn submit_verdict(result: Result<Accepted, RejectReason>) -> SideOutcome {
    match result {
        Ok(Accepted { turns, .. }) => SideOutcome::Verified { turns },
        Err(reason) => SideOutcome::Rejected {
            reason: reason.to_string(),
        },
    }
}

/// Decide a match winner from the two sides' verified-win turns. The winner is the
/// verified win with FEWER turns; ties break by the (fair, deterministic) seed index. If
/// NEITHER side posted a verified win, nobody advances (`None`) — the no-cheat property:
/// advancement requires a verified win.
fn decide(
    a: Option<&CompetitorRef>,
    a_turns: Option<usize>,
    b: Option<&CompetitorRef>,
    b_turns: Option<usize>,
) -> Option<CompetitorRef> {
    // Candidates = sides with a verified win, keyed for a total, deterministic order:
    // (turns ascending, then seed index ascending).
    let mut best: Option<(usize, usize, CompetitorRef)> = None;
    for (competitor, turns) in [(a, a_turns), (b, b_turns)] {
        let (Some(competitor), Some(turns)) = (competitor, turns) else {
            continue;
        };
        let key = (turns, competitor.seed);
        let better = match &best {
            None => true,
            Some((bt, bs, _)) => key < (*bt, *bs),
        };
        if better {
            best = Some((turns, competitor.seed, competitor.clone()));
        }
    }
    best.map(|(_, _, c)| c)
}
