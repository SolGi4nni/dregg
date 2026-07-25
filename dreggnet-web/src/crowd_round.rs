//! # `crowd_round` — the crowd-stream round driver (the WIRING layer)
//!
//! The converge-later half of the crowd-stream engine (`docs/CROWD-STREAM-ENGINE-DESIGN.md`):
//! it feeds live-stream votes into the REAL quorum-certified vote engine and lands ONE certified
//! world turn per round. Where [`dregg_stream_ingest`] is the pure, dep-light mapping (platform
//! payload → [`WeightedBallot`]), THIS module pays for the offering-stack deps and closes the
//! seam onto [`dungeon_on_dregg::collective::CollectiveRound`] — the tested
//! "signed-ballot tally → one verified turn" primitive.
//!
//! ```text
//! StreamEvent stream                (ingest here, over a round window)
//!   → events_to_ballots / aggregate (one ballot per distinct voter, their strongest option)
//!   → shaped, capped weight          (Linear or Concave/√ shaping; capped per voter)
//!   → weight-replicated custody seats (a $5 Super Chat = 5 seats under Linear; 2 under √)
//!   → CollectiveRound.cast × N       (each seat a REAL ed25519-signed ballot turn)
//!   → distinct-voter floor + quorum  (K distinct humans AND Σ weight ≥ M)
//!   → resolve_into_world             (the quorum gate → ONE certified TurnReceipt on the game)
//! ```
//!
//! ## What is real vs. the named residuals
//!
//! * **Real:** every seat casts a genuine `ed25519`-signed ballot the engine authenticates; the
//!   quorum `AffineLe` gate (`Σ TALLY ≥ M`) still certifies; `resolve_into_world` still binds the
//!   certified decision into the world cell and fires ONE real `TurnReceipt`. A sub-quorum window
//!   or a quorum-certified-but-illegal command is refused exactly as the collective's own tests
//!   prove. This driver only *sources the ballots*; it cannot vote past the executor's teeth.
//! * **Named residual — per-voter custody is CUSTODIAL (but no longer public).** The design's
//!   electorate-scaling gap: the **platform (us) mints and holds every viewer's key** — it is NOT
//!   real per-viewer custody (the viewer never signs on their own device). Real custody needs a
//!   viewer-held key enrolled out-of-band; until then a Super Chat is authenticated as *coming
//!   through YouTube*, not as *signed by that human*.
//!
//!   What is NOT residual any more: the seat secret used to be
//!   `blake3::derive_key(ctx, "crowd-stream/youtube/{author_id}#k")` over the viewer's **public**
//!   YouTube author id, so anyone watching the stream held every voter's ballot key and could mint
//!   their vote. A [`CrowdRound`] now draws one 32-byte **custody root** from OS entropy at
//!   [`open`](CrowdRound::open) and derives each seat as
//!   `Custodian::under_root(SEAT_DOMAIN/voter#k, root)` — the author id is the DOMAIN SEPARATOR,
//!   the root is the SECRET (the same shape `dreggnet-discord-identity`'s
//!   `seed_for(bot_secret, uid)` uses). Nothing public reconstructs a seat key, and the same
//!   author id in two rounds is two different keys.
//! * **Named residual — one weighted ballot (O(N) crypto).** To land a voter's weight `W`
//!   we materialize `W` (capped, shaped) replicated seats and cast `W` real signed ballots,
//!   so a window costs O(Σ shaped-weight) sign+verify operations under the overlay mutex. The
//!   backing `collective_choice` engine ALREADY has the O(1)-per-voter primitive
//!   (`cast_weighted` / `open_poll_weighted`, with a Lean mirror `castVoteW`: one signed
//!   ballot worth `W`, tallied as `W`), but the `CollectiveRound` wrapper exposes only the
//!   unweighted `cast` — wiring the weighted path through it is a `dungeon-on-dregg` change
//!   outside this crate. Until then we bound the blow-up TWO ways: the per-voter weight is
//!   **capped** (default [`DEFAULT_MAX_WEIGHT_PER_VOTER`], a small ceiling — a whale cannot
//!   mint an unbounded electorate) and can be **√-shaped** ([`WeightShaping::Concave`], seats
//!   ≤ ⌊√cap⌋), so the cost is O(N·√cap), not O(N·64).
//! * **Named residual — dynamic electorate.** `CollectiveRound` fixes its roster at open
//!   ("muster"). We honor that by materializing the electorate at **close** from exactly who voted
//!   this window, opening a fresh round each window. Join/leave within a window is fine; a
//!   persistent cross-window electorate + rotation is future work.
//! * **Named residual — the floor.** The certified turn inherits the deployed ledger's undischarged
//!   FRI/STARK floor; "certified" here means quorum-certified + executor-admitted, not
//!   FRI-sound-on-chain.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use dregg_stream_ingest::{
    PlatformAdapter, StreamEvent, WeightedBallot, YouTubeAdapter, events_to_ballots,
};
use dungeon_on_dregg::collective::{
    CertifiedTurn, CollectiveError, CollectiveRound, Custodian, FEDERATION, Proposal, Seat,
};
use spween_dregg::{Scene, WorldCell};

/// The seat-NAME domain: a voter's derived custody seats are labelled with this string so a
/// crowd-stream seat can never collide with the collective's own roster. It is a LABEL and a
/// domain separator — the seat's secret comes from the round's private custody root
/// ([`CrowdRound::custody_root`]), never from this name.
pub const SEAT_DOMAIN: &str = "crowd-stream/youtube";

/// **A live crowd-stream round.** Holds the poll question + proposals, the matchable option
/// keywords (index-aligned with the proposals), the quorum threshold, and the buffer of events
/// ingested during the current window. [`ingest`](Self::ingest) accumulates; [`preview`](Self::preview)
/// reports the running weighted tally (what the overlay pushes); [`close_into_world`](Self::close_into_world)
/// resolves the window into ONE certified world turn and advances to the next.
pub struct CrowdRound {
    question: String,
    proposals: Vec<Proposal>,
    /// Matchable keywords for each option (index-aligned with `proposals`). A viewer's chat/Super
    /// Chat text is matched against THESE (short — e.g. `"press on"`), not the full proposal label.
    options: Vec<String>,
    quorum: u64,
    federation: [u8; 32],
    /// Events ingested during the current (open) window.
    buffer: Vec<StreamEvent>,
    /// The certified turns this driver has landed, oldest first (an audit trail of the run).
    landed: Vec<CertifiedTurn>,
    /// The cap on a voter's RAW weight before shaping — the paid-influence ceiling / DoS guard
    /// (a single whale cannot mint an unbounded electorate; the shaped weight is what becomes
    /// seats, so under [`WeightShaping::Concave`] the seat count is ≤ ⌊√cap⌋).
    max_weight_per_voter: u64,
    /// How a voter's capped raw weight maps to influence (seats). See [`WeightShaping`].
    shaping: WeightShaping,
    /// The distinct-voter quorum floor `K`: a window certifies only when at least this many
    /// DISTINCT voters (humans, not replicated seats) cast a ballot — so paid weight alone (one
    /// Super Chat) can never carry a window. See [`CrowdRound::with_min_distinct_voters`].
    min_distinct_voters: u64,
    /// **The round's private custody root** — the SECRET every derived seat key hangs off.
    /// [`open_with`](CrowdRound::open_with) draws it from OS entropy; the seat name (a PUBLIC
    /// YouTube author id) only separates domains under it. Whoever holds this holds every viewer's
    /// ballot key, so a host that persists it (to rebuild a window's seats for a replay) persists
    /// it PRIVATELY, never inside anything it publishes. See [`CrowdRound::with_custody_root`].
    custody_root: [u8; 32],
}

/// The default per-voter RAW weight cap: a single voter's weight tops out here BEFORE shaping.
/// Deliberately small (was 64) — the O(Σ weight) signed-ballot blow-up under the overlay mutex
/// scales with this ceiling, so a small cap keeps a window cheap while [`WeightShaping::Concave`]
/// shrinks the seat count further (≤ ⌊√8⌋ = 2). Raise it per deployment via
/// [`CrowdRound::open_with`] when the electorate + hardware can pay for it.
pub const DEFAULT_MAX_WEIGHT_PER_VOTER: u64 = 8;

/// The default distinct-voter quorum floor: a window needs at least this many DISTINCT voters
/// (alongside meeting the weight quorum) before it can certify. `2` blocks the degenerate
/// single-Super-Chat-decides-the-world case out of the box; raise it per deployment.
pub const DEFAULT_MIN_DISTINCT_VOTERS: u64 = 2;

/// **How a voter's capped raw weight maps to influence (custody seats / tally weight).** A
/// vote's raw weight is `dregg_stream_ingest::weight_for` (≈ whole dollars for a paid event);
/// this shapes it AFTER the per-voter cap:
///
/// * [`Linear`](WeightShaping::Linear) — influence = the capped weight (a `$5` Super Chat = 5
///   seats). Faithful to the amount, but paid influence grows linearly with spend.
/// * [`Concave`](WeightShaping::Concave) — influence = `⌊√weight⌋` (min 1): a `$5` Super Chat =
///   2, a `$100` (capped) = ⌊√cap⌋. Paid influence **saturates** — doubling the spend does not
///   double the sway — which both damps whale dominance AND shrinks the replicated-seat count to
///   ≤ ⌊√cap⌋, cutting the per-window crypto cost.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum WeightShaping {
    /// Influence = capped raw weight (proportional to spend).
    Linear,
    /// Influence = `⌊√(capped weight)⌋` (min 1) — concave, saturating paid influence.
    Concave,
}

/// Floored integer square root (`⌊√n⌋`) — the [`WeightShaping::Concave`] kernel. Dependency-free
/// (a bit-by-bit method) so the shaping is exact and portable across toolchains.
fn isqrt_floor(n: u64) -> u64 {
    if n < 2 {
        return n;
    }
    let mut x = n;
    let mut y = (x + 1) / 2;
    while y < x {
        x = y;
        y = (x + n / x) / 2;
    }
    x
}

/// One option's running weighted tally in a [`TallyPreview`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OptionTally {
    /// The option's display label (the proposal label).
    pub label: String,
    /// The summed vote weight for this option this window.
    pub votes: u64,
}

/// A snapshot of a round's running weighted tally — the shape the overlay renders + pushes. It is
/// computed from the buffered events exactly as [`close_into_world`](CrowdRound::close_into_world)
/// will resolve them (per-voter aggregation + the weight cap), so the overlay never shows a total
/// the close won't honor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TallyPreview {
    /// The poll question.
    pub question: String,
    /// Per-option running tallies (index-aligned with the round's proposals).
    pub options: Vec<OptionTally>,
    /// Total weighted votes this window (Σ of the capped per-voter weights) — the value the quorum
    /// gate compares against `quorum`.
    pub total: u64,
    /// Distinct voters this window.
    pub voters: u64,
    /// The quorum threshold `M` (a seat/weight count; `total ≥ quorum` is the WEIGHT half of the
    /// certify gate).
    pub quorum: u64,
    /// The distinct-voter quorum floor `K`: a window certifies only when `voters ≥ min_distinct_voters`
    /// as well as `total ≥ quorum` — so paid weight alone cannot carry it.
    pub min_distinct_voters: u64,
    /// The current leader's option index (max weight, `> 0`), or `None` if no votes yet.
    pub leader: Option<u64>,
}

impl TallyPreview {
    /// Whether the running window would certify: BOTH the weight quorum (`total ≥ quorum`) AND
    /// the distinct-voter floor (`voters ≥ min_distinct_voters`) are met. A single big Super Chat
    /// clears the weight half but not the distinct-voter half.
    pub fn quorum_met(&self) -> bool {
        self.total >= self.quorum && self.voters >= self.min_distinct_voters
    }

    /// Whether the weight half of the gate is met (`total ≥ quorum`) — regardless of the
    /// distinct-voter floor. Useful for an overlay that wants to show "weight met, waiting on
    /// more distinct voters".
    pub fn weight_quorum_met(&self) -> bool {
        self.total >= self.quorum
    }

    /// Whether the distinct-voter floor is met (`voters ≥ min_distinct_voters`).
    pub fn distinct_floor_met(&self) -> bool {
        self.voters >= self.min_distinct_voters
    }
}

/// Everything a [`CrowdRound::close_into_world`] can refuse — the crowd-stream layer's own
/// distinct-voter floor, wrapping the backing [`CollectiveError`] (the weight quorum + the
/// executor's teeth).
#[derive(Debug)]
pub enum CrowdCloseError {
    /// Fewer distinct voters than [`CrowdRound::min_distinct_voters`] — the paid-influence
    /// saturation gate: weight alone (a single Super Chat) cannot certify a window; at least
    /// `required` distinct humans must have voted. Refused BEFORE the vote engine is touched (no
    /// crypto spent); the window is left intact for retry.
    DistinctFloor {
        /// The distinct voters this window had.
        voters: u64,
        /// The configured floor `K` it fell short of.
        required: u64,
    },
    /// The backing collective round refused — below the weight quorum
    /// ([`CollectiveError::BelowQuorum`]), a bad signature, or a quorum-certified illegal command
    /// the game executor rejected ([`CollectiveError::World`]).
    Collective(CollectiveError),
}

impl From<CollectiveError> for CrowdCloseError {
    fn from(e: CollectiveError) -> Self {
        CrowdCloseError::Collective(e)
    }
}

impl std::fmt::Display for CrowdCloseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CrowdCloseError::DistinctFloor { voters, required } => write!(
                f,
                "below the distinct-voter floor — {voters} distinct voter(s), need {required} \
                 (paid weight alone cannot carry a window); the world does not move"
            ),
            CrowdCloseError::Collective(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for CrowdCloseError {}

impl CrowdRound {
    /// Open a crowd-stream round. `proposals` and `options` are index-aligned (option `i`'s
    /// keyword matches proposal `i`'s command); `quorum` is the weight threshold `M`. Uses the
    /// collective's demo [`FEDERATION`] and the default per-voter seat cap.
    ///
    /// **The round draws a fresh 32-byte custody root from OS entropy** — a viewer's seat key is
    /// derived under that secret, never from their public author id. See
    /// [`with_custody_root`](Self::with_custody_root) for the reproducible path.
    ///
    /// Panics if `proposals` and `options` differ in length (a programming error — they are two
    /// views of the same option list).
    pub fn open(
        question: impl Into<String>,
        proposals: Vec<Proposal>,
        options: Vec<String>,
        quorum: u64,
    ) -> CrowdRound {
        Self::open_with(
            question,
            proposals,
            options,
            quorum,
            FEDERATION,
            DEFAULT_MAX_WEIGHT_PER_VOTER,
        )
    }

    /// [`open`](Self::open) with an explicit federation id + per-voter weight cap. Also draws a
    /// fresh OS-entropy custody root (see [`with_custody_root`](Self::with_custody_root)).
    pub fn open_with(
        question: impl Into<String>,
        proposals: Vec<Proposal>,
        options: Vec<String>,
        quorum: u64,
        federation: [u8; 32],
        max_weight_per_voter: u64,
    ) -> CrowdRound {
        assert_eq!(
            proposals.len(),
            options.len(),
            "proposals and option keywords must be index-aligned (one keyword per proposal)"
        );
        // THE CUSTODY ROOT. Every seat this round ever mints is `derive_key(ctx, root ‖ name)`, so
        // this value — not the viewer's public author id — is what makes a ballot unforgeable. It
        // comes from the OS, per round.
        let mut custody_root = [0u8; 32];
        getrandom::fill(&mut custody_root)
            .expect("operating-system RNG must mint the crowd-round custody root");
        CrowdRound {
            question: question.into(),
            proposals,
            options,
            quorum,
            federation,
            buffer: Vec::new(),
            landed: Vec::new(),
            max_weight_per_voter: max_weight_per_voter.max(1),
            shaping: WeightShaping::Linear,
            min_distinct_voters: DEFAULT_MIN_DISTINCT_VOTERS,
            custody_root,
        }
    }

    /// **Pin the round's custody root** instead of the OS-entropy one [`open`](Self::open) drew —
    /// the REPRODUCIBLE path, for a host that must rebuild the SAME seats later (a replayed
    /// window, a crash-safe candidate image, a differential test).
    ///
    /// `root` is a SECRET and MUST carry real entropy: every seat key is
    /// `blake3::derive_key(ctx, root ‖ "crowd-stream/youtube/{author_id}#k")`, so a guessable root
    /// is a guessable ballot key for every viewer in the window — exactly the wound the OS-entropy
    /// default closes. Pass a root only to REBUILD a round whose root you already hold privately;
    /// to make a new one, call [`open`](Self::open) and let it draw its own. Builder-style.
    pub fn with_custody_root(mut self, root: [u8; 32]) -> CrowdRound {
        self.custody_root = root;
        self
    }

    /// The round's private custody root — every seat key derives under it.
    ///
    /// ⚠ This is the SECRET that makes a viewer's ballot unforgeable. A host that persists it (to
    /// rebuild a window's seats) stores it privately; it must never reach a published round, an
    /// overlay payload, or a log line.
    pub fn custody_root(&self) -> [u8; 32] {
        self.custody_root
    }

    /// **Set the weight shaping** (default [`WeightShaping::Linear`]). Builder-style so a
    /// deployment configures it inline: `CrowdRound::open(..).with_shaping(WeightShaping::Concave)`.
    /// [`WeightShaping::Concave`] saturates paid influence and shrinks the replicated-seat count.
    pub fn with_shaping(mut self, shaping: WeightShaping) -> CrowdRound {
        self.shaping = shaping;
        self
    }

    /// **Set the distinct-voter quorum floor `K`** (default [`DEFAULT_MIN_DISTINCT_VOTERS`]). A
    /// window certifies only when at least `k` DISTINCT voters have cast a ballot, ALONGSIDE the
    /// weight quorum — so a single Super Chat's weight can never carry a window. `0`/`1` disables
    /// the floor (weight alone suffices). Builder-style.
    pub fn with_min_distinct_voters(mut self, k: u64) -> CrowdRound {
        self.min_distinct_voters = k;
        self
    }

    /// The active weight shaping.
    pub fn shaping(&self) -> WeightShaping {
        self.shaping
    }

    /// The distinct-voter quorum floor `K`.
    pub fn min_distinct_voters(&self) -> u64 {
        self.min_distinct_voters
    }

    /// A voter's INFLUENCE from their raw aggregated weight: cap to `max_weight_per_voter`, then
    /// apply the [`WeightShaping`]. This is the single place the cap + shaping live, so
    /// [`preview`](Self::preview) and [`close_into_world`](Self::close_into_world) can never
    /// diverge on how many seats a weight becomes.
    fn shaped_weight(&self, raw_weight: u64) -> u64 {
        let capped = raw_weight.clamp(1, self.max_weight_per_voter);
        match self.shaping {
            WeightShaping::Linear => capped,
            WeightShaping::Concave => isqrt_floor(capped).max(1),
        }
    }

    /// The poll question.
    pub fn question(&self) -> &str {
        &self.question
    }

    /// The round's proposals (index-aligned with the options / the tally).
    pub fn proposals(&self) -> &[Proposal] {
        &self.proposals
    }

    /// The matchable option keywords as `&str`s (what [`events_to_ballots`] matches against).
    pub fn option_keywords(&self) -> Vec<&str> {
        self.options.iter().map(String::as_str).collect()
    }

    /// The quorum threshold `M`.
    pub fn quorum(&self) -> u64 {
        self.quorum
    }

    /// Ingest one normalized event into the current window.
    pub fn ingest(&mut self, event: StreamEvent) {
        self.buffer.push(event);
    }

    /// Ingest many normalized events into the current window.
    pub fn ingest_batch(&mut self, events: impl IntoIterator<Item = StreamEvent>) {
        self.buffer.extend(events);
    }

    /// Convenience: parse a raw YouTube `liveChatMessages` JSON payload with the [`YouTubeAdapter`]
    /// and buffer the events. Returns how many were ingested.
    pub fn ingest_youtube(&mut self, raw: &str) -> usize {
        let events = YouTubeAdapter.parse(raw);
        let n = events.len();
        self.ingest_batch(events);
        n
    }

    /// How many events are buffered in the current window.
    pub fn buffered(&self) -> usize {
        self.buffer.len()
    }

    /// The certified turns landed so far (oldest first).
    pub fn landed(&self) -> &[CertifiedTurn] {
        &self.landed
    }

    /// **Aggregate the window to one ballot per distinct voter.** Each voter's PAID per-option
    /// weights are summed (paying more, or again, buys more influence), while all of a voter's
    /// UNPAID chats for one option collapse to a single unit — so chat-spam VOLUME can never stack
    /// into influence. The voter is then assigned the option they backed hardest (on a tie the
    /// higher option index wins — deterministic). This collapses a viewer who chatted the same
    /// option twice, and resolves a viewer who flip-flopped to their strongest signal. The returned
    /// weights are pre-cap (the cap is applied when seats are materialized).
    fn aggregate(&self) -> Vec<WeightedBallot> {
        let opts = self.option_keywords();
        // voter → option index → (Σ PAID weight, saw ≥1 UNPAID vote). Paid and unpaid votes are
        // aggregated DIFFERENTLY: paid SUMS, unpaid DEDUPS to a single unit, so repeated free chats
        // from one voter can never decide the vote (only paid weight, bounded by the per-voter cap,
        // accumulates).
        let mut per_voter: BTreeMap<String, BTreeMap<usize, (u64, bool)>> = BTreeMap::new();
        for e in &self.buffer {
            // Reuse the crate's canonical option matching by mapping this single event — recovering
            // its option + weight WITHOUT reimplementing `match_option`, while keeping the event
            // KIND that `events_to_ballots` discards.
            for b in events_to_ballots(std::slice::from_ref(e), &opts) {
                let slot = per_voter
                    .entry(b.voter)
                    .or_default()
                    .entry(b.option_idx)
                    .or_default();
                if e.kind.is_paid() {
                    slot.0 += b.weight;
                } else {
                    slot.1 = true;
                }
            }
        }
        per_voter
            .into_iter()
            .filter_map(|(voter, opts)| {
                // Combine each option's paid sum with a single unpaid unit, then pick the option the
                // voter backed hardest. max_by_key keeps the LAST max; BTreeMap iterates options
                // ascending, so a per-voter tie still resolves to the higher option index —
                // unchanged, deterministic.
                let (option_idx, weight) = opts
                    .into_iter()
                    .map(|(idx, (paid, unpaid))| (idx, paid + u64::from(unpaid)))
                    .max_by_key(|&(_, w)| w)?;
                Some(WeightedBallot {
                    voter,
                    option_idx,
                    weight,
                })
            })
            .collect()
    }

    /// The running weighted tally over the open window (what the overlay pushes). Computed from the
    /// SAME aggregation + cap + shaping [`close_into_world`](Self::close_into_world) uses (via
    /// [`shaped_weight`](Self::shaped_weight)), so preview and resolve agree on the seat count.
    pub fn preview(&self) -> TallyPreview {
        let ballots = self.aggregate();
        let mut votes = vec![0u64; self.options.len()];
        let mut total = 0u64;
        for b in &ballots {
            let w = self.shaped_weight(b.weight);
            if b.option_idx < votes.len() {
                votes[b.option_idx] += w;
                total += w;
            }
        }
        // Break ties to the LOWEST option index — the SAME rule collective-choice's `argmax` uses
        // to snapshot the certified winner (strict `v > best`). `max_by_key` keeps the LAST max
        // (the HIGHEST index), so on a tie the overlay would announce the OPPOSITE option to the one
        // the certified TurnReceipt executes; the differential canary pins the two equal.
        let leader = {
            let mut best: Option<(usize, u64)> = None;
            for (i, &v) in votes.iter().enumerate() {
                if best.map_or(true, |(_, bv)| v > bv) {
                    best = Some((i, v));
                }
            }
            best.and_then(|(i, v)| {
                (v > 0).then(|| {
                    u64::try_from(i).expect("the bounded crowd option list fits the stable wire")
                })
            })
        };
        let options = self
            .proposals
            .iter()
            .zip(votes.iter())
            .map(|(p, &v)| OptionTally {
                label: p.label.clone(),
                votes: v,
            })
            .collect();
        TallyPreview {
            question: self.question.clone(),
            options,
            total,
            voters: u64::try_from(ballots.len())
                .expect("the bounded crowd ballot set fits the stable wire"),
            quorum: self.quorum,
            min_distinct_voters: self.min_distinct_voters,
            leader,
        }
    }

    /// **THE SEAM — close the window, resolve into the world.** Materializes the electorate from
    /// who voted this window (each voter's SHAPED, capped weight expands to that many custody
    /// seats), opens a real [`CollectiveRound`] over that electorate, casts every seat's
    /// `ed25519`-signed ballot, and [`resolve_into_world`](CollectiveRound::resolve_into_world) →
    /// ONE certified [`CertifiedTurn`] on the game executor.
    ///
    /// Three gates fire before any seat is signed:
    /// * **distinct-voter floor** — fewer than [`min_distinct_voters`](Self::min_distinct_voters)
    ///   distinct voters ⇒ [`CrowdCloseError::DistinctFloor`], refused before ANY crypto is spent
    ///   (a single Super Chat's weight cannot carry the window);
    /// * **empty window** — no option-naming votes ⇒
    ///   [`CrowdCloseError::Collective`]`(`[`CollectiveError::BelowQuorum`]`)`;
    /// * **weight quorum** — fewer materialized seats than [`quorum`](Self::quorum) ⇒ the same
    ///   `BelowQuorum`. A seat casts one ballot worth 1, so the seat count IS the largest tally
    ///   the window can reach; refusing here (rather than letting the engine refuse the poll spec
    ///   at open) is what keeps a merely-too-small window RETAINED for retry instead of dropped.
    ///
    /// On success the certified turn is recorded and the window is reset (advanced). On refusal the
    /// window is **left intact** so the caller can decide (retry after more votes, or drop). The
    /// downstream collective teeth still hold: below the weight quorum →
    /// [`CollectiveError::BelowQuorum`]; a quorum-certified illegal command →
    /// [`CollectiveError::World`] (the executor's teeth).
    pub fn close_into_world(
        &mut self,
        world: &WorldCell,
        scene: &Scene,
    ) -> Result<CertifiedTurn, CrowdCloseError> {
        let ballots = self.aggregate();

        // Gate 1 — the DISTINCT-VOTER FLOOR. `ballots` is one entry per distinct voter (humans,
        // not replicated seats), so its length is the distinct-voter count. Enforced HERE, before
        // any seat is minted or signed, so paid weight alone (one whale) never reaches the engine.
        let distinct = u64::try_from(ballots.len())
            .expect("the bounded crowd ballot set fits the stable wire");
        if distinct < self.min_distinct_voters {
            return Err(CrowdCloseError::DistinctFloor {
                voters: distinct,
                required: self.min_distinct_voters,
            });
        }

        // Materialize the electorate: each voter's SHAPED (capped, then Linear/Concave) weight
        // expands to that many custody seats, all voting the voter's aggregated option.
        let seated = self.seated_from(&ballots);
        // No votes ⇒ below quorum, without troubling the engine with an empty electorate.
        if seated.is_empty() {
            return Err(CollectiveError::BelowQuorum.into());
        }

        // Gate 2 — the WEIGHT QUORUM, enforced HERE rather than left to the engine. Every seat
        // casts exactly one ballot worth 1, so `seated.len()` is BOTH the electorate size and the
        // largest tally this window can possibly reach: below `quorum` seats, the window can never
        // certify. `CollectiveRound::open_with` refuses that case as an OPEN-TIME
        // `BadPollSpec("quorum … exceeds the … distinct seated voter(s)")` — which is not
        // `BelowQuorum`, so the overlay close-loop classified it as `CloseTick::Skipped` and
        // ADVANCED the round, throwing away every buffered vote in a merely-too-small window (and
        // doing it again every window until the crowd got big enough). Refusing it here as the
        // `BelowQuorum` it actually is — before any seat is signed — keeps the window intact for
        // retry, which is what `TallyPreview::weight_quorum_met` has always reported.
        let reachable_total =
            u64::try_from(seated.len()).expect("the bounded crowd seat set fits the stable wire");
        if reachable_total < self.quorum {
            return Err(CollectiveError::BelowQuorum.into());
        }

        let electorate: Vec<Seat> = seated.iter().map(|(c, _)| c.seat()).collect();
        let mut round = CollectiveRound::open_with(
            self.question.clone(),
            self.proposals.clone(),
            &electorate,
            self.quorum,
            self.federation,
        )?;
        let poll = round.poll();
        for (custodian, option) in &seated {
            round.cast(&custodian.sign_ballot(poll, *option))?;
        }

        let cert = round.resolve_into_world(world, scene)?;
        self.landed.push(cert.clone());
        self.advance();
        Ok(cert)
    }

    /// Materialize the (custodian, option) seats for `ballots`: each voter's SHAPED (capped, then
    /// Linear/Concave) weight expands to that many custody seats, all voting that voter's
    /// aggregated option. Weight-as-replicated-seats is how a paid vote earns more influence on
    /// the one-ballot-per-seat engine; the shaping bounds how many seats a whale can mint
    /// (≤ ⌊√cap⌋ under Concave), keeping the per-window sign+verify cost small.
    ///
    /// The single place a seat key is minted, so [`electorate`](Self::electorate) and
    /// [`close_into_world`](Self::close_into_world) can never disagree about WHO is seated.
    fn seated_from(&self, ballots: &[WeightedBallot]) -> Vec<(Custodian, usize)> {
        let mut seated: Vec<(Custodian, usize)> = Vec::new();
        for b in ballots {
            let n = self.shaped_weight(b.weight);
            for k in 0..n {
                seated.push((
                    seat_custodian(&self.custody_root, &b.voter, k),
                    b.option_idx,
                ));
            }
        }
        seated
    }

    /// **The electorate the current window would seat** — the PUBLIC keys
    /// [`close_into_world`](Self::close_into_world) would open the round over, in the same order.
    /// Carries no secret (a [`Seat`] is a name + a public key), so an operator can inspect who is
    /// seated, and a test can hand the electorate to a real [`CollectiveRound`] and try to forge a
    /// ballot into it.
    pub fn electorate(&self) -> Vec<Seat> {
        self.seated_from(&self.aggregate())
            .iter()
            .map(|(c, _)| c.seat())
            .collect()
    }

    /// Reset the window for the next round (drop the buffered events). Called automatically after a
    /// successful [`close_into_world`](Self::close_into_world); call it directly to abandon a window
    /// (e.g. after a persistent illegal-command refusal).
    pub fn advance(&mut self) {
        self.buffer.clear();
    }
}

/// The per-voter, per-seat custody keypair — `Custodian::under_root(SEAT_DOMAIN ‖ voter ‖ #k,
/// custody_root)`, i.e. `blake3::derive_key(ctx, custody_root ‖ name)`.
///
/// **`custody_root` is the secret; `voter` is only the domain separator.** `voter` is a PUBLIC
/// YouTube `author_id` — anyone watching the stream can read it — so it is used exactly the way
/// `dreggnet-discord-identity::seed_for(bot_secret, uid)` uses a uid: to make one host secret yield
/// a distinct, non-colliding key per viewer per seat. Deriving the key from the name ALONE (the
/// old `Custodian::demo` path) handed every viewer's ballot to every viewer.
///
/// NAMED RESIDUAL (unchanged): the key is still CUSTODIAL — the platform mints and holds it, the
/// viewer never signs on their own device. It authenticates a ballot as *coming through the
/// platform*, not as *signed by that human*. Real per-viewer custody (a viewer-held key enrolled
/// out-of-band) is the electorate-scaling follow-up.
pub fn seat_custodian(custody_root: &[u8; 32], voter: &str, k: u64) -> Custodian {
    Custodian::under_root(format!("{SEAT_DOMAIN}/{voter}#{k}"), custody_root)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_stream_ingest::EventKind;
    use dungeon_on_dregg::narrator::Command;
    use dungeon_on_dregg::{deploy_keep, keep_scene};
    use spween_dregg::Value;

    /// The keep round proposals: option 0 = trade blows, option 1 = press on (the same moves the
    /// collective's own tests drive).
    fn keep_round(quorum: u64) -> CrowdRound {
        CrowdRound::open(
            "The gate-warden bars the way — what does the party do?",
            vec![
                Proposal::new("Trade blows with the gate-warden", Command::trade_blows()),
                Proposal::new("Press past into the plundered hall", Command::press_on()),
            ],
            vec!["trade blows".to_string(), "press on".to_string()],
            quorum,
        )
    }

    fn chat(author: &str, text: &str) -> StreamEvent {
        StreamEvent {
            platform: "youtube".into(),
            author_id: author.into(),
            kind: EventKind::Chat,
            amount_micros: 0,
            text: text.into(),
            ts: 0,
        }
    }

    fn super_chat(author: &str, text: &str, micros: u64) -> StreamEvent {
        StreamEvent {
            platform: "youtube".into(),
            author_id: author.into(),
            kind: EventKind::SuperChat,
            amount_micros: micros,
            text: text.into(),
            ts: 0,
        }
    }

    #[test]
    fn preview_aggregates_weighted_votes_per_voter() {
        let mut round = keep_round(3);
        round.ingest(chat("A", "press on"));
        round.ingest(chat("A", "press on")); // same voter, same option — collapses to one voter.
        round.ingest(super_chat("B", "TRADE BLOWS", 5_000_000)); // weight 5.
        round.ingest(chat("C", "trade blows"));

        let p = round.preview();
        assert_eq!(p.voters, 3, "A/B/C are three distinct voters");
        // press on: A's two UNPAID chats DEDUP to weight 1 (chat-spam cannot stack). trade blows:
        // B's $5 (paid) + C's one free chat = 6.
        assert_eq!(
            p.options[1].votes, 1,
            "A's two unpaid press-on chats dedup to weight 1"
        );
        assert_eq!(
            p.options[0].votes, 6,
            "B's $5 + C's chat = 6 on trade blows"
        );
        assert_eq!(p.total, 7);
        assert_eq!(p.leader, Some(0), "trade blows leads");
        assert!(p.quorum_met(), "7 ≥ quorum 3");
    }

    /// **CANARY — the overlay leader and the certified winner break a tie the SAME way.** On a
    /// dead 3-3 split the engine's `argmax` certifies the LOWEST option index (option 0); the
    /// preview's leader must announce the SAME option, or the OBS overlay would flash the OPPOSITE
    /// winner at the exact moment the certified `TurnReceipt` executes option 0. The old preview
    /// used `max_by_key` (LAST/highest-index max) and announced option 1 — this differential pins
    /// the overlay leader to the engine's certified winner INDEX, so they can never diverge.
    #[test]
    fn tie_preview_leader_matches_the_certified_argmax_winner() {
        let scene = keep_scene();
        let mut world = deploy_keep(36);
        world.seed_var("hp", Value::Int(50));

        let mut round = keep_round(3); // weight quorum 3; total 6 clears it.
        // A dead-even 3-3 split across SIX distinct voters (clears the distinct floor), all unpaid
        // (weight 1 each): option 0 = 3, option 1 = 3.
        for v in ["a0", "a1", "a2"] {
            round.ingest(chat(v, "trade blows"));
        }
        for v in ["b0", "b1", "b2"] {
            round.ingest(chat(v, "press on"));
        }

        let preview = round.preview();
        assert_eq!(preview.options[0].votes, 3, "option 0 has weight 3");
        assert_eq!(
            preview.options[1].votes, 3,
            "option 1 has weight 3 — a dead tie"
        );
        assert_eq!(
            preview.leader,
            Some(0),
            "the overlay breaks the tie to the LOWEST index, like the engine's argmax"
        );

        let cert = round
            .close_into_world(&world, &scene)
            .expect("a 3-3 tie still clears quorum 3 and certifies");

        // THE DIFFERENTIAL: the option the overlay announced as leader is EXACTLY the option index
        // the engine's argmax certified — never the opposite. (Old code: leader = Some(1) here,
        // while the cert executes option 0 → this assertion fails, which is what makes it a canary.)
        assert_eq!(
            preview.leader,
            Some(u64::try_from(cert.decision.winner).expect("winner index fits the wire")),
            "the overlay leader must name the certified winner's option on a tie"
        );
        assert_eq!(
            cert.command,
            Command::trade_blows(),
            "the certified turn executes option 0 (trade blows)"
        );
    }

    #[test]
    fn tally_preview_leader_round_trips_at_full_u64_wire_width() {
        let preview = TallyPreview {
            question: "wire boundary".to_string(),
            options: Vec::new(),
            total: 0,
            voters: 0,
            quorum: 1,
            min_distinct_voters: 1,
            leader: Some(u64::MAX),
        };
        let json = serde_json::to_string(&preview).expect("preview serializes");
        assert_eq!(
            serde_json::from_str::<TallyPreview>(&json).expect("preview decodes"),
            preview
        );
        assert!(json.contains("18446744073709551615"));
    }

    #[test]
    fn quorum_certified_crowd_vote_fires_a_real_world_turn() {
        let scene = keep_scene();
        let mut world = deploy_keep(30);
        world.seed_var("hp", Value::Int(50)); // the gate-warden fight begins at 50 HP.

        let mut round = keep_round(3);
        // Three viewers back trade-blows (option 0) with total weight ≥ 3.
        round.ingest(super_chat("whale", "trade blows!!", 3_000_000)); // weight 3.
        round.ingest(chat("viewerA", "trade blows"));
        round.ingest(chat("viewerB", "press on")); // a dissenter.

        let cert = round
            .close_into_world(&world, &scene)
            .expect("the quorum-certified crowd winner fires a real world turn");

        assert_eq!(
            cert.command,
            Command::trade_blows(),
            "trade-blows certified + resolved"
        );
        assert_ne!(
            cert.receipt.turn_hash, [0u8; 32],
            "a genuine committed world turn"
        );
        assert_eq!(
            world.read_var("hp"),
            30,
            "the world resolved trade-blows (50 → 30)"
        );
        assert_eq!(round.landed().len(), 1, "the certified turn is recorded");
        assert_eq!(
            round.buffered(),
            0,
            "the window advanced (buffer reset) after close"
        );
    }

    /// **A sub-quorum window is RETAINED, not dropped.** The refusal must be `BelowQuorum`
    /// specifically: `OverlayState::drive_close` classifies `BelowQuorum` as
    /// `CloseTick::Retained` (keep the votes, retry next window) and EVERYTHING ELSE as
    /// `CloseTick::Skipped`, which calls `advance()` and discards the buffer. Before
    /// `close_into_world`'s own weight-quorum gate, this window reached
    /// `CollectiveRound::open_with`, which refused it as `Vote(BadPollSpec("quorum 5 exceeds the
    /// 2 distinct seated voter(s)"))` — a *Skipped*, so the live close-loop threw away both votes
    /// every window until the crowd happened to be big enough. This test fails on that behaviour.
    #[test]
    fn sub_quorum_window_does_not_move_the_world() {
        let scene = keep_scene();
        let mut world = deploy_keep(31);
        world.seed_var("hp", Value::Int(50));

        let mut round = keep_round(5); // demand more weight than the crowd supplies.
        round.ingest(chat("A", "trade blows"));
        round.ingest(chat("B", "trade blows")); // two distinct voters (clears the floor); weight 2 < 5.

        match round.close_into_world(&world, &scene) {
            Err(CrowdCloseError::Collective(CollectiveError::BelowQuorum)) => {}
            other => panic!("a sub-quorum window must not move the world, got {other:?}"),
        }
        assert_eq!(world.read_var("hp"), 50, "the world did not move");
        assert_eq!(
            round.buffered(),
            2,
            "a refused window is left intact for retry"
        );
    }

    #[test]
    fn no_votes_is_below_the_distinct_floor() {
        let scene = keep_scene();
        let world = deploy_keep(32);
        let mut round = keep_round(1);
        round.ingest(chat("noise", "hello everyone")); // names no option ⇒ zero distinct voters.
        match round.close_into_world(&world, &scene) {
            Err(CrowdCloseError::DistinctFloor {
                voters: 0,
                required: DEFAULT_MIN_DISTINCT_VOTERS,
            }) => {}
            other => panic!("no option-naming votes ⇒ below the distinct floor, got {other:?}"),
        }
    }

    /// **The distinct-voter floor blocks a single Super Chat from carrying the world.** One whale
    /// pays enough weight to clear the quorum ALONE, but is the only distinct voter — the floor
    /// (default 2) refuses the window before any crypto is spent, and the world does not move.
    #[test]
    fn single_super_chat_cannot_carry_a_window() {
        let scene = keep_scene();
        let mut world = deploy_keep(34);
        world.seed_var("hp", Value::Int(50));
        let mut round = keep_round(3); // weight quorum 3.
        // A $9 Super Chat: raw weight 9, capped to 8 under Linear — clears the weight quorum alone.
        round.ingest(super_chat("whale", "trade blows!!", 9_000_000));

        let p = round.preview();
        assert!(
            p.weight_quorum_met(),
            "the whale's weight alone clears the quorum"
        );
        assert!(!p.distinct_floor_met(), "but it is a single distinct voter");
        assert!(!p.quorum_met(), "so the window would NOT certify");

        match round.close_into_world(&world, &scene) {
            Err(CrowdCloseError::DistinctFloor {
                voters: 1,
                required: 2,
            }) => {}
            other => panic!("one distinct voter must be refused by the floor, got {other:?}"),
        }
        assert_eq!(world.read_var("hp"), 50, "the world did not move");
    }

    /// **Concave (√) shaping saturates paid influence + shrinks the seat count.** A $5 Super Chat
    /// weighs 5 raw; under `Concave` its influence is ⌊√5⌋ = 2, so a whale no longer buys linear
    /// sway and the replicated-seat count (the per-window crypto cost) collapses.
    #[test]
    fn concave_shaping_saturates_paid_influence() {
        let mut round = keep_round(2).with_shaping(WeightShaping::Concave);
        round.ingest(super_chat("whale", "trade blows", 5_000_000)); // raw weight 5 → ⌊√5⌋ = 2.
        round.ingest(chat("viewerA", "press on")); // weight 1 → ⌊√1⌋ = 1.

        let p = round.preview();
        assert_eq!(
            p.options[0].votes, 2,
            "$5 trade-blows saturates to ⌊√5⌋ = 2"
        );
        assert_eq!(p.options[1].votes, 1, "a plain chat is ⌊√1⌋ = 1");
        assert_eq!(p.total, 3);
        assert_eq!(p.voters, 2);
        assert_eq!(round.shaping(), WeightShaping::Concave);
    }

    /// **The distinct-voter floor is configurable** — set it to 1 to let weight alone carry a
    /// window (the legacy pure-weight behaviour), or higher to demand broader participation.
    #[test]
    fn distinct_floor_is_configurable() {
        let scene = keep_scene();
        let mut world = deploy_keep(35);
        world.seed_var("hp", Value::Int(50));

        // Floor lowered to 1: a single whale's weight now certifies.
        let mut round = keep_round(3).with_min_distinct_voters(1);
        assert_eq!(round.min_distinct_voters(), 1);
        round.ingest(super_chat("whale", "trade blows!!", 4_000_000)); // weight 4 ≥ quorum 3.

        let cert = round
            .close_into_world(&world, &scene)
            .expect("with the floor at 1, weight alone certifies");
        assert_eq!(cert.command, Command::trade_blows());
        assert_eq!(world.read_var("hp"), 30, "the world resolved trade-blows");
    }

    /// **FALSIFIER — a public YouTube author id is NOT a ballot key.**
    ///
    /// The old [`seat_custodian`] was `Custodian::demo("crowd-stream/youtube/{author_id}#k")`: the
    /// seat's ed25519 SECRET was a pure function of a value printed next to every message in the
    /// live chat. Anyone watching the stream could mint any viewer's ballot.
    ///
    /// This exhibits the forgery **twice** — landing on the old derivation, refused on the new one:
    ///
    /// * (a) the public-data key is not in the round's electorate at all;
    /// * (b) cast at a real [`CollectiveRound`] over the round's REAL electorate, the engine
    ///   refuses it and the tally does not move;
    /// * (c) cast at a [`CollectiveRound`] over the OLD, name-derived electorate — reconstructed
    ///   here from public data only — the SAME forged ballot is ADMITTED and the tally moves to 1.
    ///
    /// (c) is what makes (b) a refusal rather than a dead path, and it is exactly what the old
    /// `close_into_world` seated.
    #[test]
    fn a_public_author_id_is_not_a_ballot_key_in_the_crowd_electorate() {
        // The attacker's entire input: two author ids, read off the live chat.
        const VICTIM: &str = "UCvictim_public_author_id";
        const OTHER: &str = "UCother_public_author_id";

        let mut round = keep_round(2);
        round.ingest(chat(VICTIM, "trade blows")); // option 0, weight 1 ⇒ one seat.
        round.ingest(chat(OTHER, "trade blows"));

        let electorate = round.electorate();
        assert_eq!(electorate.len(), 2, "one seat per unpaid voter");

        // The OLD derivation, reproduced verbatim from public data.
        let forger = Custodian::demo(format!("{SEAT_DOMAIN}/{VICTIM}#0"));

        // (a) — the derived-from-public-data key is not seated.
        assert!(
            !electorate.iter().any(|s| s.pk == forger.public_key()),
            "a viewer's seat key is reconstructible from their public author id"
        );

        // (b) — the forged ballot at the REAL electorate: refused, tally unmoved.
        let mut real = CollectiveRound::open_with(
            round.question().to_string(),
            round.proposals().to_vec(),
            &electorate,
            round.quorum(),
            FEDERATION,
        )
        .expect("the crowd electorate opens a real round");
        let real_poll = real.poll();
        let refused = real.cast(&forger.sign_ballot(real_poll, 1));
        assert!(
            refused.is_err(),
            "the engine ADMITTED a ballot whose key came from a public author id: {refused:?}"
        );
        assert_eq!(
            real.tally().expect("tally").total,
            0,
            "a refused forgery moved the real round's tally"
        );

        // (c) — the SAME forgery at the OLD, name-derived electorate: admitted, tally moves.
        let weak: Vec<Seat> = [VICTIM, OTHER]
            .into_iter()
            .map(|v| Custodian::demo(format!("{SEAT_DOMAIN}/{v}#0")).seat())
            .collect();
        assert!(
            weak.iter().any(|s| s.pk == forger.public_key()),
            "the old derivation seats exactly the key an author id reconstructs"
        );
        let mut old = CollectiveRound::open_with(
            round.question().to_string(),
            round.proposals().to_vec(),
            &weak,
            round.quorum(),
            FEDERATION,
        )
        .expect("the old electorate opens a round too");
        let old_poll = old.poll();
        old.cast(&forger.sign_ballot(old_poll, 1)).expect(
            "the OLD name-derived electorate ADMITS the forged ballot — that was the wound",
        );
        assert_eq!(
            old.tally().expect("tally").total,
            1,
            "the forgery landed on the old derivation"
        );
    }

    /// **FALSIFIER — the same viewer is a different seat in a different round.** Under the old
    /// derivation a seat's public key was a pure function of its author id, so every round the
    /// platform ever ran (and every other deployment) agreed on it — one leaked derivation
    /// compromised every window forever. Each round now draws its own OS-entropy custody root, so
    /// the same author id yields unrelated keys. Fails on the old behaviour: the two pks are equal.
    #[test]
    fn the_same_author_id_gets_unrelated_seats_in_two_rounds() {
        const VOTER: &str = "UCsteady_viewer";
        let mut a = keep_round(2);
        let mut b = keep_round(2);
        for round in [&mut a, &mut b] {
            round.ingest(chat(VOTER, "trade blows"));
            round.ingest(chat("UCsecond", "trade blows"));
        }
        assert_ne!(
            a.custody_root(),
            b.custody_root(),
            "two rounds drew the same custody root from the OS"
        );
        let (ea, eb) = (a.electorate(), b.electorate());
        assert_eq!(ea.len(), 2);
        assert_eq!(ea.len(), eb.len());
        for (sa, sb) in ea.iter().zip(eb.iter()) {
            assert_eq!(
                sa.name, sb.name,
                "the seat LABELS are the same in both rounds"
            );
            assert_ne!(
                sa.pk, sb.pk,
                "seat {} carries the same key in two rounds — its secret is a function of its \
                 public name",
                sa.name
            );
        }
    }

    /// The REPRODUCIBLE path still works, and it is the only way to get the same seats twice: two
    /// rounds under the SAME pinned custody root seat byte-identical public keys, and a certified
    /// turn still lands through them. This is what a replay / crash-safe rebuild uses — with a
    /// root the host drew from the OS once and keeps private.
    #[test]
    fn a_pinned_custody_root_rebuilds_the_same_seats() {
        let root = [7u8; 32];
        let build = || {
            let mut r = keep_round(2).with_custody_root(root);
            r.ingest(chat("UCreplay_a", "trade blows"));
            r.ingest(chat("UCreplay_b", "trade blows"));
            r
        };
        let (a, b) = (build(), build());
        assert_eq!(a.custody_root(), root);
        let (ea, eb) = (a.electorate(), b.electorate());
        assert_eq!(ea.len(), 2);
        for (sa, sb) in ea.iter().zip(eb.iter()) {
            assert_eq!(sa.name, sb.name);
            assert_eq!(sa.pk, sb.pk, "a pinned root must rebuild the same seat key");
        }
        // …and a pinned-root seat is still derivable ONLY with the root: the public name alone
        // reconstructs nothing.
        assert!(
            !ea.iter().any(
                |s| s.pk == Custodian::demo(format!("{SEAT_DOMAIN}/UCreplay_a#0")).public_key()
            ),
            "a pinned root still must not reduce to the seat's public name"
        );
        assert_eq!(
            seat_custodian(&root, "UCreplay_a", 0).public_key(),
            ea[0].pk,
            "seat_custodian under the round's root is what the round seats"
        );

        // The round still certifies a real world turn through those seats.
        let scene = keep_scene();
        let mut world = deploy_keep(37);
        world.seed_var("hp", Value::Int(50));
        let mut live = build();
        let cert = live
            .close_into_world(&world, &scene)
            .expect("a pinned-root round still lands a certified turn");
        assert_eq!(cert.command, Command::trade_blows());
        assert_eq!(world.read_var("hp"), 30);
    }

    #[test]
    fn isqrt_floor_is_exact() {
        assert_eq!(isqrt_floor(0), 0);
        assert_eq!(isqrt_floor(1), 1);
        assert_eq!(isqrt_floor(3), 1);
        assert_eq!(isqrt_floor(4), 2);
        assert_eq!(isqrt_floor(8), 2);
        assert_eq!(isqrt_floor(9), 3);
        assert_eq!(isqrt_floor(63), 7);
        assert_eq!(isqrt_floor(64), 8);
    }
}
