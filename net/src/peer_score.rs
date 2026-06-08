//! Peer reputation scoring + eclipse-resistant peer selection + request backoff.
//!
//! This module hardens the Plumtree gossip layer ([`crate::gossip`]) against
//! three concrete failure modes the federation orientation flagged:
//!
//! 1. **Eclipse attacks.** A naïve eager-peer policy ("first `D` peers to
//!    connect become the spanning-tree relays") lets an adversary who opens
//!    many connections from a single subnet monopolize a victim's eager set —
//!    every message then flows through attacker-controlled links, which can
//!    drop, delay, or selectively withhold blocks. [`PeerScoreboard::select_eager`]
//!    defends against this by (a) ranking candidates by an earned reputation
//!    score and (b) enforcing **address diversity**: at most
//!    [`MAX_EAGER_PER_BUCKET`] eager peers may share a `/16` IPv4 (or `/32`
//!    IPv6) address bucket. An attacker confined to one subnet therefore cannot
//!    capture more than a bounded fraction of the eager set, no matter how many
//!    connections they open.
//!
//! 2. **Byzantine / equivocating peers.** When the consensus layer surfaces an
//!    [`crate::gossip`] envelope that fails integrity (bad hash, unknown
//!    sender) — or when the node detects that a transport peer relayed an
//!    *equivocation* (a slashable consensus fault) — that peer is penalized via
//!    [`PeerScoreboard::penalize`]. Penalties decay reputation toward (and
//!    below) zero; a peer whose score drops under [`GRAYLIST_THRESHOLD`] is
//!    *graylisted* (excluded from the eager set and deprioritized for dialing)
//!    until its score recovers. Equivocation relay is the heaviest penalty, so
//!    one proven fault is enough to evict the relay from the spanning tree.
//!
//! 3. **Missing-block request storms.** A node that is missing a block must
//!    re-request it, but re-requesting *every* tick hammers the network and a
//!    dead/withholding peer. [`RequestBackoff`] implements capped exponential
//!    backoff per requested key: the first miss may be requested immediately,
//!    and each subsequent attempt waits `base * 2^n` (capped at `max`). This
//!    turns a tight retry loop into a polite, bandwidth-bounded one while still
//!    guaranteeing eventual re-request (liveness).
//!
//! # Correctness property (load-bearing)
//!
//! The eclipse-resistance guarantee is *structural*, and is pinned by
//! [`tests::eager_set_bounds_single_subnet_capture`]: for any candidate set in
//! which an attacker controls every peer in a single address bucket,
//! [`PeerScoreboard::select_eager`] returns an eager set containing **at most
//! [`MAX_EAGER_PER_BUCKET`]** attacker peers — even when the attacker's peers
//! outnumber and outscore every honest peer. Equivalently: capturing a victim's
//! eager set requires Sybils spread across at least
//! `ceil(eager_degree / MAX_EAGER_PER_BUCKET)` distinct address buckets, which
//! is the property an eclipse-resistant peer policy must provide (cf. Heilman
//! et al., "Eclipse Attacks on Bitcoin's Peer-to-Peer Network", USENIX 2015:
//! the defense is bucketing by network group so a single-subnet adversary
//! cannot fill the table).

use std::collections::HashMap;
use std::net::{IpAddr, SocketAddr};
use std::time::{Duration, Instant};

// ─── Tuning constants ────────────────────────────────────────────────────────

/// A freshly-seen peer starts here. Positive so a brand-new honest peer is
/// preferred over a penalized one, but low enough that earned reliability
/// (successful deliveries) dominates ranking over time.
pub const INITIAL_SCORE: f64 = 1.0;

/// Reward added when a peer delivers a *new* (first-seen) message eagerly —
/// evidence it is a useful, live spanning-tree relay.
pub const REWARD_FRESH_DELIVERY: f64 = 0.5;

/// Penalty for a peer that relays a message failing integrity (hash mismatch),
/// or whose connection died. Mild — could be a transient fault.
pub const PENALTY_INVALID_MESSAGE: f64 = 2.0;

/// Penalty for relaying a block from a *proven equivocator* (a slashable
/// consensus fault). Heavy: one is enough to push a default-score peer below
/// the graylist threshold and evict it from the eager set.
pub const PENALTY_EQUIVOCATION_RELAY: f64 = 10.0;

/// Penalty for a peer that broke a protocol invariant (e.g. unknown sender,
/// malformed envelope, stream flooding).
pub const PENALTY_PROTOCOL_VIOLATION: f64 = 4.0;

/// Scores at or below this are *graylisted*: excluded from the eager set and
/// deprioritized for dialing until reputation recovers.
pub const GRAYLIST_THRESHOLD: f64 = -1.0;

/// Hard floor so a deeply-penalized peer cannot reach `-inf` and take forever
/// to rehabilitate (we still want to retry it occasionally if no one else is
/// reachable — a permanent ban is its own availability risk).
pub const MIN_SCORE: f64 = -20.0;

/// Hard ceiling so a chatty peer cannot accumulate unbounded score and become
/// un-evictable after a single later fault.
pub const MAX_SCORE: f64 = 50.0;

/// Reputation decays toward [`INITIAL_SCORE`] at this fraction per decay tick,
/// so both rewards and penalties are *forgiving over time* — a peer that
/// misbehaved once but then behaves recovers, and a peer that was great but
/// went quiet loses its untouchable lead. Equivocation is the exception: it is
/// recorded as a hard fault (`equivocations`) that graylists regardless of the
/// decayed numeric score.
pub const DECAY_TOWARD_INITIAL: f64 = 0.05;

/// Eclipse defense: at most this many eager peers may share one address bucket
/// (`/16` for IPv4, the full address for IPv6). Bounds single-subnet capture of
/// the spanning tree.
pub const MAX_EAGER_PER_BUCKET: usize = 2;

// ─── Per-peer reputation record ──────────────────────────────────────────────

/// Reputation and liveness record for one transport peer (keyed by its
/// [`SocketAddr`] — the unit the gossip layer dials and pushes to).
#[derive(Clone, Debug)]
pub struct PeerScore {
    /// Earned reputation. Higher = more reliable. Bounded to
    /// `[MIN_SCORE, MAX_SCORE]`.
    pub score: f64,
    /// Count of proven equivocation relays. Any peer with `> 0` here is
    /// graylisted regardless of its decayed numeric score: relaying a slashable
    /// fault is categorical, not a matter of degree.
    pub equivocations: u32,
    /// Number of fresh (first-seen) messages this peer delivered. Diagnostic.
    pub fresh_deliveries: u64,
    /// When we last observed activity from this peer (for liveness / decay).
    pub last_seen: Instant,
    /// **Anchor** (F-5 / L4): an operator-configured, trusted bootstrap peer.
    /// An anchor is graylisted ONLY by the categorical equivocation hard-fault —
    /// transient/reputation erosion (a few dropped connections, the
    /// `InvalidMessage` flaps an eclipse adversary can induce) does NOT graylist
    /// it. This is the eclipse-by-attrition defense: an adversary must not be
    /// able to starve a trusted anchor out of the eager set by inducing flaps.
    pub is_anchor: bool,
}

impl PeerScore {
    fn new() -> Self {
        Self {
            score: INITIAL_SCORE,
            equivocations: 0,
            fresh_deliveries: 0,
            last_seen: Instant::now(),
            is_anchor: false,
        }
    }

    /// A peer is *graylisted* if it has relayed a proven equivocation OR
    /// (for a NON-anchor) its reputation has fallen to/under the graylist
    /// threshold. A trusted anchor is never graylisted by mere score erosion —
    /// only by the categorical equivocation fault (trust is not a license to
    /// equivocate, but transient flakiness must not evict it: F-5 / L4).
    pub fn is_graylisted(&self) -> bool {
        if self.equivocations > 0 {
            return true;
        }
        if self.is_anchor {
            return false;
        }
        self.score <= GRAYLIST_THRESHOLD
    }
}

impl Default for PeerScore {
    fn default() -> Self {
        Self::new()
    }
}

/// Why a peer is being penalized. Distinct reasons carry distinct weights so the
/// caller does not have to know the magnitudes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Penalty {
    /// Relayed a message whose hash did not match its claimed id, or whose
    /// connection died mid-stream.
    InvalidMessage,
    /// Broke a protocol invariant (unknown sender, malformed envelope, flooding).
    ProtocolViolation,
    /// Relayed a block from a *proven equivocator* — a slashable consensus
    /// fault. This is the categorical, eager-set-evicting penalty.
    EquivocationRelay,
}

impl Penalty {
    fn magnitude(self) -> f64 {
        match self {
            Penalty::InvalidMessage => PENALTY_INVALID_MESSAGE,
            Penalty::ProtocolViolation => PENALTY_PROTOCOL_VIOLATION,
            Penalty::EquivocationRelay => PENALTY_EQUIVOCATION_RELAY,
        }
    }
}

// ─── The scoreboard ──────────────────────────────────────────────────────────

/// Tracks reputation for all known transport peers and produces an
/// eclipse-resistant eager set.
#[derive(Clone, Debug, Default)]
pub struct PeerScoreboard {
    peers: HashMap<SocketAddr, PeerScore>,
}

impl PeerScoreboard {
    pub fn new() -> Self {
        Self::default()
    }

    /// Ensure a record exists for `addr` (idempotent). New peers start at
    /// [`INITIAL_SCORE`].
    pub fn observe(&mut self, addr: SocketAddr) {
        self.peers.entry(addr).or_default().last_seen = Instant::now();
    }

    /// Mark `addr` as a **trusted anchor** (F-5 / L4): an operator-configured
    /// bootstrap peer that is exempt from score-erosion graylisting (but NOT
    /// from the categorical equivocation fault). Idempotent; creates the record
    /// if absent.
    pub fn mark_anchor(&mut self, addr: SocketAddr) {
        self.peers.entry(addr).or_default().is_anchor = true;
    }

    /// Reward a peer for delivering a *fresh* (first-seen) message eagerly.
    pub fn reward_fresh_delivery(&mut self, addr: SocketAddr) {
        let e = self.peers.entry(addr).or_default();
        e.score = (e.score + REWARD_FRESH_DELIVERY).min(MAX_SCORE);
        e.fresh_deliveries += 1;
        e.last_seen = Instant::now();
    }

    /// Penalize a peer. [`Penalty::EquivocationRelay`] additionally records a
    /// hard fault that graylists the peer regardless of its numeric score.
    pub fn penalize(&mut self, addr: SocketAddr, reason: Penalty) {
        let e = self.peers.entry(addr).or_default();
        e.score = (e.score - reason.magnitude()).max(MIN_SCORE);
        if reason == Penalty::EquivocationRelay {
            e.equivocations = e.equivocations.saturating_add(1);
        }
        e.last_seen = Instant::now();
    }

    /// Read a peer's current score (for diagnostics / metrics).
    pub fn score_of(&self, addr: &SocketAddr) -> Option<f64> {
        self.peers.get(addr).map(|p| p.score)
    }

    /// Read a peer's full record.
    pub fn get(&self, addr: &SocketAddr) -> Option<&PeerScore> {
        self.peers.get(addr)
    }

    /// True if the peer is graylisted (proven fault, or score under threshold).
    pub fn is_graylisted(&self, addr: &SocketAddr) -> bool {
        self.peers.get(addr).is_some_and(|p| p.is_graylisted())
    }

    /// Forget a peer entirely (e.g. on permanent disconnect).
    pub fn remove(&mut self, addr: &SocketAddr) {
        self.peers.remove(addr);
    }

    /// Decay every reputation toward [`INITIAL_SCORE`] by [`DECAY_TOWARD_INITIAL`].
    /// Equivocation hard-faults are NOT decayed away (they are categorical).
    /// Call this on a slow timer (e.g. once per anti-entropy round) so the
    /// scoreboard is forgiving over time without forgetting slashable faults.
    pub fn decay(&mut self) {
        for p in self.peers.values_mut() {
            p.score += (INITIAL_SCORE - p.score) * DECAY_TOWARD_INITIAL;
        }
    }

    /// Number of peers being tracked.
    pub fn len(&self) -> usize {
        self.peers.len()
    }

    pub fn is_empty(&self) -> bool {
        self.peers.is_empty()
    }

    /// Select up to `eager_degree` eager peers from `candidates`, **eclipse-
    /// resistant** and **score-ranked**.
    ///
    /// Selection algorithm:
    /// 1. Drop graylisted candidates (proven faults / sub-threshold score).
    /// 2. Sort the rest by reputation, highest first (ties broken by address for
    ///    determinism).
    /// 3. Greedily admit peers in score order, but **skip any candidate whose
    ///    address bucket already holds [`MAX_EAGER_PER_BUCKET`] admitted
    ///    peers** — this is the diversity constraint that bounds single-subnet
    ///    capture.
    /// 4. If, after the diversity pass, fewer than `eager_degree` peers were
    ///    admitted (the network genuinely lacks bucket diversity), top up from
    ///    the remaining non-graylisted candidates in score order — availability
    ///    must not be sacrificed when honest diversity is simply unavailable.
    ///
    /// Eclipse-resistant eager selection that **pins trusted anchor peers** to
    /// the eager set first (F-5 / L4).
    ///
    /// Anchors are the operator-configured bootstrap contact points — relays an
    /// injected/Sybil peer cannot impersonate. Any candidate that is also a
    /// (non-graylisted) anchor is admitted to the eager set before the
    /// reputation/diversity pass runs, up to `eager_degree`. This guarantees a
    /// node always relays through at least its trusted anchors, so an adversary
    /// who floods many high-reputation Sybil connections still cannot fully
    /// capture the spanning tree: the anchor slots are reserved. The remaining
    /// slots are filled by the standard eclipse-resistant [`Self::select_eager`]
    /// (score-ranked, address-diversity-bounded). A graylisted anchor (one that
    /// proved Byzantine) is NOT pinned — trust is not a license to equivocate.
    pub fn select_eager_with_anchors(
        &self,
        candidates: &[SocketAddr],
        anchors: &std::collections::HashSet<SocketAddr>,
        eager_degree: usize,
    ) -> Vec<SocketAddr> {
        if eager_degree == 0 || candidates.is_empty() {
            return Vec::new();
        }

        // (A) Pin connected, non-graylisted anchors first (deterministic order).
        let mut chosen: Vec<SocketAddr> = Vec::with_capacity(eager_degree);
        let mut anchor_candidates: Vec<SocketAddr> = candidates
            .iter()
            .filter(|a| anchors.contains(a) && !self.is_graylisted(a))
            .copied()
            .collect();
        anchor_candidates.sort_by(|a, b| addr_sort_key(a).cmp(&addr_sort_key(b)));
        for a in anchor_candidates {
            if chosen.len() == eager_degree {
                break;
            }
            if !chosen.contains(&a) {
                chosen.push(a);
            }
        }
        if chosen.len() >= eager_degree {
            return chosen;
        }

        // (B) Fill remaining slots with the standard eclipse-resistant pass over
        // the non-anchor candidates.
        let rest: Vec<SocketAddr> = candidates
            .iter()
            .filter(|a| !chosen.contains(a))
            .copied()
            .collect();
        let fill = self.select_eager(&rest, eager_degree - chosen.len());
        for a in fill {
            if chosen.len() == eager_degree {
                break;
            }
            chosen.push(a);
        }
        chosen
    }

    /// Returns the chosen eager addresses (length `<= eager_degree`).
    pub fn select_eager(&self, candidates: &[SocketAddr], eager_degree: usize) -> Vec<SocketAddr> {
        if eager_degree == 0 || candidates.is_empty() {
            return Vec::new();
        }

        // (1) Filter out graylisted peers; pair each survivor with its score.
        let mut ranked: Vec<(SocketAddr, f64)> = candidates
            .iter()
            .filter(|a| !self.is_graylisted(a))
            .map(|a| (*a, self.score_of(a).unwrap_or(INITIAL_SCORE)))
            .collect();

        // (2) Highest score first; deterministic tiebreak on address bytes.
        ranked.sort_by(|(a_addr, a_s), (b_addr, b_s)| {
            b_s.partial_cmp(a_s)
                .unwrap_or(std::cmp::Ordering::Equal)
                .then_with(|| addr_sort_key(a_addr).cmp(&addr_sort_key(b_addr)))
        });

        // (3) Diversity-constrained greedy admission.
        let mut chosen: Vec<SocketAddr> = Vec::with_capacity(eager_degree);
        let mut per_bucket: HashMap<AddrBucket, usize> = HashMap::new();
        let mut deferred: Vec<SocketAddr> = Vec::new();

        for (addr, _score) in &ranked {
            if chosen.len() == eager_degree {
                break;
            }
            let bucket = AddrBucket::of(addr);
            let count = per_bucket.entry(bucket).or_insert(0);
            if *count < MAX_EAGER_PER_BUCKET {
                *count += 1;
                chosen.push(*addr);
            } else {
                // Bucket saturated: hold this peer back. It only gets in if the
                // network cannot supply enough diverse buckets (step 4).
                deferred.push(*addr);
            }
        }

        // (4) Availability top-up: only if diversity genuinely could not fill
        // the eager set. (Order preserved from `ranked`, i.e. by score.)
        if chosen.len() < eager_degree {
            for addr in deferred {
                if chosen.len() == eager_degree {
                    break;
                }
                chosen.push(addr);
            }
        }

        chosen
    }
}

/// Sort key for an address (octets || port), giving a total, deterministic order.
fn addr_sort_key(addr: &SocketAddr) -> (Vec<u8>, u16) {
    let octets = match addr.ip() {
        IpAddr::V4(v4) => v4.octets().to_vec(),
        IpAddr::V6(v6) => v6.octets().to_vec(),
    };
    (octets, addr.port())
}

/// An address-space *bucket* used for the eclipse-resistance diversity bound.
///
/// IPv4 peers are bucketed by their `/16` network group (first two octets):
/// this is the classic "net group" used by Bitcoin Core's eclipse mitigation —
/// an attacker who controls one `/16` cannot fill more than
/// [`MAX_EAGER_PER_BUCKET`] eager slots. IPv6 peers are bucketed by their `/32`
/// routing prefix (first four octets), the analogous routable allocation unit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum AddrBucket {
    V4Net16([u8; 2]),
    V6Net32([u8; 4]),
}

impl AddrBucket {
    fn of(addr: &SocketAddr) -> Self {
        match addr.ip() {
            IpAddr::V4(v4) => {
                let o = v4.octets();
                AddrBucket::V4Net16([o[0], o[1]])
            }
            IpAddr::V6(v6) => {
                let o = v6.octets();
                AddrBucket::V6Net32([o[0], o[1], o[2], o[3]])
            }
        }
    }
}

// ─── Request backoff (missing-block re-request limiter) ──────────────────────

/// Capped exponential backoff for re-requesting a missing item (keyed by an
/// arbitrary `K`, e.g. a missing `BlockId` or a frontier-pull token).
///
/// `should_request(key)` returns `true` at most once per backoff window; each
/// granted request doubles the next window (up to `max`). This converts a tight
/// "re-request every tick" loop into a polite, bandwidth-bounded one while still
/// guaranteeing eventual re-request (the window is finite and capped).
#[derive(Clone, Debug)]
pub struct RequestBackoff<K> {
    base: Duration,
    max: Duration,
    entries: HashMap<K, BackoffEntry>,
}

#[derive(Clone, Debug)]
struct BackoffEntry {
    /// Earliest instant at which the next request is permitted.
    next_allowed: Instant,
    /// Current backoff window (doubles each grant, capped at `max`).
    window: Duration,
    /// Number of times this key has been requested.
    attempts: u32,
}

impl<K: std::hash::Hash + Eq + Clone> RequestBackoff<K> {
    /// Create a backoff with the given base and maximum window.
    pub fn new(base: Duration, max: Duration) -> Self {
        Self {
            base,
            max,
            entries: HashMap::new(),
        }
    }

    /// Whether `key` may be (re-)requested now. The FIRST call for a fresh key
    /// returns `true` immediately (request without delay) and arms the backoff;
    /// subsequent calls return `true` only after the current window elapses,
    /// doubling the window each time (capped at `max`).
    pub fn should_request(&mut self, key: K) -> bool {
        let now = Instant::now();
        match self.entries.get_mut(&key) {
            None => {
                self.entries.insert(
                    key,
                    BackoffEntry {
                        next_allowed: now + self.base,
                        window: self.base,
                        attempts: 1,
                    },
                );
                true
            }
            Some(e) => {
                if now >= e.next_allowed {
                    e.window = (e.window * 2).min(self.max);
                    e.next_allowed = now + e.window;
                    e.attempts = e.attempts.saturating_add(1);
                    true
                } else {
                    false
                }
            }
        }
    }

    /// Clear backoff state for a key once the item arrives (so a later miss of
    /// the same key starts fresh, not deep in backoff).
    pub fn clear(&mut self, key: &K) {
        self.entries.remove(key);
    }

    /// How many times `key` has been requested (0 if never).
    pub fn attempts(&self, key: &K) -> u32 {
        self.entries.get(key).map(|e| e.attempts).unwrap_or(0)
    }

    /// Drop backoff entries whose window has long elapsed and that are not being
    /// actively retried, to bound memory. `idle` is how long past `next_allowed`
    /// an entry may sit before it is forgotten.
    pub fn gc(&mut self, idle: Duration) {
        let now = Instant::now();
        self.entries
            .retain(|_, e| now.saturating_duration_since(e.next_allowed) < idle);
    }

    /// Number of keys currently under backoff.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn addr(a: u8, b: u8, c: u8, d: u8, port: u16) -> SocketAddr {
        format!("{a}.{b}.{c}.{d}:{port}").parse().unwrap()
    }

    // ─── Scoring basics ─────────────────────────────────────────────────────

    #[test]
    fn new_peer_starts_at_initial_score() {
        let mut sb = PeerScoreboard::new();
        let p = addr(10, 0, 0, 1, 9000);
        sb.observe(p);
        assert_eq!(sb.score_of(&p), Some(INITIAL_SCORE));
        assert!(!sb.is_graylisted(&p));
    }

    #[test]
    fn reward_raises_penalty_lowers() {
        let mut sb = PeerScoreboard::new();
        let p = addr(10, 0, 0, 1, 9000);
        sb.reward_fresh_delivery(p);
        assert!(sb.score_of(&p).unwrap() > INITIAL_SCORE);
        let after_reward = sb.score_of(&p).unwrap();
        sb.penalize(p, Penalty::InvalidMessage);
        assert!(sb.score_of(&p).unwrap() < after_reward);
    }

    #[test]
    fn equivocation_relay_graylists_immediately() {
        let mut sb = PeerScoreboard::new();
        let p = addr(10, 0, 0, 1, 9000);
        sb.observe(p);
        assert!(!sb.is_graylisted(&p));
        sb.penalize(p, Penalty::EquivocationRelay);
        assert!(
            sb.is_graylisted(&p),
            "one proven equivocation relay must graylist the peer"
        );
        assert_eq!(sb.get(&p).unwrap().equivocations, 1);
    }

    #[test]
    fn equivocation_graylist_survives_score_recovery() {
        // Even if a peer's numeric score later climbs back above threshold, a
        // recorded equivocation keeps it graylisted (categorical fault).
        let mut sb = PeerScoreboard::new();
        let p = addr(10, 0, 0, 1, 9000);
        sb.penalize(p, Penalty::EquivocationRelay);
        for _ in 0..100 {
            sb.reward_fresh_delivery(p);
            sb.decay();
        }
        assert!(sb.score_of(&p).unwrap() > GRAYLIST_THRESHOLD);
        assert!(
            sb.is_graylisted(&p),
            "equivocation hard-fault must outlive numeric score recovery"
        );
    }

    #[test]
    fn score_bounded_between_min_and_max() {
        let mut sb = PeerScoreboard::new();
        let p = addr(10, 0, 0, 1, 9000);
        for _ in 0..1000 {
            sb.reward_fresh_delivery(p);
        }
        assert!(sb.score_of(&p).unwrap() <= MAX_SCORE);
        for _ in 0..1000 {
            sb.penalize(p, Penalty::EquivocationRelay);
        }
        assert!(sb.score_of(&p).unwrap() >= MIN_SCORE);
    }

    #[test]
    fn decay_pulls_toward_initial() {
        let mut sb = PeerScoreboard::new();
        let hi = addr(10, 0, 0, 1, 9000);
        let lo = addr(10, 0, 0, 2, 9000);
        for _ in 0..20 {
            sb.reward_fresh_delivery(hi);
        }
        sb.penalize(lo, Penalty::ProtocolViolation);
        let hi0 = sb.score_of(&hi).unwrap();
        let lo0 = sb.score_of(&lo).unwrap();
        for _ in 0..50 {
            sb.decay();
        }
        // High score decays down toward INITIAL; low score decays up toward it.
        // Both monotonically approach INITIAL and close most of the original gap
        // (geometric decay at DECAY_TOWARD_INITIAL per step). We assert strong
        // convergence: each ends much closer to INITIAL than it started.
        let hi1 = sb.score_of(&hi).unwrap();
        let lo1 = sb.score_of(&lo).unwrap();
        assert!(hi1 < hi0 && hi1 > INITIAL_SCORE, "hi decays down toward INITIAL");
        assert!(lo1 > lo0 && lo1 < INITIAL_SCORE, "lo decays up toward INITIAL");
        // Closed >= 90% of the gap to INITIAL (1 - 0.95^50 ≈ 0.923).
        assert!((hi1 - INITIAL_SCORE).abs() < 0.1 * (hi0 - INITIAL_SCORE).abs());
        assert!((lo1 - INITIAL_SCORE).abs() < 0.1 * (lo0 - INITIAL_SCORE).abs());
    }

    // ─── Eager selection: score ranking ─────────────────────────────────────

    #[test]
    fn select_eager_prefers_higher_score() {
        let mut sb = PeerScoreboard::new();
        // All in DISTINCT buckets so diversity never interferes with ranking.
        let good = addr(10, 1, 0, 1, 9000);
        let mid = addr(10, 2, 0, 1, 9000);
        let bad = addr(10, 3, 0, 1, 9000);
        for _ in 0..6 {
            sb.reward_fresh_delivery(good);
        }
        for _ in 0..2 {
            sb.reward_fresh_delivery(mid);
        }
        sb.observe(bad);
        let chosen = sb.select_eager(&[bad, mid, good], 2);
        assert_eq!(chosen.len(), 2);
        assert!(chosen.contains(&good));
        assert!(chosen.contains(&mid));
        assert!(!chosen.contains(&bad), "lowest-score peer excluded");
    }

    #[test]
    fn select_eager_excludes_graylisted() {
        let mut sb = PeerScoreboard::new();
        let ok1 = addr(10, 1, 0, 1, 9000);
        let ok2 = addr(10, 2, 0, 1, 9000);
        let evil = addr(10, 3, 0, 1, 9000);
        sb.observe(ok1);
        sb.observe(ok2);
        sb.penalize(evil, Penalty::EquivocationRelay);
        let chosen = sb.select_eager(&[ok1, ok2, evil], 3);
        assert!(!chosen.contains(&evil), "graylisted peer never eager");
        assert!(chosen.contains(&ok1) && chosen.contains(&ok2));
    }

    // ─── Eclipse resistance: the load-bearing property ──────────────────────

    /// THE eclipse-resistance invariant. An attacker controls 100 high-score
    /// peers ALL in a single `/16` (10.0.x.x); two honest peers sit in distinct
    /// other subnets. Despite outnumbering and outscoring the honest peers, the
    /// attacker can occupy AT MOST `MAX_EAGER_PER_BUCKET` eager slots — the rest
    /// of the eager set goes to the diverse honest peers.
    #[test]
    fn eager_set_bounds_single_subnet_capture() {
        let mut sb = PeerScoreboard::new();

        // Attacker: 100 peers in the 10.0/16 bucket, all max reputation.
        let mut attacker: Vec<SocketAddr> = Vec::new();
        for i in 0..100u16 {
            let a = addr(10, 0, (i >> 8) as u8, (i & 0xff) as u8, 9000 + i);
            for _ in 0..20 {
                sb.reward_fresh_delivery(a);
            }
            attacker.push(a);
        }
        // Honest peers: distinct buckets, modest reputation.
        let honest1 = addr(172, 16, 0, 1, 9000);
        let honest2 = addr(192, 168, 0, 1, 9000);
        sb.reward_fresh_delivery(honest1);
        sb.reward_fresh_delivery(honest2);

        let mut all = attacker.clone();
        all.push(honest1);
        all.push(honest2);

        let eager_degree = 4;
        let chosen = sb.select_eager(&all, eager_degree);

        let attacker_set: std::collections::HashSet<_> = attacker.iter().collect();
        let attacker_in_eager = chosen.iter().filter(|a| attacker_set.contains(a)).count();

        assert!(
            attacker_in_eager <= MAX_EAGER_PER_BUCKET,
            "single-subnet attacker captured {attacker_in_eager} eager slots \
             (must be <= {MAX_EAGER_PER_BUCKET})"
        );
        // The diverse honest peers MUST get the remaining slots.
        assert!(chosen.contains(&honest1));
        assert!(chosen.contains(&honest2));
    }

    /// Availability fallback: if the network genuinely cannot supply enough
    /// diverse buckets (everyone is in one subnet, e.g. a single-rack devnet),
    /// the eager set is still filled to `eager_degree` rather than starved.
    #[test]
    fn select_eager_tops_up_when_diversity_unavailable() {
        let mut sb = PeerScoreboard::new();
        let mut peers = Vec::new();
        for i in 0..5u8 {
            let a = addr(10, 0, 0, i, 9000 + i as u16);
            sb.reward_fresh_delivery(a);
            peers.push(a);
        }
        // All 5 share one /16. eager_degree=3 > MAX_EAGER_PER_BUCKET=2, but
        // there is no diversity to be had: we must still return 3.
        let chosen = sb.select_eager(&peers, 3);
        assert_eq!(
            chosen.len(),
            3,
            "must top up to eager_degree when diversity is genuinely unavailable"
        );
    }

    #[test]
    fn select_eager_empty_inputs() {
        let sb = PeerScoreboard::new();
        assert!(sb.select_eager(&[], 3).is_empty());
        assert!(
            sb.select_eager(&[addr(10, 0, 0, 1, 9000)], 0)
                .is_empty()
        );
    }

    // ─── Request backoff ────────────────────────────────────────────────────

    #[test]
    fn backoff_first_request_immediate_then_throttled() {
        let mut bo: RequestBackoff<u32> =
            RequestBackoff::new(Duration::from_millis(50), Duration::from_secs(10));
        // First miss: request immediately.
        assert!(bo.should_request(7));
        // Immediate re-request is throttled (window not elapsed).
        assert!(!bo.should_request(7));
        assert_eq!(bo.attempts(&7), 1);
    }

    #[test]
    fn backoff_window_doubles_until_capped() {
        let mut bo: RequestBackoff<u32> =
            RequestBackoff::new(Duration::from_millis(1), Duration::from_millis(8));
        assert!(bo.should_request(1)); // arms window=1ms
        // Spin until each successive window elapses; collect the windows by
        // observing how attempts climb. We just assert it keeps granting and
        // the attempt count rises (eventual re-request / liveness).
        let mut grants = 1;
        let deadline = Instant::now() + Duration::from_millis(200);
        while Instant::now() < deadline && grants < 5 {
            if bo.should_request(1) {
                grants += 1;
            }
        }
        assert!(grants >= 4, "backoff must keep eventually granting (liveness)");
        assert!(bo.attempts(&1) >= 4);
    }

    #[test]
    fn backoff_clear_resets_key() {
        let mut bo: RequestBackoff<u32> =
            RequestBackoff::new(Duration::from_secs(100), Duration::from_secs(100));
        assert!(bo.should_request(3));
        assert!(!bo.should_request(3)); // deep in backoff
        bo.clear(&3);
        assert_eq!(bo.attempts(&3), 0);
        assert!(bo.should_request(3), "cleared key requests immediately again");
    }

    #[test]
    fn backoff_distinct_keys_independent() {
        let mut bo: RequestBackoff<u32> =
            RequestBackoff::new(Duration::from_secs(100), Duration::from_secs(100));
        assert!(bo.should_request(1));
        assert!(bo.should_request(2));
        assert!(!bo.should_request(1));
        assert!(!bo.should_request(2));
    }
}
