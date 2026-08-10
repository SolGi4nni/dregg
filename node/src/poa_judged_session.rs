//! The judged-session TRANSPORT, with no game in it.
//!
//! # Substrate
//!
//! ⚠ **Nothing in this file judges anything.** Every rule that decides a move's
//! meaning — what a legal move is, what the feedback means, when a run is solved,
//! how many rounds it gets — is authored in Lean under
//! `metatheory/Dregg2/Games/PathOfAngels/`, reached through an `@[export]`, and
//! called by a game's own adapter. This module carries bytes to that call and a
//! verdict back. It holds no constraint, no gadget, and no `air_accepts`.
//!
//! The one place that boundary is *not* clean is [`RestatedRules`], and it is named
//! rather than hidden. Read it before trusting the seam.
//!
//! # Why this file exists
//!
//! Seven games sit on the rack (`poa-web/src/game-rack.js`). All seven have a Lean
//! judge — `judge` / `step` / `replay` in `SignalTriangulation.lean`,
//! `RelayRepair.lean`, `SalvageLock.lean`, `BlackBoxReconstruction.lean`,
//! `ArtificerLogic.lean`, `VentCrawl.lean`, `DeckDescent.lean`. **One** has node
//! transport. The others can be played in the browser in PRACTICE and settle nothing.
//!
//! ⚠ And practice is not a second implementation of the rules — the browser runtimes
//! are descriptor-driven renderers. `ventcrawl-runtime.js` says it outright: *"this
//! file derives NO odds and NO payout. It reads them."* It rolls its own rung draws
//! locally, off tables the signed descriptor published. That matters here because it
//! is why [`RestatedRules`] has a cheap fix: the descriptor is already the carrier of
//! each game's Lean-authored parameters, and the browser already reads it.
//!
//! ⚠ And "has a judge" is not "has transport", which the tree now demonstrates
//! rather than merely asserting. Vent Crawl reached the judge boundary on
//! 2026-08-09 — `GameConfigWire` is a sum, `ActionsWire` carries a per-game tag, and
//! `@[export dregg_poa_signal_judge]` scores a real Vent Crawl transcript. That
//! commit's own closing section is the point of this file: *"there is no Vent Crawl
//! claim carrier in the SDK, no vent session, no mid-run oracle, and no HTTP route.
//! A Vent Crawl run cannot be played against a live node yet."* The judge
//! generalized IN PLACE, in Lean, and the transport did not move at all.
//!
//! The obvious way to fix that is to write Signal's path six more times. Measured
//! against `poa_signal_session.rs`, that would copy ~287 lines of machinery that
//! mentions no game, six times, and the copies would agree on the day they were
//! written and drift afterwards. So the machinery moves DOWN here instead, and the
//! game-shaped part stays up in the game's own module where it is honest.
//!
//! # What is generic, and why each piece is
//!
//! | piece | why no game changes it |
//! |---|---|
//! | [`SessionAdmission`] | three budgets over IP, player key and concurrency. None reads a move |
//! | [`PlayerKeyBudget`] | a fixed window over 32 bytes of public key |
//! | [`SessionRefusal`] | a status, a stable machine token, a human detail |
//! | [`parse_hex32`] | 64 lowercase hex, refused otherwise |
//! | [`verify_player_signature`] | Ed25519 over a message the CALLER re-derived |
//!
//! # What is NOT here, deliberately
//!
//! * **The move type.** `SignalCodeWireV1` is three base-six bands; Vent Crawl's is
//!   not, and no amount of generics makes them one type worth having.
//! * **The feedback type.** LOCKED/DRIFT is Signal's mechanic.
//! * **The terminal condition.** `exact == 3` is Signal's, and it lives in
//!   `poa_signal_adapter::SessionClassification::solved`.
//! * **The oracle call.** Each game calls its own `@[export]`.
//! * **The store**, and this is the one that will actually stop game two. Measured
//!   in `persist/src/`: the session key is `authority_id || slot_be64 || player_key`
//!   (72 bytes) and the slot key is `authority_id || slot_be64` (40 bytes).
//!   **Neither carries a game.** The tables are `poa_signal_session_v1`,
//!   `poa_signal_slot_v1`, `poa_signal_open_slot_v1`.
//!
//!   So one authority has exactly ONE open slot across all games, and two games
//!   cannot hold a session for the same player at the same slot number without
//!   colliding on the key. The sideways fix — copy the tables per game — is the
//!   thing this file exists to refuse. The fix that moves it down is a game field in
//!   the key and one table set, which costs a re-genesis. `PersistentStore`'s
//!   re-genesis gate and the canonical schema epoch exist for exactly that, and the
//!   devnet is wiped whenever convenient. It is NOT done here — this module owns no
//!   storage — and it is named so the next lane does not discover it mid-mount.
//!
//! A game is therefore: a descriptor here, a move type, a statement encoder, an
//! oracle call, and a store. It is not a second copy of the admission ladder.

use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::{Duration, Instant};

use axum::Json;
use axum::http::{HeaderMap, StatusCode};
use ed25519_dalek::{Signature, Verifier, VerifyingKey};
use serde::Serialize;
use tokio::sync::{Mutex, OwnedSemaphorePermit, Semaphore};

use crate::api::RateLimiter;

/// Per-IP write budget (`open` + `guess`), proxy-aware. Not any game's budget — a
/// game's budget is durable and lives in its store. This is the ceiling on how fast
/// one network origin may make this node do Ed25519 work.
pub(crate) const SESSION_REQUESTS_PER_MINUTE: u32 = 60;

/// Per-IP read budget for a transcript read-back. Higher than the write budget
/// because a read classifies nothing and spends nothing — but not unbounded, because
/// these surfaces are anonymous and a read does open the store.
pub(crate) const SESSION_READS_PER_MINUTE: u32 = 180;

/// ⚑ Per-PLAYER-KEY write budget, charged only once a signature has verified.
///
/// A whole judged run is `1 + <the game's round budget>` writes. Twelve per minute
/// admits two complete five-round runs — far above any human hand and far below what
/// automation would want.
///
/// ⚠ This is the one generic constant with a game-shaped obligation attached: it must
/// exceed `1 + max_rounds` for every game mounted on this transport, or the budget
/// meant to protect a player refuses them mid-run.
/// [`RestatedRules::admits_a_whole_run`] is that obligation, discharged per game.
pub(crate) const SESSION_WRITES_PER_PLAYER_PER_MINUTE: u32 = 12;

/// Concurrent session requests in flight across the whole surface, all games.
pub(crate) const SESSION_MAX_IN_FLIGHT: usize = 32;

/// Prune the per-key window map once it exceeds this many live keys.
const PLAYER_BUDGET_PRUNE_AT: usize = 4096;

/// ⚠ **THE RULES THIS HOST RESTATES, AND THE REASON IT HAS TO.**
///
/// A judged session needs three numbers the Lean judge already knows and **does not
/// send**: how many rounds a run gets, and — for the host's own sanity check on a
/// reply — the bounds of the feedback. Signal's oracle reply wire is
/// `{format, exact, present}` (`poa_signal_adapter::classify_session_guess`). It
/// carries no budget, no `solved`, and no `open`. So the host restates them.
///
/// Before this record existed, Signal restated them in **four** places and no gate
/// compared any pair:
///
/// | value | Lean source | Rust copies at 2026-08-09 |
/// |---|---|---|
/// | round budget `5` | `SignalTriangulation.MAX_TURNS` | `dregg_persist::POA_SIGNAL_SESSION_MAX_ROUNDS`, `dregg_sdk::poa_signal::SIGNAL_MAX_TRANSCRIPT_ROUNDS` |
/// | feedback bound `3` | `SignalTriangulation.feedback_match_bound` | `poa_signal_adapter::classify_session_guess` |
/// | solved `exact == 3` | `SignalTriangulation.accepted_solved_iff_target` | `poa_signal_adapter::SessionClassification::solved` |
///
/// ⚑ **And the test named for that obligation could not go red.**
/// `poa_signal_session::tests::the_session_budget_is_the_rules_budget` reads, whole:
/// `assert_eq!(POA_SIGNAL_SESSION_MAX_ROUNDS, 5)` — a literal against a literal. It
/// does not compare the two Rust copies to each other and it cannot see Lean. The
/// docblock on `dregg_persist::POA_SIGNAL_SESSION_MAX_ROUNDS` meanwhile asserts that
/// *"the node's session module asserts the pair on every guess it records"*. **No
/// such assertion exists anywhere in the tree.**
///
/// # What this record does and does not fix
///
/// It does **not** close the restatement. A number typed in Rust is a rule in Rust
/// whatever struct holds it, and moving it here does not make Lean the authority.
///
/// What it does:
///
/// 1. **One site per game** instead of four, so a reader checks one thing.
/// 2. **The Lean source is a required field**, so a copy cannot exist without naming
///    what it is a copy of.
/// 3. **A gate that can actually go red** — [`RestatedRules::agrees_with`] compares
///    the copies that do exist, which is strictly more than the zero comparisons
///    there were.
///
/// # ⚑ What would actually close it — and it is SMALL, because Lean already emits it
///
/// Measured 2026-08-09, not assumed. **Every one of the seven games on the rack
/// already emits its round budget from its own Lean constant into the signed
/// descriptor**, via `action_limit`:
///
/// | game | Lean constant | emitter |
/// |---|---|---|
/// | signal-triangulation | `SignalTriangulation.MAX_TURNS` | `Emit.lean` |
/// | relay-repair | `RelayRepair.MAX_TURNS` | `Emit.lean` |
/// | salvage-lock | `SalvageLock.MAX_TURNS` | `Emit.lean` |
/// | black-box-reconstruction | `BlackBoxReconstruction.MAX_TURNS` | `Emit.lean` |
/// | vent-crawl | `VentCrawl.ACTION_LIMIT` | `VentCrawlEmit.lean` |
/// | deck-descent | `DeckDescent.AIR` | `DeckDescentEmit.lean` |
/// | artificer-logic | `ArtificerLogic.ACTION_LIMIT` | `ArtificerLogicEmit.lean` |
///
/// And the value is already CONSUMED by two independent readers: the browser
/// (`poa-web/src/mission-catalog.js`, `ventcrawl-runtime.js`, `blackbox-runtime.js`)
/// and the curator, which cross-checks descriptor against mission
/// (`poa-curator/src/lib.rs`, the `action_limit` comparison).
///
/// ⚠ **The node is the only consumer that restates it.** `grep action_limit` over
/// `node/`, `persist/` and `sdk/` returns nothing. The fix is therefore not a Lean
/// redesign and not a new wire — it is: **read `action_limit` off the signed
/// descriptor this node already loads, and delete the Rust constants.** A drift then
/// becomes a descriptor mismatch at load rather than a disagreement a player
/// discovers after paying a turn fee.
///
/// # What the drift costs today, at the right resolution
///
/// Not a silently-settled over-long run. `NetworkJudgeWire.parseRequest` refuses a
/// transcript longer than `GameTag.actionLimit` (and
/// `NetworkJudgeWire.the_per_game_bounds_are_distinct` proves Signal's and Vent
/// Crawl's limits are not the same number, so the shared outer fuse
/// `WIRE_ACTION_LIMIT` is not quietly granting Signal a sixth round), so Lean is the
/// backstop. The harm is the one the store's own
/// docblock names: a run the host admitted and the judge then refuses — **the player
/// pays the turn fee and the settle fails**, reading as a broken judge.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RestatedRules {
    /// The number of rounds one judged run gets.
    pub max_rounds: usize,
    /// The exact Lean name `max_rounds` is a copy of. Required: a restatement that
    /// does not name its source is indistinguishable from an invention.
    pub max_rounds_lean_source: &'static str,
}

impl RestatedRules {
    /// The obligation attached to [`SESSION_WRITES_PER_PLAYER_PER_MINUTE`]: the
    /// per-key allowance must fit a whole run **plus a resume**, or a player who
    /// loses one response is locked out of a run they already paid bursts into.
    pub const fn admits_a_whole_run(self) -> bool {
        (SESSION_WRITES_PER_PLAYER_PER_MINUTE as usize) > 1 + self.max_rounds
    }

    /// ⚠ The gate that can go red. Compare this descriptor's budget against another
    /// Rust copy of the same Lean constant.
    ///
    /// This is a Rust-to-Rust comparison and it is honest about that: it detects two
    /// copies drifting apart, which is what actually happens during a refactor. It
    /// cannot detect both copies drifting away from Lean together. Only the reply
    /// wire carrying the budget closes that, and it is not closed.
    pub const fn agrees_with(self, other_rust_copy: usize) -> bool {
        self.max_rounds == other_rust_copy
    }
}

/// One game's judged-session transport identity.
///
/// ⚠ **Keyed by `game_id`, and that key is the rack's key** — the same string
/// `poa-web/src/game-rack.js` and `mission-launcher.js`'s dispatch table key by
/// (`"signal-triangulation"`, `"vent-crawl"`, …). One identity for a game across the
/// browser, the launcher and the node, rather than three spellings that agree today.
///
/// A descriptor is a frozen record. It is not a place to put behaviour: the moment
/// a field here would need to be a function of a move, it belongs in the game's own
/// module.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JudgedGameDescriptor {
    /// The rack's key. See above — this must match `game-rack.js` exactly.
    pub game_id: &'static str,
    /// Route prefix, e.g. `/api/poa/signal`. The transport appends
    /// `/{authority}/session/...`; it does not invent the prefix.
    pub route_prefix: &'static str,
    /// Format tag of the served session document.
    pub session_format: &'static str,
    /// Schema of the statement a player signs to open a session.
    pub open_statement_schema: &'static str,
    /// Schema of the statement a player signs to spend one round.
    pub guess_statement_schema: &'static str,
    /// ⚠ See [`RestatedRules`]. Read it before adding a second game here.
    pub rules: RestatedRules,
}

/// A named refusal. `reason` is a stable machine token; `detail` is for a human.
///
/// ⚠ Every game's refusals share this shape so a client does not learn a new refusal
/// grammar per game. What a game may NOT share is the token vocabulary for its own
/// rules — a band bound is Signal's, and it names itself.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct JudgedSessionRefusalBodyV1 {
    pub reason: &'static str,
    pub detail: String,
}

#[derive(Debug)]
pub struct SessionRefusal {
    status: StatusCode,
    reason: &'static str,
    detail: String,
}

impl SessionRefusal {
    pub fn new(status: StatusCode, reason: &'static str, detail: impl Into<String>) -> Self {
        Self {
            status,
            reason,
            detail: detail.into(),
        }
    }

    /// The stable machine token. Public because a refusal's TOKEN is the contract a
    /// client codes against, and a game's own tests must be able to assert that its
    /// route refused for the reason it claims — `session-signature` and
    /// `session-player-rate-limit` are different facts about who was locked out.
    pub fn reason(&self) -> &'static str {
        self.reason
    }

    /// The HTTP status. Public for the same reason as [`Self::reason`].
    pub fn status(&self) -> StatusCode {
        self.status
    }

    pub fn into_response(self) -> (StatusCode, Json<JudgedSessionRefusalBodyV1>) {
        (
            self.status,
            Json(JudgedSessionRefusalBodyV1 {
                reason: self.reason,
                detail: self.detail,
            }),
        )
    }
}

pub type SessionResult<T> = Result<T, (StatusCode, Json<JudgedSessionRefusalBodyV1>)>;

/// A fixed-window request budget keyed by the **player key**, charged only once a
/// signature has proved possession of that key.
///
/// ⚑ THE ORDERING IS THE WHOLE DESIGN. A per-key budget charged BEFORE verification
/// is a griefing primitive, not a defence: anyone could name a victim's public key —
/// they are public on chain — send garbage, and lock that player out of their own
/// run. So [`SessionAdmission::charge_player`] runs after
/// [`verify_player_signature`], and the only caller who can move a counter in this
/// map is the holder of the corresponding secret.
///
/// That also settles the memory question this map would otherwise raise on an
/// anonymous surface: an attacker cannot grow it at all without holding secret keys,
/// so [`PLAYER_BUDGET_PRUNE_AT`] is a generous housekeeping bound rather than a
/// defence.
#[derive(Clone)]
pub struct PlayerKeyBudget {
    state: Arc<Mutex<HashMap<[u8; 32], (u32, Instant)>>>,
    max_requests: u32,
    window: Duration,
}

impl PlayerKeyBudget {
    pub fn new(max_requests: u32, window_secs: u64) -> Self {
        Self {
            state: Arc::new(Mutex::new(HashMap::new())),
            max_requests,
            window: Duration::from_secs(window_secs),
        }
    }

    /// `true` if this key may proceed. Fixed window, same shape as
    /// `api::RateLimiter`.
    pub async fn charge(&self, player_key: [u8; 32]) -> bool {
        let mut map = self.state.lock().await;
        let now = Instant::now();
        if map.len() > PLAYER_BUDGET_PRUNE_AT {
            let window = self.window;
            map.retain(|_, (_, started)| now.duration_since(*started) < window);
        }
        let entry = map.entry(player_key).or_insert((0, now));
        if now.duration_since(entry.1) >= self.window {
            *entry = (0, now);
        }
        entry.0 += 1;
        entry.0 <= self.max_requests
    }
}

/// ⚑ THE ABUSE BUDGET THAT REPLACES A BEARER TOKEN ON A PLAYER-FACING SURFACE.
///
/// A judged-session route cannot require an operator secret — a player holds none —
/// so the bearer that incidentally made abuse require a credential is gone. It is
/// replaced here, explicitly, with three budgets that bind different resources:
///
/// | budget | keyed on | what it bounds |
/// |---|---|---|
/// | [`SESSION_REQUESTS_PER_MINUTE`] | client IP (proxy-aware) | how fast one network origin can make this node verify Ed25519 |
/// | [`SESSION_WRITES_PER_PLAYER_PER_MINUTE`] | player key, POST-verification | how fast one identity can drive the store, regardless of how many IPs it has |
/// | [`SESSION_MAX_IN_FLIGHT`] | nothing — global | how much work can be held open at once, regardless of windows |
///
/// The per-IP one alone is not enough (one identity behind many addresses walks past
/// it); the per-key one alone is not enough (an unsigned flood never reaches it); and
/// neither bounds concurrency, which is what a slow-loris flood actually consumes.
/// Hence three, and hence in this order:
///
/// 1. **concurrency permit** — refused as `session-busy`, before any parsing,
/// 2. **per-IP window** — refused as `session-rate-limit`, before any crypto,
/// 3. **signature verification** — `session-signature`,
/// 4. **per-key window** — refused as `session-player-rate-limit`, and ONLY here,
///    because a key's budget must not be spendable by someone who cannot sign for it.
///
/// A read-back takes 1 and 2 with a larger window ([`SESSION_READS_PER_MINUTE`]) and
/// deliberately NOT 4: charging a read against the named player's key would hand
/// anyone who knows a public key a way to exhaust that player's allowance, which is
/// the exact griefing this ordering exists to refuse.
///
/// ⚠ None of the four steps reads a move. That is why this ladder is here and not in
/// a game's module, and why a second game inherits it rather than re-deriving it.
#[derive(Clone)]
pub struct SessionAdmission {
    per_ip_writes: RateLimiter,
    per_ip_reads: RateLimiter,
    per_player_writes: PlayerKeyBudget,
    in_flight: Arc<Semaphore>,
}

impl Default for SessionAdmission {
    fn default() -> Self {
        Self::new()
    }
}

impl SessionAdmission {
    pub fn new() -> Self {
        Self {
            per_ip_writes: RateLimiter::new(SESSION_REQUESTS_PER_MINUTE, 60),
            per_ip_reads: RateLimiter::new(SESSION_READS_PER_MINUTE, 60),
            per_player_writes: PlayerKeyBudget::new(SESSION_WRITES_PER_PLAYER_PER_MINUTE, 60),
            in_flight: Arc::new(Semaphore::new(SESSION_MAX_IN_FLIGHT)),
        }
    }

    /// Step 1. Held for the life of the request; dropping the permit returns it.
    pub fn enter(&self) -> Result<OwnedSemaphorePermit, SessionRefusal> {
        self.in_flight.clone().try_acquire_owned().map_err(|_| {
            SessionRefusal::new(
                StatusCode::SERVICE_UNAVAILABLE,
                "session-busy",
                format!(
                    "this node is already serving {SESSION_MAX_IN_FLIGHT} judged session requests; \
                     nothing was spent, retry"
                ),
            )
        })
    }

    /// Step 2, write side.
    pub async fn admit_write(
        &self,
        addr: SocketAddr,
        headers: &HeaderMap,
    ) -> Result<(), SessionRefusal> {
        if self.per_ip_writes.check_request(addr.ip(), headers).await {
            return Ok(());
        }
        Err(SessionRefusal::new(
            StatusCode::TOO_MANY_REQUESTS,
            "session-rate-limit",
            format!(
                "more than {SESSION_REQUESTS_PER_MINUTE} judged session writes from this address in \
                 one minute. No round was spent — a whole run is a handful of writes"
            ),
        ))
    }

    /// Step 2, read side.
    pub async fn admit_read(
        &self,
        addr: SocketAddr,
        headers: &HeaderMap,
    ) -> Result<(), SessionRefusal> {
        if self.per_ip_reads.check_request(addr.ip(), headers).await {
            return Ok(());
        }
        Err(SessionRefusal::new(
            StatusCode::TOO_MANY_REQUESTS,
            "session-rate-limit",
            format!(
                "more than {SESSION_READS_PER_MINUTE} judged session reads from this address in one \
                 minute. A read spends nothing; slow down"
            ),
        ))
    }

    /// Step 4. ⚠ Call this only after [`verify_player_signature`] has returned `Ok`.
    pub async fn charge_player(&self, player_key: [u8; 32]) -> Result<(), SessionRefusal> {
        if self.per_player_writes.charge(player_key).await {
            return Ok(());
        }
        Err(SessionRefusal::new(
            StatusCode::TOO_MANY_REQUESTS,
            "session-player-rate-limit",
            format!(
                "this player key has made more than {SESSION_WRITES_PER_PLAYER_PER_MINUTE} judged \
                 session writes in one minute, and a whole run is a handful. No round was spent. \
                 This budget is charged only against a signature that verified, so nobody else can \
                 exhaust it for you"
            ),
        ))
    }
}

/// Parse exactly 64 lowercase hex digits.
///
/// ⚠ Case-sensitive on purpose. An uppercase spelling of the same bytes is a second
/// spelling of a key, and a surface that accepts both has two names for one player.
pub fn parse_hex32(what: &'static str, value: &str) -> Result<[u8; 32], SessionRefusal> {
    if value.len() != 64
        || !value.bytes().all(|b| b.is_ascii_hexdigit())
        || value != value.to_ascii_lowercase()
    {
        return Err(SessionRefusal::new(
            StatusCode::BAD_REQUEST,
            "session-malformed-key",
            format!("{what} must be exactly 64 lowercase hexadecimal digits"),
        ));
    }
    let mut out = [0u8; 32];
    for (index, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16).map_err(|_| {
            SessionRefusal::new(
                StatusCode::BAD_REQUEST,
                "session-malformed-key",
                format!("{what} is not hexadecimal"),
            )
        })?;
    }
    Ok(out)
}

/// Verify possession of the player key over exactly `message`.
///
/// ⚠ **`message` must be RE-DERIVED by the caller from the structured request
/// fields.** It is never accepted pre-encoded, and this function takes bytes rather
/// than a request precisely so that the re-derivation is visible at every call site.
/// A route that verified a caller-supplied message would report "player-signed" for a
/// statement the caller never made — the same trap `poa_signal_slot_api` refuses to
/// walk into by not serving its signing bytes.
///
/// This is the ONLY authorization a judged session write has. It is not layered on a
/// bearer: a bearer says "a client of this node", never "this player".
pub fn verify_player_signature(
    player_key: [u8; 32],
    signature_hex: &str,
    message: &[u8],
) -> Result<(), SessionRefusal> {
    let bad = |detail: &str| {
        SessionRefusal::new(
            StatusCode::UNAUTHORIZED,
            "session-signature",
            format!(
                "{detail}. A judged session spends a per-player budget against a live slot \
                 secret, so it requires proof of possession of the player key"
            ),
        )
    };
    if signature_hex.len() != 128 || !signature_hex.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(bad(
            "the signature must be exactly 128 lowercase hexadecimal digits",
        ));
    }
    let mut raw = [0u8; 64];
    for (index, byte) in raw.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&signature_hex[index * 2..index * 2 + 2], 16)
            .map_err(|_| bad("the signature is not hexadecimal"))?;
    }
    let key =
        VerifyingKey::from_bytes(&player_key).map_err(|_| bad("the player key is not on-curve"))?;
    key.verify(message, &Signature::from_bytes(&raw))
        .map_err(|_| bad("the signature does not verify against the re-derived statement"))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The descriptor under test is Signal's, because Signal is the only game with
    /// transport. When a second one lands, add it to this array — the obligations
    /// below are then discharged for both, which is the point of the seam.
    fn mounted() -> Vec<JudgedGameDescriptor> {
        vec![crate::poa_signal_session::SIGNAL_JUDGED_GAME]
    }

    /// ⚑ THE GATE THAT REPLACES A LITERAL-AGAINST-A-LITERAL.
    ///
    /// `poa_signal_session::tests::the_session_budget_is_the_rules_budget` asserted
    /// `POA_SIGNAL_SESSION_MAX_ROUNDS == 5`. Both sides were constants in the same
    /// crate graph and the right-hand one was typed by hand, so the test could not go
    /// red for the drift it was named after: change the store's budget and re-type
    /// the `5`, and it stays green.
    ///
    /// This compares the two INDEPENDENT Rust copies of `SignalTriangulation.
    /// MAX_TURNS` — the store's and the SDK's — against the descriptor. They are
    /// reached through different crates and a refactor moves one without the other.
    ///
    /// ⚠ Honest reach: three Rust copies agreeing is not Lean agreeing with any of
    /// them. See [`RestatedRules`] for what would close that and why it is Lean work.
    #[test]
    fn every_mounted_game_agrees_with_its_other_rust_copies() {
        for game in mounted() {
            assert!(
                game.rules
                    .agrees_with(dregg_persist::POA_SIGNAL_SESSION_MAX_ROUNDS),
                "{}: the descriptor's round budget ({}) and the STORE's \
                 ({}) disagree. One of them was moved without the other, and the \
                 store is what a player's durable run is bounded by",
                game.game_id,
                game.rules.max_rounds,
                dregg_persist::POA_SIGNAL_SESSION_MAX_ROUNDS,
            );
            assert!(
                game.rules
                    .agrees_with(dregg_sdk::poa_signal::SIGNAL_MAX_TRANSCRIPT_ROUNDS),
                "{}: the descriptor's round budget ({}) and the SDK CARRIER's \
                 ({}) disagree. A transcript the store admits that the carrier cannot \
                 hold is a run a player pays for and cannot settle",
                game.game_id,
                game.rules.max_rounds,
                dregg_sdk::poa_signal::SIGNAL_MAX_TRANSCRIPT_ROUNDS,
            );
        }
    }

    /// The gate can go red: a descriptor with a drifted budget must fail the
    /// comparison. Without this the assertion above could be vacuously true for a
    /// reason nobody checked (an `agrees_with` that returned `true` unconditionally
    /// would pass every case above and be invisible).
    #[test]
    fn the_agreement_gate_actually_refuses_a_disagreement() {
        let honest = crate::poa_signal_session::SIGNAL_JUDGED_GAME.rules;
        assert!(honest.agrees_with(honest.max_rounds));
        assert!(
            !honest.agrees_with(honest.max_rounds + 1),
            "agrees_with accepts a budget that differs; it is not comparing anything"
        );
    }

    /// Every restatement names the Lean definition it is a copy of. A number with no
    /// source is indistinguishable from a number someone chose.
    #[test]
    fn every_restated_rule_names_its_lean_source() {
        for game in mounted() {
            let source = game.rules.max_rounds_lean_source;
            assert!(
                source.contains('.'),
                "{}: {source:?} is not a Lean qualified name",
                game.game_id
            );
            assert!(
                !source.is_empty() && source.len() > 8,
                "{}: the round budget names no Lean source",
                game.game_id
            );
        }
    }

    /// The obligation attached to the shared per-key allowance, discharged for every
    /// game rather than restated per game.
    ///
    /// A per-key budget that cannot fit one run plus a resume refuses honest play: a
    /// player who lost a response and re-opened would be locked out mid-game by the
    /// very budget meant to protect them.
    #[test]
    fn the_shared_allowance_admits_every_mounted_games_whole_run() {
        for game in mounted() {
            assert!(
                game.rules.admits_a_whole_run(),
                "{}: a run is 1 + {} writes and the shared per-key allowance is \
                 {SESSION_WRITES_PER_PLAYER_PER_MINUTE}. Mounting this game would refuse its own \
                 players mid-run",
                game.game_id,
                game.rules.max_rounds,
            );
        }
    }

    /// And it is not so loose as to be decorative: it must be under what the shared
    /// per-IP window already permits, or it bounds nothing the per-IP one did not. Two
    /// constants, so this is a build obligation and is discharged as one.
    const _: () = assert!(
        SESSION_WRITES_PER_PLAYER_PER_MINUTE < SESSION_REQUESTS_PER_MINUTE,
        "a per-key budget at or above the per-IP window bounds nothing the per-IP one did not"
    );

    /// ⚑ ONE KEY'S BUDGET IS ONE KEY'S. Exhausting one leaves every other untouched —
    /// the same separation `budgets_do_not_cross_players` asserts for the durable game
    /// budget, now for the rate budget, because a shared counter would be a way to
    /// grief every player at once.
    #[tokio::test]
    async fn a_player_key_budget_is_exhausted_alone() {
        let budget = PlayerKeyBudget::new(3, 60);
        let mine = [0x11u8; 32];
        let yours = [0x22u8; 32];
        for attempt in 1..=3 {
            assert!(
                budget.charge(mine).await,
                "charge {attempt} must be admitted"
            );
        }
        assert!(
            !budget.charge(mine).await,
            "the fourth charge against a budget of three must be refused"
        );
        assert!(
            budget.charge(yours).await,
            "another key's budget must be untouched by mine"
        );
    }

    /// A fresh window admits again. The budget is a rate, not a lifetime cap — the
    /// lifetime cap is the game's round budget and it is durable.
    #[tokio::test]
    async fn a_player_key_budget_is_a_window_not_a_lifetime() {
        let budget = PlayerKeyBudget::new(1, 60);
        let key = [0x33u8; 32];
        assert!(budget.charge(key).await);
        assert!(!budget.charge(key).await);
        // Reach in and age the window rather than sleeping a minute in a unit test.
        {
            let mut map = budget.state.lock().await;
            let entry = map.get_mut(&key).expect("the key was charged");
            entry.1 = Instant::now() - Duration::from_secs(61);
        }
        assert!(
            budget.charge(key).await,
            "a new window must admit the same key again"
        );
    }

    /// The in-flight ceiling refuses BY NAME rather than queueing, and the permit is
    /// returned when it drops — a ceiling that leaked permits would wedge the surface
    /// closed after `SESSION_MAX_IN_FLIGHT` requests, forever.
    // ⚠ `#[tokio::test]`, not `#[test]`: `SessionAdmission::new` builds two
    // `RateLimiter`s and each spawns its own prune task, so constructing one
    // outside a runtime panics with "there is no reactor running".
    #[tokio::test]
    async fn the_in_flight_ceiling_refuses_by_name_and_returns_its_permits() {
        let admission = SessionAdmission::new();
        let held: Vec<_> = (0..SESSION_MAX_IN_FLIGHT)
            .map(|index| {
                admission
                    .enter()
                    .unwrap_or_else(|_| panic!("permit {index} must be available"))
            })
            .collect();
        let refusal = admission
            .enter()
            .expect_err("the ceiling must refuse rather than queue");
        assert_eq!(refusal.reason, "session-busy");
        assert_eq!(refusal.status, StatusCode::SERVICE_UNAVAILABLE);
        drop(held);
        let _returned = admission
            .enter()
            .expect("permits must come back when the requests holding them finish");
    }

    /// ⚠ THE KEY IS THE RACK'S KEY. A descriptor whose `game_id` is not a game the
    /// browser rack knows is a game no player can reach, and — worse — a second
    /// spelling of one they can.
    ///
    /// `game-rack.js` is read as BYTES rather than reimplemented, so a rack edit that
    /// drops or renames a game breaks this test rather than silently orphaning a
    /// transport.
    #[test]
    fn every_descriptor_key_is_a_key_the_browser_rack_knows() {
        const RACK: &str = include_str!("../../poa-web/src/game-rack.js");
        // The scan reads real bytes: a rack that moved or emptied must fail here
        // rather than pass over nothing.
        assert!(
            RACK.contains("GAME_RACK") && RACK.len() > 1_000,
            "game-rack.js is not the rack; this gate is scanning the wrong file"
        );
        for game in mounted() {
            assert!(
                RACK.contains(&format!("gameId: \"{}\"", game.game_id)),
                "{:?} is not a gameId in poa-web/src/game-rack.js. The node, the launcher \
                 and the rack must key a game by ONE string",
                game.game_id
            );
        }
    }

    /// Route prefixes are distinct per game, or two games' sessions land on one
    /// surface and the second one mounted silently shadows the first.
    #[test]
    fn mounted_games_do_not_share_a_route_prefix_or_a_key() {
        let games = mounted();
        for (i, a) in games.iter().enumerate() {
            for b in games.iter().skip(i + 1) {
                assert_ne!(a.game_id, b.game_id, "two descriptors share a game id");
                assert_ne!(
                    a.route_prefix, b.route_prefix,
                    "{} and {} share a route prefix; one shadows the other",
                    a.game_id, b.game_id
                );
                assert_ne!(
                    a.open_statement_schema, b.open_statement_schema,
                    "{} and {} share an open-statement schema, so a signature scoped to \
                     one authorizes the other",
                    a.game_id, b.game_id
                );
                assert_ne!(
                    a.guess_statement_schema, b.guess_statement_schema,
                    "{} and {} share a guess-statement schema, so a signature scoped to \
                     one authorizes the other",
                    a.game_id, b.game_id
                );
            }
        }
    }

    #[test]
    fn a_hex32_must_be_exactly_sixty_four_lowercase_digits() {
        assert_eq!(parse_hex32("k", &"ab".repeat(32)).unwrap(), [0xab; 32]);
        assert!(parse_hex32("k", &"AB".repeat(32)).is_err(), "uppercase");
        assert!(parse_hex32("k", &"ab".repeat(31)).is_err(), "short");
        assert!(parse_hex32("k", &"zz".repeat(32)).is_err(), "not hex");
    }

    /// The signature must cover the message the node re-derived, not one it was
    /// handed. The falsifier changes the MESSAGE and asserts it changed before
    /// reading the verdict.
    #[test]
    fn a_signature_verifies_only_over_the_rederived_message() {
        use ed25519_dalek::{Signer as _, SigningKey};
        let key = SigningKey::from_bytes(&[0x77; 32]);
        let public = key.verifying_key().to_bytes();
        let honest = b"{\"schema\":\"X\",\"round\":0}".to_vec();
        let signature = dregg_types::hex_encode(&key.sign(&honest).to_bytes());
        verify_player_signature(public, &signature, &honest).expect("the honest message verifies");

        let forged = b"{\"schema\":\"X\",\"round\":1}".to_vec();
        assert_ne!(forged, honest, "the falsifier did not change the message");
        assert!(
            verify_player_signature(public, &signature, &forged).is_err(),
            "a signature over round 0 must not authorize round 1"
        );

        // A wrong key over the right message fails too.
        let other = SigningKey::from_bytes(&[0x88; 32])
            .verifying_key()
            .to_bytes();
        assert_ne!(other, public);
        assert!(verify_player_signature(other, &signature, &honest).is_err());
    }
}
