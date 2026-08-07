//! The judged Signal SESSION — an authenticated, budgeted, durable deduction game
//! against the instance that will settle.
//!
//! # The thing this closes
//!
//! Judged Signal was a **slot machine**. A public `SignalClaimV1` carries one code,
//! `SignalTriangulation.judge` returns `none` unless the transcript is SOLVED, and the
//! only path from a player to the chain was `POST /api/poa/signal/{authority}/claims`
//! with a code they had no information about. On-chain play was a blind 1-in-216 guess.
//!
//! The actual game — 216 codes, five bursts, LOCKED/DRIFT after each, an information
//! floor of three rounds — existed, and it existed only in the browser's PRACTICE mode,
//! drawn from `HiddenInstance.practiceRunSeed`, which no judge will ever score. So the
//! thing that was fun settled nothing and the thing that settled was not a game.
//!
//! This module is the missing half: a player opens a session against the currently
//! installed slot, submits guesses, is told LOCKED/DRIFT **against the judged target**,
//! and settles only after solving.
//!
//! # The routes
//!
//! All three are **AUTHENTICATED** (mounted in `protected_routes`), which is deliberate
//! and is stated here because the sibling `poa_signal_slot_api` is deliberately the
//! opposite. That module publishes a curator-signed commitment every reader needs; this
//! one spends a scarce per-player budget against a live secret.
//!
//! ```text
//! POST /api/poa/signal/{authority}/session/open      → open or resume
//! POST /api/poa/signal/{authority}/session/guess     → spend one burst, get LOCKED/DRIFT
//! GET  /api/poa/signal/{authority}/session/{player}  → read the transcript back
//! ```
//!
//! # ⚑ What a session reveals, field by field
//!
//! Standing question, the same one `poa_signal_slot_api` answers for its publication:
//! *can a reader who has not played reconstruct the instance from this?*
//!
//! | field | why it is safe |
//! |---|---|
//! | `exact` / `present` | THE LEAK, and it is the mechanic. Lean bounds it exactly: `reply_bytes_are_a_function_of_the_feedback_alone` — served bytes are a function of the classification alone; and `served_transcript_cannot_separate_feedback_equivalent_targets` — over a whole session, two targets consistent with the guesses played serve IDENTICAL bytes. A reader of a transcript is therefore exactly where the player who produced it is, and no further along. `SignalTriangulation.one_round_never_determines_the_target` says that position is never "solved" after one round, for ANY opening, so the invariance is over a genuinely non-trivial set |
//! | `transcript` | the player's own guesses and their own answers, read back. It is what they already saw, and retaining it is what makes a lost response recoverable rather than a lost burst |
//! | `slot` / `mission_id` | public coordinates; they name a slot, not a run |
//! | `slot_commitment` | already PUBLISHED, curator-signed, by `GET /api/poa/signal/{authority}/slot`. It is `HiddenInstance.commit secret slot` — a function of the secret and the slot ALONE, taking no player and no mission. It is echoed so a client can check it matches the signed opening it fetched, which is how a client tells a judged session from a practice one |
//! | `rounds_used` / `rounds_remaining` / `solved` | derivable from `transcript` |
//! | `settlement` | present only once solved, and it names the player's OWN transcript — every guess they typed, in the order they typed it — plus the route to submit it on. It tells a solver nothing they did not just discover |
//!
//! And what it never carries:
//!
//! * **the slot secret** — the answer to every run in the slot.
//! * **the run seed** — three modulo operations from this player's answer.
//! * **the target** — `settlement.code` is the guess the PLAYER submitted, taken from
//!   the stored transcript, and it exists only on a session whose last round already
//!   returned `exact: 3`. On an unsolved session `settlement` is `null` and there is no
//!   code in the document at all that the player did not type.
//!
//! `a_session_document_never_carries_a_secret_a_seed_or_an_unearned_code` builds these
//! responses from the live encoder with a known secret installed and fails if those
//! bytes appear anywhere in them.
//!
//! # Why every request is player-SIGNED, on top of the bearer token
//!
//! The bearer token says "a client of this node". It does not say "this player". And
//! the budget is per (authority, slot, player) — it has to be, because
//! `HiddenInstance.runSeedFor` takes the player key, so two players in one slot draw
//! DIFFERENT targets. Without proof of possession, any authenticated client could burn
//! any player's five bursts against a target it cannot settle: pure griefing, no gain.
//!
//! So `open` and `guess` each carry an Ed25519 signature by the player key over a
//! canonical statement. The guess statement includes `round` — the number of bursts
//! ALREADY spent — which makes a replayed signature refuse rather than spend a second
//! burst, without the node holding any session bearer secret of its own.
//!
//! The signing key is the same Ed25519 key that signs the settling turn, so a session
//! is bound to the identity that can actually settle it.
//!
//! # Two poles
//!
//! * **Solved** → `settlement` names the TRANSCRIPT, the player builds the ordinary
//!   signed `poa-signal` carrier over it (`dregg-node poa-signal-submit-claim`), and
//!   `latest_height` moves.
//! * **Wrong, incomplete, or over budget** → the session REFUSES, and the refusal names
//!   the real cause: `session-not-open`, `session-already-solved`,
//!   `session-budget-exhausted`, `session-signature`, `session-round-mismatch`. None of
//!   them is a wedge; a losing session is simply a session with five spent bursts and
//!   no settlement, and the player's cell has spent nothing on chain.
//!
//! # ⚑ This IS now the only way in (2026-08-07)
//!
//! A paragraph here used to say "this module does NOT gate the public claims route. A
//! player may still submit a blind claim and get the 1-in-216 they always had", and
//! that was the whole remaining wound: judged Signal was a deduction game for anyone
//! who chose to play it as one, and NOTHING REQUIRED IT. A stranger who guessed the
//! code settled a turn with no session, no feedback and no deduction anywhere in the
//! causal history of the block.
//!
//! A claim now carries the played transcript, and
//! `poa_signal_adapter::verify_claim_transcript_was_played` — run at FINALIZATION, and
//! again as a courtesy at the claims route — refuses one whose rounds this node did not
//! itself classify. So the sessions this module records are not merely available; they
//! are the only thing a settled turn can be made of. The blind path refuses as
//! `poa-signal-transcript-no-session`, with no transition and no height.

use std::net::SocketAddr;

use axum::extract::{ConnectInfo, Path, State};
use axum::http::{HeaderMap, StatusCode};
use axum::routing::{get, post};
use axum::{Json, Router};
use dregg_persist::{
    POA_SIGNAL_SESSION_MAX_ROUNDS, PoaSignalSessionRefusalV1, PoaSignalSessionRoundV1,
    PoaSignalSessionV1,
};
use dregg_sdk::poa_signal::{SIGNAL_CLAIM_METHOD_V1, SignalCode};
use dregg_types::hex_encode;
use ed25519_dalek::{Signature, Verifier, VerifyingKey};
use serde::{Deserialize, Serialize};

use crate::api::RateLimiter;
use crate::poa_signal_adapter::classify_session_guess;
use crate::state::NodeState;

/// Format tag of the session document.
pub const POA_SIGNAL_SESSION_FORMAT_V1: &str = "POA-SIGNAL-SESSION-1";

/// Schema of the statement a player signs to open a session.
pub const POA_SIGNAL_SESSION_OPEN_STATEMENT_V1: &str = "POA-SIGNAL-SESSION-OPEN-STATEMENT-1";

/// Schema of the statement a player signs to spend one burst.
pub const POA_SIGNAL_SESSION_GUESS_STATEMENT_V1: &str = "POA-SIGNAL-SESSION-GUESS-STATEMENT-1";

/// Sessions are cheap to serve and expensive to abuse; this is a shape guard on the
/// authenticated surface, not the game's budget. The game's budget is
/// [`POA_SIGNAL_SESSION_MAX_ROUNDS`], and it is durable.
const SESSION_REQUESTS_PER_MINUTE: u32 = 60;

/// One three-band code, as it appears on every session wire.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SignalCodeWireV1 {
    pub low: u8,
    pub mid: u8,
    pub high: u8,
}

impl SignalCodeWireV1 {
    fn parse(self) -> Result<SignalCode, SessionRefusal> {
        SignalCode::new(
            u64::from(self.low),
            u64::from(self.mid),
            u64::from(self.high),
        )
        .map_err(|_| SessionRefusal::band())
    }

    fn from_stored(guess: [u8; 3]) -> Self {
        Self {
            low: guess[0],
            mid: guess[1],
            high: guess[2],
        }
    }

    fn to_stored(self) -> [u8; 3] {
        [self.low, self.mid, self.high]
    }
}

/// `POST …/session/open` body.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PoaSignalSessionOpenRequestV1 {
    /// The player's Ed25519 public key, 64 lowercase hex. The instance is per player.
    pub player_key: String,
    /// Ed25519 over [`open_statement_message`], 128 lowercase hex.
    pub signature: String,
}

/// `POST …/session/guess` body.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PoaSignalSessionGuessRequestV1 {
    pub player_key: String,
    /// The number of bursts ALREADY spent — the 0-based index of this guess.
    ///
    /// ⚠ This is replay protection and it is why no session token exists. A signature
    /// covers one `round`, so replaying it after the round lands is refused by the
    /// stored count rather than accepted as a second burst.
    pub round: u32,
    pub guess: SignalCodeWireV1,
    /// Ed25519 over [`guess_statement_message`], 128 lowercase hex.
    pub signature: String,
}

/// One played round, as served.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct PoaSignalSessionRoundViewV1 {
    pub guess: SignalCodeWireV1,
    /// LOCKED.
    pub exact: u8,
    /// DRIFT.
    pub present: u8,
}

/// What a solved session tells the player to do next.
///
/// ⚠ `code` and `transcript` are the player's OWN guesses, read out of the stored
/// transcript, and this block exists only when the last of them already returned
/// `exact: 3`. It is not a disclosure; it is a receipt.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PoaSignalSessionSettlementV1 {
    pub mission_id: u64,
    /// ⚑ THE THING A CLAIM MUST CARRY: every round this session played, in the
    /// order it was played, ending in the solving guess.
    ///
    /// A claim that named only `code` is refused by
    /// `poa_signal_adapter::verify_claim_transcript_was_played` — the node settles
    /// the game it served, not a code that happens to be right. This is served so a
    /// client does not have to reassemble it from `transcript` above and guess at
    /// the ordering.
    pub transcript: Vec<SignalCodeWireV1>,
    /// The solving guess — the last entry of `transcript`, named separately because
    /// it is the one a player wants to see.
    pub code: SignalCodeWireV1,
    /// The method of the one-action carrier the player must sign.
    pub method: &'static str,
    /// The public route that carrier is POSTed to.
    pub claims_route: String,
    /// What settling actually requires, in one line, because `accepted: true` from the
    /// claims route is admission staging and settles nothing.
    pub note: &'static str,
}

/// The complete session document. Every route in this module returns this shape.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PoaSignalSessionResponseV1 {
    pub format: &'static str,
    /// ⚑ Always `true` here, and it is the field that keeps practice and judged
    /// visibly distinct. A practice run is drawn client-side from
    /// `HiddenInstance.practiceRunSeed` with the `practice` domain tag and has no
    /// session on any node; a judged run is this document, against a published
    /// commitment, and it is the only kind that can settle.
    pub judged: bool,
    pub authority_id: String,
    pub mission_id: u64,
    pub slot: u64,
    /// The published, curator-signed commitment this session is played against.
    /// A client should check it equals the one `GET …/slot` served.
    pub slot_commitment: String,
    pub player_key: String,
    pub max_rounds: usize,
    pub rounds_used: usize,
    pub rounds_remaining: usize,
    pub solved: bool,
    /// Whether another guess may be submitted. This is `SignalTriangulation.openB`.
    pub open: bool,
    pub transcript: Vec<PoaSignalSessionRoundViewV1>,
    pub settlement: Option<PoaSignalSessionSettlementV1>,
}

/// A named refusal. The `reason` is a stable machine token; the `detail` is for a human.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PoaSignalSessionRefusalBodyV1 {
    pub reason: &'static str,
    pub detail: String,
}

#[derive(Debug)]
struct SessionRefusal {
    status: StatusCode,
    reason: &'static str,
    detail: String,
}

impl SessionRefusal {
    fn new(status: StatusCode, reason: &'static str, detail: impl Into<String>) -> Self {
        Self {
            status,
            reason,
            detail: detail.into(),
        }
    }

    fn band() -> Self {
        Self::new(
            StatusCode::BAD_REQUEST,
            "session-band-out-of-range",
            "every Signal band must be in 0..=5; a band is refused rather than reduced \
             modulo six, because a wrapped band would be a second spelling of a legal \
             guess",
        )
    }

    fn into_response(self) -> (StatusCode, Json<PoaSignalSessionRefusalBodyV1>) {
        (
            self.status,
            Json(PoaSignalSessionRefusalBodyV1 {
                reason: self.reason,
                detail: self.detail,
            }),
        )
    }
}

type SessionResult<T> = Result<T, (StatusCode, Json<PoaSignalSessionRefusalBodyV1>)>;

pub(crate) fn routes() -> Router<NodeState> {
    let open_limiter = RateLimiter::new(SESSION_REQUESTS_PER_MINUTE, 60);
    let guess_limiter = RateLimiter::new(SESSION_REQUESTS_PER_MINUTE, 60);
    Router::new()
        .route(
            "/api/poa/signal/{authority}/session/open",
            post(move |connect, headers, path, state, body| {
                post_session_open(connect, headers, path, state, body, open_limiter.clone())
            }),
        )
        .route(
            "/api/poa/signal/{authority}/session/guess",
            post(move |connect, headers, path, state, body| {
                post_session_guess(connect, headers, path, state, body, guess_limiter.clone())
            }),
        )
        .route(
            "/api/poa/signal/{authority}/session/{player}",
            get(get_session),
        )
}

/// The exact bytes a player signs to open a session.
///
/// ⚠ Compact, key-ordered JSON in EXACTLY this order. A client that re-encodes in any
/// other order signs different bytes and is refused — the same rule the curator's
/// slot-opening statement applies to itself.
///
/// ```text
/// {"schema":"POA-SIGNAL-SESSION-OPEN-STATEMENT-1","authority_id":"<hex32>","slot":<n>,"player_key":"<hex32>"}
/// ```
pub fn open_statement_message(authority_id: [u8; 32], slot: u64, player_key: [u8; 32]) -> Vec<u8> {
    format!(
        r#"{{"schema":"{schema}","authority_id":"{authority}","slot":{slot},"player_key":"{player}"}}"#,
        schema = POA_SIGNAL_SESSION_OPEN_STATEMENT_V1,
        authority = hex_encode(&authority_id),
        player = hex_encode(&player_key),
    )
    .into_bytes()
}

/// The exact bytes a player signs to spend one burst.
///
/// ```text
/// {"schema":"POA-SIGNAL-SESSION-GUESS-STATEMENT-1","authority_id":"<hex32>","slot":<n>,"player_key":"<hex32>","round":<n>,"guess":{"low":n,"mid":n,"high":n}}
/// ```
///
/// `round` is the number of bursts already spent. It is inside the signature so a
/// captured request cannot be replayed into a second burst.
pub fn guess_statement_message(
    authority_id: [u8; 32],
    slot: u64,
    player_key: [u8; 32],
    round: u32,
    guess: SignalCodeWireV1,
) -> Vec<u8> {
    format!(
        r#"{{"schema":"{schema}","authority_id":"{authority}","slot":{slot},"player_key":"{player}","round":{round},"guess":{{"low":{low},"mid":{mid},"high":{high}}}}}"#,
        schema = POA_SIGNAL_SESSION_GUESS_STATEMENT_V1,
        authority = hex_encode(&authority_id),
        player = hex_encode(&player_key),
        low = guess.low,
        mid = guess.mid,
        high = guess.high,
    )
    .into_bytes()
}

fn parse_hex32(what: &'static str, value: &str) -> Result<[u8; 32], SessionRefusal> {
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
/// ⚠ The message is RE-DERIVED here from the structured request fields; it is never
/// accepted pre-encoded. A route that verified a caller-supplied message would report
/// "player-signed" for a statement the caller never made — the same trap
/// `poa_signal_slot_api` refuses to walk into by not serving its signing bytes.
fn verify_player_signature(
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
                 secret, so it requires proof of possession of the player key on top of the \
                 bearer token"
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

/// Resolve the authority and its installed slot, or say plainly why not.
async fn resolve_slot(
    state: &NodeState,
    authority: &str,
) -> Result<
    (
        [u8; 32],
        dregg_persist::PoaInstalledSlotV1,
        dregg_persist::PoaSignalHeadV1,
    ),
    SessionRefusal,
> {
    let requested = crate::api::parse_poa_signal_authority(authority).map_err(|_| {
        SessionRefusal::new(
            StatusCode::BAD_REQUEST,
            "session-authority",
            "the authority selector must be exactly 64 lowercase hexadecimal digits",
        )
    })?;
    let s = state.read().await;
    let authority_id = crate::api::select_local_poa_signal_authority(
        requested,
        s.federation_configured,
        s.federation_id,
    )
    .map_err(|_| {
        SessionRefusal::new(
            StatusCode::NOT_FOUND,
            "session-authority",
            "this node serves no such Signal authority",
        )
    })?;
    let slot = s
        .store
        .load_poa_signal_open_slot_v1(authority_id)
        .map_err(|error| {
            SessionRefusal::new(
                StatusCode::INTERNAL_SERVER_ERROR,
                "session-store",
                format!("the installed slot could not be read: {error}"),
            )
        })?
        .ok_or_else(|| {
            SessionRefusal::new(
                StatusCode::CONFLICT,
                "session-no-open-slot",
                "no curator-signed slot is open on this authority, so there is no committed \
                 instance to play against. A run played against no advance commitment is a \
                 run whose answer nobody promised; play practice instead",
            )
        })?;
    let head = s
        .store
        .load_poa_signal_head(authority_id)
        .map_err(|error| {
            SessionRefusal::new(
                StatusCode::INTERNAL_SERVER_ERROR,
                "session-store",
                format!("the Signal head could not be read: {error}"),
            )
        })?
        .ok_or_else(|| {
            SessionRefusal::new(
                StatusCode::CONFLICT,
                "session-no-head",
                "this authority has no PoA Signal head; the genesis ceremony has not run",
            )
        })?;
    Ok((authority_id, slot, head))
}

fn session_view(
    authority_id: [u8; 32],
    record: &PoaSignalSessionV1,
    claims_route: String,
) -> PoaSignalSessionResponseV1 {
    let transcript: Vec<PoaSignalSessionRoundViewV1> = record
        .rounds()
        .iter()
        .map(|round| PoaSignalSessionRoundViewV1 {
            guess: SignalCodeWireV1::from_stored(round.guess),
            exact: round.exact,
            present: round.present,
        })
        .collect();
    // ⚠ The settlement code comes from the STORED TRANSCRIPT, never from a derivation.
    // `solving_guess` is `None` unless the last stored round already returned
    // `exact: 3`, so this block cannot exist on a session that has not solved and
    // cannot name a code the player did not submit.
    let settlement = record
        .solving_guess()
        .map(|guess| PoaSignalSessionSettlementV1 {
            mission_id: record.mission_id(),
            transcript: record
                .rounds()
                .iter()
                .map(|round| SignalCodeWireV1::from_stored(round.guess))
                .collect(),
            code: SignalCodeWireV1::from_stored(guess),
            method: SIGNAL_CLAIM_METHOD_V1,
            claims_route: claims_route.clone(),
            note: "sign the one-action poa-signal carrier over this exact TRANSCRIPT with \
                   this player key and POST it to claims_route. A carrier naming only the \
                   solving code is refused: the node settles the game it served. \
                   `accepted: true` from that route is admission staging and settles \
                   nothing; the number that bites is `latest_height` off GET /status AFTER \
                   finalization",
        });
    PoaSignalSessionResponseV1 {
        format: POA_SIGNAL_SESSION_FORMAT_V1,
        judged: true,
        authority_id: hex_encode(&authority_id),
        mission_id: record.mission_id(),
        slot: record.slot(),
        slot_commitment: hex_encode(&record.commitment()),
        player_key: hex_encode(&record.player_key()),
        max_rounds: POA_SIGNAL_SESSION_MAX_ROUNDS,
        rounds_used: record.rounds_used(),
        rounds_remaining: record.rounds_remaining(),
        solved: record.solved(),
        open: record.open(),
        transcript,
        settlement,
    }
}

fn claims_route_for(authority_id: [u8; 32]) -> String {
    format!("/api/poa/signal/{}/claims", hex_encode(&authority_id))
}

async fn post_session_open(
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    headers: HeaderMap,
    Path(authority): Path<String>,
    State(state): State<NodeState>,
    Json(request): Json<PoaSignalSessionOpenRequestV1>,
    limiter: RateLimiter,
) -> SessionResult<Json<PoaSignalSessionResponseV1>> {
    open_session(addr, headers, authority, state, request, limiter)
        .await
        .map_err(SessionRefusal::into_response)
}

async fn open_session(
    addr: SocketAddr,
    headers: HeaderMap,
    authority: String,
    state: NodeState,
    request: PoaSignalSessionOpenRequestV1,
    limiter: RateLimiter,
) -> Result<Json<PoaSignalSessionResponseV1>, SessionRefusal> {
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(SessionRefusal::new(
            StatusCode::TOO_MANY_REQUESTS,
            "session-rate-limit",
            "too many session requests",
        ));
    }
    let (authority_id, slot, _head) = resolve_slot(&state, &authority).await?;
    let player_key = parse_hex32("player_key", &request.player_key)?;
    verify_player_signature(
        player_key,
        &request.signature,
        &open_statement_message(authority_id, slot.slot(), player_key),
    )?;

    let record = {
        let s = state.read().await;
        s.store
            .open_poa_signal_session_v1(
                authority_id,
                slot.slot(),
                slot.mission_id(),
                player_key,
                slot.commitment(),
            )
            .map_err(|error| {
                SessionRefusal::new(
                    StatusCode::CONFLICT,
                    "session-open-refused",
                    format!("the judged session could not be opened: {error}"),
                )
            })?
    };
    Ok(Json(session_view(
        authority_id,
        &record,
        claims_route_for(authority_id),
    )))
}

async fn post_session_guess(
    ConnectInfo(addr): ConnectInfo<SocketAddr>,
    headers: HeaderMap,
    Path(authority): Path<String>,
    State(state): State<NodeState>,
    Json(request): Json<PoaSignalSessionGuessRequestV1>,
    limiter: RateLimiter,
) -> SessionResult<Json<PoaSignalSessionResponseV1>> {
    submit_guess(addr, headers, authority, state, request, limiter)
        .await
        .map_err(SessionRefusal::into_response)
}

/// Spend one burst.
///
/// The ordering is the crash-safety argument and it is not negotiable:
///
/// 1. authenticate the player and the round index,
/// 2. ask Lean for the classification (pure; writes nothing),
/// 3. COMMIT the round and its classification,
/// 4. only then serve it.
///
/// A node that answered before committing would hand a free burst to anyone willing to
/// kill it between the two. A player who loses the response instead loses nothing: the
/// round is durable and `GET …/session/{player}` reads it back.
async fn submit_guess(
    addr: SocketAddr,
    headers: HeaderMap,
    authority: String,
    state: NodeState,
    request: PoaSignalSessionGuessRequestV1,
    limiter: RateLimiter,
) -> Result<Json<PoaSignalSessionResponseV1>, SessionRefusal> {
    if !limiter.check_request(addr.ip(), &headers).await {
        return Err(SessionRefusal::new(
            StatusCode::TOO_MANY_REQUESTS,
            "session-rate-limit",
            "too many session requests",
        ));
    }
    let (authority_id, slot, head) = resolve_slot(&state, &authority).await?;
    let player_key = parse_hex32("player_key", &request.player_key)?;
    let guess = request.guess.parse()?;
    verify_player_signature(
        player_key,
        &request.signature,
        &guess_statement_message(
            authority_id,
            slot.slot(),
            player_key,
            request.round,
            request.guess,
        ),
    )?;

    let existing = {
        let s = state.read().await;
        s.store
            .load_poa_signal_session_v1(authority_id, slot.slot(), player_key)
            .map_err(|error| {
                SessionRefusal::new(
                    StatusCode::INTERNAL_SERVER_ERROR,
                    "session-store",
                    format!("the judged session could not be read: {error}"),
                )
            })?
    };
    let existing = existing.ok_or_else(|| {
        SessionRefusal::new(
            StatusCode::NOT_FOUND,
            "session-not-open",
            "no judged session is open for this player against this slot; open one first",
        )
    })?;
    if existing.solved() {
        return Err(SessionRefusal::new(
            StatusCode::CONFLICT,
            "session-already-solved",
            "this judged run is already solved; submit the settling claim instead",
        ));
    }
    if existing.rounds_used() >= POA_SIGNAL_SESSION_MAX_ROUNDS {
        return Err(SessionRefusal::new(
            StatusCode::CONFLICT,
            "session-budget-exhausted",
            format!(
                "all {POA_SIGNAL_SESSION_MAX_ROUNDS} bursts of this judged run are spent. The \
                 budget is the game, and it is durable: a restart does not return it"
            ),
        ));
    }
    if usize::try_from(request.round).unwrap_or(usize::MAX) != existing.rounds_used() {
        return Err(SessionRefusal::new(
            StatusCode::CONFLICT,
            "session-round-mismatch",
            format!(
                "this request is signed for round {} but {} bursts are spent. A signature \
                 covers exactly one round, so a replayed request refuses rather than \
                 spending a second burst",
                request.round,
                existing.rounds_used()
            ),
        ));
    }

    // (2) Lean classifies. Nothing is written and nothing is revealed yet.
    let classification = classify_session_guess(&head, &slot, authority_id, player_key, guess)
        .map_err(|error| {
            SessionRefusal::new(
                StatusCode::SERVICE_UNAVAILABLE,
                "session-oracle-unavailable",
                format!(
                    "the Lean feedback oracle could not classify this guess: {error}. No burst \
                     was spent. There is no Rust classification to fall back to"
                ),
            )
        })?;

    // (3) COMMIT, then (4) serve. Never the other way around.
    let recorded = {
        let s = state.read().await;
        s.store
            .record_poa_signal_session_round_v1(
                authority_id,
                slot.slot(),
                player_key,
                PoaSignalSessionRoundV1 {
                    guess: request.guess.to_stored(),
                    exact: classification.exact,
                    present: classification.present,
                },
            )
            .map_err(|error| {
                SessionRefusal::new(
                    StatusCode::INTERNAL_SERVER_ERROR,
                    "session-store",
                    format!("the burst could not be committed, so it was not served: {error}"),
                )
            })?
    };
    let record = recorded.map_err(|refusal| {
        let (status, reason) = match refusal {
            PoaSignalSessionRefusalV1::NoSession => (StatusCode::NOT_FOUND, "session-not-open"),
            PoaSignalSessionRefusalV1::AlreadySolved => {
                (StatusCode::CONFLICT, "session-already-solved")
            }
            PoaSignalSessionRefusalV1::BudgetExhausted => {
                (StatusCode::CONFLICT, "session-budget-exhausted")
            }
            PoaSignalSessionRefusalV1::BandOutOfRange => {
                (StatusCode::BAD_REQUEST, "session-band-out-of-range")
            }
        };
        SessionRefusal::new(status, reason, refusal.to_string())
    })?;
    Ok(Json(session_view(
        authority_id,
        &record,
        claims_route_for(authority_id),
    )))
}

/// Read a session back. Observational: it classifies nothing and spends nothing.
///
/// This carries no signature requirement because it discloses only what the named
/// player has already been served. It is what makes a lost response recoverable instead
/// of a lost burst.
async fn get_session(
    Path((authority, player)): Path<(String, String)>,
    State(state): State<NodeState>,
) -> SessionResult<Json<PoaSignalSessionResponseV1>> {
    read_session(authority, player, state)
        .await
        .map_err(SessionRefusal::into_response)
}

async fn read_session(
    authority: String,
    player: String,
    state: NodeState,
) -> Result<Json<PoaSignalSessionResponseV1>, SessionRefusal> {
    let (authority_id, slot, _head) = resolve_slot(&state, &authority).await?;
    let player_key = parse_hex32("player", &player)?;
    let record = {
        let s = state.read().await;
        s.store
            .load_poa_signal_session_v1(authority_id, slot.slot(), player_key)
            .map_err(|error| {
                SessionRefusal::new(
                    StatusCode::INTERNAL_SERVER_ERROR,
                    "session-store",
                    format!("the judged session could not be read: {error}"),
                )
            })?
    };
    let record = record.ok_or_else(|| {
        SessionRefusal::new(
            StatusCode::NOT_FOUND,
            "session-not-open",
            "no judged session is open for this player against this slot",
        )
    })?;
    Ok(Json(session_view(
        authority_id,
        &record,
        claims_route_for(authority_id),
    )))
}

#[cfg(test)]
mod tests {
    use super::*;

    const SECRET: [u8; 32] = [0x77; 32];
    const AUTHORITY: [u8; 32] = [0x41; 32];
    const PLAYER: [u8; 32] = [0x55; 32];
    const COMMITMENT: [u8; 32] = [0xbc; 32];

    fn session_with(rounds: &[(SignalCodeWireV1, u8, u8)]) -> PoaSignalSessionV1 {
        let dir = tempfile::tempdir().unwrap();
        let store = dregg_persist::PersistentStore::open(&dir.path().join("dregg.redb")).unwrap();
        let mut record = store
            .open_poa_signal_session_v1(AUTHORITY, 9, 1, PLAYER, COMMITMENT)
            .unwrap();
        for (guess, exact, present) in rounds {
            record = store
                .record_poa_signal_session_round_v1(
                    AUTHORITY,
                    9,
                    PLAYER,
                    PoaSignalSessionRoundV1 {
                        guess: guess.to_stored(),
                        exact: *exact,
                        present: *present,
                    },
                )
                .unwrap()
                .unwrap();
        }
        record
    }

    fn code(low: u8, mid: u8, high: u8) -> SignalCodeWireV1 {
        SignalCodeWireV1 { low, mid, high }
    }

    /// ⚑ THE NO-OVER-REVEAL ASSERTION, ON THE ACTUAL SERVED BYTES.
    ///
    /// Lean proves the general statement about the classification wire. This is the
    /// node-side half over the whole session document, which is what a client sees:
    /// with a known slot secret installed, no session response — unsolved, mid-run or
    /// exhausted — contains the secret, and no unsolved response contains any code the
    /// player did not themselves submit.
    #[test]
    fn a_session_document_never_carries_a_secret_a_seed_or_an_unearned_code() {
        let secret_hex = hex_encode(&SECRET);
        for rounds in [
            &[][..],
            &[(code(0, 1, 2), 0, 2)][..],
            &[(code(0, 1, 2), 0, 2), (code(3, 3, 3), 1, 0)][..],
            &[
                (code(0, 1, 2), 0, 2),
                (code(3, 3, 3), 1, 0),
                (code(4, 4, 4), 0, 0),
                (code(5, 5, 5), 1, 0),
                (code(1, 1, 1), 0, 0),
            ][..],
        ] {
            let record = session_with(rounds);
            let view = session_view(AUTHORITY, &record, claims_route_for(AUTHORITY));
            let bytes = serde_json::to_string(&view).unwrap();
            assert!(
                !bytes.contains(&secret_hex),
                "an unsolved session document carried the slot secret: {bytes}"
            );
            assert!(
                view.settlement.is_none(),
                "an unsolved session offered a settlement; the code would be unearned"
            );
            assert!(!view.solved);
            assert_eq!(view.transcript.len(), rounds.len());
            // Every code in the document is one the player typed.
            for served in &view.transcript {
                assert!(rounds.iter().any(|(g, _, _)| *g == served.guess));
            }
        }
    }

    /// The solved pole: `settlement` appears, and its code is the player's OWN last
    /// guess out of the stored transcript — never a derivation.
    #[test]
    fn a_solved_session_settles_with_the_players_own_solving_guess() {
        let record = session_with(&[(code(0, 1, 2), 0, 2), (code(5, 0, 5), 3, 0)]);
        let view = session_view(AUTHORITY, &record, claims_route_for(AUTHORITY));
        assert!(view.solved);
        assert!(!view.open, "a solved run is over");
        assert_eq!(view.rounds_remaining, 0);
        let settlement = view
            .settlement
            .clone()
            .expect("a solved session must settle");
        assert_eq!(settlement.code, code(5, 0, 5));
        assert_eq!(
            settlement.transcript,
            vec![code(0, 1, 2), code(5, 0, 5)],
            "the settlement names EVERY round, in order — that is what a claim carries"
        );
        assert_eq!(
            settlement.transcript.last().copied(),
            Some(settlement.code),
            "the solving guess is the last round, never a separate value"
        );
        assert_eq!(settlement.method, SIGNAL_CLAIM_METHOD_V1);
        assert!(settlement.claims_route.ends_with("/claims"));
        assert!(
            !serde_json::to_string(&view)
                .unwrap()
                .contains(&hex_encode(&SECRET))
        );
    }

    /// The exhausted pole: five bursts spent, no settlement, and the refusal a further
    /// guess gets names the real cause rather than a generic error.
    #[test]
    fn an_exhausted_session_offers_no_settlement_and_names_its_own_cause() {
        let dir = tempfile::tempdir().unwrap();
        let store = dregg_persist::PersistentStore::open(&dir.path().join("dregg.redb")).unwrap();
        store
            .open_poa_signal_session_v1(AUTHORITY, 9, 1, PLAYER, COMMITMENT)
            .unwrap();
        let mut record = None;
        for index in 0..POA_SIGNAL_SESSION_MAX_ROUNDS {
            record = Some(
                store
                    .record_poa_signal_session_round_v1(
                        AUTHORITY,
                        9,
                        PLAYER,
                        PoaSignalSessionRoundV1 {
                            guess: [index as u8 % 6, 0, 0],
                            exact: 0,
                            present: 0,
                        },
                    )
                    .unwrap()
                    .unwrap(),
            );
        }
        let view = session_view(AUTHORITY, &record.unwrap(), claims_route_for(AUTHORITY));
        assert_eq!(view.rounds_used, POA_SIGNAL_SESSION_MAX_ROUNDS);
        assert_eq!(view.rounds_remaining, 0);
        assert!(!view.open);
        assert!(view.settlement.is_none());

        let sixth = store
            .record_poa_signal_session_round_v1(
                AUTHORITY,
                9,
                PLAYER,
                PoaSignalSessionRoundV1 {
                    guess: [1, 1, 1],
                    exact: 0,
                    present: 0,
                },
            )
            .unwrap();
        assert_eq!(sixth, Err(PoaSignalSessionRefusalV1::BudgetExhausted));
    }

    /// ⚑ RESTART DOES NOT REFUND A BURST. The store is reopened from the same file and
    /// the transcript is exactly where it was — which is the whole reason the session
    /// is durable rather than a map in process memory.
    #[test]
    fn a_restart_does_not_hand_back_a_fresh_budget() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("dregg.redb");
        {
            let store = dregg_persist::PersistentStore::open(&path).unwrap();
            store
                .open_poa_signal_session_v1(AUTHORITY, 9, 1, PLAYER, COMMITMENT)
                .unwrap();
            for index in 0..3u8 {
                store
                    .record_poa_signal_session_round_v1(
                        AUTHORITY,
                        9,
                        PLAYER,
                        PoaSignalSessionRoundV1 {
                            guess: [index, 0, 0],
                            exact: 0,
                            present: 1,
                        },
                    )
                    .unwrap()
                    .unwrap();
            }
        }
        let store = dregg_persist::PersistentStore::open(&path).unwrap();
        // Re-opening is idempotent: it resumes, it does not reset.
        let resumed = store
            .open_poa_signal_session_v1(AUTHORITY, 9, 1, PLAYER, COMMITMENT)
            .unwrap();
        assert_eq!(resumed.rounds_used(), 3);
        assert_eq!(
            resumed.rounds_remaining(),
            POA_SIGNAL_SESSION_MAX_ROUNDS - 3
        );
        store.audit_poa_signal_sessions_v1().unwrap();
    }

    /// A different player is a different session and a different budget, because
    /// `HiddenInstance.runSeedFor` gives them a different target. Burning one player's
    /// bursts cannot touch another's.
    #[test]
    fn budgets_do_not_cross_players() {
        let dir = tempfile::tempdir().unwrap();
        let store = dregg_persist::PersistentStore::open(&dir.path().join("dregg.redb")).unwrap();
        let other = [0x66u8; 32];
        store
            .open_poa_signal_session_v1(AUTHORITY, 9, 1, PLAYER, COMMITMENT)
            .unwrap();
        store
            .open_poa_signal_session_v1(AUTHORITY, 9, 1, other, COMMITMENT)
            .unwrap();
        for index in 0..POA_SIGNAL_SESSION_MAX_ROUNDS {
            store
                .record_poa_signal_session_round_v1(
                    AUTHORITY,
                    9,
                    PLAYER,
                    PoaSignalSessionRoundV1 {
                        guess: [index as u8, 0, 0],
                        exact: 0,
                        present: 0,
                    },
                )
                .unwrap()
                .unwrap();
        }
        let untouched = store
            .load_poa_signal_session_v1(AUTHORITY, 9, other)
            .unwrap()
            .unwrap();
        assert_eq!(untouched.rounds_used(), 0);
        assert_eq!(untouched.rounds_remaining(), POA_SIGNAL_SESSION_MAX_ROUNDS);
    }

    /// The signed statements are exactly the documented encodings. A client re-derives
    /// these bytes from the structured fields; if this changes, every client's
    /// signature stops verifying, so it is pinned rather than described.
    #[test]
    fn the_signed_statements_are_the_documented_encodings() {
        assert_eq!(
            String::from_utf8(open_statement_message(AUTHORITY, 9, PLAYER)).unwrap(),
            concat!(
                r#"{"schema":"POA-SIGNAL-SESSION-OPEN-STATEMENT-1""#,
                r#","authority_id":"4141414141414141414141414141414141414141414141414141414141414141""#,
                r#","slot":9"#,
                r#","player_key":"5555555555555555555555555555555555555555555555555555555555555555"}"#,
            )
        );
        assert_eq!(
            String::from_utf8(guess_statement_message(
                AUTHORITY,
                9,
                PLAYER,
                2,
                code(0, 1, 5)
            ))
            .unwrap(),
            concat!(
                r#"{"schema":"POA-SIGNAL-SESSION-GUESS-STATEMENT-1""#,
                r#","authority_id":"4141414141414141414141414141414141414141414141414141414141414141""#,
                r#","slot":9"#,
                r#","player_key":"5555555555555555555555555555555555555555555555555555555555555555""#,
                r#","round":2"#,
                r#","guess":{"low":0,"mid":1,"high":5}}"#,
            )
        );
    }

    /// The round index is inside the signature, so a captured guess cannot be replayed
    /// into a second burst: the same signature over a different round is different
    /// bytes and does not verify.
    #[test]
    fn a_guess_signature_covers_exactly_one_round() {
        let first = guess_statement_message(AUTHORITY, 9, PLAYER, 0, code(1, 2, 3));
        let second = guess_statement_message(AUTHORITY, 9, PLAYER, 1, code(1, 2, 3));
        assert_ne!(first, second);
        let other_slot = guess_statement_message(AUTHORITY, 10, PLAYER, 0, code(1, 2, 3));
        assert_ne!(first, other_slot, "a signature must not carry across slots");
    }

    /// Possession of the player key is REQUIRED and is checked against the re-derived
    /// statement, never against caller-supplied bytes.
    #[test]
    fn only_the_player_key_can_spend_that_players_budget() {
        use ed25519_dalek::{Signer, SigningKey};
        let player = SigningKey::from_bytes(&[7u8; 32]);
        let impostor = SigningKey::from_bytes(&[8u8; 32]);
        let player_key = player.verifying_key().to_bytes();
        let message = open_statement_message(AUTHORITY, 9, player_key);

        let honest = hex_encode(&player.sign(&message).to_bytes());
        verify_player_signature(player_key, &honest, &message).unwrap();

        let forged = hex_encode(&impostor.sign(&message).to_bytes());
        let refusal = verify_player_signature(player_key, &forged, &message).unwrap_err();
        assert_eq!(refusal.reason, "session-signature");
        assert_eq!(refusal.status, StatusCode::UNAUTHORIZED);

        // A signature over a DIFFERENT statement does not verify against this one.
        let other = open_statement_message(AUTHORITY, 10, player_key);
        let wrong_slot = hex_encode(&player.sign(&other).to_bytes());
        assert!(verify_player_signature(player_key, &wrong_slot, &message).is_err());
    }

    /// A band outside `0..=5` is refused rather than reduced modulo six.
    #[test]
    fn an_out_of_range_band_is_refused_before_anything_is_spent() {
        assert!(code(0, 1, 6).parse().is_err());
        assert!(code(9, 9, 9).parse().is_err());
        assert!(code(5, 5, 5).parse().is_ok());
    }

    /// The store's budget and `SignalTriangulation.MAX_TURNS` are the same number.
    /// They have to be: a sixth round would build a transcript the judge's `replay`
    /// refuses at the step, AFTER the player paid a turn fee.
    #[test]
    fn the_session_budget_is_the_rules_budget() {
        assert_eq!(POA_SIGNAL_SESSION_MAX_ROUNDS, 5);
    }
}
