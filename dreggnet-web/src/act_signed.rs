//! # `act_signed` — the SIGNED-turn route: the browser extension's verifying consumer.
//!
//! `POST /offerings/{key}/session/{id}/act-signed` closes the G1 signed-identity ladder end to
//! end: the extension SIGNS an offering turn (`extension/src/offering-sign.ts`,
//! `dregg.signOfferingTurn`) and this route VERIFIES it into one real turn via
//! [`OfferingHost::advance_signed`](dreggnet_offerings::OfferingHost::advance_signed) — the turn's
//! actor lands as a **verified** Ed25519 public key
//! ([`Attribution::Signed`](dreggnet_offerings::Attribution)), not a frontend-asserted cookie
//! label like the unsigned `/act` twin.
//!
//! ## The wire (what the extension README's step-4 fetch sends)
//!
//! JSON, not a form:
//!
//! ```json
//! {
//!   "action": { "turn": "choose", "arg": 3, "text": null, "label": "…", "enabled": true },
//!   "actor_pubkey_hex": "…64 lowercase hex chars…",
//!   "counter": 0,
//!   "signature_hex": "…128 hex chars…"
//! }
//! ```
//!
//! Decode decisions (all fail-closed, `400` on any malformation — before any crypto):
//! - `counter` is a **u64** accepted as a JSON number OR a decimal string (the extension's
//!   `counterWire`: a JS number silently loses precision beyond 2^53 − 1, so large counters ride
//!   as strings). `action.arg` is an **i64** with the same number-or-string acceptance.
//! - `signature_hex` must be exactly 128 hex chars → `[u8; 64]` ([`SignedAction`]'s signature
//!   cannot derive serde, so the decode is manual).
//! - `action.label` / `action.enabled` are optional surface decorations (deliberately NOT part of
//!   the signed message — see `signed.rs::signing_message`); absent they default to the turn verb
//!   and `true`.
//!
//! ## Honest statuses
//!
//! - `400` — malformed body (bad JSON, bad hex, unparsable counter/arg, or a pubkey that is not
//!   32 bytes of hex — [`SignedError::MalformedKey`]): the request never named a verifiable turn.
//! - `403` — a WELL-FORMED envelope the verifier REFUSED: forged/tampered/spliced signature
//!   ([`SignedError::BadSignature`]) or a replayed counter ([`SignedError::StaleCounter`]).
//!   A refused signature is the gate WORKING, never a 500. Nothing advances, nothing is recorded.
//! - `404` — no such offering / session (routing miss, before the substrate).
//! - `429` / `409` — the open-lifecycle gates, exactly as the unsigned path's
//!   [`refused_open_response`](crate::refused_open_response) maps them.
//! - `200` — the envelope VERIFIED and the executor resolved the turn: a landed move re-renders
//!   the session surface (the SAME one-render-path the unsigned `/act` uses, `X-Fragment`-aware)
//!   with the verified signer named in the notice; an executor refusal of a *correctly signed*
//!   move is the anti-ghost banner at `200`, mirroring the unsigned twin (the signature gate
//!   passed; the substrate refereed the move itself).

use std::sync::Arc;

use axum::{
    body::Bytes,
    extract::{Path, State},
    http::{HeaderMap, StatusCode},
    response::{Html, IntoResponse, Response},
};
use serde::Deserialize;
use serde_json::Value;

use dreggnet_catalog::{
    GameActionRef, GameHostIncarnation, GameResult, GameSessionRef, PublicGameReceipt,
    SignedGameAction, execute_bound_signed_game_turn_with_outcome, game_kind,
    project_public_game_receipt, verify_signed_game_action,
};
use dreggnet_offerings::player_turn_receipt::{PlayerReplaySurface, PlayerTurnReceipt};
use dreggnet_offerings::{
    Action, Attribution, Custody, DreggIdentity, HostError, OfferingHost, Outcome, SessionId,
    SignedAction, SignedError, verify_signed,
};

use crate::{
    CatalogGameError, CatalogState, audit, open_audit_parts, refused_open_response,
    render_offering_response, wants_fragment,
};

pub(crate) enum SignedAdvance {
    Advanced {
        outcome: Outcome,
        publication: Option<PublicGameReceipt>,
    },
    CommittedButPublicationFailed {
        outcome: Outcome,
        error: String,
    },
    HostError(HostError),
    GameRouteRefused(String),
}

pub(crate) enum RoutedSignedAction {
    Game(SignedGameAction),
    Legacy(SignedAction),
}

/// Resolve one already-formed signed action through the authority-bound game
/// spine, or retain the legacy host path for non-game offerings. Telegram and
/// Discord call this from the same atomic host job that allocates their
/// custodial counter, so all signed surfaces share the exact routing and
/// viewer-blind publication boundary.
///
/// `custody` records WHOSE key signed on the legacy path: a server-held
/// ([`Custody::Custodial`], the telegram/discord `seed_for` adapters) or a
/// user-held ([`Custody::UserHeld`], the browser-extension route) one — the
/// grade a bare `Signed` receipt used to collapse. A custodial legacy advance
/// also BINDS this host's incarnation ([`OfferingHost::signing_epoch`]) into the
/// signature so a captured envelope cannot re-verify on a reopened id; the
/// user-held (extension) route is not yet epoch-bound (the extension must echo +
/// sign the epoch, as it already echoes the game authority coordinates — a named
/// residual), so it passes `None` and keeps working unchanged. The game branch
/// carries its own replay binding (its authority signature) and ignores this.
pub(crate) fn advance_signed_on_host(
    host: &mut OfferingHost,
    key: String,
    sid: SessionId,
    game_context: Option<(GameHostIncarnation, u64, GameSessionRef)>,
    signed: RoutedSignedAction,
    custody: Custody,
) -> SignedAdvance {
    match (game_context, signed) {
        (Some((incarnation, generation, session)), RoutedSignedAction::Game(command)) => {
            match verify_signed_game_action(&command) {
                Ok(_) => {}
                Err(error) => return SignedAdvance::HostError(HostError::Signature(error)),
            }
            match execute_bound_signed_game_turn_with_outcome(
                host,
                incarnation,
                generation,
                &session,
                command,
            ) {
                Ok(execution) => {
                    let publication = match &execution.result {
                        GameResult::Landed(receipt) => match project_public_game_receipt(receipt) {
                            Ok(publication) => Some(publication),
                            Err(error) => {
                                return SignedAdvance::CommittedButPublicationFailed {
                                    outcome: execution.outcome,
                                    error: error.to_string(),
                                };
                            }
                        },
                        GameResult::Refused { .. } => None,
                    };
                    SignedAdvance::Advanced {
                        outcome: execution.outcome,
                        publication,
                    }
                }
                Err(error) => SignedAdvance::GameRouteRefused(error.to_string()),
            }
        }
        (None, RoutedSignedAction::Legacy(signed)) => {
            // A CUSTODIAL legacy advance binds this host incarnation (the signer signed under the
            // same `signing_epoch`); the USER-HELD (extension) route is not yet epoch-bound (the
            // extension must echo + sign the epoch — a named residual), so it stays epoch-free.
            let epoch = custody.is_custodial().then(|| host.signing_epoch());
            match host.advance_signed_attributed(&key, &sid, signed, epoch, custody) {
                Ok(outcome) => SignedAdvance::Advanced {
                    outcome,
                    publication: None,
                },
                Err(error) => SignedAdvance::HostError(error),
            }
        }
        (None, RoutedSignedAction::Game(_)) => SignedAdvance::GameRouteRefused(
            "game command reached execution without a live ledger authority context".to_string(),
        ),
        (Some(_), RoutedSignedAction::Legacy(_)) => SignedAdvance::GameRouteRefused(
            "bound game route requires a client-signed game authority envelope".to_string(),
        ),
    }
}

/// The act-signed audit-envelope skeleton (`signed` attribution — the user-held-key grade).
/// The caller stamps decision + outcome; `detail` carries the PUBLIC wire material only
/// (turn/arg/counter — §8: the pubkey and even the signature are public, secrets never
/// reach this route).
fn signed_audit_event(
    actor: audit::Actor,
    key: &str,
    sid: &SessionId,
    detail: serde_json::Value,
) -> audit::AuditEvent {
    audit::AuditEvent::new(
        "web",
        actor,
        audit::Surface::Http,
        audit::Input::new("POST /offerings/{key}/session/{id}/act-signed", detail),
    )
    .in_session(Some(key.to_string()), Some(sid.0.clone()))
}

// ─────────────────────────────────────────────────────────────────────────────
// The wire → SignedAction decode.
// ─────────────────────────────────────────────────────────────────────────────

/// The JSON body of `POST /offerings/{key}/session/{id}/act-signed` — the shape the extension
/// README's step-4 `fetch` assembles from `dregg.signOfferingTurn`'s result plus the action
/// fields the message was signed over. [`SignedAction`] itself cannot derive serde (the
/// `[u8; 64]` signature), so this wire struct + [`decode`] are the manual bridge.
#[derive(Debug, Clone, Deserialize)]
pub struct SignedActionWire {
    /// The action fields the canonical message was signed over (plus optional decorations).
    pub action: ActionWire,
    /// The signer's Ed25519 public key, hex (64 chars; the verifier canonicalizes case).
    pub actor_pubkey_hex: String,
    /// The replay counter — a u64 as a JSON number, or a decimal string beyond 2^53 − 1
    /// (the extension's `counterWire` JSON-safety rule).
    pub counter: Value,
    /// The 64-byte Ed25519 signature over the canonical signing message — 128 hex chars.
    pub signature_hex: String,
    /// Required on game routes. These are the exact authority coordinates the
    /// client observed and signed; the server never replaces them with its
    /// current generation/head.
    #[serde(default)]
    pub game_authority: Option<GameAuthorityWire>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct GameAuthorityWire {
    pub host_incarnation_hex: String,
    pub session_generation: Value,
    pub expected_pre_head_hex: String,
    pub authority_signature_hex: String,
}

#[derive(Debug, Clone)]
pub struct DecodedSignedAction {
    pub signed_action: SignedAction,
    pub game_authority: Option<DecodedGameAuthority>,
}

#[derive(Debug, Clone)]
pub struct DecodedGameAuthority {
    pub host_incarnation: GameHostIncarnation,
    pub session_generation: u64,
    pub expected_pre_head: Vec<u8>,
    pub authority_signature: [u8; 64],
}

/// The wire form of the [`Action`] being fired. `turn`, `arg`, and `text` are the SIGNED fields;
/// `label` and `enabled` are unsigned surface decorations (optional, defaulted).
#[derive(Debug, Clone, Deserialize)]
pub struct ActionWire {
    /// The affordance verb (`Action::turn`) — signed.
    pub turn: String,
    /// The affordance argument (`Action::arg`, an i64) — signed. Number or decimal string.
    pub arg: Value,
    /// Optional free-text payload (`Action::text`) — signed (absent signs as empty).
    #[serde(default)]
    pub text: Option<String>,
    /// Optional display label — NOT signed (decoration; defaults to the turn verb).
    #[serde(default)]
    pub label: Option<String>,
    /// Optional enabled decoration — NOT signed (the executor is the sole referee anyway).
    #[serde(default)]
    pub enabled: Option<bool>,
}

/// A `400` with a named reason — the decode's only failure shape.
fn bad(reason: impl Into<String>) -> (StatusCode, String) {
    (StatusCode::BAD_REQUEST, reason.into())
}

/// Parse a u64 from a JSON number or a decimal string (the counter wire). A float, a negative,
/// a non-digit string, or an overflow is a named `400`.
fn parse_u64_wire(v: &Value, field: &str) -> Result<u64, (StatusCode, String)> {
    match v {
        Value::Number(n) => n
            .as_u64()
            .ok_or_else(|| bad(format!("{field} must be a non-negative integer"))),
        Value::String(s) => {
            if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
                return Err(bad(format!(
                    "{field} string must be a non-negative decimal integer"
                )));
            }
            s.parse::<u64>()
                .map_err(|_| bad(format!("{field} exceeds u64::MAX")))
        }
        _ => Err(bad(format!("{field} must be a number or a decimal string"))),
    }
}

/// Parse an i64 from a JSON number or a decimal string (the arg wire).
fn parse_i64_wire(v: &Value, field: &str) -> Result<i64, (StatusCode, String)> {
    match v {
        Value::Number(n) => n
            .as_i64()
            .ok_or_else(|| bad(format!("{field} must be an integer within i64 range"))),
        Value::String(s) => s.parse::<i64>().map_err(|_| {
            bad(format!(
                "{field} string must be a decimal integer in i64 range"
            ))
        }),
        _ => Err(bad(format!("{field} must be a number or a decimal string"))),
    }
}

/// Decode exactly 128 hex chars into 64 bytes (case-insensitive). `None` on any other shape —
/// a truncated, padded, or non-hex signature never reaches the verifier.
fn decode_hex_64(s: &str) -> Option<[u8; 64]> {
    let bytes = s.as_bytes();
    if bytes.len() != 128 {
        return None;
    }
    let nib = |c: u8| -> Option<u8> {
        match c {
            b'0'..=b'9' => Some(c - b'0'),
            b'a'..=b'f' => Some(c - b'a' + 10),
            b'A'..=b'F' => Some(c - b'A' + 10),
            _ => None,
        }
    };
    let mut out = [0u8; 64];
    for (i, chunk) in bytes.chunks_exact(2).enumerate() {
        out[i] = (nib(chunk[0])? << 4) | nib(chunk[1])?;
    }
    Some(out)
}

fn decode_hex<const N: usize>(s: &str) -> Option<[u8; N]> {
    let bytes = s.as_bytes();
    if bytes.len() != N * 2 {
        return None;
    }
    let nibble = |byte: u8| match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    };
    let mut out = [0; N];
    for (index, pair) in bytes.chunks_exact(2).enumerate() {
        out[index] = (nibble(pair[0])? << 4) | nibble(pair[1])?;
    }
    Some(out)
}

/// **Decode the JSON wire into the [`SignedAction`] the host verifies** — hex + counter/arg
/// parsing, `400` with a named reason on any malformation. No crypto happens here; a decoded
/// envelope is merely WELL-FORMED, and only [`advance_signed`
/// ](dreggnet_offerings::OfferingHost::advance_signed) can admit it.
pub fn decode(wire: SignedActionWire) -> Result<DecodedSignedAction, (StatusCode, String)> {
    let counter = parse_u64_wire(&wire.counter, "counter")?;
    let arg = parse_i64_wire(&wire.action.arg, "action.arg")?;
    let signature = decode_hex_64(&wire.signature_hex)
        .ok_or_else(|| bad("signature_hex must be exactly 128 hex chars (64 bytes)"))?;

    let label = wire
        .action
        .label
        .unwrap_or_else(|| wire.action.turn.clone());
    let enabled = wire.action.enabled.unwrap_or(true);
    let mut action = Action::new(label, wire.action.turn, arg, enabled);
    if let Some(text) = wire.action.text {
        action = action.with_text(text);
    }

    let game_authority = match wire.game_authority {
        Some(authority) => {
            let incarnation =
                decode_hex::<32>(&authority.host_incarnation_hex).ok_or_else(|| {
                    bad("game_authority.host_incarnation_hex must be exactly 64 hex chars")
                })?;
            let host_incarnation = GameHostIncarnation::new(incarnation)
                .map_err(|error| bad(format!("invalid game host incarnation: {error}")))?;
            let session_generation = parse_u64_wire(
                &authority.session_generation,
                "game_authority.session_generation",
            )?;
            let expected_pre_head = decode_hex::<32>(&authority.expected_pre_head_hex)
                .ok_or_else(|| {
                    bad("game_authority.expected_pre_head_hex must be exactly 64 hex chars")
                })?
                .to_vec();
            let authority_signature = decode_hex_64(&authority.authority_signature_hex)
                .ok_or_else(|| {
                    bad("game_authority.authority_signature_hex must be exactly 128 hex chars")
                })?;
            Some(DecodedGameAuthority {
                host_incarnation,
                session_generation,
                expected_pre_head,
                authority_signature,
            })
        }
        None => None,
    };

    Ok(DecodedSignedAction {
        signed_action: SignedAction {
            action,
            actor_pubkey_hex: wire.actor_pubkey_hex,
            counter,
            signature,
        },
        game_authority,
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// The handler.
// ─────────────────────────────────────────────────────────────────────────────

/// `POST /offerings/{key}/session/{id}/act-signed` — decode the JSON wire, ensure the session is
/// open (lifecycle-aware, exactly as the unsigned `/act` twin), and land ONE signature-verified
/// turn via [`advance_signed`](dreggnet_offerings::OfferingHost::advance_signed). See the module
/// doc for the wire shape and the status mapping.
pub async fn post_offering_act_signed(
    State(state): State<Arc<CatalogState>>,
    Path((key, id)): Path<(String, String)>,
    headers: HeaderMap,
    body: Bytes,
) -> Response {
    let sid = SessionId::new(id);

    // THE SEAT LOCK on a minted automatafl table. A seat-locked table binds its two seats to two
    // unguessable BROWSER labels; a signed envelope carries a pubkey-derived actor instead, which
    // can never be one of them. Refuse the whole route for such a table rather than let a signed
    // stranger claim a seat the link was supposed to hold — fail-closed, and before any crypto or
    // any open, so nothing commits.
    if let Err(why) = crate::automatafl_web::enforce_seat_lock(&key, &sid.0, "") {
        audit::log().emit(
            signed_audit_event(
                audit::Actor::unattributed(),
                &key,
                &sid,
                serde_json::json!({ "error": why.clone() }),
            )
            .decided("gated", why.clone()),
        );
        return (StatusCode::FORBIDDEN, why).into_response();
    }

    // Decode: body → wire → SignedAction. Any malformation is a named 400, before any crypto.
    let wire: SignedActionWire = match serde_json::from_slice(&body) {
        Ok(w) => w,
        Err(e) => {
            // AUDIT EMIT: the request never named a verifiable turn — refused at the shape.
            audit::log().emit(
                signed_audit_event(
                    audit::Actor::unattributed(),
                    &key,
                    &sid,
                    serde_json::json!({ "error": e.to_string() }),
                )
                .decided("refused", "malformed_body"),
            );
            return (
                StatusCode::BAD_REQUEST,
                format!("malformed act-signed body: {e}"),
            )
                .into_response();
        }
    };
    let decoded = match decode(wire) {
        Ok(decoded) => decoded,
        Err((status, reason)) => {
            audit::log().emit(
                signed_audit_event(
                    audit::Actor::unattributed(),
                    &key,
                    &sid,
                    serde_json::json!({ "error": reason.clone() }),
                )
                .decided("refused", "malformed_envelope"),
            );
            return (status, reason).into_response();
        }
    };

    // The PUBLIC wire material for the audit envelope (captured before `sa` moves into the
    // host job): turn/arg/counter — the signature itself is public too, but the join needs
    // only the signed intent.
    let audit_detail = serde_json::json!({
        "turn": decoded.signed_action.action.turn,
        "arg": decoded.signed_action.action.arg,
        "counter": decoded.signed_action.counter,
    });

    // Authenticate before opening or privately projecting anything. A forged
    // victim key therefore cannot distinguish private affordance state by the
    // status code or create a session under a falsely "signed" audit actor.
    let (routed_signed, verified_actor) = if game_kind(&key).is_some() {
        let Some(authority) = decoded.game_authority else {
            return bad("game routes require game_authority signed coordinates").into_response();
        };
        let session = match GameSessionRef::bound(
            key.clone(),
            sid.clone(),
            authority.host_incarnation,
            authority.session_generation,
        ) {
            Ok(session) => session,
            Err(error) => return bad(error.to_string()).into_response(),
        };
        let reference = GameActionRef::new(
            session,
            &decoded.signed_action.action,
            authority.expected_pre_head,
        );
        let command = SignedGameAction {
            reference,
            signed_action: decoded.signed_action,
            authority_signature: authority.authority_signature,
        };
        let actor = match verify_signed_game_action(&command).and_then(|outer_actor| {
            verify_signed(&key, &sid, 0, &command.signed_action).and_then(|inner_actor| {
                if inner_actor == outer_actor {
                    Ok(inner_actor)
                } else {
                    Err(SignedError::BadSignature)
                }
            })
        }) {
            Ok(actor) => actor,
            Err(error) => {
                audit::log().emit(
                    signed_audit_event(audit::Actor::unattributed(), &key, &sid, audit_detail)
                        .decided("gated", "bad_signature"),
                );
                return (
                    StatusCode::FORBIDDEN,
                    format!("signed advance refused: {error}"),
                )
                    .into_response();
            }
        };
        (RoutedSignedAction::Game(command), actor)
    } else {
        if decoded.game_authority.is_some() {
            return bad("non-game routes must not carry game_authority").into_response();
        }
        let actor = match verify_signed(&key, &sid, 0, &decoded.signed_action) {
            Ok(actor) => actor,
            Err(error) => {
                audit::log().emit(
                    signed_audit_event(audit::Actor::unattributed(), &key, &sid, audit_detail)
                        .decided("gated", "bad_signature"),
                );
                return (
                    StatusCode::FORBIDDEN,
                    format!("signed advance refused: {error}"),
                )
                    .into_response();
            }
        };
        (RoutedSignedAction::Legacy(decoded.signed_action), actor)
    };

    // The signer's derived identity — for an RPG key this selects the signer's OWN per-identity
    // world (their isolated inventory); a shared table ignores it (one host for everyone).
    let viewer = verified_actor.clone();
    // Legacy non-game routes retain lazy open. A bound game command must name
    // an already-live epoch; `run_presented_bound_game` compares it with the
    // ledger before touching the host and refuses any fresh-open ghost.
    if matches!(&routed_signed, RoutedSignedAction::Legacy(_)) {
        let k = key.clone();
        let sid_for_open = sid.clone();
        let opener = Attribution::Signed {
            pubkey_hex: verified_actor.0.clone(),
        };
        let opened = state.run_offering(&key, &viewer, move |host| {
            host.ensure_open_as(&k, &sid_for_open, Some(&opener))
        });
        match opened {
            Ok(_) => {}
            Err(HostError::UnknownOffering(k)) => {
                audit::log().emit(
                    signed_audit_event(
                        audit::Actor::signed(verified_actor.0.clone(), verified_actor.0.clone()),
                        &key,
                        &sid,
                        audit_detail,
                    )
                    .decided("refused", "unknown_offering"),
                );
                return (
                    StatusCode::NOT_FOUND,
                    format!("no offering registered under key {k:?}"),
                )
                    .into_response();
            }
            Err(e @ (HostError::Policy(_) | HostError::ResumeFailed { .. })) => {
                let (kind, reason) = open_audit_parts(&e);
                audit::log().emit(
                    signed_audit_event(
                        audit::Actor::signed(verified_actor.0.clone(), verified_actor.0.clone()),
                        &key,
                        &sid,
                        audit_detail,
                    )
                    .decided(kind, reason),
                );
                return refused_open_response(&sid, &e);
            }
            Err(error) => {
                return (StatusCode::INTERNAL_SERVER_ERROR, error.to_string()).into_response();
            }
        }
    }

    let outcome = match routed_signed {
        RoutedSignedAction::Game(command) => {
            let presented = command.reference.session.clone();
            let routed_key = key.clone();
            let routed_sid = sid.clone();
            let opener = Attribution::Signed {
                pubkey_hex: verified_actor.0.clone(),
            };
            match state.run_presented_bound_game(
                presented,
                &viewer,
                opener,
                move |host, incarnation, generation, session| {
                    advance_signed_on_host(
                        host,
                        routed_key,
                        routed_sid,
                        Some((incarnation, generation, session)),
                        RoutedSignedAction::Game(command),
                        // The extension holds the signing key (user-held), though the game route's
                        // own authority signature is what binds replay here.
                        Custody::UserHeld,
                    )
                },
            ) {
                Ok(outcome) => outcome,
                Err(CatalogGameError::Host(error)) => SignedAdvance::HostError(error),
                Err(error) => SignedAdvance::GameRouteRefused(error.to_string()),
            }
        }
        RoutedSignedAction::Legacy(signed) => {
            let routed_key = key.clone();
            let routed_sid = sid.clone();
            state.run_offering(&key, &viewer, move |host| {
                advance_signed_on_host(
                    host,
                    routed_key,
                    routed_sid,
                    None,
                    RoutedSignedAction::Legacy(signed),
                    // The browser extension holds the signing key — a genuinely user-held key.
                    Custody::UserHeld,
                )
            })
        }
    };

    // AUDIT EMIT: the signature-verified advance — `Landed` carries the receipt-chain join;
    // a verifier refusal (forged/tampered/replayed counter) is a `gated` envelope, nothing
    // committed (anti-ghost).
    {
        let (kind, reason, out) = match &outcome {
            SignedAdvance::Advanced {
                outcome: Outcome::Landed { receipt, ended },
                ..
            } => (
                "routed",
                String::new(),
                audit::AuditOutcome::Landed {
                    turn_hash: audit::hex32(&receipt.turn_hash),
                    ended: *ended,
                },
            ),
            SignedAdvance::Advanced {
                outcome: Outcome::Refused(why),
                ..
            } => (
                "routed",
                String::new(),
                audit::AuditOutcome::Refused { why: why.clone() },
            ),
            SignedAdvance::CommittedButPublicationFailed { outcome, error, .. } => {
                let out = match outcome {
                    Outcome::Landed { receipt, ended } => audit::AuditOutcome::Landed {
                        turn_hash: audit::hex32(&receipt.turn_hash),
                        ended: *ended,
                    },
                    Outcome::Refused(why) => audit::AuditOutcome::Refused { why: why.clone() },
                };
                ("committed", format!("publication_failed:{error}"), out)
            }
            SignedAdvance::HostError(e) => {
                let (kind, reason) = open_audit_parts(e);
                (kind, reason, audit::AuditOutcome::None)
            }
            SignedAdvance::GameRouteRefused(reason) => {
                ("gated", reason.clone(), audit::AuditOutcome::None)
            }
        };
        audit::log().emit(
            signed_audit_event(
                audit::Actor::signed(verified_actor.0.clone(), verified_actor.0.clone()),
                &key,
                &sid,
                audit_detail,
            )
            .decided(kind, reason)
            .with_outcome(out),
        );
    }

    let notice = match outcome {
        SignedAdvance::Advanced {
            outcome: Outcome::Landed { receipt, ended },
            publication,
            ..
        } => format!(
            "Turn committed — {}",
            publication.as_ref().map_or_else(
                || PlayerTurnReceipt::from_landed_signed(
                    &receipt,
                    ended,
                    Custody::UserHeld,
                    verified_actor.0.clone(),
                )
                .compact_text(PlayerReplaySurface::Web),
                |publication| crate::game_session::public_receipt_text(
                    publication,
                    PlayerReplaySurface::Web,
                ),
            )
        ),
        // The signature VERIFIED; the executor refused the move itself — the same anti-ghost
        // banner (and status) the unsigned twin gives a refused move.
        SignedAdvance::Advanced {
            outcome: Outcome::Refused(why),
            ..
        } => {
            format!("Refused: {why} (nothing committed — anti-ghost).")
        }
        SignedAdvance::CommittedButPublicationFailed { error, .. } => format!(
            "Turn committed, but its public receipt card could not be rendered: {error}. Do not retry this command."
        ),
        // A malformed KEY is a request-shape problem (the envelope never named a verifiable
        // signer) — 400, like every other malformation.
        SignedAdvance::HostError(HostError::Signature(e @ SignedError::MalformedKey)) => {
            return (
                StatusCode::BAD_REQUEST,
                format!("signed advance refused: {e}"),
            )
                .into_response();
        }
        // A forged/tampered/spliced signature or a replayed counter is the verifier REFUSING a
        // well-formed envelope: 403, nothing advanced, nothing recorded. Not a server fault.
        SignedAdvance::HostError(HostError::Signature(e)) => {
            return (
                StatusCode::FORBIDDEN,
                format!("signed advance refused: {e}"),
            )
                .into_response();
        }
        SignedAdvance::HostError(
            e @ (HostError::UnknownOffering(_) | HostError::UnknownSession { .. }),
        ) => {
            return (StatusCode::NOT_FOUND, e.to_string()).into_response();
        }
        SignedAdvance::HostError(e @ (HostError::Policy(_) | HostError::ResumeFailed { .. })) => {
            return refused_open_response(&sid, &e);
        }
        SignedAdvance::HostError(e @ HostError::Deploy(_)) => {
            return (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()).into_response();
        }
        SignedAdvance::GameRouteRefused(reason) => {
            return (StatusCode::CONFLICT, reason).into_response();
        }
    };

    // Re-render AS the verified signer (their own per-player projection) through the SAME
    // one-render-path the unsigned twin uses — full page for a plain POST, bare fragment under
    // `X-Fragment: 1`.
    Html(render_offering_response(
        &state,
        &key,
        &sid,
        Some(&notice),
        &verified_actor,
        wants_fragment(&headers),
    ))
    .into_response()
}
