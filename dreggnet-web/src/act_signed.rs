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
    GameActionRef, GameAffordance, GameAudience, GameHostIncarnation, GameResult, GameSessionRef,
    PublicGameReceipt, execute_bound_signed_game_turn_with_outcome, game_kind,
    inspect_bound_game_session, project_public_game_receipt,
};
use dreggnet_offerings::player_turn_receipt::{PlayerReplaySurface, PlayerTurnReceipt};
use dreggnet_offerings::{
    Action, Attribution, DreggIdentity, HostError, OfferingHost, Outcome, SessionId, SignedAction,
    SignedError,
};

use crate::{
    CatalogState, audit, game_epoch_refusal_response, open_audit_parts, refused_open_response,
    render_offering_response, wants_fragment,
};

pub(crate) enum SignedAdvance {
    Advanced {
        outcome: Outcome,
        publication: Option<PublicGameReceipt>,
    },
    HostError(HostError),
    GameRouteRefused(String),
}

/// Resolve one already-formed signed action through the authority-bound game
/// spine, or retain the legacy host path for non-game offerings. Telegram and
/// Discord call this from the same atomic host job that allocates their
/// custodial counter, so all signed surfaces share the exact routing and
/// viewer-blind publication boundary.
pub(crate) fn advance_signed_on_host(
    host: &mut OfferingHost,
    key: String,
    sid: SessionId,
    viewer: DreggIdentity,
    game_context: Option<(GameHostIncarnation, u64, GameSessionRef)>,
    signed: SignedAction,
) -> SignedAdvance {
    if let Some((incarnation, generation, session)) = game_context {
        let view = match inspect_bound_game_session(
            host,
            incarnation,
            generation,
            session.clone(),
            &GameAudience::AssertedPrivate(viewer),
        ) {
            Ok(view) => view,
            Err(error) => return SignedAdvance::GameRouteRefused(error.to_string()),
        };
        if !view.affordances.iter().any(|affordance| {
            matches!(
                affordance,
                GameAffordance::Turn { action, .. } if action.turn == signed.action.turn
            )
        }) {
            return SignedAdvance::GameRouteRefused(
                "signed turn is not a current viewer affordance".to_string(),
            );
        }
        let reference =
            GameActionRef::new(session.clone(), &signed.action, view.surface_commitment);
        return match execute_bound_signed_game_turn_with_outcome(
            host,
            incarnation,
            generation,
            &session,
            reference,
            signed,
        ) {
            Ok(execution) => {
                let publication = match &execution.result {
                    GameResult::Landed(receipt) => match project_public_game_receipt(receipt) {
                        Ok(publication) => Some(publication),
                        Err(error) => {
                            return SignedAdvance::GameRouteRefused(error.to_string());
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
        };
    }
    match host.advance_signed(&key, &sid, signed) {
        Ok(outcome) => SignedAdvance::Advanced {
            outcome,
            publication: None,
        },
        Err(error) => SignedAdvance::HostError(error),
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

/// **Decode the JSON wire into the [`SignedAction`] the host verifies** — hex + counter/arg
/// parsing, `400` with a named reason on any malformation. No crypto happens here; a decoded
/// envelope is merely WELL-FORMED, and only [`advance_signed`
/// ](dreggnet_offerings::OfferingHost::advance_signed) can admit it.
pub fn decode(wire: SignedActionWire) -> Result<SignedAction, (StatusCode, String)> {
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

    Ok(SignedAction {
        action,
        actor_pubkey_hex: wire.actor_pubkey_hex,
        counter,
        signature,
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
    let sa = match decode(wire) {
        Ok(sa) => sa,
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

    // The claimed signer, canonicalized — the render viewer on success, and the ADVISORY opener
    // attribution (`Asserted`: nothing is verified yet; verification is advance_signed's job, and
    // the unsigned twin's cookie label is exactly as forgeable — capacity/TTL are the backstops).
    let claimed = sa.actor_pubkey_hex.to_ascii_lowercase();
    // The PUBLIC wire material for the audit envelope (captured before `sa` moves into the
    // host job): turn/arg/counter — the signature itself is public too, but the join needs
    // only the signed intent.
    let audit_detail = serde_json::json!({
        "turn": sa.action.turn,
        "arg": sa.action.arg,
        "counter": sa.counter,
    });

    // The signer's derived identity — for an RPG key this selects the signer's OWN per-identity
    // world (their isolated inventory); a shared table ignores it (one host for everyone).
    let viewer = DreggIdentity(claimed.clone());
    // Ensure open first (lazily, lifecycle-aware) — mirroring the unsigned POST: a policy refusal
    // is an honest 4xx, an evicted persisted session resumes, an unknown offering is a 404.
    let opened = {
        let k = key.clone();
        let sid = sid.clone();
        let opener = Attribution::Asserted {
            label: claimed.clone(),
        };
        state.run_offering(&key, &viewer, move |h| {
            h.ensure_open_as(&k, &sid, Some(&opener))
        })
    };
    let newly_opened = match opened {
        Ok(newly_opened) => newly_opened,
        Err(HostError::UnknownOffering(k)) => {
            audit::log().emit(
                signed_audit_event(
                    audit::Actor::signed(claimed.clone(), claimed),
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
                    audit::Actor::signed(claimed.clone(), claimed),
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
    };
    if let Err(error) = state.bind_game_after_open(&key, &sid, newly_opened) {
        return game_epoch_refusal_response(&sid, &error);
    }

    // ONE signature-verified turn on the host thread: verify (key/session/counter-bound) →
    // consume the counter → the executor referees the move → a landed turn records with
    // `Attribution::Signed` provenance.
    let game_context = if game_kind(&key).is_some() {
        match state.game_epoch_context(&key, &sid) {
            Ok(context) => Some(context),
            Err(error) => return game_epoch_refusal_response(&sid, &error),
        }
    } else {
        None
    };
    let routed_key = key.clone();
    let routed_sid = sid.clone();
    let routed_viewer = viewer.clone();
    let outcome = state.run_offering(&key, &viewer, move |h| {
        advance_signed_on_host(h, routed_key, routed_sid, routed_viewer, game_context, sa)
    });

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
                audit::Actor::signed(claimed.clone(), claimed.clone()),
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
        } => format!(
            "Turn committed — {}",
            publication.as_ref().map_or_else(
                || PlayerTurnReceipt::from_landed(&receipt, ended)
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
    let viewer = DreggIdentity(claimed);
    Html(render_offering_response(
        &state,
        &key,
        &sid,
        Some(&notice),
        &viewer,
        wants_fragment(&headers),
    ))
    .into_response()
}
