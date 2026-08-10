//! Publication of the curator-signed Signal slot opening.
//!
//! # The thing this closes
//!
//! `poa_signal_slot_ceremony` opens a slot; `persist::poa_signal_slot` stores it;
//! `blocklace_sync` refuses to judge a scored run unless one is open. Between the
//! store and the player there was **nothing**. No route, export, descriptor or
//! manifest field said "a slot is open, here is the commitment, here is the
//! curator signature over it" — so:
//!
//! * a client could not tell a node that can settle a run from one that cannot,
//!   which makes every game in the browser permanently PRACTICE; and
//! * the slot commitment bound nothing. `poa_signal_slot_ceremony`'s own doctrine
//!   says it plainly — *"Installing the secret is not publication. The signed
//!   opening must reach players BEFORE they play, or the commitment binds nothing:
//!   a commitment revealed afterwards is compatible with any instance the operator
//!   likes."* Without a publication surface the commitment was a private note the
//!   node kept to itself, and the honest description of judged play was "trust the
//!   operator", not "the operator committed in advance".
//!
//! # What it exposes, field by field
//!
//! Standing question for every field: *can a reader who has not played reconstruct
//! the instance from this?*
//!
//! | field | why it is safe to publish |
//! |---|---|
//! | `slot`, `mission_id` | public coordinates; they name a slot, not a run |
//! | `commitment` | `HiddenInstance.commit secret slot` — a function of the secret and the slot ALONE. It takes no player and no mission, so it says nothing about any particular run. It is also the ONE field publication exists for. Inverting it is the sponge capacity, ~2^124 — not 2^248 |
//! | `curator_key` | already public: it is the pin the content bundle is signed under, and `install_poa_signal_slot_v1` refuses any envelope naming a different one, so this is provably the installed pin |
//! | `signature` | the curator's Ed25519 over the statement. Publishing a signature is the point of having one |
//!
//! And what it does NOT carry, deliberately:
//!
//! * **`secret`** — WHILE THE SLOT IS LIVE. (Once it closes, the sibling
//!   `poa_signal_slot_reveal_api` publishes it on purpose: an unopened commitment
//!   is one no player can check. That route serves only superseded slots and
//!   refuses this one, so the redaction below is unchanged for everything this
//!   route can reach.) The run seed is `runSeedFor ⟨secret, slot, playerKey⟩`, and the
//!   target is three modulo ops from the run seed. The secret is the answer to
//!   every run in the slot. [`slot_publication_never_carries_the_secret`] builds
//!   the response from the live encoder with a known secret installed and fails if
//!   those bytes appear anywhere in it.
//! * **`run_seed` / `target`** — per player, derived only inside the Lean judge.
//! * **the pre-encoded signing message.** This is the one that looks like a
//!   convenience and is not. If the response carried the exact bytes the signature
//!   covers, a client could verify the signature against THOSE bytes and never
//!   check that they encode the statement beside them — so a node could serve
//!   statement `S` next to a valid signature over a different statement `S'` and a
//!   verifying client would report "curator-signed" for `S`. A client must
//!   re-derive the message from the structured fields, which is exactly the rule
//!   `poa-curator`'s signer applies to itself on the other side of the ceremony.
//!   The encoding it must reproduce is pinned in
//!   [`the_message_a_client_must_rederive_is_the_documented_encoding`] and in
//!   `PoaSlotOpeningStatementV1::signing_message`:
//!
//!   ```text
//!   {"schema":"POA-SLOT-OPENING-STATEMENT-1","authority_id":"<hex32>","mission_id":<n>,"slot":<n>,"commitment":"<hex32>"}
//!   ```
//!
//! # What it does not claim
//!
//! `open: true` says a curator-signed opening for this authority is installed and
//! that the store checked the signature against its pin and the secret against the
//! commitment by calling Lean. It is not a finality claim, and it is not a promise
//! that a run will settle: the judge re-derives the commitment on every single run
//! and refuses on mismatch.

use axum::Json;
use axum::Router;
use axum::extract::{Path, State};
use axum::http::StatusCode;
use axum::routing::get;
use dregg_types::hex_encode;
use serde::Serialize;

use crate::state::NodeState;

/// Format tag of the publication document.
pub const POA_SIGNAL_SLOT_FORMAT_V1: &str = "POA-SIGNAL-SLOT-1";

/// The statement the curator signed, spelled exactly as
/// `PoaSlotOpeningStatementV1::signing_message` spells it.
///
/// ⚠ **The field order of this struct is the order a client must re-encode in.**
/// It is not style. `signing_message` is compact, key-ordered JSON in exactly this
/// order, and a client that re-derives the bytes in any other order verifies
/// nothing. A `#[derive(Serialize)]` emits declaration order unconditionally;
/// `serde_json::json!` would only preserve it via the undeclared `preserve_order`
/// feature, which is how this wire would become an accident of the dependency
/// graph.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PoaSlotOpeningStatementViewV1 {
    pub schema: &'static str,
    pub authority_id: String,
    pub mission_id: u64,
    pub slot: u64,
    pub commitment: String,
}

/// One curator-signed slot opening, as published.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PoaSignalSlotOpeningViewV1 {
    pub statement: PoaSlotOpeningStatementViewV1,
    /// The curator public key. `install_poa_signal_slot_v1` refuses an envelope
    /// whose key is not the store's installed pin, so this IS the pin.
    pub curator_key: String,
    /// Ed25519 over the re-derived statement bytes, 64 bytes as lowercase hex.
    pub signature: String,
}

/// `GET /api/poa/signal/{authority}/slot`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PoaSignalSlotResponseV1 {
    pub format: &'static str,
    pub authority_id: String,
    pub federation_id: String,
    /// Whether a curator-signed opening is installed for this authority.
    ///
    /// `false` is the honest and common answer: a node with no open slot cannot
    /// settle a scored run at all, and a client reading `false` must present
    /// practice and only practice.
    pub open: bool,
    pub opening: Option<PoaSignalSlotOpeningViewV1>,
    /// Repeated from the sibling Signal views so no reader mistakes this document
    /// for a finality assertion.
    pub consensus_finality: &'static str,
}

pub(crate) fn routes() -> Router<NodeState> {
    Router::new().route("/api/poa/signal/{authority}/slot", get(get_poa_signal_slot))
}

/// Publish the open slot, or say plainly that there is none.
///
/// Observational: it opens no ceremony, derives nothing, and writes nothing. The
/// authority selector is the same one the sibling Signal views use — the path
/// component must equal this node's configured federation, so the route cannot be
/// used to enumerate authority rows in a shared store.
async fn get_poa_signal_slot(
    Path(authority): Path<String>,
    State(state): State<NodeState>,
) -> Result<Json<PoaSignalSlotResponseV1>, StatusCode> {
    let requested = crate::api::parse_poa_signal_authority(&authority)?;
    let s = state.read().await;
    let authority_id = crate::api::select_local_poa_signal_authority(
        requested,
        s.federation_configured,
        s.federation_id,
    )?;
    let installed = s
        .store
        .load_poa_signal_open_slot_v1(authority_id)
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    let normalized_authority = hex_encode(&authority_id);
    Ok(Json(PoaSignalSlotResponseV1 {
        format: POA_SIGNAL_SLOT_FORMAT_V1,
        authority_id: normalized_authority.clone(),
        federation_id: normalized_authority,
        open: installed.is_some(),
        opening: installed.as_ref().map(slot_opening_view),
        consensus_finality: crate::api::POA_SIGNAL_VIEW_FINALITY_CLAIM,
    }))
}

/// Project one installed slot into the published document.
///
/// ⚠ This function is the whole redaction boundary. It reads `envelope()` and
/// never `secret()`, and `PoaInstalledSlotV1` has exactly those two parts — so the
/// secret cannot reach the wire without an edit here.
fn slot_opening_view(installed: &dregg_persist::PoaInstalledSlotV1) -> PoaSignalSlotOpeningViewV1 {
    let envelope = installed.envelope();
    let statement = envelope.statement();
    PoaSignalSlotOpeningViewV1 {
        statement: PoaSlotOpeningStatementViewV1 {
            schema: dregg_persist::POA_SLOT_OPENING_STATEMENT_SCHEMA_V1,
            authority_id: hex_encode(&statement.authority_id()),
            mission_id: statement.mission_id(),
            slot: statement.slot(),
            commitment: hex_encode(&statement.commitment()),
        },
        curator_key: hex_encode(&envelope.curator_key()),
        signature: hex_encode(envelope.signature()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::Request;
    use dregg_persist::{PoaSlotOpeningStatementV1, SignedPoaSlotOpeningEnvelopeV1};
    use ed25519_dalek::{Signer as _, SigningKey};
    use http_body_util::BodyExt as _;
    use tower::ServiceExt as _;

    /// ⚠ Deliberately a byte with a hex LETTER in it. The first spelling of this
    /// fixture was `[0x41; 32]` — `"4141…"` — and the case-sensitivity check below
    /// uppercased it into *itself*, so the hostile input equalled the honest one
    /// and the route answered 200 to what the test called a malformed selector.
    /// A falsifier over a spelling needs a value the spelling can actually change.
    const AUTHORITY: [u8; 32] = [0xa4; 32];
    const MISSION_ID: u64 = 1;
    const SLOT: u64 = 9;
    /// The secret this test installs. Every byte is distinct from the curator seed
    /// so a leak of either is unambiguous.
    const SECRET: [u8; 32] = [0x5c; 32];

    fn curator() -> SigningKey {
        SigningKey::from_bytes(&[0xc0; 32])
    }

    async fn configured_state(tmp: &std::path::Path) -> NodeState {
        let state = NodeState::new(tmp, vec![]).expect("node state");
        {
            let mut s = state.write().await;
            s.federation_id = AUTHORITY;
            s.federation_configured = true;
        }
        state
    }

    async fn get(app: &Router, uri: &str) -> (StatusCode, serde_json::Value) {
        let response = app
            .clone()
            .oneshot(
                Request::builder()
                    .uri(uri)
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("response");
        let status = response.status();
        let bytes = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();
        let json = if bytes.is_empty() {
            serde_json::Value::Null
        } else {
            serde_json::from_slice(&bytes).expect("json body")
        };
        (status, json)
    }

    /// Run the REAL install: derive the commitment through the Lean export, sign
    /// the statement with a curator key, and put it through
    /// `install_poa_signal_slot_v1` — which re-checks the signature against the
    /// installed pin and re-derives the commitment through Lean a second time.
    ///
    /// ⚠ This PANICS without the linked Lean archive rather than skipping. A test
    /// that quietly stopped exercising the commitment check would report green for
    /// a publication surface publishing a commitment nobody checked.
    async fn install_a_real_slot(state: &NodeState) -> [u8; 32] {
        assert!(
            dregg_lean_ffi::poa_slot_derive_ffi::poa_slot_derive_available(),
            "this test requires the linked Lean slot-derivation export; without it the \
             commitment below would be an unchecked number"
        );
        let commitment = crate::poa_signal_slot_ceremony::derive_commitment(SECRET, SLOT)
            .expect("Lean must derive the slot commitment");
        let statement = PoaSlotOpeningStatementV1::new(AUTHORITY, MISSION_ID, SLOT, commitment);
        let key = curator();
        let signature = key.sign(&statement.signing_message().expect("signing message"));
        let envelope = SignedPoaSlotOpeningEnvelopeV1::new(
            statement,
            key.verifying_key().to_bytes(),
            signature.to_bytes(),
        );
        let s = state.write().await;
        s.store
            .install_poa_world_curator_pin_v1(key.verifying_key().to_bytes())
            .expect("curator pin");
        s.store
            .install_poa_signal_slot_v1(&envelope, SECRET)
            .expect("a curator-signed opening whose secret opens it must install");
        commitment
    }

    /// Before any ceremony the route answers, and it answers "no".
    ///
    /// This is the state every node is in until a curator opens a slot, and a
    /// client reading it must show practice only.
    #[tokio::test]
    async fn an_unopened_slot_is_published_as_closed_not_as_an_error() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = configured_state(tmp.path()).await;
        let app = routes().with_state(state);
        let authority = hex_encode(&AUTHORITY);

        let (status, body) = get(&app, &format!("/api/poa/signal/{authority}/slot")).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(body["format"], POA_SIGNAL_SLOT_FORMAT_V1);
        assert_eq!(body["authority_id"], authority);
        assert_eq!(body["federation_id"], authority);
        assert_eq!(body["open"], false);
        assert!(body["opening"].is_null());
    }

    /// The selector is the same one the sibling Signal views use: this route
    /// cannot be pointed at another authority's rows.
    #[tokio::test]
    async fn the_authority_selector_admits_only_this_node_s_federation() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = configured_state(tmp.path()).await;
        let app = routes().with_state(state);

        let canonical = hex_encode(&AUTHORITY);
        let shouting = canonical.to_uppercase();
        assert_ne!(
            shouting, canonical,
            "the case falsifier must actually change the selector it sends"
        );

        for path in [
            "/api/poa/signal/not-hex/slot".to_string(),
            format!("/api/poa/signal/{}/slot", hex_encode(&[0x42; 32])),
            format!("/api/poa/signal/{shouting}/slot"),
        ] {
            let (status, _) = get(&app, &path).await;
            assert_eq!(status, StatusCode::BAD_REQUEST, "must refuse: {path}");
        }

        // …and the canonical spelling of the same bytes is served, so the refusals
        // above are about the SPELLING and not about the route being closed.
        let (status, _) = get(&app, &format!("/api/poa/signal/{canonical}/slot")).await;
        assert_eq!(status, StatusCode::OK);
    }

    /// A discovery-mode node has no authority to publish and says 503 rather than
    /// inventing an empty one.
    #[tokio::test]
    async fn an_unconfigured_node_publishes_nothing() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(tmp.path(), vec![]).expect("node state");
        let app = routes().with_state(state);
        let (status, _) = get(
            &app,
            &format!("/api/poa/signal/{}/slot", hex_encode(&AUTHORITY)),
        )
        .await;
        assert_eq!(status, StatusCode::SERVICE_UNAVAILABLE);
    }

    /// The published document is the installed envelope, and a client that
    /// re-derives the statement bytes can verify the curator signature over them.
    ///
    /// The verification here is deliberately performed the way a browser must
    /// perform it — re-encode from the published structured fields, then verify —
    /// rather than by handing `signing_message()` its own output.
    #[tokio::test]
    async fn a_published_opening_verifies_under_a_client_side_rederivation() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = configured_state(tmp.path()).await;
        let commitment = install_a_real_slot(&state).await;
        let app = routes().with_state(state);
        let authority = hex_encode(&AUTHORITY);

        let (status, body) = get(&app, &format!("/api/poa/signal/{authority}/slot")).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(body["open"], true);
        let opening = &body["opening"];
        assert_eq!(
            opening["statement"]["schema"],
            dregg_persist::POA_SLOT_OPENING_STATEMENT_SCHEMA_V1
        );
        assert_eq!(opening["statement"]["authority_id"], authority);
        assert_eq!(opening["statement"]["mission_id"], MISSION_ID);
        assert_eq!(opening["statement"]["slot"], SLOT);
        assert_eq!(opening["statement"]["commitment"], hex_encode(&commitment));
        assert_eq!(
            opening["curator_key"],
            hex_encode(&curator().verifying_key().to_bytes())
        );

        // ── the client half ──────────────────────────────────────────────────
        let rederived = client_rederived_message(opening);
        let key = ed25519_dalek::VerifyingKey::from_bytes(
            &dregg_types::parse_hex32(opening["curator_key"].as_str().expect("curator key"))
                .expect("curator key hex"),
        )
        .expect("published curator key is a valid Ed25519 key");
        let signature = ed25519_dalek::Signature::from_bytes(&client_hex64(
            opening["signature"].as_str().expect("signature"),
        ));
        key.verify_strict(rederived.as_bytes(), &signature)
            .expect("a client that re-derives the statement must be able to verify it");

        // ── the falsifier, built from the same live document ─────────────────
        // Constructed by mutating the SERVED commitment, so the hostile input is
        // this response and not a hand-written neighbour. The mutation is asserted
        // BEFORE the verdict is read: an encoder change that made these bytes equal
        // would otherwise turn this check into a no-op that still passes.
        let mut forged = opening.clone();
        let mut bytes = dregg_types::parse_hex32(
            opening["statement"]["commitment"]
                .as_str()
                .expect("commitment"),
        )
        .expect("commitment hex");
        bytes[0] ^= 0x01;
        forged["statement"]["commitment"] = serde_json::Value::String(hex_encode(&bytes));
        let forged_message = client_rederived_message(&forged);
        assert_ne!(
            forged_message, rederived,
            "the falsifier did not change the bytes it verifies; it would pass vacuously"
        );
        assert!(
            key.verify_strict(forged_message.as_bytes(), &signature)
                .is_err(),
            "a one-bit commitment change must break the curator signature"
        );
    }

    /// The secret is the answer to every run in the slot. It must not be anywhere
    /// in the published bytes — not in a field, not in a nested object, not in a
    /// stray debug spelling.
    #[tokio::test]
    async fn slot_publication_never_carries_the_secret() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = configured_state(tmp.path()).await;
        install_a_real_slot(&state).await;
        let app = routes().with_state(state.clone());
        let authority = hex_encode(&AUTHORITY);

        let response = app
            .oneshot(
                Request::builder()
                    .uri(format!("/api/poa/signal/{authority}/slot"))
                    .body(Body::empty())
                    .expect("request"),
            )
            .await
            .expect("response");
        let served = response
            .into_body()
            .collect()
            .await
            .expect("body")
            .to_bytes();

        // Prove the stored record really does hold this secret, so the search below
        // is looking for something that exists rather than for a value that was
        // never installed.
        {
            let s = state.read().await;
            let stored = s
                .store
                .load_poa_signal_open_slot_v1(AUTHORITY)
                .expect("load")
                .expect("a slot is installed");
            assert_eq!(
                stored.secret(),
                SECRET,
                "the fixture must have installed the secret it then searches for"
            );
        }

        let secret_hex = hex_encode(&SECRET);
        let served_text = String::from_utf8(served.to_vec()).expect("utf-8 body");
        assert!(
            !served_text.contains(&secret_hex),
            "the published slot document contains the slot secret: {served_text}"
        );
        assert!(
            !served_text.to_lowercase().contains("secret"),
            "the published slot document names a secret field: {served_text}"
        );
        assert!(
            !served.windows(SECRET.len()).any(|w| w == SECRET),
            "the published slot document contains the raw secret bytes"
        );
    }

    /// Two independent spellings of the bytes a client must re-derive: this
    /// function (the client's), and `PoaSlotOpeningStatementV1::signing_message`
    /// (the node's). They must agree, and this pins the shape against a literal so
    /// a drift in either stops here rather than silently invalidating every
    /// previously signed opening.
    #[test]
    fn the_message_a_client_must_rederive_is_the_documented_encoding() {
        let statement = PoaSlotOpeningStatementV1::new(AUTHORITY, MISSION_ID, SLOT, [0xbc; 32]);
        let view = serde_json::to_value(PoaSlotOpeningStatementViewV1 {
            schema: dregg_persist::POA_SLOT_OPENING_STATEMENT_SCHEMA_V1,
            authority_id: hex_encode(&AUTHORITY),
            mission_id: MISSION_ID,
            slot: SLOT,
            commitment: hex_encode(&[0xbc; 32]),
        })
        .expect("view json");

        let expected = format!(
            "{{\"schema\":\"POA-SLOT-OPENING-STATEMENT-1\",\"authority_id\":\"{}\",\
             \"mission_id\":{MISSION_ID},\"slot\":{SLOT},\"commitment\":\"{}\"}}",
            "a4".repeat(32),
            "bc".repeat(32)
        );
        assert_eq!(client_rederived_message(&view), expected);
        assert_eq!(
            String::from_utf8(statement.signing_message().expect("signing message"))
                .expect("utf-8"),
            expected
        );
    }

    /// Decode the published 64-byte signature the way a client would, refusing any
    /// spelling that is not exactly 128 lowercase hex digits.
    fn client_hex64(spelling: &str) -> [u8; 64] {
        assert_eq!(spelling.len(), 128, "signature must be 128 hex digits");
        let mut out = [0u8; 64];
        for (index, byte) in out.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&spelling[index * 2..index * 2 + 2], 16)
                .expect("signature is lowercase hex");
        }
        assert!(
            spelling
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
            "signature must be lowercase hex"
        );
        out
    }

    /// Exactly what a browser has to do with the published document: rebuild the
    /// canonical statement bytes from the structured fields. Nothing here reads a
    /// pre-encoded message, because the route deliberately does not serve one.
    fn client_rederived_message(opening: &serde_json::Value) -> String {
        let statement = if opening.get("statement").is_some() {
            &opening["statement"]
        } else {
            opening
        };
        format!(
            "{{\"schema\":\"{}\",\"authority_id\":\"{}\",\"mission_id\":{},\"slot\":{},\
             \"commitment\":\"{}\"}}",
            statement["schema"].as_str().expect("schema"),
            statement["authority_id"].as_str().expect("authority_id"),
            statement["mission_id"].as_u64().expect("mission_id"),
            statement["slot"].as_u64().expect("slot"),
            statement["commitment"].as_str().expect("commitment"),
        )
    }
}
