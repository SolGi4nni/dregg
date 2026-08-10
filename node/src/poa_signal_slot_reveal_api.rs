//! **The slot-close opening** — publication of a CLOSED slot's secret, so a player
//! can check the instance they were judged against was fixed before they played.
//!
//! # The declaration this closes
//!
//! Every Path of Angels game descriptor carries, and two independent consumers
//! enforce, a promise about when the per-slot commitment is opened:
//!
//! * `poa/artifacts/poag1/games/*.json` → `instance.commitment.opened_after:
//!   "slot-close"`, required verbatim by `poa-web/src/hidden-instance.js`'s
//!   `loadHiddenInstanceDeclaration` (a descriptor that says anything else is
//!   REFUSED with `instance-commitment`);
//! * `poa/artifacts/poag1/schema.json` → `slot_opening.opened_after_close:
//!   ["slot", "slot_secret"]` beside `verify: "commit(slot_secret, slot) ==
//!   commitment"`, required verbatim by `poa-curator`'s catalog gate
//!   (`poa-curator/src/lib.rs`).
//!
//! Between them those two pin the whole ceremony — WHEN (at slot close), WHAT
//! (the slot and its secret) and the CHECK (`commit(slot_secret, slot)` must equal
//! the commitment the curator signed). Until this module there was no code
//! anywhere that published either value. The commitment was opened by nobody, and
//! `HiddenInstance`'s own docblock said so: the secret is *"committed to before the
//! slot opens, and opened after it closes"*, immediately followed by *"`Emit` has
//! NO function that renders it"*.
//!
//! So the system asserted a property in a signed artifact, refused any descriptor
//! that did not assert it, and supplied no way for anyone to check it.
//!
//! # ⚠ A route that publishes a slot secret ON PURPOSE
//!
//! This is the only surface in the node that renders `PoaInstalledSlotV1::secret`,
//! and it is a sibling module rather than a second handler in
//! `poa_signal_slot_api` precisely so that file's redaction boundary — *"reads
//! `envelope()` and never `secret()`"* — stays literally true and this one stays
//! conspicuous.
//!
//! The secret is safe to publish here and nowhere else, for one reason: the store
//! will only produce it for a slot it can show is **superseded**.
//! `PersistentStore::load_poa_signal_slot_reveal_v1` holds that gate, beside the
//! monotone install that creates the fact, and this handler cannot reach around it
//! — it has no other accessor. A superseded slot cannot settle a run
//! (`blocklace_sync` judges against the OPEN slot), so its secret is the answer to
//! a question nobody can still be asked.
//!
//! The standing question the unauthenticated-router census asks — *can a reader who
//! has never played reconstruct a hidden instance from this?* — is answered YES
//! here, deliberately, and only for slots whose every run has already settled. That
//! is what opening a commitment IS. For the live slot the answer is still no: the
//! route refuses it with `409`.
//!
//! # What a player checks, and why they need not trust this node
//!
//! The document is **self-authenticating**. It carries the curator's original
//! Ed25519 signature over the statement `(authority_id, mission_id, slot,
//! commitment)` — the same bytes published before the slot opened, which the player
//! already holds — plus the secret. A verifier:
//!
//! 1. re-derives the signing message from the STRUCTURED fields (never from a
//!    string this node supplies) and checks the curator signature against the pin;
//! 2. checks the commitment equals the one it retained BEFORE playing;
//! 3. checks `HiddenInstance.commit secret slot == commitment` through Lean;
//! 4. optionally re-derives `HiddenInstance.runSeedFor` for its own player key and
//!    confirms the instance it was served.
//!
//! None of those steps trusts the responder. A hostile relay can withhold or
//! corrupt this document; to forge one it would have to second-preimage a
//! curator-signed commitment (the sponge capacity, ~2^124). The verifier is
//! `dregg-node poa-verify-slot-reveal`, which takes two files and touches neither a
//! database nor a network.
//!
//! # ⚠ What this does NOT establish — read before quoting it
//!
//! * **It does not make the instance unpredictable to the operator.** The curator
//!   draws the secret off-line and knows every instance in the slot in advance;
//!   `operator_knows_instance: true` is declared in every descriptor and the design
//!   gate REQUIRES it to be. Nothing here changes that, and a reveal must never be
//!   described as if it did. Closing it needs a beacon feeding the slot secret —
//!   named as UNDONE WORK in `NightWatchCampaign.lean`, and still absent.
//! * **It does not force publication.** The current slot is never closed, so an
//!   authority that stops opening slots never opens its last one. Withholding is
//!   VISIBLE — this route keeps answering `409 still_open` — but it is not
//!   prevented.
//!
//! What it does establish is the declared property and only that: the instance you
//! were judged against is a function of a secret the curator signed a commitment to
//! at a moment you can pin, so it could not have been adapted to your play.

use axum::Json;
use axum::Router;
use axum::extract::{Path, State};
use axum::http::StatusCode;
use axum::routing::get;
use dregg_types::hex_encode;
use serde::Serialize;

use crate::state::NodeState;

/// Format tag of the reveal document.
pub const POA_SIGNAL_SLOT_REVEAL_FORMAT_V1: &str = "POA-SIGNAL-SLOT-REVEAL-1";

/// Why the node answered the way it did.
///
/// Three distinct strings rather than a bare presence check, because "no such
/// slot" and "that slot is still live" are different facts, and a client that
/// cannot tell them apart cannot tell a typo from a withheld secret. Each is also
/// carried by a distinct HTTP status, so a refusal cannot be mistaken for a
/// success at either layer independently.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum PoaSlotRevealStateV1 {
    /// The slot is closed and `opening` + `slot_secret` are present. `200`.
    Revealed,
    /// The slot is installed but is the live one, or is above it. The secret is
    /// withheld. `409`.
    StillOpen,
    /// No slot with these coordinates is installed for this authority. `404`.
    Unknown,
}

/// The statement the curator signed, in the order a verifier must re-encode it.
///
/// ⚠ Declaration order IS the wire order, for the same reason it is in
/// `poa_signal_slot_api`: `signing_message` is compact key-ordered JSON in exactly
/// this order, and a client that re-derives the bytes in any other order verifies
/// nothing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PoaSlotRevealStatementViewV1 {
    pub schema: &'static str,
    pub authority_id: String,
    pub mission_id: u64,
    pub slot: u64,
    pub commitment: String,
}

/// The curator-signed opening, republished beside the secret that opens it.
///
/// It is repeated here rather than assumed the player kept it so the reveal is a
/// self-contained document — but a verifier must still compare it against the copy
/// it retained BEFORE playing. Checking the secret against a commitment this node
/// supplied at the same time proves only that the node can do arithmetic.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PoaSlotRevealOpeningViewV1 {
    pub statement: PoaSlotRevealStatementViewV1,
    pub curator_key: String,
    pub signature: String,
}

/// `GET /api/poa/signal/{authority}/slot/{slot}/reveal`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PoaSignalSlotRevealResponseV1 {
    pub format: &'static str,
    pub authority_id: String,
    /// The slot that was asked about.
    pub slot: u64,
    pub state: PoaSlotRevealStateV1,
    /// The authority's current open slot, when one exists. Publishing it lets a
    /// reader compute for themselves which slots are closed and therefore which
    /// reveals they are entitled to ask for.
    pub open_slot: Option<u64>,
    /// Present only when `state` is `revealed`.
    pub opening: Option<PoaSlotRevealOpeningViewV1>,
    /// The opened per-slot secret, 32 bytes as lowercase hex. Present only when
    /// `state` is `revealed`.
    pub slot_secret: Option<String>,
    /// Repeated from the sibling Signal views so no reader mistakes this document
    /// for a finality assertion.
    pub consensus_finality: &'static str,
}

pub(crate) fn routes() -> Router<NodeState> {
    Router::new().route(
        "/api/poa/signal/{authority}/slot/{slot}/reveal",
        get(get_poa_signal_slot_reveal),
    )
}

/// Decode a slot coordinate from the path.
///
/// Canonical decimal only — no leading zeroes, so each slot has exactly one URL
/// and attacker-controlled path work stays constant. Unlike
/// `api::parse_poa_signal_sequence` this ACCEPTS zero: nothing in the slot
/// ceremony forbids opening slot 0, and a parser that refused it would make the
/// first slot of an authority permanently unopenable.
fn parse_slot_coordinate(slot: &str) -> Result<u64, StatusCode> {
    if slot.is_empty()
        || slot.len() > 20
        || !slot.bytes().all(|byte| byte.is_ascii_digit())
        || (slot.len() > 1 && slot.starts_with('0'))
    {
        return Err(StatusCode::BAD_REQUEST);
    }
    slot.parse::<u64>().map_err(|_| StatusCode::BAD_REQUEST)
}

/// Open a closed slot, or say precisely why not.
///
/// Observational: it runs no ceremony, derives nothing and writes nothing. The
/// authority selector is the same one every sibling Signal view uses, so the path
/// cannot be pointed at another authority's rows.
async fn get_poa_signal_slot_reveal(
    Path((authority, slot)): Path<(String, String)>,
    State(state): State<NodeState>,
) -> Result<(StatusCode, Json<PoaSignalSlotRevealResponseV1>), StatusCode> {
    let requested = crate::api::parse_poa_signal_authority(&authority)?;
    let slot = parse_slot_coordinate(&slot)?;
    let s = state.read().await;
    let authority_id = crate::api::select_local_poa_signal_authority(
        requested,
        s.federation_configured,
        s.federation_id,
    )?;
    let status = s
        .store
        .load_poa_signal_slot_reveal_v1(authority_id, slot)
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    // The open pointer is published in every answer, including the refusals: a
    // reader who is told "still open" should be able to see what it is open AT
    // without a second request.
    let open_slot = s
        .store
        .load_poa_signal_open_slot_v1(authority_id)
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?
        .map(|installed| installed.slot());
    let authority_id = hex_encode(&authority_id);

    let (code, state_tag, opening, secret) = match status {
        dregg_persist::PoaSlotRevealStatusV1::Revealed(reveal) => (
            StatusCode::OK,
            PoaSlotRevealStateV1::Revealed,
            Some(reveal_opening_view(&reveal)),
            Some(hex_encode(&reveal.secret())),
        ),
        dregg_persist::PoaSlotRevealStatusV1::StillOpen { .. } => (
            StatusCode::CONFLICT,
            PoaSlotRevealStateV1::StillOpen,
            None,
            None,
        ),
        dregg_persist::PoaSlotRevealStatusV1::Unknown => (
            StatusCode::NOT_FOUND,
            PoaSlotRevealStateV1::Unknown,
            None,
            None,
        ),
    };

    Ok((
        code,
        Json(PoaSignalSlotRevealResponseV1 {
            format: POA_SIGNAL_SLOT_REVEAL_FORMAT_V1,
            authority_id,
            slot,
            state: state_tag,
            open_slot,
            opening,
            slot_secret: secret,
            consensus_finality: crate::api::POA_SIGNAL_VIEW_FINALITY_CLAIM,
        }),
    ))
}

/// Project one opened slot into the published document.
fn reveal_opening_view(reveal: &dregg_persist::PoaSlotRevealV1) -> PoaSlotRevealOpeningViewV1 {
    let envelope = reveal.envelope();
    let statement = envelope.statement();
    PoaSlotRevealOpeningViewV1 {
        statement: PoaSlotRevealStatementViewV1 {
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

    const AUTHORITY: [u8; 32] = [0xa4; 32];
    const MISSION_ID: u64 = 1;
    /// The slot that will be CLOSED by opening `LATER_SLOT` on top of it.
    const SLOT: u64 = 9;
    const LATER_SLOT: u64 = 10;
    /// Distinct secrets, so a leak of either is unambiguous about which slot it
    /// came from.
    const SECRET: [u8; 32] = [0x5c; 32];
    const LATER_SECRET: [u8; 32] = [0x7e; 32];

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
    /// the statement with the curator key, and put it through
    /// `install_poa_signal_slot_v1`, which re-checks the signature against the pin
    /// and re-derives the commitment through Lean a second time.
    ///
    /// ⚠ PANICS without the linked Lean archive rather than skipping. A reveal
    /// suite that quietly stopped exercising `HiddenInstance.commit` would be
    /// reporting green for a ceremony whose one cryptographic step never ran.
    async fn install_a_real_slot(state: &NodeState, slot: u64, secret: [u8; 32]) -> [u8; 32] {
        assert!(
            dregg_lean_ffi::poa_slot_derive_ffi::poa_slot_derive_available(),
            "this test requires the linked Lean slot-derivation export; without it the \
             commitment below would be an unchecked number"
        );
        let commitment = crate::poa_signal_slot_ceremony::derive_commitment(secret, slot)
            .expect("Lean must derive the slot commitment");
        let statement = PoaSlotOpeningStatementV1::new(AUTHORITY, MISSION_ID, slot, commitment);
        let key = curator();
        let signature = key.sign(&statement.signing_message().expect("signing message"));
        let envelope = SignedPoaSlotOpeningEnvelopeV1::new(
            statement,
            key.verifying_key().to_bytes(),
            signature.to_bytes(),
        );
        let s = state.write().await;
        // Idempotent: the second call in a test installs the same pin.
        s.store
            .install_poa_world_curator_pin_v1(key.verifying_key().to_bytes())
            .expect("curator pin");
        s.store
            .install_poa_signal_slot_v1(&envelope, secret)
            .expect("a curator-signed opening whose secret opens it must install");
        commitment
    }

    fn reveal_uri(slot: u64) -> String {
        format!(
            "/api/poa/signal/{}/slot/{slot}/reveal",
            hex_encode(&AUTHORITY)
        )
    }

    /// ⚑ **POLE ONE — A LEGITIMATE RUN'S BINDING VERIFIES.**
    ///
    /// Slot 9 is opened, then superseded by slot 10. Slot 9 is now closed, and the
    /// reveal hands back the secret together with the curator signature that was
    /// published before it opened. The secret OPENS the commitment — checked here
    /// by re-deriving through the same Lean export the install used, from the
    /// served hex rather than from the constant.
    #[tokio::test]
    async fn a_closed_slot_is_opened_and_its_secret_verifiably_opens_the_commitment() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = configured_state(tmp.path()).await;
        let commitment = install_a_real_slot(&state, SLOT, SECRET).await;
        install_a_real_slot(&state, LATER_SLOT, LATER_SECRET).await;
        let app = routes().with_state(state);

        let (status, body) = get(&app, &reveal_uri(SLOT)).await;
        assert_eq!(status, StatusCode::OK, "a closed slot must open: {body}");
        assert_eq!(body["format"], POA_SIGNAL_SLOT_REVEAL_FORMAT_V1);
        assert_eq!(body["state"], "revealed");
        assert_eq!(body["slot"], SLOT);
        assert_eq!(body["open_slot"], LATER_SLOT);
        assert_eq!(body["opening"]["statement"]["slot"], SLOT);
        assert_eq!(body["opening"]["statement"]["mission_id"], MISSION_ID);
        assert_eq!(
            body["opening"]["statement"]["commitment"],
            hex_encode(&commitment),
            "the republished commitment must be the one the curator signed"
        );
        assert_eq!(
            body["opening"]["curator_key"],
            hex_encode(&curator().verifying_key().to_bytes())
        );

        // THE CHECK A PLAYER MAKES, run here on the served bytes: the published
        // secret opens the published commitment, through Lean.
        let served_secret = body["slot_secret"].as_str().expect("a revealed secret");
        assert_eq!(served_secret, hex_encode(&SECRET));
        let mut secret = [0u8; 32];
        for (index, byte) in secret.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&served_secret[index * 2..index * 2 + 2], 16)
                .expect("lowercase hex");
        }
        let reopened = crate::poa_signal_slot_ceremony::derive_commitment(secret, SLOT)
            .expect("Lean must re-derive the commitment from the served secret");
        assert_eq!(
            hex_encode(&reopened),
            body["opening"]["statement"]["commitment"],
            "commit(slot_secret, slot) must equal the commitment the curator signed — this \
             is the whole ceremony"
        );
    }

    /// ⚑ **POLE TWO(a) — THE LIVE SLOT IS REFUSED BY NAME.**
    ///
    /// A run whose instance was drawn after the session opened is exactly the
    /// attack a leaked LIVE secret enables: hand out the current slot's secret and
    /// anyone can compute every instance still being played. The open slot must
    /// refuse, and it must refuse with a name a client can act on rather than a
    /// generic error.
    ///
    /// The precondition is asserted before the verdict is read: slot 9 IS
    /// installed and IS the open slot, so the refusal is about closure and not
    /// about the row being missing.
    #[tokio::test]
    async fn the_live_slot_refuses_to_open_and_leaks_no_secret() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = configured_state(tmp.path()).await;
        install_a_real_slot(&state, SLOT, SECRET).await;
        {
            let s = state.read().await;
            let open = s
                .store
                .load_poa_signal_open_slot_v1(AUTHORITY)
                .expect("store read")
                .expect("a slot was installed, so one must be open");
            assert_eq!(
                open.slot(),
                SLOT,
                "the precondition of this test is that slot {SLOT} is the LIVE slot; \
                 without it the refusal below would be about a missing row"
            );
        }
        let app = routes().with_state(state);

        let (status, body) = get(&app, &reveal_uri(SLOT)).await;
        assert_eq!(
            status,
            StatusCode::CONFLICT,
            "the live slot must refuse: {body}"
        );
        assert_eq!(body["state"], "still_open");
        assert!(
            body["slot_secret"].is_null(),
            "a refusal must not carry the secret it refused to serve: {body}"
        );
        assert!(body["opening"].is_null());
        assert_eq!(body["open_slot"], SLOT);

        // The live secret must not appear ANYWHERE in the refusal, not merely in
        // the field that would have held it.
        let rendered = body.to_string();
        assert!(
            !rendered.contains(&hex_encode(&SECRET)),
            "the live slot secret appeared in a refusal body: {rendered}"
        );
    }

    /// ⚑ **POLE TWO(b) — A SWAPPED COMMITMENT IS REFUSED, AND THE MUTATION IS
    /// ASSERTED PRESENT FIRST.**
    ///
    /// The reveal republishes the curator-signed opening. This builds the hostile
    /// document CONSTRUCTIVELY from the honest one — swap the commitment for
    /// another slot's real commitment, assert it actually changed — and shows the
    /// two independent checks a verifier makes both fire: the curator signature no
    /// longer verifies over the re-derived statement, AND the published secret no
    /// longer opens the published commitment.
    ///
    /// Both are checked because either alone would be a weaker gate: a signature
    /// check alone misses a substitution by whoever holds the curator key, and a
    /// commit check alone misses a substitution of BOTH fields together.
    #[tokio::test]
    async fn a_swapped_commitment_fails_both_the_signature_and_the_opening() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = configured_state(tmp.path()).await;
        let honest = install_a_real_slot(&state, SLOT, SECRET).await;
        let foreign = install_a_real_slot(&state, LATER_SLOT, LATER_SECRET).await;
        assert_ne!(
            honest, foreign,
            "the two slots must have different commitments, or the swap below is a no-op"
        );
        let app = routes().with_state(state);

        let (status, body) = get(&app, &reveal_uri(SLOT)).await;
        assert_eq!(status, StatusCode::OK);
        let honest_commitment = body["opening"]["statement"]["commitment"]
            .as_str()
            .expect("commitment")
            .to_owned();
        assert_eq!(honest_commitment, hex_encode(&honest));

        // THE MUTATION, asserted present before any verdict is read.
        let swapped = hex_encode(&foreign);
        assert_ne!(
            swapped, honest_commitment,
            "the mutation must actually change the commitment, or this test asserts nothing"
        );

        // (1) The curator signature is over the statement bytes, so a swapped
        //     commitment re-derives a different message and fails. This is exactly
        //     the check a client makes: rebuild the message from the STRUCTURED
        //     fields, never from a pre-encoded string the responder supplied.
        let mut signature = [0u8; 64];
        let served = body["opening"]["signature"].as_str().expect("signature");
        for (index, byte) in signature.iter_mut().enumerate() {
            *byte =
                u8::from_str_radix(&served[index * 2..index * 2 + 2], 16).expect("lowercase hex");
        }
        let signature = ed25519_dalek::Signature::from_bytes(&signature);
        let pin = curator().verifying_key();
        let swapped_message = PoaSlotOpeningStatementV1::new(AUTHORITY, MISSION_ID, SLOT, foreign)
            .signing_message()
            .expect("signing message");
        assert!(
            pin.verify_strict(&swapped_message, &signature).is_err(),
            "a swapped commitment under the honest signature must fail verification"
        );
        // ...and the honest statement under the same signature still verifies, or
        // the refusal above would be about a broken signature rather than the swap.
        let honest_message = PoaSlotOpeningStatementV1::new(AUTHORITY, MISSION_ID, SLOT, honest)
            .signing_message()
            .expect("signing message");
        assert!(
            pin.verify_strict(&honest_message, &signature).is_ok(),
            "the served signature must be a real curator signature over the honest statement"
        );

        // (2) And independently: the published secret does not open the swapped
        //     commitment. This is the check that still fires if the swap were made
        //     by whoever holds the curator key.
        let reopened = crate::poa_signal_slot_ceremony::derive_commitment(SECRET, SLOT)
            .expect("Lean must derive");
        assert_ne!(
            hex_encode(&reopened),
            swapped,
            "the published secret must NOT open a commitment it was not committed to"
        );
        assert_eq!(
            hex_encode(&reopened),
            honest_commitment,
            "...while still opening the honest one, or the refusal above proves nothing"
        );
    }

    /// A slot nobody installed is `unknown`, not `still_open` — a client must be
    /// able to tell a typo from a withheld secret.
    #[tokio::test]
    async fn an_uninstalled_slot_is_unknown_rather_than_withheld() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = configured_state(tmp.path()).await;
        install_a_real_slot(&state, SLOT, SECRET).await;
        install_a_real_slot(&state, LATER_SLOT, LATER_SECRET).await;
        let app = routes().with_state(state);

        let (status, body) = get(&app, &reveal_uri(4)).await;
        assert_eq!(status, StatusCode::NOT_FOUND);
        assert_eq!(body["state"], "unknown");
        assert!(body["slot_secret"].is_null());
        // Even for an unknown slot the open pointer is published, so a reader can
        // work out which coordinates are worth asking for.
        assert_eq!(body["open_slot"], LATER_SLOT);
    }

    /// Before any ceremony there is no pointer at all, and every slot is `unknown`
    /// rather than revealed. The fail-closed path when the store is empty.
    #[tokio::test]
    async fn an_authority_with_no_slots_reveals_nothing() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = configured_state(tmp.path()).await;
        let app = routes().with_state(state);

        let (status, body) = get(&app, &reveal_uri(SLOT)).await;
        assert_eq!(status, StatusCode::NOT_FOUND);
        assert_eq!(body["state"], "unknown");
        assert!(body["open_slot"].is_null());
        assert!(body["slot_secret"].is_null());
    }

    /// The selector is the same one every sibling Signal view uses: this route
    /// cannot be pointed at another authority's rows, and a non-canonical slot
    /// coordinate is refused rather than normalised.
    #[tokio::test]
    async fn a_foreign_authority_or_a_non_canonical_slot_is_refused() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let state = configured_state(tmp.path()).await;
        install_a_real_slot(&state, SLOT, SECRET).await;
        install_a_real_slot(&state, LATER_SLOT, LATER_SECRET).await;
        let app = routes().with_state(state);

        let foreign = hex_encode(&[0xb7u8; 32]);
        assert_ne!(foreign, hex_encode(&AUTHORITY));
        let (status, _) = get(&app, &format!("/api/poa/signal/{foreign}/slot/9/reveal")).await;
        assert_eq!(status, StatusCode::BAD_REQUEST);

        let authority = hex_encode(&AUTHORITY);
        // A leading zero is a second URL for the same slot; refuse it.
        let (status, _) = get(&app, &format!("/api/poa/signal/{authority}/slot/09/reveal")).await;
        assert_eq!(status, StatusCode::BAD_REQUEST);
        let (status, _) = get(&app, &format!("/api/poa/signal/{authority}/slot/x9/reveal")).await;
        assert_eq!(status, StatusCode::BAD_REQUEST);
        // ...and the honest coordinate still works, or the three refusals above
        // would pass for a reason unrelated to the spelling.
        let (status, _) = get(&app, &reveal_uri(SLOT)).await;
        assert_eq!(status, StatusCode::OK);
    }

    /// Slot 0 is openable, so it must be revealable. `parse_slot_coordinate`
    /// deliberately differs from `api::parse_poa_signal_sequence` here, and this is
    /// the test that would fail if someone "unified" them.
    #[test]
    fn slot_zero_is_a_valid_coordinate() {
        assert_eq!(parse_slot_coordinate("0"), Ok(0));
        assert_eq!(parse_slot_coordinate("9"), Ok(9));
        assert!(parse_slot_coordinate("00").is_err());
        assert!(parse_slot_coordinate("").is_err());
    }
}
