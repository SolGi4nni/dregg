//! The Lean-authored Descent, driven through its frontend-neutral Offering in a browser.
//!
//! This is intentionally separate from [`crate::bindings_descent::DescentWorld`], which
//! wraps the older, Rust-authored daily/procgen game. [`NativeDescentWorld`] owns the actual
//! [`NativeDescentOffering`]: its installed program is loaded from Lean-emitted
//! `dungeon_program.json`, and every browser action crosses the same
//! [`Offering::advance`] boundary as Discord, Telegram, and the generic web host. This
//! module only translates wasm strings/JSON into that API; it does not mirror a game rule.
//!
//! A portable record contains the action tape, complete serialized executor receipts,
//! exact post-states, journal roots, checkpoint, and terminal settlement. Import treats all
//! of it as untrusted: it opens a fresh session, replays each action through the Offering,
//! and accepts only if the complete record reproduces byte-for-byte. The record is therefore
//! suitable input for a later opt-in board publisher without making publication implicit in
//! private, in-tab play.
//!
//! ## wasm assurance boundary
//!
//! `wasm32` cannot link the native Lean library. The wasm graph's existing `no-lean-link`
//! platform feature still installs the checked-in Lean-emitted program in the real embedded
//! executor, but does not run the native Lean differential at browser runtime. Native/CI
//! validation of that artifact remains the assurance bridge.
//!
//! This low-level binding accepts the opaque [`DreggIdentity`] string supplied by its host.
//! It binds a session to that value but does not authenticate ownership of it; a production
//! page must derive/authenticate the identity (or verify a signed submission) before calling
//! [`NativeDescentWorld::advance`]. Likewise, export is replay material rather than a node
//! anchor or succinct proof; those belong to the later opt-in publication boundary.

use serde::Serialize;
use wasm_bindgen::prelude::*;

use dreggnet_offerings::native_descent::{
    NativeDescentOffering, NativeDescentRecord, NativeDescentSession,
};
// ⚑ THE WIRE IS NOT DECLARED HERE. `dreggnet_offerings::native_descent_wire` owns the portable
// record's one and only Rust type + its one exact-replay gate; this binding is the browser
// PRODUCER of that type, and `dreggnet-web` is the server CONSUMER of the same type. The
// hand-mirrored pair these two crates used to keep in step is deleted — which is what stopped
// `banked_notes` from crossing at all.
use dreggnet_offerings::native_descent_wire::{
    MAX_PORTABLE_RECORD_BYTES, PortableCheckpoint, PortableCompletion, PortableRecord, PortableSim,
    replay_portable_record,
};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig, VerifyReport};
use procgen_dregg::beacon::DailyBeacon;

/// The browser-owned Lean-native Descent session.
///
/// The first action that actually lands binds `actor`; a refusal cannot claim the run.
/// Afterwards every action must carry the same actor identity.
#[wasm_bindgen]
pub struct NativeDescentWorld {
    offering: NativeDescentOffering,
    session: NativeDescentSession,
}

#[wasm_bindgen]
impl NativeDescentWorld {
    /// Open a deterministic Lean-native Descent.
    ///
    /// `seed` is normalized by the Offering exactly as it is on the other frontends. The
    /// deployed genesis is unclaimed; the first landed action binds its actor.
    #[wasm_bindgen(constructor)]
    pub fn new(seed: u32) -> Result<NativeDescentWorld, JsError> {
        Self::try_new(u64::from(seed)).map_err(|error| JsError::new(&error))
    }

    /// **Open a Descent whose banked relics mint under TODAY'S REVEALED DAY, verified in the
    /// tab.** `round` + `signature_hex` are the day's fetched drand `quicknet` pair; this builds
    /// the real [`DailyBeacon`], runs the BLS pairing check against the pinned group key
    /// (`DailyBeacon::seed` verifies before it derives), and binds the run day-seed to it.
    ///
    /// This is the browser half of the same tooth [`crate::bindings_descent::DescentWorld::
    /// from_beacon`] carries for the procgen daily: FAIL-CLOSED — a forged, mutated, or
    /// wrong-round signature does not verify, so there is no world and no day. The ordinary
    /// [`new`](Self::new) constructor is the seed-derived (reproducible, and therefore
    /// PRE-COMPUTABLE) path, right for a practice world and wrong for a run whose relic ids are
    /// supposed to be unpredictable until the round matures.
    #[wasm_bindgen(js_name = fromBeacon)]
    pub fn from_beacon(
        seed: u32,
        round: u64,
        signature_hex: String,
    ) -> Result<NativeDescentWorld, JsError> {
        Self::try_from_beacon(u64::from(seed), round, &signature_hex)
            .map_err(|error| JsError::new(&error))
    }

    /// Restore an untrusted portable record by exact re-execution.
    ///
    /// No serialized state is installed directly. A fresh Offering session replays every
    /// command and must reproduce the full event/receipt/state/root/checkpoint/completion
    /// envelope byte-for-byte.
    #[wasm_bindgen(js_name = fromRecordJson)]
    pub fn from_record_json(record_json: String) -> Result<NativeDescentWorld, JsError> {
        Self::try_from_record_json(&record_json).map_err(|error| JsError::new(&error))
    }

    /// Candidate native affordances for `viewer`, as JSON.
    ///
    /// The Offering computes eligibility from the real native state. Once another actor has
    /// claimed the run, every row is disabled for this viewer. The executor remains the final
    /// referee even for rows decorated `enabled: true`.
    #[wasm_bindgen(js_name = actionsJson)]
    pub fn actions_json(&self, viewer: String) -> String {
        let viewer = DreggIdentity(viewer);
        let rows: Vec<ActionWire> = self
            .offering
            .actions_for(&self.session, &viewer)
            .iter()
            .map(ActionWire::from)
            .collect();
        serde_json::to_string(&rows).expect("native Descent action JSON is serializable")
    }

    /// Submit exactly one `{turn, arg}` native action for the host-authenticated `actor`.
    ///
    /// A landed call advances the journal by exactly one revision and returns its full current
    /// state. A refused call returns `{ok:false, error,...}` and preserves actor, revision, and
    /// root. The label/enabled decoration is not trusted input; the Offering parses the exact
    /// verb and argument and the installed executor decides whether it lands. This low-level
    /// method binds the supplied opaque identity; the embedding host is responsible for proving
    /// that the browser controls that identity.
    pub fn advance(&mut self, turn: String, arg: i32, actor: String) -> String {
        self.advance_value(turn, i64::from(arg), actor).to_string()
    }

    /// Current exact native state, journal head, checkpoint, and completion as JSON.
    #[wasm_bindgen(js_name = stateJson)]
    pub fn state_json(&self) -> String {
        self.state_value().to_string()
    }

    /// The actor bound by the first landed move, or `undefined` while unclaimed.
    pub fn actor(&self) -> Option<String> {
        self.session.actor().map(|actor| actor.as_str().to_string())
    }

    /// Number of landed actions. The genesis receipt is reported separately by verification,
    /// so a new world has revision zero.
    pub fn revision(&self) -> u32 {
        u32::try_from(self.session.revision())
            .expect("native Descent's fixed journal bound fits u32")
    }

    /// The actor-bound, hash-chained journal head.
    #[wasm_bindgen(js_name = rootHex)]
    pub fn root_hex(&self) -> String {
        hex(&self.session.root())
    }

    /// Whether a terminal native `flee` settlement has landed.
    #[wasm_bindgen(js_name = isComplete)]
    pub fn is_complete(&self) -> bool {
        self.session.completion().is_some()
    }

    /// Whether that terminal settlement banked the complete native relic set.
    #[wasm_bindgen(js_name = isCrowned)]
    pub fn is_crowned(&self) -> bool {
        self.session
            .completion()
            .is_some_and(|completion| completion.crowned)
    }

    /// Re-execute the complete live record and return a structured verification report.
    #[wasm_bindgen(js_name = verifyJson)]
    pub fn verify_json(&self) -> String {
        verify_wire(self.offering.verify(&self.session)).to_string()
    }

    /// Re-execute the complete live record. This is replay verification, not a succinct proof.
    pub fn verify(&self) -> bool {
        self.offering.verify(&self.session).verified
    }

    /// Export the versioned portable action/receipt/state/root record.
    ///
    /// Export is local only: it does not publish the run or submit it to a leaderboard.
    #[wasm_bindgen(js_name = recordJson)]
    pub fn record_json(&self) -> String {
        serde_json::to_string(&PortableRecord::from_record(&self.session.export_record()))
            .expect("native Descent portable record is serializable")
    }
}

impl NativeDescentWorld {
    fn try_new(seed: u64) -> Result<Self, String> {
        Self::open_with(NativeDescentOffering::new(), seed)
    }

    /// The fallible core of [`Self::from_beacon`] — `String` errors, wasm-bindgen-free, so the
    /// fail-closed path is testable NATIVELY (constructing a `JsError` panics off-wasm).
    fn try_from_beacon(seed: u64, round: u64, signature_hex: &str) -> Result<Self, String> {
        let signature = decode_hex_vec(signature_hex)?;
        let beacon = DailyBeacon::quicknet(round, signature);
        // `seed()` runs the pairing check FIRST: a beacon that does not verify yields no day.
        let day = beacon
            .seed()
            .map_err(|error| format!("beacon did not verify: {error:?}"))?;
        Self::open_with(NativeDescentOffering::on_day(day), seed)
    }

    fn open_with(offering: NativeDescentOffering, seed: u64) -> Result<Self, String> {
        let session = offering
            .open(SessionConfig::with_seed(seed))
            .map_err(|error| error.to_string())?;
        Ok(Self { offering, session })
    }

    fn try_from_record_json(record_json: &str) -> Result<Self, String> {
        if record_json.len() > MAX_PORTABLE_RECORD_BYTES {
            return Err(format!(
                "native Descent record exceeds the {} byte import bound",
                MAX_PORTABLE_RECORD_BYTES
            ));
        }
        let expected: PortableRecord =
            serde_json::from_str(record_json).map_err(|error| format!("record JSON: {error}"))?;
        // ⚑ ONE GATE, SHARED WITH THE SERVER. Structural validation, deployment on the record's
        // OWN run day-seed, exact command re-drive, `Offering::verify`, the by-name banked-note
        // re-mint comparison, and the byte-for-byte envelope comparison all live in
        // `native_descent_wire::replay_portable_record` — the same function `dreggnet-web`'s
        // `/descent/native/submit` admits with. Nothing about "how a record is checked" is
        // spelled twice any more, so the browser and the board cannot drift apart.
        let (offering, session) = replay_portable_record(&expected)?;
        Ok(Self { offering, session })
    }

    fn advance_value(&mut self, turn: String, arg: i64, actor: String) -> serde_json::Value {
        let before = self.session.export_record();
        let before_revision = self.session.revision();
        let before_root = self.session.root();
        let before_actor = self.session.actor().cloned();
        let input = Action::new(&turn, turn.clone(), arg, true);

        match self
            .offering
            .advance(&mut self.session, input, DreggIdentity(actor))
        {
            Outcome::Landed { receipt, ended } => {
                let exact_single_step = self.session.revision() == before_revision + 1
                    && self.session.events().len() == before.events.len() + 1
                    && self.session.root() != before_root;
                if !exact_single_step {
                    return self.rollback_invariant_failure(
                        &before,
                        "native Offering did not map one browser action to exactly one journal event",
                    );
                }
                let mut value = self.state_value();
                value["ok"] = serde_json::json!(true);
                value["ended"] = serde_json::json!(ended);
                value["receiptHashHex"] = serde_json::json!(hex(&receipt.receipt_hash()));
                value["turnHashHex"] = serde_json::json!(hex(&receipt.turn_hash));
                value
            }
            Outcome::Refused(reason) => {
                let preserved = self.session.revision() == before_revision
                    && self.session.root() == before_root
                    && self.session.actor() == before_actor.as_ref();
                if !preserved {
                    return self.rollback_invariant_failure(
                        &before,
                        "a refused native Offering action changed the journal head",
                    );
                }
                let mut value = self.state_value();
                value["ok"] = serde_json::json!(false);
                value["error"] = serde_json::json!(reason);
                value
            }
        }
    }

    fn rollback_invariant_failure(
        &mut self,
        before: &NativeDescentRecord,
        reason: &str,
    ) -> serde_json::Value {
        match self.offering.resume_record(before) {
            Ok(restored) => self.session = restored,
            Err(error) => {
                return serde_json::json!({
                    "ok": false,
                    "fatal": true,
                    "error": format!("{reason}; rollback replay failed: {error}"),
                });
            }
        }
        let mut value = self.state_value();
        value["ok"] = serde_json::json!(false);
        value["fatal"] = serde_json::json!(true);
        value["error"] = serde_json::json!(reason);
        value
    }

    fn state_value(&self) -> serde_json::Value {
        let record = self.session.export_record();
        let state = PortableSim::from(self.session.game().sim());
        serde_json::json!({
            "seed": record.seed,
            "actor": self.actor(),
            "revision": self.session.revision(),
            "rootHex": self.root_hex(),
            "state": state,
            "ended": self.is_complete(),
            "crowned": self.is_crowned(),
            "checkpoint": record.checkpoint.as_ref().map(PortableCheckpoint::from),
            "completion": record.completion.as_ref().map(PortableCompletion::from),
        })
    }
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct ActionWire {
    label: String,
    turn: String,
    arg: i64,
    enabled: bool,
    wants_text: bool,
}

impl From<&Action> for ActionWire {
    fn from(action: &Action) -> Self {
        Self {
            label: action.label.clone(),
            turn: action.turn.clone(),
            arg: action.arg,
            enabled: action.enabled,
            wants_text: action.wants_text,
        }
    }
}

fn verify_wire(report: VerifyReport) -> serde_json::Value {
    serde_json::json!({
        "verified": report.verified,
        "turns": report.turns,
        "detail": report.detail,
        "kind": "exact-native-replay",
    })
}

fn hex(bytes: &[u8]) -> String {
    crate::bindings::hex_encode(bytes)
}

/// Decode a byte vector from hex (a drand signature). Accepts an optional `0x` prefix; rejects
/// odd length / non-hex digits (fail-closed).
fn decode_hex_vec(text: &str) -> Result<Vec<u8>, String> {
    let text = text.strip_prefix("0x").unwrap_or(text);
    if text.len() % 2 != 0 {
        return Err("hex string has an odd number of digits".to_string());
    }
    (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16).map_err(|e| e.to_string()))
        .collect()
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;

    fn value(json: &str) -> serde_json::Value {
        serde_json::from_str(json).expect("binding response is JSON")
    }

    #[test]
    fn first_landed_move_binds_actor_and_refusals_do_not_advance() {
        let mut world = NativeDescentWorld::try_new(17).expect("native world opens");
        let root = world.root_hex();

        let refused = value(&world.advance("smite".to_string(), 0, "mallory".to_string()));
        assert_eq!(refused["ok"], false);
        assert_eq!(world.revision(), 0);
        assert_eq!(world.actor(), None);
        assert_eq!(world.root_hex(), root);

        let landed = value(&world.advance("delve".to_string(), 0, "alice".to_string()));
        assert_eq!(landed["ok"], true);
        assert_eq!(world.revision(), 1, "one action is one Offering advance");
        assert_eq!(world.actor().as_deref(), Some("alice"));
        assert_ne!(world.root_hex(), root);

        let claimed_root = world.root_hex();
        let intruder = value(&world.advance("flee".to_string(), 0, "bob".to_string()));
        assert_eq!(intruder["ok"], false);
        assert_eq!(world.revision(), 1);
        assert_eq!(world.root_hex(), claimed_root);
        assert_eq!(world.actor().as_deref(), Some("alice"));
    }

    #[test]
    fn portable_record_restores_only_after_exact_native_replay() {
        let mut original = NativeDescentWorld::try_new(22).expect("native world opens");
        assert_eq!(
            value(&original.advance("delve".to_string(), 0, "alice".to_string()))["ok"],
            true
        );
        assert_eq!(
            value(&original.advance("smite".to_string(), 0, "alice".to_string()))["ok"],
            true
        );
        let record = original.record_json();

        let restored = NativeDescentWorld::try_from_record_json(&record)
            .expect("exact portable record replays");
        assert_eq!(restored.record_json(), record);
        assert_eq!(restored.root_hex(), original.root_hex());
        assert_eq!(restored.revision(), 2);
        assert!(restored.verify());

        let mut forged = value(&record);
        forged["rootHex"] = serde_json::json!("00".repeat(32));
        assert!(
            NativeDescentWorld::try_from_record_json(&forged.to_string()).is_err(),
            "a forged journal head is not trusted as a state blob"
        );
    }

    #[test]
    fn terminal_settlement_and_full_receipt_are_portable() {
        let mut world = NativeDescentWorld::try_new(9).expect("native world opens");
        let landed = value(&world.advance("flee".to_string(), 0, "alice".to_string()));
        assert_eq!(landed["ok"], true);
        assert_eq!(landed["ended"], true);
        assert!(world.is_complete());
        assert!(!world.is_crowned());

        let record = value(&world.record_json());
        assert!(record["completion"].is_object());
        assert_eq!(
            record["completion"]["bankedNotes"],
            serde_json::json!([]),
            "a run that banked nothing minted nothing — and stays portable"
        );
        assert!(record["events"][0]["receipt"].is_object());
        assert_eq!(record["events"][0]["turn"], "flee");
        assert!(world.verify());

        let restored = NativeDescentWorld::try_from_record_json(&record.to_string())
            .expect("a note-less settlement still replays exactly");
        assert_eq!(restored.record_json(), world.record_json());
    }

    /// Drive the shortest run that BANKS a relic: delve, slay the floor-1 guardian, probe the
    /// relic slots until the one lying on floor 1 loots (a refusal preserves the journal, so
    /// probing is sound), then flee — flee banks the carried relic and settlement mints its note.
    fn world_with_a_banked_note() -> NativeDescentWorld {
        let mut world = NativeDescentWorld::try_new(22).expect("native world opens");
        assert_eq!(
            value(&world.advance("delve".to_string(), 0, "alice".to_string()))["ok"],
            true
        );
        assert_eq!(
            value(&world.advance("smite".to_string(), 0, "alice".to_string()))["ok"],
            true
        );
        let looted = (0..8).any(|relic| {
            value(&world.advance("loot".to_string(), relic, "alice".to_string()))["ok"] == true
        });
        assert!(looted, "some relic lies on floor 1");
        assert_eq!(
            value(&world.advance("flee".to_string(), 0, "alice".to_string()))["ok"],
            true
        );
        assert!(world.is_complete());
        world
    }

    #[test]
    fn banked_note_payload_survives_the_portable_boundary_content_address_unchanged() {
        let world = world_with_a_banked_note();
        // Ground truth from the OFFERING's own completion, not the wire under test.
        let minted = world
            .session
            .completion()
            .expect("the run settled")
            .banked_notes
            .clone();
        assert_eq!(minted.len(), 1, "the probe run banked exactly one relic");

        let record_json = world.record_json();
        let record = value(&record_json);
        let notes = record["completion"]["bankedNotes"]
            .as_array()
            .expect("v3 completion carries bankedNotes");
        assert_eq!(notes.len(), 1);
        assert_eq!(notes[0]["relic"], serde_json::json!(minted[0].relic));
        assert_eq!(
            notes[0]["assetIdHex"],
            serde_json::json!(hex(&minted[0].asset_id.bytes())),
            "the note's content-address crosses the wire unchanged"
        );
        assert_eq!(
            notes[0]["rarity"],
            serde_json::json!(minted[0].rarity.tag())
        );
        assert_eq!(
            notes[0]["ownerHex"],
            serde_json::json!(hex(&minted[0].owner))
        );

        let restored = NativeDescentWorld::try_from_record_json(&record_json)
            .expect("the note-bearing record replays exactly");
        assert_eq!(
            restored.record_json(),
            record_json,
            "import re-mints the identical note payload"
        );
    }

    #[test]
    fn a_forged_banked_note_is_refused_by_name() {
        let world = world_with_a_banked_note();
        let record = value(&world.record_json());

        // A substituted content-address: structurally valid hex, but it does not re-mint.
        let mut forged_id = record.clone();
        forged_id["completion"]["bankedNotes"][0]["assetIdHex"] =
            serde_json::json!("11".repeat(32));
        let error = NativeDescentWorld::try_from_record_json(&forged_id.to_string())
            .err()
            .expect("a substituted asset id is a forgery");
        assert!(
            error.contains("banked notes do not re-mint"),
            "refusal names the notes: {error}"
        );

        // An inflated rarity: the canonical-tag gate refuses a non-canonical byte by name…
        let mut fake_tier = record.clone();
        fake_tier["completion"]["bankedNotes"][0]["rarity"] = serde_json::json!(9);
        let error = NativeDescentWorld::try_from_record_json(&fake_tier.to_string())
            .err()
            .expect("a non-canonical rarity tag fails closed");
        assert!(
            error.contains("rarity tag 9 is not canonical"),
            "refusal names the tag: {error}"
        );

        // …and a canonical-but-wrong tier is caught by the re-mint, not believed.
        let honest_tag = record["completion"]["bankedNotes"][0]["rarity"]
            .as_u64()
            .expect("wire tag");
        let wrong_tag = (honest_tag + 1) % 4;
        let mut relabeled = record.clone();
        relabeled["completion"]["bankedNotes"][0]["rarity"] = serde_json::json!(wrong_tag);
        let error = NativeDescentWorld::try_from_record_json(&relabeled.to_string())
            .err()
            .expect("a relabeled tier does not re-mint");
        assert!(
            error.contains("banked notes do not re-mint"),
            "refusal names the notes: {error}"
        );

        // A stolen note: same run, different claimed owner key.
        let mut stolen = record.clone();
        stolen["completion"]["bankedNotes"][0]["ownerHex"] = serde_json::json!("22".repeat(32));
        let error = NativeDescentWorld::try_from_record_json(&stolen.to_string())
            .err()
            .expect("a substituted owner does not re-mint");
        assert!(
            error.contains("banked notes do not re-mint"),
            "refusal names the notes: {error}"
        );
    }

    #[test]
    fn completion_relic_ids_round_trip_at_the_full_u64_wire_width() {
        let completion = PortableCompletion {
            actor: "wire-auditor".to_string(),
            revision: 1,
            root_hex: "00".repeat(32),
            settlement_receipt_hash_hex: "11".repeat(32),
            banked_relics: vec![u64::MAX],
            banked_notes: vec![],
            crowned: false,
        };
        let json = serde_json::to_string(&completion).expect("completion wire serializes");
        let value = value(&json);
        assert_eq!(
            value["bankedRelics"][0],
            serde_json::json!(u64::MAX),
            "the browser record must not narrow a stable relic id to usize"
        );
        assert_eq!(
            serde_json::from_str::<PortableCompletion>(&json).expect("completion wire decodes"),
            completion
        );
    }
}
