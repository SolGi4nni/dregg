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

use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;

use dreggnet_offerings::native_descent::{
    MAX_NATIVE_DESCENT_EVENTS, NativeDescentCompletion, NativeDescentEvent, NativeDescentMove,
    NativeDescentOffering, NativeDescentRecord, NativeDescentSession,
};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig, VerifyReport};

const PORTABLE_FORMAT: &str = "dregg.native-descent.record";
const PORTABLE_VERSION: u32 = 1;
const MAX_PORTABLE_RECORD_BYTES: usize = 8 * 1024 * 1024;

// Kept as a local projection macro so this boundary does not gain a second direct dependency
// on `dungeon-on-dregg`: the authoritative `Sim` reaches us through the Offering session/event
// types, and its public state is only copied into the transport record.
macro_rules! sim_wire {
    ($sim:expr) => {{
        let sim = $sim;
        SimWire {
            depth: sim.depth,
            spent: sim.spent,
            wounds: sim.wounds,
            fate: sim.fate,
            ways: sim.ways,
            custody: sim.custody.to_vec(),
            pack: sim.pack(),
            banked: sim.bank(),
        }
    }};
}

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
        Self::try_new(seed as u64).map_err(|error| JsError::new(&error))
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
        let offering = NativeDescentOffering::new();
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
        expected.validate_header()?;
        if expected.events.len() > MAX_NATIVE_DESCENT_EVENTS {
            return Err(format!(
                "{} events exceeds the native Descent bound",
                expected.events.len()
            ));
        }
        if expected.seed == 0 || expected.seed > 251 {
            return Err("portable native Descent seed is outside 1..=251".to_string());
        }

        // Offering::open normalizes n as (n % 251) + 1. `seed - 1` therefore opens the
        // exact already-normalized seed carried by the portable record.
        let mut world = Self::try_new(u64::from(expected.seed - 1))?;
        for event in &expected.events {
            let input = Action::new(&event.turn, &event.turn, event.arg, true);
            match world.offering.advance(
                &mut world.session,
                input,
                DreggIdentity(event.actor.clone()),
            ) {
                Outcome::Landed { .. } => {}
                Outcome::Refused(reason) => {
                    return Err(format!(
                        "portable event {} refused on native replay: {reason}",
                        event.revision
                    ));
                }
            }
        }

        let report = world.offering.verify(&world.session);
        if !report.verified {
            return Err(format!(
                "native replay verification failed: {}",
                report.detail
            ));
        }
        let actual = PortableRecord::from_record(&world.session.export_record());
        if actual != expected {
            return Err(
                "portable record differs from exact native action/receipt/state replay".to_string(),
            );
        }
        Ok(world)
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
        let state = sim_wire!(self.session.game().sim());
        serde_json::json!({
            "seed": record.seed,
            "actor": self.actor(),
            "revision": self.session.revision(),
            "rootHex": self.root_hex(),
            "state": state,
            "ended": self.is_complete(),
            "crowned": self.is_crowned(),
            "checkpoint": record.checkpoint.as_ref().map(CheckpointWire::from),
            "completion": record.completion.as_ref().map(CompletionWire::from),
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SimWire {
    depth: u64,
    spent: u64,
    wounds: u64,
    fate: u64,
    ways: [u64; 3],
    custody: Vec<u64>,
    pack: u64,
    banked: u64,
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct PortableRecord {
    format: String,
    version: u32,
    seed: u8,
    actor: Option<String>,
    events: Vec<PortableEvent>,
    root_hex: String,
    checkpoint: Option<CheckpointWire>,
    completion: Option<CompletionWire>,
}

impl PortableRecord {
    fn from_record(record: &NativeDescentRecord) -> Self {
        Self {
            format: PORTABLE_FORMAT.to_string(),
            version: PORTABLE_VERSION,
            seed: record.seed,
            actor: record
                .actor
                .as_ref()
                .map(|actor| actor.as_str().to_string()),
            events: record.events.iter().map(PortableEvent::from).collect(),
            root_hex: hex(&record.root),
            checkpoint: record.checkpoint.as_ref().map(CheckpointWire::from),
            completion: record.completion.as_ref().map(CompletionWire::from),
        }
    }

    fn validate_header(&self) -> Result<(), String> {
        if self.format != PORTABLE_FORMAT {
            return Err(format!(
                "unsupported native Descent record format {:?}",
                self.format
            ));
        }
        if self.version != PORTABLE_VERSION {
            return Err(format!(
                "unsupported native Descent record version {}",
                self.version
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct PortableEvent {
    revision: u64,
    actor: String,
    turn: String,
    arg: i64,
    receipt: serde_json::Value,
    post: SimWire,
    root_hex: String,
}

impl From<&NativeDescentEvent> for PortableEvent {
    fn from(event: &NativeDescentEvent) -> Self {
        let (turn, arg) = move_wire(event.command);
        Self {
            revision: event.revision,
            actor: event.actor.as_str().to_string(),
            turn: turn.to_string(),
            arg,
            receipt: serde_json::to_value(&event.receipt)
                .expect("native Descent receipt is serializable"),
            post: sim_wire!(&event.post),
            root_hex: hex(&event.root),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CheckpointWire {
    actor: String,
    revision: u64,
    root_hex: String,
    state: SimWire,
}

impl From<&dreggnet_offerings::native_descent::NativeDescentCheckpoint> for CheckpointWire {
    fn from(checkpoint: &dreggnet_offerings::native_descent::NativeDescentCheckpoint) -> Self {
        Self {
            actor: checkpoint.actor.as_str().to_string(),
            revision: checkpoint.revision,
            root_hex: hex(&checkpoint.root),
            state: sim_wire!(&checkpoint.state),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CompletionWire {
    actor: String,
    revision: u64,
    root_hex: String,
    settlement_receipt_hash_hex: String,
    banked_relics: Vec<usize>,
    crowned: bool,
}

impl From<&NativeDescentCompletion> for CompletionWire {
    fn from(completion: &NativeDescentCompletion) -> Self {
        Self {
            actor: completion.actor.as_str().to_string(),
            revision: completion.revision,
            root_hex: hex(&completion.root),
            settlement_receipt_hash_hex: hex(&completion.settlement_receipt_hash),
            banked_relics: completion.banked_relics.clone(),
            crowned: completion.crowned,
        }
    }
}

fn move_wire(command: NativeDescentMove) -> (&'static str, i64) {
    match command {
        NativeDescentMove::Delve => ("delve", 0),
        NativeDescentMove::Unlock { way } => ("unlock", way as i64),
        NativeDescentMove::Smite => ("smite", 0),
        NativeDescentMove::Loot { relic } => ("loot", relic as i64),
        NativeDescentMove::Flee => ("flee", 0),
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
        assert!(record["events"][0]["receipt"].is_object());
        assert_eq!(record["events"][0]["turn"], "flee");
        assert!(world.verify());
    }
}
