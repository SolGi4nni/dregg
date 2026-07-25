//! # `native_descent_wire` — THE portable-record wire of the Lean-native Descent. One copy.
//!
//! A browser plays the Descent in a tab, exports a record, and a server admits it. That record
//! used to be declared **twice** — `wasm::bindings_native_descent::PortableRecord` and
//! `dreggnet_web::descent::NativePortableRecord` — same format string, same version, both
//! `deny_unknown_fields`, no shared code. That mirror was not merely duplication: it was the
//! MECHANISM by which the settled run's real minted relics stopped at the process boundary.
//! `deny_unknown_fields` on both halves makes every additive field a lockstep edit in two
//! crates, so the field that nobody edited twice (`banked_notes`) simply did not cross.
//!
//! This module is the deletion of that mirror. The producer and the consumer now name the same
//! Rust type, so "the two sides agree" is a compile-time fact rather than a review discipline,
//! and a field added here crosses the wire by construction.
//!
//! ## What is untrusted (all of it)
//!
//! Every field here is attacker-supplied. Nothing is installed as state. [`replay_portable_record`]
//! opens a FRESH [`NativeDescentOffering`] session on the record's own day-seed, re-drives every
//! command through [`Offering::advance`], re-runs [`Offering::verify`], re-exports, and requires
//! the whole envelope to match byte-for-byte. Fail-closed at three depths:
//!
//! 1. **Structural** — [`PortableRecord::validate`] refuses a wrong format/version, an
//!    out-of-range seed, an over-long event tape, and a malformed banked note BY NAME (a
//!    non-32-byte asset id/owner, a non-canonical rarity tag) before any replay runs.
//! 2. **Provenance** — the record's `day_seed_hex` is what the replay is DONE UNDER, never
//!    believed: the day-seed is folded into the genesis root, so a record re-pointed at another
//!    day's provenance no longer recomputes its own hash chain.
//! 3. **Envelope** — the re-minted banked notes are compared BY NAME first (so a forged note is
//!    reported as a forged note rather than an anonymous whole-record mismatch), then the entire
//!    re-exported record is compared to the submitted one.
//!
//! `deny_unknown_fields` stays on every struct: an unknown field is a refusal, not a silent drop.

use serde::{Deserialize, Serialize};

use procgen_dregg::CommittedSeed;

use crate::native_descent::{
    MAX_NATIVE_DESCENT_EVENTS, NativeDescentBankedNote, NativeDescentCheckpoint,
    NativeDescentCompletion, NativeDescentEvent, NativeDescentMove, NativeDescentOffering,
    NativeDescentRecord, NativeDescentSession, Rarity,
};
use crate::{Action, DreggIdentity, Offering, Outcome, SessionConfig};

/// The wire format tag. A record that does not carry it exactly is refused.
pub const PORTABLE_FORMAT: &str = "dregg.native-descent.record";

/// The wire version.
///
/// * v1 described only a seed-derived (pre-computable) day; there is no honest upgrade of one.
/// * v2 added `daySeedHex` — the run day-seed the session deployed on.
/// * v3 added `completion.bankedNotes` — the real owned [`dreggnet_asset`] notes the banked
///   relics minted at settlement (asset id, canonical rarity tag, owner pubkey). Those notes are
///   part of the settled completion the byte-for-byte envelope attests, so a v2 envelope no
///   longer says everything this boundary compares.
///
/// Older versions are REFUSED rather than partially compared or silently re-pointed at another
/// provenance: a client re-exports the same run from replay.
pub const PORTABLE_VERSION: u32 = 3;

/// The import/export size bound both halves of the wire enforce.
pub const MAX_PORTABLE_RECORD_BYTES: usize = 8 * 1024 * 1024;

/// **The portable native-Descent record** — the exact JSON `NativeDescentWorld.recordJson()`
/// emits and `POST /descent/native/submit` admits. One declaration, two consumers.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct PortableRecord {
    /// Always [`PORTABLE_FORMAT`].
    pub format: String,
    /// Always [`PORTABLE_VERSION`].
    pub version: u32,
    /// The session's already-normalized deploy seed, `1..=251`.
    pub seed: u8,
    /// **The run day-seed the session deployed on** — the provenance root its banked relics mint
    /// under, folded into the genesis journal root. Carried because import RE-OPENS a fresh
    /// session and re-drives the tape: without it a beacon-bound run would be replayed against
    /// the seed-derived root and nothing (genesis, chain, notes) would re-derive.
    pub day_seed_hex: String,
    /// The actor bound by the first landed move; `None` while the run is unclaimed.
    pub actor: Option<String>,
    /// The action tape with its complete receipts and exact post-states.
    pub events: Vec<PortableEvent>,
    /// The actor-bound, hash-chained journal head.
    pub root_hex: String,
    /// The restart checkpoint, when one exists.
    pub checkpoint: Option<PortableCheckpoint>,
    /// The terminal `flee` settlement, when the run ended.
    pub completion: Option<PortableCompletion>,
}

/// One admitted event as it crosses the wire.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct PortableEvent {
    pub revision: u64,
    pub actor: String,
    pub turn: String,
    pub arg: i64,
    /// The complete serialized executor receipt (compared, never installed).
    pub receipt: serde_json::Value,
    pub post: PortableSim,
    pub root_hex: String,
}

/// The public native game state at one revision.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct PortableSim {
    pub depth: u64,
    pub spent: u64,
    pub wounds: u64,
    pub fate: u64,
    pub ways: [u64; 3],
    pub custody: Vec<u64>,
    pub pack: u64,
    pub banked: u64,
}

/// The restart/verification checkpoint.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct PortableCheckpoint {
    pub actor: String,
    pub revision: u64,
    pub root_hex: String,
    pub state: PortableSim,
}

/// The terminal bank settlement — including **what the banked relics BECAME**.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct PortableCompletion {
    pub actor: String,
    pub revision: u64,
    pub root_hex: String,
    pub settlement_receipt_hash_hex: String,
    /// Stable relic identifiers. Never Rust's platform-sized `usize` in a persisted/browser
    /// artifact.
    pub banked_relics: Vec<u64>,
    /// The real owned notes the banked relics minted at settlement, in the same slot order as
    /// [`banked_relics`](Self::banked_relics). Empty exactly when the run banked nothing.
    /// Untrusted like every other field: replay re-mints each note from the record's day-seed +
    /// committed custody and a note that does not re-derive byte-identically is refused BY NAME.
    pub banked_notes: Vec<PortableBankedNote>,
    pub crowned: bool,
}

/// One banked relic's minted owned-note as it crosses the wire — the transport of
/// [`NativeDescentBankedNote`]. The asset id is content-addressed to (run day-seed, custody slot,
/// player key), so carrying it unchanged is exactly what "the note survives the process boundary"
/// means.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct PortableBankedNote {
    /// The stable relic identifier (the custody slot the relic banked in).
    pub relic: u64,
    /// The minted note's content-addressed asset id (64 hex chars).
    pub asset_id_hex: String,
    /// The canonical [`Rarity::tag`] byte — the committed wire encoding of the tier.
    pub rarity: u8,
    /// The owning player's pubkey at mint (64 hex chars).
    pub owner_hex: String,
}

impl PortableBankedNote {
    /// Structural fail-closed decode gate, refusing a malformed note BY NAME before replay: a
    /// non-32-byte asset id / owner or a non-canonical rarity tag never reaches the envelope
    /// comparison as an anonymous mismatch.
    pub fn validate(&self) -> Result<(), String> {
        decode_hex_32(&self.asset_id_hex)
            .map_err(|error| format!("banked note (relic {}) asset id: {error}", self.relic))?;
        decode_hex_32(&self.owner_hex)
            .map_err(|error| format!("banked note (relic {}) owner: {error}", self.relic))?;
        if Rarity::from_tag(self.rarity).is_none() {
            return Err(format!(
                "banked note (relic {}) rarity tag {} is not canonical",
                self.relic, self.rarity
            ));
        }
        Ok(())
    }
}

impl From<&NativeDescentBankedNote> for PortableBankedNote {
    fn from(note: &NativeDescentBankedNote) -> Self {
        Self {
            relic: note.relic,
            asset_id_hex: hex32(&note.asset_id.bytes()),
            rarity: note.rarity.tag(),
            owner_hex: hex32(&note.owner),
        }
    }
}

impl From<&NativeDescentCompletion> for PortableCompletion {
    fn from(completion: &NativeDescentCompletion) -> Self {
        Self {
            actor: completion.actor.as_str().to_string(),
            revision: completion.revision,
            root_hex: hex32(&completion.root),
            settlement_receipt_hash_hex: hex32(&completion.settlement_receipt_hash),
            banked_relics: completion.banked_relics.clone(),
            banked_notes: completion
                .banked_notes
                .iter()
                .map(PortableBankedNote::from)
                .collect(),
            crowned: completion.crowned,
        }
    }
}

impl From<&NativeDescentCheckpoint> for PortableCheckpoint {
    fn from(checkpoint: &NativeDescentCheckpoint) -> Self {
        Self {
            actor: checkpoint.actor.as_str().to_string(),
            revision: checkpoint.revision,
            root_hex: hex32(&checkpoint.root),
            state: PortableSim::from(&checkpoint.state),
        }
    }
}

impl From<&dungeon_on_dregg::descent::Sim> for PortableSim {
    fn from(sim: &dungeon_on_dregg::descent::Sim) -> Self {
        Self {
            depth: sim.depth,
            spent: sim.spent,
            wounds: sim.wounds,
            fate: sim.fate,
            ways: sim.ways,
            custody: sim.custody.to_vec(),
            pack: sim.pack(),
            banked: sim.bank(),
        }
    }
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
            post: PortableSim::from(&event.post),
            root_hex: hex32(&event.root),
        }
    }
}

impl PortableRecord {
    /// Project an authoritative exported record onto the wire. This is the ONLY producer, so a
    /// field this type carries is a field every frontend emits.
    pub fn from_record(record: &NativeDescentRecord) -> Self {
        Self {
            format: PORTABLE_FORMAT.to_string(),
            version: PORTABLE_VERSION,
            seed: record.seed,
            day_seed_hex: hex32(record.day_seed.as_bytes()),
            actor: record
                .actor
                .as_ref()
                .map(|actor| actor.as_str().to_string()),
            events: record.events.iter().map(PortableEvent::from).collect(),
            root_hex: hex32(&record.root),
            checkpoint: record.checkpoint.as_ref().map(PortableCheckpoint::from),
            completion: record.completion.as_ref().map(PortableCompletion::from),
        }
    }

    /// The format/version gate on its own (the header a caller may want to report separately).
    pub fn validate_header(&self) -> Result<(), String> {
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

    /// **The complete structural gate**, run before any replay: header, seed range, event bound,
    /// day-seed shape, and every banked note. Each refusal names what was wrong.
    pub fn validate(&self) -> Result<(), String> {
        self.validate_header()?;
        if self.seed == 0 || self.seed > 251 {
            return Err("portable native Descent seed is outside 1..=251".to_string());
        }
        if self.events.len() > MAX_NATIVE_DESCENT_EVENTS {
            return Err(format!(
                "{} events exceeds the native Descent bound",
                self.events.len()
            ));
        }
        self.day_seed()?;
        for note in self.banked_notes() {
            note.validate()?;
        }
        Ok(())
    }

    /// The run day-seed the record names — the provenance root a replay must DEPLOY ON.
    pub fn day_seed(&self) -> Result<CommittedSeed, String> {
        decode_hex_32(&self.day_seed_hex)
            .map(CommittedSeed::from_bytes)
            .map_err(|error| format!("native Descent record day seed: {error}"))
    }

    /// The record's claimed banked notes (empty when the run did not settle or banked nothing).
    pub fn banked_notes(&self) -> &[PortableBankedNote] {
        self.completion
            .as_ref()
            .map_or(&[], |completion| completion.banked_notes.as_slice())
    }

    /// Whether the run reached a terminal settlement that banked the complete relic set.
    pub fn crowned(&self) -> bool {
        self.completion
            .as_ref()
            .is_some_and(|completion| completion.crowned)
    }
}

/// **THE ONE EXACT-REPLAY GATE.** Re-execute an untrusted portable record and return the fresh
/// offering + session it re-derived, or the reason it is refused.
///
/// No serialized state is installed. A fresh session is opened on the record's OWN run day-seed
/// (the only way a beacon-bound run re-derives at all — the day-seed is folded into the genesis
/// root), every command is re-driven through [`Offering::advance`], [`Offering::verify`] must
/// pass, and the re-exported envelope must equal the submitted one. The re-minted banked notes
/// are compared first so a forged note is refused BY NAME rather than as an anonymous mismatch.
pub fn replay_portable_record(
    expected: &PortableRecord,
) -> Result<(NativeDescentOffering, NativeDescentSession), String> {
    expected.validate()?;
    let day_seed = expected.day_seed()?;

    // `Offering::open` normalizes n as (n % 251) + 1. `seed - 1` therefore opens the exact
    // already-normalized seed the record carries.
    let offering = NativeDescentOffering::on_run_day_seed(day_seed);
    let mut session = offering
        .open(SessionConfig::with_seed(u64::from(expected.seed - 1)))
        .map_err(|error| format!("native Descent deployment failed: {error}"))?;

    for event in &expected.events {
        let input = Action::new(&event.turn, &event.turn, event.arg, true);
        match offering.advance(&mut session, input, DreggIdentity(event.actor.clone())) {
            Outcome::Landed { .. } => {}
            Outcome::Refused(reason) => {
                return Err(format!(
                    "portable event {} refused on replay: {reason}",
                    event.revision
                ));
            }
        }
    }

    let report = offering.verify(&session);
    if !report.verified {
        return Err(format!(
            "native replay verification failed: {}",
            report.detail
        ));
    }

    let actual = PortableRecord::from_record(&session.export_record());
    if actual.banked_notes() != expected.banked_notes() {
        return Err(
            "portable banked notes do not re-mint from the record's day-seed and committed \
             custody"
                .to_string(),
        );
    }
    if &actual != expected {
        return Err(
            "portable record differs from exact native action/receipt/state replay".to_string(),
        );
    }
    Ok((offering, session))
}

/// The canonical `{turn, arg}` spelling of one native command. Private: the wire's own encoding,
/// not a second public move vocabulary.
fn move_wire(command: NativeDescentMove) -> (&'static str, i64) {
    match command {
        NativeDescentMove::Delve => ("delve", 0),
        NativeDescentMove::Ascend => ("ascend", 0),
        NativeDescentMove::Unlock { way } => (
            "unlock",
            i64::try_from(way).expect("native way index fits the action wire"),
        ),
        NativeDescentMove::Smite => ("smite", 0),
        NativeDescentMove::Lunge => ("lunge", 0),
        NativeDescentMove::Loot { relic } => (
            "loot",
            i64::try_from(relic).expect("native relic index fits the action wire"),
        ),
        NativeDescentMove::Flee => ("flee", 0),
    }
}

/// Lowercase-hex encode a 32-byte commitment (the wire's only byte encoding).
pub fn hex32(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for byte in bytes {
        out.push(char::from_digit(u32::from(byte >> 4), 16).expect("nibble is a hex digit"));
        out.push(char::from_digit(u32::from(byte & 0x0f), 16).expect("nibble is a hex digit"));
    }
    out
}

/// Decode exactly 64 lowercase/uppercase hex characters into 32 bytes. Anything else is refused.
pub fn decode_hex_32(text: &str) -> Result<[u8; 32], String> {
    if text.len() != 64 {
        return Err(format!("expected 64 hex chars, got {}", text.len()));
    }
    let mut out = [0u8; 32];
    let bytes = text.as_bytes();
    for (index, slot) in out.iter_mut().enumerate() {
        let hi = (bytes[index * 2] as char)
            .to_digit(16)
            .ok_or_else(|| "not hexadecimal".to_string())?;
        let lo = (bytes[index * 2 + 1] as char)
            .to_digit(16)
            .ok_or_else(|| "not hexadecimal".to_string())?;
        *slot = ((hi << 4) | lo) as u8;
    }
    Ok(out)
}
