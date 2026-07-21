//! Opt-in narrated turns on a hosted [`DungeonSession`](super::DungeonSession).
//!
//! This is the production offering boundary for a confined narrator such as Chutes:
//! the provider may propose one of Dungeon's native typed commands and some prose, but
//! it never supplies an [`Effect`](dregg_app_framework::Effect). This module rechecks
//! the command against [`dungeon_on_dregg::narrator::legal_commands`] for the session's
//! current room, then delegates the transition to the existing real-world
//! [`narrate_turn`](dungeon_on_dregg::narrator::narrate_turn) path. That path lowers the
//! typed command, lets the installed `CellProgram` referee it, and binds the narration
//! commitment as a receipt-only event in the same turn.
//!
//! The operation is deliberately opt-in rather than an [`Offering`](crate::Offering)
//! default. Normal player and collective advances keep their existing behavior. A
//! frontend must explicitly call [`DungeonSession::advance_narrated_receipt`] after
//! provider admission and a player-credit hold; the returned native receipt lets it
//! verify provenance before committing that hold.

use dungeon_on_dregg::narrator::{
    BrainRefusal, NarrateError, Narrated, NarratedReceipt, SceneView, legal_commands, narrate_turn,
    parse_confined_response, scene_view,
};
use spween_dregg::{StepReceipt, WorldError};

use crate::chutes_consent::{ViewerBlindChutesConsent, admits_chutes_consent};
use crate::{BinaryOperationError, DreggIdentity, Outcome};

use super::DungeonSession;

/// Stable operation route shared by web, Discord, Telegram, and native hosts.
pub const CHUTES_NARRATED_OPERATION: &str = "dungeon.chutes-narrated-turn.v1";
/// Exact owning request media type for [`ChutesNarratedRequest`].
pub const CHUTES_NARRATED_MEDIA_TYPE: &str =
    "application/vnd.dregg.dungeon.chutes-narrated-turn.v1+binary";
/// A Chutes response is deliberately compact; frontends reject larger bodies before buffering.
pub const MAX_CHUTES_NARRATED_REQUEST_BYTES: usize = 16 * 1024;
/// The disclosure rendered beside the operation on every frontend.
pub const CHUTES_NARRATED_DISCLOSURE: &str = "The player explicitly opts into one paid Chutes narration. The canonical request retains the public model id, operator cost ceiling and spend, exact consent value, closed command, and public narration for deterministic restart replay. It contains no player identity, balance, provider credential, hidden game input, prompt, tool transcript, or token count. The model can name only one command from the current room's finite vocabulary; the real executor decides the effect. A provider, parser, stale-command, or executor refusal commits no turn and authorizes no player charge.";

const CHUTES_WIRE_MAGIC: [u8; 8] = *b"DREGGCHU";
const CHUTES_WIRE_VERSION: u8 = 1;
const MAX_CHUTES_RESPONSE_BYTES: usize = 8 * 1024;

/// Canonical input to one explicitly consented Chutes-backed Dungeon operation.
///
/// This is the post-provider public result, not the provider prompt or tool transcript. The
/// player identity remains the separately supplied `actor` attribution of the generic host
/// operation. Keeping the fields private makes [`Self::encode`] the only wire constructor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChutesNarratedRequest {
    model: String,
    operator_cap_micro_usd: u64,
    operator_spend_micro_usd: u64,
    consent: String,
    provider_output: String,
}

impl ChutesNarratedRequest {
    /// Construct a request only from the exact affirmative consent and an exact two-line
    /// closed-command response. Room-specific legality is checked against the live session when
    /// the operation is invoked.
    pub fn new(
        model: impl Into<String>,
        operator_cap_micro_usd: u64,
        operator_spend_micro_usd: u64,
        consent: impl Into<String>,
        provider_output: impl Into<String>,
    ) -> Result<Self, BinaryOperationError> {
        let model = model.into();
        ViewerBlindChutesConsent::new(model.clone(), operator_cap_micro_usd)
            .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
        if operator_spend_micro_usd > operator_cap_micro_usd {
            return Err(BinaryOperationError::Refused(format!(
                "Chutes operator spend {operator_spend_micro_usd} micro-USD exceeds the consented {operator_cap_micro_usd} micro-USD ceiling"
            )));
        }
        let consent = consent.into();
        if !admits_chutes_consent(&consent) {
            return Err(BinaryOperationError::Refused(
                "the exact Chutes consent value was not presented".to_string(),
            ));
        }
        let provider_output = provider_output.into();
        validate_exact_response_shape(&provider_output)?;
        if provider_output.len() > MAX_CHUTES_RESPONSE_BYTES {
            return Err(BinaryOperationError::Malformed(format!(
                "Chutes provider output is {} bytes; maximum is {MAX_CHUTES_RESPONSE_BYTES}",
                provider_output.len()
            )));
        }
        Ok(Self {
            model,
            operator_cap_micro_usd,
            operator_spend_micro_usd,
            consent,
            provider_output,
        })
    }

    pub fn model(&self) -> &str {
        &self.model
    }

    pub const fn operator_cap_micro_usd(&self) -> u64 {
        self.operator_cap_micro_usd
    }

    pub const fn operator_spend_micro_usd(&self) -> u64 {
        self.operator_spend_micro_usd
    }

    pub fn provider_output(&self) -> &str {
        &self.provider_output
    }

    /// Encode the one canonical owning wire accepted by [`crate::OfferingHost`].
    pub fn encode(&self) -> Result<Vec<u8>, BinaryOperationError> {
        let model_len = u16::try_from(self.model.len()).map_err(|_| {
            BinaryOperationError::Malformed("Chutes model id exceeds the canonical wire".into())
        })?;
        let consent_len = u16::try_from(self.consent.len()).map_err(|_| {
            BinaryOperationError::Malformed("Chutes consent exceeds the canonical wire".into())
        })?;
        let response_len = u32::try_from(self.provider_output.len()).map_err(|_| {
            BinaryOperationError::Malformed("Chutes response exceeds the canonical wire".into())
        })?;
        let mut out = Vec::with_capacity(
            8 + 1
                + 2
                + self.model.len()
                + 8
                + 8
                + 2
                + self.consent.len()
                + 4
                + self.provider_output.len(),
        );
        out.extend_from_slice(&CHUTES_WIRE_MAGIC);
        out.push(CHUTES_WIRE_VERSION);
        out.extend_from_slice(&model_len.to_be_bytes());
        out.extend_from_slice(self.model.as_bytes());
        out.extend_from_slice(&self.operator_cap_micro_usd.to_be_bytes());
        out.extend_from_slice(&self.operator_spend_micro_usd.to_be_bytes());
        out.extend_from_slice(&consent_len.to_be_bytes());
        out.extend_from_slice(self.consent.as_bytes());
        out.extend_from_slice(&response_len.to_be_bytes());
        out.extend_from_slice(self.provider_output.as_bytes());
        if out.len() > MAX_CHUTES_NARRATED_REQUEST_BYTES {
            return Err(BinaryOperationError::Malformed(format!(
                "Chutes request is {} bytes; maximum is {MAX_CHUTES_NARRATED_REQUEST_BYTES}",
                out.len()
            )));
        }
        Ok(out)
    }

    /// Decode and re-encode, refusing alternate encodings and trailing bytes.
    pub fn decode(bytes: &[u8]) -> Result<Self, BinaryOperationError> {
        if bytes.len() > MAX_CHUTES_NARRATED_REQUEST_BYTES {
            return Err(BinaryOperationError::Malformed(format!(
                "Chutes request is {} bytes; maximum is {MAX_CHUTES_NARRATED_REQUEST_BYTES}",
                bytes.len()
            )));
        }
        let mut reader = ChutesReader::new(bytes);
        if reader.array::<8>()? != CHUTES_WIRE_MAGIC {
            return Err(BinaryOperationError::Malformed(
                "Chutes request wire magic mismatch".to_string(),
            ));
        }
        let version = reader.byte()?;
        if version != CHUTES_WIRE_VERSION {
            return Err(BinaryOperationError::Malformed(format!(
                "unsupported Chutes request wire version {version}"
            )));
        }
        let model_len = usize::from(reader.u16()?);
        let model = reader.utf8(model_len)?;
        let cap = reader.u64()?;
        let spend = reader.u64()?;
        let consent_len = usize::from(reader.u16()?);
        let consent = reader.utf8(consent_len)?;
        let response_len = usize::try_from(reader.u32()?).map_err(|_| {
            BinaryOperationError::Malformed(
                "Chutes response length does not fit the host address space".to_string(),
            )
        })?;
        let provider_output = reader.utf8(response_len)?;
        reader.finish()?;
        let request = Self::new(model, cap, spend, consent, provider_output)?;
        if request.encode()? != bytes {
            return Err(BinaryOperationError::Malformed(
                "Chutes request is not canonically encoded".to_string(),
            ));
        }
        Ok(request)
    }

    /// Resolve the exact provider response against the live room's finite command vocabulary.
    pub fn narrated_for(&self, view: &SceneView) -> Result<Narrated, BinaryOperationError> {
        parse_exact_chutes_response(view, &self.provider_output)
    }
}

/// Parse exactly `COMMAND: <keyword>\nNARRATION: <one public line>`, then use the owning
/// Dungeon command table for room-specific admission. Extra fields, duplicate markers, leading
/// or trailing whitespace, and a legal command from a stale room all refuse.
pub fn parse_exact_chutes_response(
    view: &SceneView,
    provider_output: &str,
) -> Result<Narrated, BinaryOperationError> {
    validate_exact_response_shape(provider_output)?;
    parse_confined_response(view, provider_output).map_err(|error| match error {
        BrainRefusal::IllegalCommand(_) => BinaryOperationError::Refused(error.to_string()),
        _ => BinaryOperationError::Malformed(error.to_string()),
    })
}

fn validate_exact_response_shape(provider_output: &str) -> Result<(), BinaryOperationError> {
    if provider_output.contains('\r') {
        return Err(BinaryOperationError::Malformed(
            "Chutes response must use the canonical LF wire".to_string(),
        ));
    }
    let mut lines = provider_output.split('\n');
    let command_line = lines.next().unwrap_or_default();
    let narration_line = lines.next().ok_or_else(|| {
        BinaryOperationError::Malformed(
            "Chutes response must contain exactly command and narration lines".to_string(),
        )
    })?;
    if lines.next().is_some() {
        return Err(BinaryOperationError::Malformed(
            "Chutes response carries fields beyond command and narration".to_string(),
        ));
    }
    let keyword = command_line.strip_prefix("COMMAND: ").ok_or_else(|| {
        BinaryOperationError::Malformed("Chutes response command line is not canonical".to_string())
    })?;
    if keyword.is_empty()
        || keyword.len() > 64
        || !keyword
            .bytes()
            .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'_')
    {
        return Err(BinaryOperationError::Malformed(
            "Chutes command keyword is not canonical".to_string(),
        ));
    }
    let narration = narration_line.strip_prefix("NARRATION: ").ok_or_else(|| {
        BinaryOperationError::Malformed(
            "Chutes response narration line is not canonical".to_string(),
        )
    })?;
    if narration.is_empty()
        || narration.trim() != narration
        || narration.chars().any(char::is_control)
        || narration.contains("{{")
    {
        return Err(BinaryOperationError::Malformed(
            "Chutes narration is empty, non-canonical, or injection-shaped".to_string(),
        ));
    }
    Ok(())
}

struct ChutesReader<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> ChutesReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8], BinaryOperationError> {
        let end = self.position.checked_add(len).ok_or_else(|| {
            BinaryOperationError::Malformed("Chutes request offset overflow".to_string())
        })?;
        let value = self.bytes.get(self.position..end).ok_or_else(|| {
            BinaryOperationError::Malformed("truncated Chutes request".to_string())
        })?;
        self.position = end;
        Ok(value)
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], BinaryOperationError> {
        self.take(N)?.try_into().map_err(|_| {
            BinaryOperationError::Malformed("truncated Chutes fixed-width field".to_string())
        })
    }

    fn byte(&mut self) -> Result<u8, BinaryOperationError> {
        Ok(self.array::<1>()?[0])
    }

    fn u16(&mut self) -> Result<u16, BinaryOperationError> {
        Ok(u16::from_be_bytes(self.array()?))
    }

    fn u32(&mut self) -> Result<u32, BinaryOperationError> {
        Ok(u32::from_be_bytes(self.array()?))
    }

    fn u64(&mut self) -> Result<u64, BinaryOperationError> {
        Ok(u64::from_be_bytes(self.array()?))
    }

    fn utf8(&mut self, len: usize) -> Result<String, BinaryOperationError> {
        std::str::from_utf8(self.take(len)?)
            .map(str::to_string)
            .map_err(|_| BinaryOperationError::Malformed("Chutes text is not UTF-8".to_string()))
    }

    fn finish(self) -> Result<(), BinaryOperationError> {
        if self.position != self.bytes.len() {
            return Err(BinaryOperationError::Malformed(
                "Chutes request carries trailing bytes".to_string(),
            ));
        }
        Ok(())
    }
}

/// A narrated turn that landed on the hosted session: the complete native
/// [`NarratedReceipt`] plus the session's terminal-state bit.
///
/// Provider-facing callers use this richer result to verify their own receipt-bound
/// provenance before committing a held player credit. Call [`Self::into_outcome`] when
/// only the standard offering result is needed.
#[derive(Clone, Debug)]
pub struct NarratedSessionTurn {
    /// The native receipt plus the typed command and bound narration metadata.
    pub narrated: NarratedReceipt,
    /// Whether this committed command ended the Dungeon session.
    pub ended: bool,
}

impl NarratedSessionTurn {
    /// Discard the presentation metadata and retain the standard offering outcome.
    pub fn into_outcome(self) -> Outcome {
        Outcome::Landed {
            receipt: self.narrated.receipt,
            ended: self.ended,
        }
    }
}

impl DungeonSession {
    /// An owned, read-only narrator view of the session's authoritative current room.
    ///
    /// A provider seam calls this immediately before deriving its
    /// [`legal_commands`] tool schema. It exposes no `WorldCell`, executor handle, or
    /// effect surface, and a later call observes any intervening landed turn.
    pub fn narrated_view(&self) -> SceneView {
        scene_view(&self.world, &self.scene)
    }

    /// Resolve an already-typed narrated proposal as one real hosted Dungeon turn.
    ///
    /// Admission is layered and fail-closed:
    ///
    /// 1. the command must be in Dungeon's native closed vocabulary for the session's
    ///    current room (so a stale, wrong-room, private-result, or invented command is
    ///    refused before submission);
    /// 2. empty or `{{`-injecting prose is refused before submission;
    /// 3. the real world executor decides whether the typed command's effects land.
    ///
    /// On success the resulting [`TurnReceipt`](dregg_app_framework::TurnReceipt) is
    /// recorded in the session's ordinary [`spween_dregg::Playthrough`] and actor log,
    /// so [`crate::Offering::verify`] replays it with every other Dungeon step. The
    /// narration commitment is inside that exact receipt; the prose itself never enters
    /// the effect list and therefore has no state authority.
    pub fn advance_narrated_receipt(
        &mut self,
        narrated: &Narrated,
        actor: DreggIdentity,
    ) -> Result<NarratedSessionTurn, String> {
        let view = self.narrated_view();
        let admitted = legal_commands(&view)
            .into_iter()
            .any(|(_, command)| command == narrated.command);
        if !admitted {
            return Err(
                "the narrated command is not in the current room's closed legal set".to_string(),
            );
        }
        if narrated.narration.trim().is_empty() {
            return Err("the narrated turn has empty prose".to_string());
        }
        if narrated.narration.contains("{{") {
            return Err("the narrated turn carries a refused `{{` injection delimiter".to_string());
        }

        let passage = narrated.command.room.clone();
        let choice_index = narrated.command.choice;
        match narrate_turn(&self.world, &self.scene, narrated) {
            Ok(narrated_receipt) => {
                self.steps.push(StepReceipt {
                    passage,
                    choice_index,
                    receipt: narrated_receipt.receipt.clone(),
                    state: self.world.snapshot(),
                    // The Chutes/narrator lane carries no certified private-result
                    // authority. Those choices are excluded by `legal_commands` above.
                    decision_commitment: None,
                });
                self.actors.push(actor);
                // This is an explicit single-actor operation, never an implicit crowd
                // decision. A collective frontend keeps using `advance_collective`.
                self.collectives.push(None);
                let ended = self.world.read_passage().is_none();
                Ok(NarratedSessionTurn {
                    narrated: narrated_receipt,
                    ended,
                })
            }
            Err(NarrateError::World(WorldError::Refused(why))) => Err(why),
            Err(error) => Err(error.to_string()),
        }
    }

    /// The standard [`Outcome`] adapter for [`Self::advance_narrated_receipt`].
    ///
    /// Use the richer operation when a paid/provider frontend must inspect the native
    /// [`NarratedReceipt`] before committing its player-credit hold.
    pub fn advance_narrated(&mut self, narrated: &Narrated, actor: DreggIdentity) -> Outcome {
        match self.advance_narrated_receipt(narrated, actor) {
            Ok(turn) => turn.into_outcome(),
            Err(why) => Outcome::Refused(why),
        }
    }
}
