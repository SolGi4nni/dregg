//! Viewer-blind consent and receipt disclosures for paid Chutes narration.
//!
//! A public Discord channel, web page, or Telegram group has no single viewer. Its disclosure
//! therefore must not carry an actor id, player balance, prompt, tool input, private result,
//! narration source material, or token counts. These types deliberately have no fields for those
//! values. They expose only operator-configured provider/model facts, the fixed player charge,
//! the operator's USD ceiling/actual spend, and (after success) the public executor receipt.

use std::fmt;

use crate::player_turn_receipt::{
    PlayerReplaySurface, PlayerSessionDisposition, PlayerTurnReceipt,
};

/// Exact, versioned consent value transported by web forms and Telegram callbacks.
pub const CHUTES_CONSENT_WIRE: &str = "chutes-consent-v1";
/// The only player charge an explicit Chutes turn may consume after its verified receipt lands.
pub const CHUTES_PLAYER_CREDITS: u8 = 1;
/// Cross-surface text bound. Discord fields, Telegram messages, and compact web cards all fit.
pub const CHUTES_DISCLOSURE_MAX_CHARS: usize = 700;

/// Invalid operator-controlled public metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChutesDisclosureError {
    UnsafeModel,
    UnsafeCommand,
}

impl fmt::Display for ChutesDisclosureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsafeModel => write!(
                f,
                "Chutes model id must be 1..=128 safe ASCII identity bytes"
            ),
            Self::UnsafeCommand => {
                write!(f, "Chutes command must be 1..=64 safe public keyword bytes")
            }
        }
    }
}

impl std::error::Error for ChutesDisclosureError {}

fn validate_model(model: &str) -> Result<(), ChutesDisclosureError> {
    let valid = !model.is_empty()
        && model.len() <= 128
        && model
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || b"-_.:/@".contains(&byte));
    valid
        .then_some(())
        .ok_or(ChutesDisclosureError::UnsafeModel)
}

fn dollars(micro_usd: u64) -> String {
    format!("{}.{:06}", micro_usd / 1_000_000, micro_usd % 1_000_000)
}

fn bounded(text: String) -> String {
    if text.chars().count() <= CHUTES_DISCLOSURE_MAX_CHARS {
        return text;
    }
    let mut out: String = text
        .chars()
        .take(CHUTES_DISCLOSURE_MAX_CHARS.saturating_sub(1))
        .collect();
    out.push('…');
    out
}

/// Public pre-call disclosure. It is structurally viewer-blind: no identity, balance, prompt,
/// narration, private input, or session secret can be placed in it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ViewerBlindChutesConsent {
    model: String,
    operator_cap_micro_usd: u64,
}

impl ViewerBlindChutesConsent {
    pub fn new(
        model: impl Into<String>,
        operator_cap_micro_usd: u64,
    ) -> Result<Self, ChutesDisclosureError> {
        let model = model.into();
        validate_model(&model)?;
        Ok(Self {
            model,
            operator_cap_micro_usd,
        })
    }

    pub fn model(&self) -> &str {
        &self.model
    }

    pub const fn operator_cap_micro_usd(&self) -> u64 {
        self.operator_cap_micro_usd
    }

    /// One compact disclosure shared byte-for-byte in meaning across surfaces.
    pub fn compact_text(&self) -> String {
        bounded(format!(
            "Chutes/Bittensor model `{}` gets only the current public room and closed legal commands. No private input, player identity, balance, or account data is sent. It may propose one; the verified executor, not model prose, decides every effect. Player cost: exactly 1 run credit, consumed only after a provenance-bound executor receipt lands. Provider, stale, parser, or executor refusal costs 0 player credits. Operator inference ceiling: ${}. Public result: full receipt + replay instruction. Shared cards omit prompts/tool payloads/token counts.",
            self.model,
            dollars(self.operator_cap_micro_usd),
        ))
    }

    pub const fn button_label(&self) -> &'static str {
        "Opt in · 1 credit if verified"
    }
}

/// Admit only the exact versioned affirmative consent. Prefixes, suffixes, whitespace, and
/// injection-shaped values are all refusals.
pub fn admits_chutes_consent(value: &str) -> bool {
    value.as_bytes() == CHUTES_CONSENT_WIRE.as_bytes()
}

/// Fixed replay guidance prevents a surface from smuggling viewer/private text into the public
/// disclosure under the guise of an instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChutesReplaySurface {
    Discord,
    Web,
    Telegram,
}

impl ChutesReplaySurface {
    const fn player_surface(self) -> PlayerReplaySurface {
        match self {
            Self::Discord => PlayerReplaySurface::DiscordDungeon,
            Self::Web => PlayerReplaySurface::Web,
            Self::Telegram => PlayerReplaySurface::Telegram,
        }
    }
}

/// Public post-call disclosure. The full receipt is the verification handle; deliberately absent
/// are the actor, remaining balance, prompts/tool inputs, private results, and token counts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ViewerBlindChutesReceipt {
    model: String,
    command: String,
    receipt_hash: [u8; 32],
    operator_spend_micro_usd: u64,
}

impl ViewerBlindChutesReceipt {
    pub fn new(
        model: impl Into<String>,
        command: impl Into<String>,
        receipt_hash: [u8; 32],
        operator_spend_micro_usd: u64,
    ) -> Result<Self, ChutesDisclosureError> {
        let model = model.into();
        validate_model(&model)?;
        let command = command.into();
        // Commands come from the closed public keyword set. Refuse anything capable of turning a
        // public receipt card into a formatting or injection carrier.
        if command.is_empty()
            || command.len() > 64
            || !command
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-'))
        {
            return Err(ChutesDisclosureError::UnsafeCommand);
        }
        Ok(Self {
            model,
            command,
            receipt_hash,
            operator_spend_micro_usd,
        })
    }

    pub fn receipt_hex(&self) -> String {
        PlayerTurnReceipt::from_verified_id(
            self.receipt_hash,
            PlayerSessionDisposition::Undisclosed,
        )
        .receipt_hex()
    }

    pub fn compact_text(&self, replay_surface: ChutesReplaySurface) -> String {
        let receipt = PlayerTurnReceipt::from_verified_id(
            self.receipt_hash,
            PlayerSessionDisposition::Undisclosed,
        );
        bounded(format!(
            "Verified Chutes turn · command `{}` · provider `chutes:{}` · player charge 1 run credit · operator spend ${}. {} This shared record contains no player identity, balance, prompt/tool input, private result, or token count.",
            self.command,
            self.model,
            dollars(self.operator_spend_micro_usd),
            receipt.compact_text(replay_surface.player_surface()),
        ))
    }
}
