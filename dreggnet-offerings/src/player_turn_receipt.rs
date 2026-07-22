//! The one player-visible receipt card for an ordinary game turn.
//!
//! Every game keeps its own rules and replay verifier.  The browser, Discord,
//! Telegram, and a paid narrator should nevertheless hand a player the same
//! useful thing after a move: the complete receipt-chain join, the known
//! session disposition, and the surface's replay control.  This type is the
//! small viewer-blind grammar for that card.  It has no actor, prompt, private
//! action, balance, or state fields to accidentally publish.

use dregg_app_framework::TurnReceipt;

/// What the landing surface knows about the session after this receipt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlayerSessionDisposition {
    Continues,
    Complete,
    /// Used by a public operation receipt whose owning adapter deliberately
    /// withholds the session lifecycle fact.
    Undisclosed,
}

/// The replay affordance available beside the receipt on each hosted surface.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlayerReplaySurface {
    Discord,
    /// The dedicated Dungeon slash-command surface used by a paid Chutes turn.
    DiscordDungeon,
    Web,
    Telegram,
}

impl PlayerReplaySurface {
    pub const fn instruction(self) -> &'static str {
        match self {
            Self::Discord => "Use the re-verify chain control to replay the record.",
            Self::DiscordDungeon => "Run `/dungeon verify` to replay-verify the session.",
            Self::Web => "Open Replay-verify to replay the record.",
            Self::Telegram => "Run `/verify` to replay the record.",
        }
    }
}

/// A viewer-blind, copyable handle for one landed executor turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlayerTurnReceipt {
    receipt_id: [u8; 32],
    disposition: PlayerSessionDisposition,
}

impl PlayerTurnReceipt {
    /// Project the complete receipt-chain join from a genuine landed turn.
    pub fn from_landed(receipt: &TurnReceipt, ended: bool) -> Self {
        Self {
            receipt_id: receipt.receipt_hash(),
            disposition: if ended {
                PlayerSessionDisposition::Complete
            } else {
                PlayerSessionDisposition::Continues
            },
        }
    }

    /// Project a receipt already checked by an owning operation adapter.
    ///
    /// `disposition` must be `Undisclosed` unless that adapter also checked the
    /// exact post-turn lifecycle fact; receipt existence alone cannot infer it.
    pub const fn from_verified_id(
        receipt_id: [u8; 32],
        disposition: PlayerSessionDisposition,
    ) -> Self {
        Self {
            receipt_id,
            disposition,
        }
    }

    pub const fn receipt_id(&self) -> &[u8; 32] {
        &self.receipt_id
    }

    pub const fn disposition(&self) -> PlayerSessionDisposition {
        self.disposition
    }

    /// Complete lowercase receipt id.  Hosted surfaces intentionally publish
    /// all 32 bytes: a short prefix is decoration, not an audit join.
    pub fn receipt_hex(&self) -> String {
        const HEX: &[u8; 16] = b"0123456789abcdef";
        let mut out = String::with_capacity(64);
        for byte in self.receipt_id {
            out.push(HEX[(byte >> 4) as usize] as char);
            out.push(HEX[(byte & 0x0f) as usize] as char);
        }
        out
    }

    /// The same concise record grammar used by all hosted surfaces.
    pub fn compact_text(&self, replay: PlayerReplaySurface) -> String {
        let lifecycle = match self.disposition {
            PlayerSessionDisposition::Continues => "Session continues.",
            PlayerSessionDisposition::Complete => "Session complete.",
            PlayerSessionDisposition::Undisclosed => "Session state is not disclosed by this card.",
        };
        format!(
            "Verified turn · executor receipt {}. {lifecycle} {}",
            self.receipt_hex(),
            replay.instruction(),
        )
    }
}
