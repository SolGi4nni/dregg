//! The one player-visible receipt card for an ordinary game turn.
//!
//! Every game keeps its own rules and replay verifier.  The browser, Discord,
//! Telegram, and a paid narrator should nevertheless hand a player the same
//! useful thing after a move: the complete receipt-chain join, the known
//! session disposition, and the surface's replay control.  This type is the
//! small viewer-blind grammar for that card.  It has no actor, prompt, private
//! action, balance, or state fields to accidentally publish.

use dregg_app_framework::TurnReceipt;

use crate::signed::Custody;

/// **The attribution grade a receipt card announces** — what the landing surface actually PROVED
/// about who moved, so "Verified turn" is not shown identically for a turn with zero identity
/// verification and a signature-verified one.
///
/// * [`Asserted`](PlayerAttributionGrade::Asserted) — executor-admitted, actor NOT cryptographically
///   verified (a frontend-asserted label; every unsigned advance). "Verified" would be a lie here.
/// * [`SignedCustodial`](PlayerAttributionGrade::SignedCustodial) — a signature verified, but under a
///   SERVER-held key (the custodial `seed_for` derivation): the server signed *for* the user.
/// * [`SignedUserHeld`](PlayerAttributionGrade::SignedUserHeld) — a signature verified under a key the
///   USER holds (a device/extension key the server never saw).
/// * [`OperationVerified`](PlayerAttributionGrade::OperationVerified) — a receipt already checked by an
///   owning operation adapter ([`PlayerTurnReceipt::from_verified_id`]); the adapter did the
///   verification, so this card only re-publishes its handle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlayerAttributionGrade {
    Asserted,
    SignedCustodial,
    SignedUserHeld,
    OperationVerified,
}

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
            // ⚑ WHAT REPLAY-VERIFY DOES, not just where it is. "Open Replay-verify to replay the
            // record" told a first-time player nothing they could act on — it named a control and a
            // noun they had no meaning for. The offer is the same offer; it just says what pressing
            // it buys.
            Self::Web => {
                "Want proof? Replay-verify below re-runs this whole session from its first move and \
                 reports whether anything changed."
            }
            Self::Telegram => "Run `/verify` to replay the record.",
        }
    }
}

/// A viewer-blind, copyable handle for one landed executor turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlayerTurnReceipt {
    receipt_id: [u8; 32],
    disposition: PlayerSessionDisposition,
    /// The attribution grade this card announces (see [`PlayerAttributionGrade`]) — so an asserted
    /// turn is not dressed as "Verified".
    grade: PlayerAttributionGrade,
    /// The actor identity to name in the lead phrase, when the surface knows it (a signed turn's
    /// verified pubkey). Kept `Option` so the actor-blind default omits it rather than publishing a
    /// bare unverified label.
    identity: Option<String>,
}

impl PlayerTurnReceipt {
    /// Project the complete receipt-chain join from a genuine landed turn — an ASSERTED turn
    /// (executor-admitted, actor NOT cryptographically verified). A signature-verified turn uses
    /// [`from_landed_signed`](PlayerTurnReceipt::from_landed_signed) so the card can say so.
    pub fn from_landed(receipt: &TurnReceipt, ended: bool) -> Self {
        Self {
            receipt_id: receipt.receipt_hash(),
            disposition: if ended {
                PlayerSessionDisposition::Complete
            } else {
                PlayerSessionDisposition::Continues
            },
            grade: PlayerAttributionGrade::Asserted,
            identity: None,
        }
    }

    /// Project the receipt-chain join from a genuine landed **signature-verified** turn, carrying
    /// its custody grade and the verified signer identity — so the card says "Signed by …" (a
    /// user-held key) or "Signed (custodial) by …" (a server-held key signing for the user), never
    /// the same "Verified turn" an asserted turn would show.
    pub fn from_landed_signed(
        receipt: &TurnReceipt,
        ended: bool,
        custody: Custody,
        identity: impl Into<String>,
    ) -> Self {
        Self {
            receipt_id: receipt.receipt_hash(),
            disposition: if ended {
                PlayerSessionDisposition::Complete
            } else {
                PlayerSessionDisposition::Continues
            },
            grade: match custody {
                Custody::Custodial => PlayerAttributionGrade::SignedCustodial,
                Custody::UserHeld => PlayerAttributionGrade::SignedUserHeld,
            },
            identity: Some(identity.into()),
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
            grade: PlayerAttributionGrade::OperationVerified,
            identity: None,
        }
    }

    /// The attribution grade this card announces.
    pub const fn grade(&self) -> PlayerAttributionGrade {
        self.grade
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

    /// The same concise record grammar used by all hosted surfaces. The lead phrase names the
    /// ACTUAL attribution grade (see [`PlayerAttributionGrade`]) instead of an undifferentiated
    /// "Verified turn": an asserted turn reads "Recorded (asserted …)" (executor-admitted, actor not
    /// verified), a user-held signature "Signed by …", a custodial one "Signed (custodial) by …".
    pub fn compact_text(&self, replay: PlayerReplaySurface) -> String {
        let lifecycle = match self.disposition {
            PlayerSessionDisposition::Continues => "Session continues.",
            PlayerSessionDisposition::Complete => "Session complete.",
            PlayerSessionDisposition::Undisclosed => "Session state is not disclosed by this card.",
        };
        format!(
            "{} · executor receipt {}. {lifecycle} {}",
            self.lead_phrase(),
            self.receipt_hex(),
            replay.instruction(),
        )
    }

    /// The grade-appropriate lead phrase, naming the actor identity when the surface knows it.
    /// Sober register — no "Verified" for an unverified actor, no hype.
    fn lead_phrase(&self) -> String {
        let by = |verb: &str| match &self.identity {
            Some(id) => format!("{verb} by {id}"),
            None => verb.to_string(),
        };
        match self.grade {
            // Executor-admitted; the actor is a frontend-asserted label, NOT cryptographically
            // verified. Name it parenthetically when known, honestly flagged as asserted.
            PlayerAttributionGrade::Asserted => match &self.identity {
                Some(id) => format!("Recorded (asserted {id})"),
                None => "Recorded (asserted)".to_string(),
            },
            // A key the user holds signed.
            PlayerAttributionGrade::SignedUserHeld => by("Signed"),
            // A server-held key signed for the user — honest that the server, not the user's device,
            // produced the signature.
            PlayerAttributionGrade::SignedCustodial => by("Signed (custodial)"),
            // An owning operation adapter already verified the receipt this card re-publishes.
            PlayerAttributionGrade::OperationVerified => "Verified turn".to_string(),
        }
    }
}
