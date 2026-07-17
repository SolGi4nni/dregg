//! `/link-prove` — **the ownership-proof step `/link-cipherclerk` was missing.**
//!
//! `/link-cipherclerk` records an external cell + a blake3 challenge and parks the identity at
//! [`IdentityMode::ExternalPending`] — which the rest of the bot rightly refuses to sign for.
//! Before this command there was no way to leave that state: the pending link was a permanent
//! dead-end (backlog 2026-07-17 #4). This closes the loop:
//!
//! 1. the user signs the EXACT challenge string (shown by `/link-cipherclerk`) with their
//!    external cell's Ed25519 key;
//! 2. `/link-prove public-key:<64 hex> signature:<128 hex>` verifies, in front of the user:
//!    * the supplied public key **derives the linked cell id** (the canonical
//!      `CellId::derive_raw(pk, blake3("default"))` — the same derivation every
//!      `AppCipherclerk` identity uses), or IS the linked address verbatim (key-as-address);
//!    * the Ed25519 signature over the challenge bytes **verifies against that key**
//!      (`verify_strict` — no malleable acceptances);
//! 3. on success the row is promoted to [`IdentityMode::ExternalVerified`] — which genuinely
//!    unlocks the paths gated on `mode != ExternalPending`: redeeming handoffs, receiving
//!    `/cap-delegate` grants, and the dashboard actions that only need an attributable cell.
//!
//! HONEST SCOPE: a verified EXTERNAL link still cannot be custodially signed for — the user
//! holds the key, the bot does not. The success embed says exactly which doors open and which
//! stay hosted-only.

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use crate::BotState;
use crate::db::IdentityMode;
use crate::embeds;

// ─── Registration ───────────────────────────────────────────────────────────

/// Register `/link-prove <public-key> <signature>`.
pub fn register() -> CreateCommand {
    CreateCommand::new("link-prove")
        .description("Prove you own your linked external cell — sign the challenge, submit here")
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "public-key",
                "Your cell's Ed25519 public key (64 hex chars)",
            )
            .required(true),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::String,
                "signature",
                "Ed25519 signature over the exact challenge string (128 hex chars)",
            )
            .required(true),
        )
}

// ─── The pure verification core (unit-tested without Discord) ───────────────

/// The outcome of checking a link proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LinkProofCheck {
    /// The key derives (or is) the linked cell AND the signature verifies over the challenge.
    Verified {
        /// `true` when the linked address was the raw public key itself rather than the
        /// canonical derived cell id.
        key_is_address: bool,
    },
    /// The supplied public key neither derives the linked cell id (canonical `"default"`
    /// domain) nor equals it verbatim.
    KeyDoesNotDeriveCell,
    /// The public key bytes are not a valid Ed25519 point.
    BadPublicKey,
    /// The signature does not verify over the challenge bytes under the supplied key.
    BadSignature,
}

/// Check one ownership proof: does `public_key` account for `cell_id_hex`, and does
/// `signature` verify over the EXACT `challenge` string under it?
pub fn check_link_proof(
    cell_id_hex: &str,
    challenge: &str,
    public_key: &[u8; 32],
    signature: &[u8; 64],
) -> LinkProofCheck {
    // The canonical cell-id derivation every AppCipherclerk identity uses:
    // CellId::derive_raw(pk, blake3(domain)) with the framework default domain "default".
    let token_id = *blake3::hash(b"default").as_bytes();
    let derived = dregg_types::CellId::derive_raw(public_key, &token_id);
    let derived_hex = hex::encode(derived.0);
    let key_hex = hex::encode(public_key);

    let key_is_address = key_hex.eq_ignore_ascii_case(cell_id_hex);
    if !key_is_address && !derived_hex.eq_ignore_ascii_case(cell_id_hex) {
        return LinkProofCheck::KeyDoesNotDeriveCell;
    }

    let Ok(vk) = ed25519_dalek::VerifyingKey::from_bytes(public_key) else {
        return LinkProofCheck::BadPublicKey;
    };
    let sig = ed25519_dalek::Signature::from_bytes(signature);
    if vk.verify_strict(challenge.as_bytes(), &sig).is_err() {
        return LinkProofCheck::BadSignature;
    }
    LinkProofCheck::Verified { key_is_address }
}

/// The one-paragraph "how to produce the signature" instruction, shared with the
/// `/link-cipherclerk` pending embed so both surfaces teach the same incantation.
pub fn how_to_prove() -> &'static str {
    "Sign the EXACT challenge string (UTF-8 bytes, no newline) with your cell's Ed25519 \
     key, hex-encode the 64-byte signature, then run \
     `/link-prove public-key:<your 64-hex pubkey> signature:<128 hex>`."
}

// ─── Handler ────────────────────────────────────────────────────────────────

/// Handle `/link-prove`.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let public_key_hex = str_opt(command, "public-key").unwrap_or_default();
    let signature_hex = str_opt(command, "signature").unwrap_or_default();

    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;

    let discord_id = command.user.id.get().to_string();
    let identity = match state.db.get_user_identity(&discord_id).await {
        Ok(Some(identity)) => identity,
        Ok(None) => {
            return edit(
                ctx,
                command,
                embeds::warning_embed(
                    "Nothing To Prove",
                    "No identity is linked to your Discord account. `/link-cipherclerk` records \
                     an external cell (and its challenge) first; `/cipherclerk create` makes a \
                     hosted one that needs no proof.",
                ),
            )
            .await;
        }
        Err(e) => {
            return edit(
                ctx,
                command,
                embeds::error_embed("Database Error", &e.to_string()),
            )
            .await;
        }
    };

    match identity.mode {
        IdentityMode::ExternalPending => {}
        IdentityMode::ExternalVerified => {
            return edit(
                ctx,
                command,
                embeds::success_embed("Already Proven").description(
                    "This external link already passed its ownership proof — nothing to redo.",
                ),
            )
            .await;
        }
        IdentityMode::Hosted => {
            return edit(
                ctx,
                command,
                embeds::warning_embed(
                    "Hosted Identity Needs No Proof",
                    "Your identity is a hosted cipherclerk (the bot derives and holds its key), \
                     so there is no external ownership to prove.",
                ),
            )
            .await;
        }
    }

    let Some(challenge) = identity.link_challenge.clone() else {
        return edit(
            ctx,
            command,
            embeds::error_embed(
                "No Challenge On Record",
                "The pending link has no stored challenge. Run `/unlink-cipherclerk` then \
                 `/link-cipherclerk` again to mint a fresh one.",
            ),
        )
        .await;
    };

    let Some(public_key) = decode_fixed::<32>(&public_key_hex) else {
        return edit(
            ctx,
            command,
            embeds::error_embed(
                "Invalid Public Key",
                "public-key must be 64 hex characters.",
            ),
        )
        .await;
    };
    let Some(signature) = decode_fixed::<64>(&signature_hex) else {
        return edit(
            ctx,
            command,
            embeds::error_embed("Invalid Signature", "signature must be 128 hex characters."),
        )
        .await;
    };

    match check_link_proof(&identity.cell_id, &challenge, &public_key, &signature) {
        LinkProofCheck::Verified { key_is_address } => {
            if let Err(e) = state
                .db
                .register_user_with_mode(
                    &discord_id,
                    &identity.cell_id,
                    IdentityMode::ExternalVerified,
                    None,
                )
                .await
            {
                return edit(
                    ctx,
                    command,
                    embeds::error_embed("Promotion Failed", &e.to_string()),
                )
                .await;
            }
            let binding = if key_is_address {
                "the linked address IS this public key"
            } else {
                "this key derives the linked cell id (canonical `default`-domain derivation)"
            };
            edit(
                ctx,
                command,
                embeds::success_embed("Ownership Proven")
                    .description(format!(
                        "The Ed25519 signature verifies over your challenge and {binding}. \
                         Your link is now **verified**."
                    ))
                    .field(
                        "Cell",
                        format!(
                            "`{}...`",
                            &identity.cell_id[..16.min(identity.cell_id.len())]
                        ),
                        true,
                    )
                    .field(
                        "Now unlocked",
                        "Redeeming handoff tokens (`/cap-accept`), receiving `/cap-delegate` \
                         grants, and every surface that needs an attributable (non-pending) cell.",
                        false,
                    )
                    .field(
                        "Still hosted-only",
                        "The bot cannot SIGN for an external cell — you hold its key. \
                         `/cap-share`, `/cap-delegate`-as-granter, and custodial turns need a \
                         hosted `/cipherclerk create` identity.",
                        false,
                    ),
            )
            .await;
        }
        LinkProofCheck::KeyDoesNotDeriveCell => {
            edit(
                ctx,
                command,
                embeds::error_embed(
                    "Key Does Not Match The Linked Cell",
                    "The supplied public key neither derives the linked cell id (canonical \
                     `default`-domain derivation) nor equals it verbatim. Check you pasted the \
                     public key of the SAME cell you linked.",
                ),
            )
            .await;
        }
        LinkProofCheck::BadPublicKey => {
            edit(
                ctx,
                command,
                embeds::error_embed(
                    "Invalid Public Key",
                    "Those 32 bytes are not a valid Ed25519 public key.",
                ),
            )
            .await;
        }
        LinkProofCheck::BadSignature => {
            edit(
                ctx,
                command,
                embeds::error_embed(
                    "Signature Does Not Verify",
                    &format!(
                        "The signature does not verify over the challenge under that key. \
                         {}\nYour challenge (sign THESE bytes):\n```\n{}\n```",
                        how_to_prove(),
                        challenge
                    ),
                ),
            )
            .await;
        }
    }
}

// ─── Helpers ────────────────────────────────────────────────────────────────

fn str_opt(command: &CommandInteraction, name: &str) -> Option<String> {
    command
        .data
        .options
        .iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
}

fn decode_fixed<const N: usize>(hex_str: &str) -> Option<[u8; N]> {
    hex::decode(hex_str.trim()).ok()?.try_into().ok()
}

async fn edit(ctx: &Context, command: &CommandInteraction, embed: serenity::all::CreateEmbed) {
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the verification core driven with REAL Ed25519 keys. No Discord.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::Signer;

    fn keypair() -> (ed25519_dalek::SigningKey, [u8; 32]) {
        let sk = ed25519_dalek::SigningKey::from_bytes(&[42u8; 32]);
        let pk = sk.verifying_key().to_bytes();
        (sk, pk)
    }

    /// A signature over the exact challenge, under a key that DERIVES the linked cell id
    /// (the canonical derivation), verifies.
    #[test]
    fn a_real_proof_over_the_derived_cell_verifies() {
        let (sk, pk) = keypair();
        let token_id = *blake3::hash(b"default").as_bytes();
        let cell_hex = hex::encode(dregg_types::CellId::derive_raw(&pk, &token_id).0);
        let challenge = "dregg-discord-link-v1:deadbeef";
        let sig = sk.sign(challenge.as_bytes()).to_bytes();
        assert_eq!(
            check_link_proof(&cell_hex, challenge, &pk, &sig),
            LinkProofCheck::Verified {
                key_is_address: false
            }
        );
    }

    /// A linked address that IS the raw public key (key-as-address) also verifies, and is
    /// labeled as such.
    #[test]
    fn a_key_as_address_link_verifies() {
        let (sk, pk) = keypair();
        let challenge = "dregg-discord-link-v1:cafe";
        let sig = sk.sign(challenge.as_bytes()).to_bytes();
        assert_eq!(
            check_link_proof(&hex::encode(pk), challenge, &pk, &sig),
            LinkProofCheck::Verified {
                key_is_address: true
            }
        );
    }

    /// A signature over the WRONG message is refused — the challenge is load-bearing.
    #[test]
    fn a_signature_over_another_message_is_refused() {
        let (sk, pk) = keypair();
        let token_id = *blake3::hash(b"default").as_bytes();
        let cell_hex = hex::encode(dregg_types::CellId::derive_raw(&pk, &token_id).0);
        let sig = sk.sign(b"a different message").to_bytes();
        assert_eq!(
            check_link_proof(&cell_hex, "dregg-discord-link-v1:deadbeef", &pk, &sig),
            LinkProofCheck::BadSignature
        );
    }

    /// A key that does not account for the linked cell is refused BEFORE any signature check —
    /// a valid signature under an unrelated key must not promote the link.
    #[test]
    fn an_unrelated_key_is_refused_even_with_a_valid_signature() {
        let (sk, pk) = keypair();
        let challenge = "dregg-discord-link-v1:beef";
        let sig = sk.sign(challenge.as_bytes()).to_bytes();
        let unrelated_cell = hex::encode([9u8; 32]);
        assert_eq!(
            check_link_proof(&unrelated_cell, challenge, &pk, &sig),
            LinkProofCheck::KeyDoesNotDeriveCell
        );
    }
}
