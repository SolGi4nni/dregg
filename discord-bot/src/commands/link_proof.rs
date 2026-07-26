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

use webauth_core::link_registry::LinkStore;

use crate::BotState;
use crate::db::IdentityMode;
use crate::embeds;

// ─── Registration ───────────────────────────────────────────────────────────

/// How long a `/link-web` code is good for. ⚑ Read from
/// [`webauth_core::link_claim::PHRASE_LINK_CODE_TTL_SECS`] rather than restated here: the web page
/// tells the player this window in prose, and a second constant on this side is exactly how a page
/// ends up promising a window its issuer does not honour.
pub const LINK_WEB_CODE_TTL_SECS: u64 = webauth_core::link_claim::PHRASE_LINK_CODE_TTL_SECS;

/// The web page a `/link-web` code is pasted into, relative to `DESCENT_WEB_BASE`.
const LINK_WEB_PATH: &str = "/identity/link";

/// Register `/link-web` — mint a single-use code that proves this Discord account to the web surface.
pub fn register_link_web() -> CreateCommand {
    CreateCommand::new("link-web")
        .description("Get a code that proves this Discord account to the web identity page")
}

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
/// The stable server key for the nonce'd link challenge (`webauth_core::challenge`), derived from
/// the bot secret so it survives restarts without a separate env, domain-separated from every
/// other use of the secret. Shared by `/link-cipherclerk` (issue) and `/link-prove` (verify).
pub fn link_challenge_key(bot_secret: &[u8; 32]) -> [u8; 32] {
    blake3::derive_key("dregg-discord-link-challenge-v1", bot_secret)
}

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

// ─── `/link-web` — the phrase-link ceremony's issuer half ───────────────────

/// Handle `/identity link-web` — **hand this user a single-use code that proves this Discord account
/// to the web identity page.**
///
/// The gap this closes: the web surface's own identity is **24 BIP39 words** the player holds
/// (`dreggnet-web`'s `seed_identity`), and the two existing link ceremonies (`/tg/link`, `/da/link`)
/// both require a root key sitting in a browser's `localStorage`. A phrase-derived key is not there —
/// it exists only while the phrase is in hand. So a web player and their Discord self stayed two
/// different people with two histories on one board, and no command here could change that.
///
/// What the code is, and why the uid in it cannot be edited: the code is
/// `<discord uid>:<challenge>`, and the challenge is minted under
/// [`webauth_core::link_claim::account_challenge_key`]`(base, "discord", uid)` — a key derived PER
/// ACCOUNT from `bot_secret`. The web verifier recomputes that key from the uid it was handed, so a
/// code re-presented under a different uid authenticates under nothing. The uid is therefore proven,
/// not asserted, and only a holder of `bot_secret` can mint one at all.
///
/// ⚑ HONEST SCOPE, said in the reply: linking does not stop this identity being CUSTODIAL. The
/// operator holds `bot_secret` and can derive this user's key before the link and after it. What a
/// link buys is that the boards rank the human once instead of twice.
pub async fn handle_link_web(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;

    let uid = command.user.id.get();
    let uid_str = uid.to_string();
    let now_secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);

    // ONE mint, in `webauth-core`, shared with the web verifier — never re-derived beside it.
    let Some(code) = webauth_core::link_claim::mint_phrase_link_code(
        &state.config.bot_secret,
        "discord",
        &uid_str,
        now_secs,
        LINK_WEB_CODE_TTL_SECS,
    ) else {
        return edit(
            ctx,
            command,
            embeds::error_embed(
                "Could Not Mint A Code",
                "This account id could not be encoded into a link code. That should be impossible \
                 for a Discord snowflake — please report it.",
            ),
        )
        .await;
    };

    // ⚑ THE PHONE PATH. With a web base configured, hand the player a TAPPABLE link that carries the
    // code, so a phone reader taps once and lands on the page with the box already filled — copying a
    // 117-character token between two apps on a phone was the real friction here. Without a web base
    // the code is still correct and still usable: say the path rather than inventing a host.
    //
    // A code in a URL is a real (bounded) widening — see `dreggnet-web`'s `identity_link::LinkQuery`
    // for the three bounds and the residual. It is why this reply is EPHEMERAL: only the caller sees
    // it, it is not in channel history, and the page strips the code from the address bar on arrival.
    let base = super::descent::descent_web_base();
    let where_to = match &base {
        Some(base) => format!("{}{LINK_WEB_PATH}", base.trim_end_matches('/')),
        None => format!(
            "the identity page of the dregg web surface you play on, at `{LINK_WEB_PATH}` \
             (this bot has no web base configured, so it cannot print the full link)"
        ),
    };
    // The code is `<uid>:<base64url>.<hex>`; `:` and `.` are sub-delims/unreserved in a query value
    // and every other character is already URL-safe, so the code needs no percent-encoding — pinned
    // by `webauth_core::link_claim`'s own code-shape test rather than assumed here.
    let tap_link = base
        .as_ref()
        .map(|base| format!("{}{LINK_WEB_PATH}?code={code}", base.trim_end_matches('/')));

    // Is this account ALREADY resolved to a root? Say so, so a re-link reads as a rebind rather than
    // as a mystery. Read-only; a missing/unreadable store just omits the line.
    let custodial = crate::cipherclerk::UserCipherclerk::derive(
        &state.config.bot_secret,
        uid,
        state.federation_id_bytes,
    );
    let already = webauth_core::link_registry::FileLinkStore::new(
        webauth_core::link_registry::default_store_path(),
    )
    .resolve_root(custodial.public_key_hex())
    .ok()
    .flatten();

    let mut embed =
        embeds::dregg_embed("Link This Account To Your Web Identity").description(format!(
            "Paste the whole line below into **{where_to}**, together with your 24 words. \
             The code is good for **{minutes} minutes** and works **once**.",
            minutes = LINK_WEB_CODE_TTL_SECS / 60,
        ));
    // On a phone this is the whole flow: one tap, then type your words. Listed FIRST because it is
    // the path most readers want, with the raw code kept below for desktop and for copy-paste.
    if let Some(link) = &tap_link {
        embed = embed.field(
            "📱 On your phone — one tap",
            format!(
                "[Open the link page with this code filled in]({link})\n\
                 _Only you can see this message. Do not forward the link: inside its \
                 {minutes} minutes the code is a bearer token._",
                minutes = LINK_WEB_CODE_TTL_SECS / 60,
            ),
            false,
        );
    }
    embed = embed
        .field("Your code", format!("```\n{code}\n```"), false)
        .field(
            "Why your 24 words are asked for there",
            "The link is a signature by the key your words derive, and nothing but those words can \
             produce it — the web server holds no copy and neither does your browser. So the signing \
             happens inside that one request and every byte of secret material is wiped before the \
             page answers. If you have no 24 words yet, claim them on that surface's `/identity` \
             page first: there is nothing to link to without them.",
            false,
        )
        .field(
            "What linking gives you",
            "One row on the Descent board instead of two strangers, and a `/you` page that counts \
             the tables and runs from BOTH sides.",
            false,
        )
        .field(
            "⚑ What linking does NOT change",
            "This Discord identity stays **custodial**. Its key is derived from the bot operator's \
             secret, so they can act as you here — that was true before you link and it is true \
             after. Only your 24 words are self-held. A link joins the RECORDS, never the custody, \
             and the web page says the same thing in the same words.",
            false,
        );
    if let Some(root) = already {
        embed = embed.field(
            "Already linked",
            format!(
                "This account is already bound to the root key `{}…`. Using a new code with a \
                 DIFFERENT phrase rebinds it to that one instead — the old link is superseded, not \
                 edited, and nothing is deleted.",
                &root[..16.min(root.len())]
            ),
            false,
        );
    }
    edit(ctx, command, embed).await;
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

    // Freshness gate — the challenge is a nonce'd, TTL'd webauth token issued by /link-cipherclerk.
    // A signature REPLAYED over a stale challenge dies here, closing the deterministic-challenge
    // replay wound. check_link_proof below verifies the signature ITSELF over the challenge bytes.
    let now_secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    if webauth_core::challenge::verify(
        &link_challenge_key(&state.config.bot_secret),
        &challenge,
        now_secs,
    )
    .is_err()
    {
        return edit(
            ctx,
            command,
            embeds::warning_embed(
                "Challenge Expired",
                "This link challenge is expired or invalid — challenges are time-limited and \
                 single-use now. Run `/link-cipherclerk` again for a fresh one, then `/link-prove`.",
            ),
        )
        .await;
    }

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

            // CROSS-PLATFORM: record (discord custodial pubkey -> the proven ROOT key K) into the
            // SHARED link registry. The proven external key IS the root; the bot-derived discord
            // custodial pubkey is what turns are attributed under and what `resolve_root` maps FROM.
            // A Telegram/web session that later links to the SAME K resolves to one human.
            let root_pubkey_hex = public_key_hex.trim().to_lowercase();
            let custodial = crate::cipherclerk::UserCipherclerk::derive(
                &state.config.bot_secret,
                command.user.id.get(),
                state.federation_id_bytes,
            );
            let now_secs = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs())
                .unwrap_or(0);
            let cross_platform_recorded = webauth_core::link_registry::FileLinkStore::new(
                webauth_core::link_registry::default_store_path(),
            )
            .record(&webauth_core::link_registry::LinkRecord {
                root_pubkey_hex,
                platform: "discord".to_string(),
                platform_uid: discord_id.clone(),
                custodial_pubkey_hex: custodial.public_key_hex().to_string(),
                verified_at: now_secs,
            })
            .is_ok();

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
                    )
                    .field(
                        "One you, everywhere",
                        if cross_platform_recorded {
                            "This key is now your **root identity** across platforms. Link the \
                             same key from Telegram (the Mini App) and you become ONE human — your \
                             Discord and Telegram play resolve together on boards + leaderboards."
                        } else {
                            "_(the cross-platform link registry was unavailable; the local proof \
                             still holds — retry to record the cross-platform binding.)_"
                        },
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
    /// The link challenge is now NONCE'D and TTL'd — closing the deterministic-challenge replay
    /// wound (the old blake3(discord_id:address) was identical forever, so a captured signature
    /// replayed across unlink/relink). Two issuances differ; a fresh one verifies; a stale one does not.
    #[test]
    fn a_link_challenge_is_nonced_fresh_and_expires() {
        let key = super::link_challenge_key(&[7u8; 32]);
        let c = webauth_core::challenge::issue(&key, 1_000, 900);
        assert!(
            webauth_core::challenge::verify(&key, &c, 1_005).is_ok(),
            "fresh challenge verifies"
        );
        assert!(
            webauth_core::challenge::verify(&key, &c, 1_000 + 10_000).is_err(),
            "a challenge past its TTL is refused (a replayed old signature dies here)"
        );
        assert_ne!(
            c,
            webauth_core::challenge::issue(&key, 1_000, 900),
            "each issuance is a fresh nonce — never the old deterministic string"
        );
    }

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

    // ─── `/link-web` — the cross-process weld ────────────────────────────────

    /// ⚑ THE CROSS-PROCESS WELD. A code this command mints is one the WEB verifier accepts, and the
    /// two sides never share code beyond `webauth-core` — so this test drives exactly the pair of
    /// functions the two processes call. A drift in either derivation lands here.
    #[test]
    fn a_link_web_code_verifies_under_the_shared_verifier() {
        let bot_secret = [0x3cu8; 32];
        let uid = 6_913_902_526_u64;
        let now = 1_790_000_000u64;
        let code = webauth_core::link_claim::mint_phrase_link_code(
            &bot_secret,
            "discord",
            &uid.to_string(),
            now,
            LINK_WEB_CODE_TTL_SECS,
        )
        .expect("a snowflake mints");

        let (uid_out, chal) =
            webauth_core::link_claim::parse_link_code(&code).expect("the code round-trips");
        assert_eq!(uid_out, uid.to_string(), "the uid survives the encoding");

        // The verifier's side: recompute the per-account key, derive the custodial pubkey the way
        // THIS bot does, and check a root-signed claim over it.
        let account_key = webauth_core::link_claim::account_challenge_key(
            &webauth_core::link_claim::phrase_link_challenge_key(&bot_secret),
            "discord",
            uid_out,
        );
        let custodial = crate::cipherclerk::UserCipherclerk::derive(&bot_secret, uid, [0u8; 32])
            .public_key_hex()
            .to_string();
        let root_seed = [0x77u8; 32];
        let (root_pk, sig) = webauth_core::link_claim::sign_link_claim(
            &root_seed, "discord", uid_out, &custodial, chal,
        )
        .expect("the root signs");
        assert_eq!(
            webauth_core::link_claim::verify_link_claim(
                &account_key,
                "discord",
                uid_out,
                &custodial,
                &root_pk,
                chal,
                &sig,
                now + 30,
            ),
            Ok(())
        );

        // ⚑ THE UID TOOTH, from this side: swapping the uid in the pasted code makes it authenticate
        // under nothing, so a player cannot claim somebody else's Discord account.
        let other_key = webauth_core::link_claim::account_challenge_key(
            &webauth_core::link_claim::phrase_link_challenge_key(&bot_secret),
            "discord",
            "222",
        );
        assert!(webauth_core::challenge::verify(&other_key, chal, now + 30).is_err());

        // And a code past its window is dead, so a screenshot in a channel goes stale.
        assert!(
            webauth_core::challenge::verify(&account_key, chal, now + LINK_WEB_CODE_TTL_SECS + 1)
                .is_err(),
            "a code must expire at its stated window"
        );
    }

    /// The `/link-web` window is the SHARED constant, not a second number beside the web page's copy.
    #[test]
    fn the_link_web_window_is_the_shared_constant() {
        assert_eq!(
            LINK_WEB_CODE_TTL_SECS,
            webauth_core::link_claim::PHRASE_LINK_CODE_TTL_SECS
        );
        assert_eq!(LINK_WEB_CODE_TTL_SECS / 60, 15, "the page says 15 minutes");
    }

    /// The `/link-web` code's challenge key is DISTINCT from this file's own `/link-prove` challenge
    /// key: the two ceremonies prove different things (holding a phrase vs. holding an external
    /// cell's key), so a code from one must never be spendable in the other.
    #[test]
    fn the_link_web_key_is_not_the_link_prove_key() {
        let secret = [5u8; 32];
        assert_ne!(
            webauth_core::link_claim::phrase_link_challenge_key(&secret),
            link_challenge_key(&secret)
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
