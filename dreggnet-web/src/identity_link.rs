//! # `identity_link` — **your web self and your Discord self are ONE player.**
//!
//! ## The measured problem
//!
//! All three shipped games (`descent`, `automatafl`, `tug`) are playable on the web, in Discord and
//! in Telegram, and **a player was a different person on each**, with a different history on the
//! same board. The two identities are not merely differently *named*; they have different CUSTODY,
//! and that difference is real:
//!
//! | | web ([`crate::seed_identity`]) | Discord / Telegram |
//! |---|---|---|
//! | key | derived from **your** 24 words | `BLAKE3_derive_key(bot-domain, bot_secret ‖ uid)` |
//! | who can produce it | only a holder of the phrase | **the operator**, for any user |
//! | stored | nowhere | nowhere — it is *re-derivable* from the operator's secret |
//!
//! ## What this module does, and what it deliberately does NOT
//!
//! It **does not merge the keys.** There is no key import, no re-keying, and no path by which the
//! bot begins signing as your self-held key or your phrase begins deriving the custodial one. Those
//! two keys stay distinct, with the custody difference above intact, because laundering that
//! difference would be the dishonest version of this feature.
//!
//! What it unions is the **view**: after a proven link, `GET /you` counts the tables and runs of
//! *both* identities as yours, and the Descent board ranks you **once** instead of twice as
//! strangers. That is exactly the resolution seam [`webauth_core::link_registry`] and
//! [`webauth_core::identity_resolve::RootResolver`] were built for — and which the web player could
//! not reach, because every existing ceremony (`/tg/link`, `/da/link`) requires a root key K sitting
//! in the browser's `localStorage`, and a phrase-derived key is not in `localStorage`. It only
//! exists while the phrase is in hand.
//!
//! ## The ceremony, and WHERE THE SIGNATURE HAPPENS
//!
//! ```text
//!   Discord: /cipherclerk link-web     →  a pasteable CODE, ephemeral, 15 minutes
//!            (mints challenge::issue under account_challenge_key(platform, uid))
//!            ⚑ NOT `/identity link-web`: `24e47322b` demoted `/identity` to a lab-only
//!            command, which is why the ceremony's issuer was folded onto `/cipherclerk`.
//!
//!   Web:     POST /identity/link       →  code + your 24 words, in ONE request
//!            gate:   OUR OWN PAGE — seed_identity::request_origin, fail-closed  ← gate 0
//!            gate:   challenge::verify under the SAME derived key   ← the platform's half
//!            derive: 24 words → the root Ed25519 key                ← your half
//!            sign:   webauth_core::link_claim::sign_link_claim
//!            check:  verify_link_claim (the shared verifier, on our own output)
//!            record: two LinkRecords, then zeroize
//! ```
//!
//! **The signature is produced SERVER-SIDE, inside the one POST that holds the phrase, and the
//! phrase is asked for again rather than captured at claim time.** Both halves of that were choices:
//!
//! * *Server-side, not in the browser* — because turning 24 words into a key needs BIP39 + BLAKE3,
//!   and `seed_identity`'s doc records that hand-rolling BLAKE3 in JS is forbidden here and adding a
//!   JS BLAKE3 is **a dependency decision left for ember**. So this reuses the exact trust posture
//!   `POST /identity/restore` already has (a phrase in a POST body, derived and zeroized in-request,
//!   never logged or persisted) and adds **no new exposure and no new dependency**. It is stated
//!   plainly on the page rather than implied.
//! * *Asked for again, not captured at claim time* — linking needs a code that only exists after the
//!   player has gone to Discord and run a command. Asking at claim time would put a Discord round
//!   trip in front of "write these words down", which is the one screen that must not grow a step.
//!   Re-entry costs the player a paste and costs the system nothing new, because it is the identical
//!   code path `/identity/restore` is.
//!
//! ## Why the pasted account id is PROVEN, not asserted
//!
//! A code is `<platform_uid>:<challenge>`, and the challenge is minted under
//! [`webauth_core::link_claim::account_challenge_key`]`(base, platform, uid)` — a key **derived per
//! account**. The verifier recomputes that key from the uid it was handed, so a code minted for uid
//! `A` fails its MAC the moment it is presented as uid `B`. The uid is therefore *tested*, never
//! trusted; and the custodial pubkey is never pasted at all — it is derived here from the uid with
//! the same `seed_for` the bot itself uses. Only a holder of the platform `bot_secret` can mint a
//! code that verifies, and the bot only ever mints one for the caller of the slash command.
//!
//! There is no "type in a public key" path anywhere in this module. That is deliberate: a public key
//! is public, so an asserted one would let anybody read a leaderboard and claim to be that player.
//!
//! ## ONE-TO-MANY: one web identity, several platforms
//!
//! A phrase may link **Discord *and* Telegram** (and, later, anything else with a `bot_secret`).
//! This costs nothing extra: [`webauth_core::link_registry`] is already keyed
//! `custodial → root`, its [`LinkStore::platforms_for_root`] already answers the reverse, and the
//! resolver already collapses N custodial keys onto one account id. The record is append-only and
//! latest-wins per custodial key, so a **rebind** (linking the same Discord account to a different
//! phrase) is just a later line — the older link is superseded, never mutated. The reverse
//! direction is bounded by the same rule: one Discord account resolves to exactly one human at a
//! time, which is what stops two people sharing a board row.
//!
//! ## Where the record lives
//!
//! `$DREGG_LINK_DIR/links.tsv` ([`webauth_core::link_registry::default_store_path`]) — **the store
//! that already exists**, that `/tg/link`, `/da/link` and the bot's `/identity link-prove` already
//! append to, and that the web Descent board and the bot's boards already read. No new store, no
//! new schema, no migration. Set `DREGG_LINK_DIR` to the same directory in every unit.
//!
//! ⚑ **The web row is a SELF-link, and that is not a fudge.** A link appends TWO records: the
//! platform's (`root = your phrase key`, `custodial = the bot-derived key`) and a `platform = "web"`
//! row whose `custodial` IS the root. Without that second row the resolver would map your Discord
//! key to `account_id_of_root(K)` while your web key still resolved to its own raw hex — two
//! different join keys, so the board would *still* print two rows. The web row is also literally
//! true: on the web your turns are attributed under that very key, and that key is self-held, so its
//! "custodial" key is itself.
//!
//! ## Feeding the eventual private version
//!
//! `webauth_core::linked_platforms` is the destination — "prove I am the same human across ≥N
//! platforms *without revealing which accounts*", via `dregg-credentials` STARK presentations. It is
//! unwired, and this module does not wire it. It does feed it: that construction is stated over a
//! root key K and a set of platform bindings under K, which is precisely what
//! [`LinkStore::platforms_for_root`] now returns for a phrase-derived K. The residual is that these
//! records are PLAINTEXT and PUBLIC-to-the-operator — the private version replaces the read path,
//! not the record.
//!
//! ## The phone path
//!
//! `GET /identity/link?code=…` prefills the code box, and the bot's ephemeral reply carries a
//! tappable link with the code in it — so a player reading Discord on a phone taps once and only has
//! to add their words. See [`LinkQuery`] for the cost of a code in a URL and the three bounds on it,
//! and [`link_form`] for the two-step flow (code -> "this is account N, is that you?" -> words)
//! that makes a forwarded link safe to look at: a prefilled code now lands on a screen with no
//! phrase box on it at all.
//!
//! ## Named residuals (work not done, said as such)
//!
//! * ⚑ **NO UN-LINK DOOR.** A rebind supersedes for the same custodial key, but a link made by
//!   mistake — or one made on a stranger's code that the player ticked through anyway — leaves a row
//!   that nothing here removes. It is display-only, and the consent box + the account disclosure are
//!   what stand in for the missing undo. A real revocation wants the deep version's identity cell
//!   (`docs/IDENTITY-LINK-DEEP-VERSION-DESIGN.md`), not another TSV line. **This is the first thing
//!   to build next.**
//! * ⚑ **NO QR CODE, and it is a dependency decision, not an oversight.** The obvious phone
//!   affordance is a QR of the prefill URL for a desktop→phone handoff. There is no QR encoder in this
//!   tree and none in the workspace graph, and a hand-written one carries ~160 recalled table entries
//!   (per-version alignment positions and EC block structure) whose errors produce a code that LOOKS
//!   right and does not scan — a failure this repo has no way to detect without a camera. So it is
//!   left for ember as a one-line choice: add a pure-Rust encoder crate (`qrcode`, no default
//!   features, matrix out → we draw the SVG ourselves, no image codec) or vendor a JS one beside
//!   `assets/noble-ed25519.js`. The tappable link already solves the in-Discord-on-a-phone case,
//!   which is the common one; the QR is only for the two-device case.
//! * Single-use is per-process ([`webauth_core::replay::NonceCache`]), so a restart re-opens a live
//!   code's window. Same posture as `/da/link`'s `link_replay`.
//! * A link is a display/grouping join. It does NOT make a browser turn signed, and it does NOT make
//!   your Discord key self-held. Both are said on the page, in those words.
//! * The consent box is a gate against a code a stranger HANDED you. It is not a gate against a
//!   request you never made: a hostile page can submit its own code with `mine=yes` already ticked,
//!   and the victim's browser makes the request. That is what
//!   [`LinkRefusal::NotFromOurPage`] refuses, and it is why the origin gate is gate 0 rather than a
//!   belt-and-braces afterthought — the consent box cannot defend a submission the player never saw.
//! * The consent box and the phrase ride in the SAME `POST`, so a player who was going to be fooled
//!   has already transmitted their words by the time they see the account id — which is why the id is
//!   printed on the GET, before the box is filled. A two-step flow (code → "this is account N, is
//!   that you?" → words) would make that structural instead of advisory.
//! * An access log or reverse proxy that records query strings sees a prefilled code for that one
//!   request. The page says to paste by hand on a shared machine.

use std::sync::Arc;

use axum::Router;
use axum::extract::{Form, Query, State};
use axum::http::{HeaderMap, StatusCode, header};
use axum::response::{Html, IntoResponse, Response};
use axum::routing::{get, post};
use serde::Deserialize;
use zeroize::{Zeroize, Zeroizing};

use dreggnet_offerings::{DreggIdentity, TurnSigner};
use webauth_core::challenge;
use webauth_core::link_claim::{
    PHRASE_LINK_CODE_TTL_SECS, account_challenge_key, parse_link_code, phrase_link_challenge_key,
    sign_link_claim, verify_link_claim,
};
use webauth_core::link_registry::{FileLinkStore, LinkRecord, LinkStore, default_store_path};
use webauth_core::replay::NonceCache;

use crate::seed_identity::{
    self, CLAIM_COOKIE, derive_root_keypair, honest_limits_html, normalize_typed_phrase,
    read_cookie, short_tag,
};
use crate::{document_with_head, esc, notice_html};

// ─────────────────────────────────────────────────────────────────────────────
// Constants.
// ─────────────────────────────────────────────────────────────────────────────

/// The `platform` string the web identity's own self-link record wears. NOT a bot-derived surface —
/// see the ⚑ note in the module doc for why a self-link row exists and why it is honest.
pub const WEB_PLATFORM: &str = "web";

/// The bound on in-flight single-use code nonces (the `/da/link` bound).
const REPLAY_CAPACITY: usize = 8192;

/// The code window in MINUTES, for the page copy — computed from
/// [`PHRASE_LINK_CODE_TTL_SECS`] so the sentence a player reads cannot drift from the window the
/// issuer actually mints.
fn code_window_minutes() -> u64 {
    PHRASE_LINK_CODE_TTL_SECS / 60
}

// ─────────────────────────────────────────────────────────────────────────────
// The platforms a phrase can link to.
// ─────────────────────────────────────────────────────────────────────────────

/// A platform whose custodial identity a phrase can be proven to control.
///
/// Adding one is: a variant, its wire name, and its `seed_for`. The ceremony, the code format, the
/// record and the pages are all platform-generic — which is why Telegram cost this module nothing
/// beyond three match arms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinkPlatform {
    /// Discord, custodial key `dreggnet_discord_identity::seed_for(BOT_SECRET, uid)`.
    Discord,
    /// Telegram, custodial key `dreggnet_telegram::cipherclerk::seed_for(bot_secret, uid)`.
    Telegram,
}

impl LinkPlatform {
    /// **Every platform this module knows**, so a sweep over the surface (the dead-command tooth
    /// below) cannot silently miss a variant somebody adds later.
    pub const ALL: [LinkPlatform; 2] = [LinkPlatform::Discord, LinkPlatform::Telegram];

    /// The `platform` field written into the [`LinkRecord`] — the SAME strings `/da/link` and
    /// `/tg/link` already write, so a link made here and a link made there are one record shape.
    pub fn wire(self) -> &'static str {
        match self {
            LinkPlatform::Discord => "discord",
            LinkPlatform::Telegram => "telegram",
        }
    }

    /// The name a human reads.
    pub fn display(self) -> &'static str {
        match self {
            LinkPlatform::Discord => "Discord",
            LinkPlatform::Telegram => "Telegram",
        }
    }

    /// Where the player gets a code, in one sentence.
    ///
    /// ⚑ **This string names a command a PLAYER can type, which is not the same thing as a command
    /// that exists.** It said `/identity link-web` until 2026-07-26, and `24e47322b` had demoted
    /// `/identity` to `Door::Lab` — registered only inside `DREGG_LAB_GUILD_ID`, so an ordinary
    /// player typing it in a normal server got no autocomplete and no command. `link-web` was
    /// deliberately folded into `/cipherclerk` for exactly that reason, and the bot's own copy
    /// already said so (`discord-bot/src/commands/menus.rs:1312`, `start.rs:239`), with
    /// `the_rehomed_paths_land_on_advertised_commands` asserting `home_of("link-web") ==
    /// Some("cipherclerk")`. This page was the one surface left pointing at the dead spelling.
    /// `no_player_facing_copy_names_a_lab_only_bot_command` is the tooth on this file.
    pub fn how_to_get_a_code(self) -> &'static str {
        match self {
            LinkPlatform::Discord => {
                "In any server the bot is in (or a DM with it), run \
                 <code>/cipherclerk link-web</code>. The reply is only visible to you."
            }
            LinkPlatform::Telegram => {
                "DM the bot and send <code>/link-web</code>. The reply is only visible to you."
            }
        }
    }

    /// **The custodial dregg identity a platform uid resolves to** — the bot's OWN derivation,
    /// CALLED rather than mirrored (`dreggnet_discord_identity` / `dreggnet_telegram::cipherclerk`
    /// are the one impl each), so the key recorded here is byte-identical to the key that platform
    /// attributes turns under. The transient seed is wiped on drop.
    fn custodial_identity(self, bot_secret: &[u8; 32], uid: u64) -> DreggIdentity {
        let seed = match self {
            LinkPlatform::Discord => {
                Zeroizing::new(dreggnet_discord_identity::seed_for(bot_secret, uid))
            }
            LinkPlatform::Telegram => {
                Zeroizing::new(dreggnet_telegram::cipherclerk::seed_for(bot_secret, uid))
            }
        };
        TurnSigner::from_seed(*seed).identity()
    }
}

/// One configured platform: its identity master secret, and the phrase-link base key derived from
/// it once at mount.
struct ConfiguredPlatform {
    platform: LinkPlatform,
    /// The identity master secret — the SAME value the bot process reads. A fork here forks every
    /// user into two identities, which is why both sides resolve it from the same env var.
    bot_secret: Zeroizing<[u8; 32]>,
    /// `phrase_link_challenge_key(bot_secret)`, precomputed at mount.
    base_key: [u8; 32],
}

// ─────────────────────────────────────────────────────────────────────────────
// State + mount.
// ─────────────────────────────────────────────────────────────────────────────

/// The link door's axum state. Holds no player material — only the platform secrets, the spent-code
/// cache, and the store path.
pub struct IdentityLinkState {
    /// Every platform this deployment can link to. EMPTY is impossible: the router is not mounted.
    platforms: Vec<ConfiguredPlatform>,
    /// Spent code nonces, so ONE code links once (see the residual in the module doc).
    replay: NonceCache,
    /// The shared append-only link store. Resolved once so a test can point it elsewhere.
    store_path: std::path::PathBuf,
}

impl IdentityLinkState {
    /// Assemble state over an explicit platform list + store path — the seam tests drive.
    fn new(platforms: Vec<ConfiguredPlatform>, store_path: std::path::PathBuf) -> Self {
        IdentityLinkState {
            platforms,
            replay: NonceCache::new(true, REPLAY_CAPACITY),
            store_path,
        }
    }

    /// The platforms, for rendering.
    fn kinds(&self) -> Vec<LinkPlatform> {
        self.platforms.iter().map(|p| p.platform).collect()
    }
}

/// **Mount the link door.** Additive: `/identity/link` sits under the `/identity` prefix
/// [`seed_identity::identity_router`] already owns and overlaps nothing else.
pub fn identity_link_router(state: Arc<IdentityLinkState>) -> Router {
    Router::new()
        .route("/identity/link", get(get_link).post(post_link))
        // ⚑ STEP ONE of the two-step flow: a code alone, checked, answering "whose account is
        // this?" before any box on this site has asked for 24 words. See `authenticate_code`.
        .route("/identity/link/account", post(post_link_account))
        .with_state(state)
}

/// **Resolve the link door from the environment.** Reads whichever platform identity master secrets
/// are present:
///
/// * **Discord** — `BOT_SECRET` as 64 hex chars (the same var + parse
///   [`crate::discord_activity`] and `discord-bot/src/config.rs` use).
/// * **Telegram** — `TELEGRAM_BOT_TOKEN`, through
///   [`dreggnet_telegram::cipherclerk::master_secret_from_env`] (explicit `TELEGRAM_BOT_SECRET`,
///   else token-derived) — the same resolution [`crate::telegram_miniapp`] performs.
///
/// ⚑ **ALWAYS MOUNTED, even with no platform configured**, unlike the `/da` and `/tg` surfaces. The
/// reason is that `/identity`, `/you` and the Descent board all LINK here — and a link to a route
/// that does not exist is a 404 that teaches a player nothing. So an unconfigured deployment gets the
/// [`crate::explorer`] treatment: the page's job becomes SAYING that this server cannot prove a link
/// and naming what an operator would have to set, which is strictly more use than a dead link.
/// (An env-gated door would also mean the linking pages had to become conditional everywhere, i.e.
/// three more places that could silently drift out of agreement about whether the feature exists.)
pub fn identity_link_from_env() -> Router {
    identity_link_router(Arc::new(IdentityLinkState::new(
        platforms_from_env(),
        default_store_path(),
    )))
}

/// The configured platforms, from env. Empty is a legitimate state — see
/// [`identity_link_from_env`].
fn platforms_from_env() -> Vec<ConfiguredPlatform> {
    let mut platforms = Vec::new();

    if let Some(secret) = std::env::var(crate::discord_activity::BOT_SECRET_ENV)
        .ok()
        .filter(|v| !v.trim().is_empty())
        .and_then(|v| crate::discord_activity::bot_secret_from_hex(&v))
    {
        platforms.push(ConfiguredPlatform {
            platform: LinkPlatform::Discord,
            base_key: phrase_link_challenge_key(&secret),
            bot_secret: Zeroizing::new(secret),
        });
    }

    if let Some(secret) = std::env::var(crate::telegram_miniapp::TELEGRAM_BOT_TOKEN_ENV)
        .ok()
        .filter(|v| !v.trim().is_empty())
        .and_then(|token| dreggnet_telegram::cipherclerk::master_secret_from_env(&token).ok())
    {
        platforms.push(ConfiguredPlatform {
            platform: LinkPlatform::Telegram,
            base_key: phrase_link_challenge_key(&secret),
            bot_secret: Zeroizing::new(secret),
        });
    }

    if platforms.is_empty() {
        tracing::warn!(
            "/identity/link is mounted but can prove NOTHING — neither {} nor {} resolved an \
             identity master secret, so no platform code can be authenticated. The page says so. \
             Set the same {} (64 hex) the Discord bot reads, and/or {}, to enable linking.",
            crate::discord_activity::BOT_SECRET_ENV,
            crate::telegram_miniapp::TELEGRAM_BOT_TOKEN_ENV,
            crate::discord_activity::BOT_SECRET_ENV,
            crate::telegram_miniapp::TELEGRAM_BOT_TOKEN_ENV,
        );
    } else {
        let names: Vec<&str> = platforms.iter().map(|p| p.platform.wire()).collect();
        tracing::info!(
            platforms = ?names,
            store = %default_store_path().display(),
            "cross-platform identity linking LIVE at /identity/link (a phrase-derived root key \
             proves control of a platform account; the platform key stays CUSTODIAL and the link \
             does not change that)"
        );
    }
    platforms
}

// ─────────────────────────────────────────────────────────────────────────────
// The issuer side, as a library — so the bot and the tests mint the SAME code.
// ─────────────────────────────────────────────────────────────────────────────

/// **Mint the pasteable link code for a platform account** — a typed wrapper over
/// [`webauth_core::link_claim::mint_phrase_link_code`], which is where the mint actually lives.
///
/// The mint is in `webauth-core` and not here because the ISSUER is a different process in a
/// different workspace: `discord-bot` has `webauth-core` and does NOT have `dreggnet-web`, so a mint
/// exported from this crate would have forced the bot to re-derive the challenge key beside it — the
/// mirroring that is the drift class. This wrapper exists so THIS crate's tests drive the same
/// function the bot calls, byte for byte; if they ever disagreed, every test below would go red.
pub fn mint_link_code(
    bot_secret: &[u8; 32],
    platform: LinkPlatform,
    uid: u64,
    now: u64,
    ttl_secs: u64,
) -> String {
    webauth_core::link_claim::mint_phrase_link_code(
        bot_secret,
        platform.wire(),
        &uid.to_string(),
        now,
        ttl_secs,
    )
    .expect("a decimal uid is non-empty and carries no separator")
}

// ─────────────────────────────────────────────────────────────────────────────
// The refusal taxonomy — one variant per fail-closed gate, so a page can say WHICH bit.
// ─────────────────────────────────────────────────────────────────────────────

/// Why a link was refused. Every variant is a gate that ran and said no; nothing was recorded in any
/// of them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LinkRefusal {
    /// ⚑ **The request did not come from a page on this site.** The FIRST gate, ahead of everything
    /// else, because the ceremony writes a durable record and a cross-origin submission is how an
    /// attacker gets one written without the player watching.
    ///
    /// The attack this is against: a hostile page auto-submits an ordinary form carrying a code for
    /// **the attacker's own account** plus a ticked consent box, and the victim's browser makes the
    /// request. Every gate below then passes honestly — the code is genuine, the box is "ticked" — and
    /// the attacker's account lands on the victim's `/you` and merges into their board row, with no
    /// un-link door to undo it. Nothing is derived and no nonce is spent for a request that cannot
    /// show where it came from; see [`crate::seed_identity::request_origin`] for the mechanism and
    /// why it fails closed on a request that says nothing at all.
    NotFromOurPage,
    /// ⚑ This deployment holds NO platform identity secret, so no code could be authenticated even
    /// in principle. Distinct from [`CodeNotOurs`](LinkRefusal::CodeNotOurs) because telling a player
    /// their code "expired" when the server was never able to check one is a lie about whose fault it
    /// is — this is an operator's missing env, and the message says exactly that.
    NoPlatformConfigured,
    /// The pasted code is not `<uid>:<challenge>`.
    MalformedCode,
    /// The uid half is not a `u64` (no platform issues non-numeric account ids here).
    MalformedUid,
    /// No configured platform's key authenticates this code: forged, or minted by a deployment whose
    /// `bot_secret` this server does not share, or expired. Deliberately ONE refusal for all three —
    /// distinguishing them would be an oracle over which platforms are configured.
    CodeNotOurs,
    /// The code authenticated but has already been used (single-use).
    CodeAlreadyUsed,
    /// ⚑ The "this account is mine" box was not ticked, naming the account the code is for.
    ///
    /// **The attack this is against.** A stranger can hand you a link (or a code) for *their* account
    /// and ask you to run the ceremony. Nothing about that steals your words or your key — the phrase
    /// never leaves this request and no capability changes hands — but it would bind THEIR account to
    /// YOUR root, so their play would show up on your `/you` and merge into your board row. With no
    /// unlink door (a named residual), that is a mess you cannot tidy up.
    ///
    /// The defence is DISCLOSURE plus consent: the page prints the account id the code names, right
    /// beside the box asking for your words, and refuses until you say that account is yours.
    AccountNotConfirmed {
        /// The platform the code authenticated against.
        platform: LinkPlatform,
        /// The account id it is for.
        uid: String,
    },
    /// The phrase did not validate. Carries the WHICH-check-failed sentence already rendered
    /// ([`phrase_detail`]) rather than the `MnemonicError` itself, because "invalid phrase" is
    /// useless to somebody holding a piece of paper — and because `MnemonicError` is not `PartialEq`,
    /// so keeping it here would cost this taxonomy its equality (which every gate test compares on).
    BadPhrase(String),
    /// ⚑ Our OWN construction failed the shared verifier. Not a statement about the player: a
    /// refusal to write a record [`verify_link_claim`] would not accept. Should be unreachable.
    SelfCheckFailed(String),
    /// The append to the shared store failed (a read-only mount, a bad `DREGG_LINK_DIR`).
    NotRecorded(String),
}

impl LinkRefusal {
    fn http_status(&self) -> StatusCode {
        match self {
            LinkRefusal::MalformedCode | LinkRefusal::MalformedUid | LinkRefusal::BadPhrase(_) => {
                StatusCode::BAD_REQUEST
            }
            LinkRefusal::NotFromOurPage
            | LinkRefusal::CodeNotOurs
            | LinkRefusal::CodeAlreadyUsed => StatusCode::FORBIDDEN,
            LinkRefusal::AccountNotConfirmed { .. } => StatusCode::BAD_REQUEST,
            // Not the player's request being wrong — the deployment is incomplete.
            LinkRefusal::NoPlatformConfigured => StatusCode::SERVICE_UNAVAILABLE,
            LinkRefusal::SelfCheckFailed(_) | LinkRefusal::NotRecorded(_) => {
                StatusCode::INTERNAL_SERVER_ERROR
            }
        }
    }

    /// The sentence shown to the player. Every one begins "Refused:" so
    /// [`notice_html`] paints it as a refusal rather than as a success.
    fn message(&self) -> String {
        match self {
            LinkRefusal::NotFromOurPage => "Refused: this did not come from our page, so nothing \
                 was linked and nothing was recorded; your code was not spent and your words were \
                 not used. Open the link page here (/identity/link), paste your code, and try again. \
                 If something on another website submitted this for you, it was trying to attach an \
                 account to your identity without showing you which one."
                .to_string(),
            LinkRefusal::NoPlatformConfigured => "Refused: this server holds no chat-platform \
                 identity secret, so it cannot authenticate a link code from any bot; nothing was \
                 linked, and nothing you could paste would change that. This is an operator setting, \
                 not something wrong with your code or your words."
                .to_string(),
            LinkRefusal::MalformedCode => "Refused: that does not look like a link code. A code is \
                 your account id, a colon, then a long token. Copy the whole line the bot gave \
                 you, including the number at the front. Nothing was linked."
                .to_string(),
            LinkRefusal::MalformedUid => "Refused: the part of the code before the colon is not an \
                 account id. Copy the bot's line again without editing it. Nothing was linked."
                .to_string(),
            LinkRefusal::CodeNotOurs => format!(
                "Refused: this server cannot authenticate that code. Either it has expired (a code \
                 is good for {} minutes), or it was not issued by a bot this server shares an \
                 identity secret with. Ask the bot for a fresh code. Nothing was linked.",
                code_window_minutes()
            ),
            LinkRefusal::CodeAlreadyUsed => "Refused: that code has already been used, so nothing \
                 was linked by this attempt. Codes are single-use on purpose; otherwise somebody \
                 who saw yours over your shoulder could attach their own words to your account \
                 afterwards. Ask the bot for a fresh one."
                .to_string(),
            LinkRefusal::AccountNotConfirmed { platform, uid } => format!(
                "Refused: nothing was linked, because the confirmation box was not ticked. This code \
                 is for {} account {uid}. If that is not YOUR account (if somebody sent you this \
                 code or this link), stop here: linking it would put their play on your record. You \
                 can undo a link now, on the removal page, but not having made it is better. Your 24 \
                 words were not stored and your code was not spent either way.",
                platform.display()
            ),
            LinkRefusal::BadPhrase(detail) => format!(
                "Refused: {detail} Nothing was linked, and your code was NOT spent; you can fix \
                 the phrase and submit the same code again."
            ),
            LinkRefusal::SelfCheckFailed(detail) => format!(
                "Refused: this server built a link claim that its own verifier would not accept \
                 ({detail}), so it declined to record anything. That is a bug here, not something \
                 you did wrong."
            ),
            LinkRefusal::NotRecorded(detail) => format!(
                "Refused: the link was proven but could not be written to the shared record \
                 ({detail}), so nothing is linked. This is an operator problem: the link store may \
                 be read-only or misconfigured."
            ),
        }
    }
}

/// **Say WHICH phrase check failed**, in a sentence somebody holding a piece of paper can act on.
/// The same three branches `POST /identity/restore` prints, so the two phrase boxes teach the same
/// thing: a checksum failure in particular almost always means one mistyped word.
fn phrase_detail(error: &dregg_sdk::mnemonic::MnemonicError) -> String {
    use dregg_sdk::mnemonic::MnemonicError;
    match error {
        MnemonicError::InvalidWordCount(n) => format!(
            "that is {n} word{}; a dregg phrase is exactly 24.",
            if *n == 1 { "" } else { "s" }
        ),
        MnemonicError::UnknownWord(word) => format!(
            "{:?} is not one of the 2048 words in the list; check that word's spelling.",
            esc(word)
        ),
        MnemonicError::InvalidChecksum => "all 24 words are real words, but the phrase's own \
             checksum does not match, which almost always means ONE word is wrong or two are \
             swapped."
            .to_string(),
    }
}

/// **Parse and AUTHENTICATE a link code, naming the account it is really for.**
///
/// ⚑ This is the half of [`prove_and_record`] that the **two-step flow** needs on its own. The
/// residual it closes was stated plainly in this module's own list: *"The consent box and the phrase
/// ride in the SAME `POST`, so a player who was going to be fooled has already transmitted their
/// words by the time they see the account id … A two-step flow (code → 'this is account N, is that
/// you?' → words) would make that structural instead of advisory."*
///
/// Two things make the step-one page worth having rather than cosmetic:
///
/// * the account it names is **verified, not read out of the paste**. The retired note read the
///   plaintext uid half and the page had to admit it was unchecked; this recomputes
///   [`account_challenge_key`] per `(platform, uid)` and refuses a code presented under a uid it was
///   not minted for — so the number on the confirmation page is one the bot actually issued;
/// * it is reached **before any box asks for 24 words**, so the disclosure cannot arrive after the
///   words are already on the wire. That is the structural part.
///
/// Nothing is spent here. The single-use nonce is consumed at the END of [`prove_and_record`]
/// (step 7), so a player who reads the account id and stops has an unspent code and has transmitted
/// nothing but the code they were given.
fn authenticate_code<'s>(
    state: &'s IdentityLinkState,
    raw_code: &str,
    now: u64,
) -> Result<(&'s ConfiguredPlatform, String), LinkRefusal> {
    if state.platforms.is_empty() {
        return Err(LinkRefusal::NoPlatformConfigured);
    }
    let (uid_str, chal) = parse_link_code(raw_code).ok_or(LinkRefusal::MalformedCode)?;
    // Shape-check the uid here as well as in the caller: a non-numeric uid is a malformed code, and
    // saying so is more use than "this server cannot authenticate that code".
    uid_str
        .parse::<u64>()
        .map_err(|_| LinkRefusal::MalformedUid)?;
    let uid_str = uid_str.to_string();
    let configured = state
        .platforms
        .iter()
        .find(|p| {
            let key = account_challenge_key(&p.base_key, p.platform.wire(), &uid_str);
            challenge::verify(&key, chal, now).is_ok()
        })
        .ok_or(LinkRefusal::CodeNotOurs)?;
    Ok((configured, uid_str))
}

/// What a successful link produced — the two rows appended, plus the platform, for the page.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Linked {
    /// The platform now bound to this phrase.
    pub platform: LinkPlatform,
    /// The platform account id.
    pub platform_uid: String,
    /// The platform's CUSTODIAL pubkey — derived here from the uid, never pasted.
    pub custodial_pubkey_hex: String,
    /// The phrase's own (root) pubkey — the join key both identities now resolve through.
    pub root_pubkey_hex: String,
}

// ─────────────────────────────────────────────────────────────────────────────
// ⚑ THE CEREMONY — pure over its clock and its store, so the whole gate order is testable.
// ─────────────────────────────────────────────────────────────────────────────

/// **Prove and record a link.** The complete gate order, and the ONLY place a link record is written
/// on the web surface:
///
/// 1. **parse** the code into `(uid, challenge)` → [`LinkRefusal::MalformedCode`];
/// 2. **the platform's half** — for each configured platform, recompute
///    [`account_challenge_key`]`(base, platform, uid)` and [`challenge::verify`] the challenge under
///    it. Exactly one platform can pass (the keys are domain- and account-separated), and a
///    mismatched uid dies HERE, before any key is derived → [`LinkRefusal::CodeNotOurs`];
/// 2b. ⚑ **consent, naming the account** — the box must be ticked
///    ([`LinkRefusal::AccountNotConfirmed`]). Placed after the code gate so the refusal can name the
///    VERIFIED platform + uid, and before the derivation so it costs neither the code nor a phrase;
/// 3. **your half** — the 24 words derive the root Ed25519 key ([`derive_root_keypair`], the same
///    `dregg/0` path the whole surface pins) → [`LinkRefusal::BadPhrase`]. Deliberately AFTER the
///    code gate so a bad code never costs a phrase submission, and deliberately BEFORE the nonce is
///    spent so a typo does not burn the code;
/// 4. **derive** the platform's custodial pubkey from the uid — never pasted, so never lied about;
/// 5. **sign** the canonical link claim with the root key ([`sign_link_claim`]);
/// 6. **self-check** with the shared [`verify_link_claim`]. The signature half of this is true by
///    construction (we just made it); the CHALLENGE half is a real re-run, and the point of the call
///    is that no record is ever written that the independent verifier would reject —
///    [`LinkRefusal::SelfCheckFailed`];
/// 7. **spend** the code's nonce (single-use) → [`LinkRefusal::CodeAlreadyUsed`]. Last, so every
///    refusal above leaves the code usable;
/// 8. **record** two rows: the platform binding, and the `web` self-link that makes the resolver
///    give BOTH keys the same account id (see the ⚑ note in the module doc).
///
/// Every secret is wiped before returning: the phrase copy, the root seed (`Zeroizing`).
fn prove_and_record(
    state: &IdentityLinkState,
    raw_code: &str,
    raw_phrase: &str,
    confirmed_mine: bool,
    now: u64,
) -> Result<Linked, LinkRefusal> {
    // 0. Nothing to prove against. Named separately so the page does not blame the player's code for
    //    an operator's missing env (see `LinkRefusal::NoPlatformConfigured`).
    if state.platforms.is_empty() {
        return Err(LinkRefusal::NoPlatformConfigured);
    }

    // 1 + 2. Parse and AUTHENTICATE. Shared with the step-one route, so the account a player is
    //        asked to confirm is decided by the same code that decides what gets recorded.
    let (configured, uid_str) = authenticate_code(state, raw_code, now)?;
    let (_, chal) = parse_link_code(raw_code).ok_or(LinkRefusal::MalformedCode)?;
    let uid: u64 = uid_str.parse().map_err(|_| LinkRefusal::MalformedUid)?;
    let platform = configured.platform;
    let account_key = account_challenge_key(&configured.base_key, platform.wire(), &uid_str);

    // 2b. ⚑ CONSENT, naming the account. The code is genuine — but genuine for WHOSE account? A code
    //     handed to you by a stranger authenticates perfectly and binds THEIR account to YOUR root.
    //     Placed here rather than earlier so the refusal can name the real, verified platform + uid
    //     rather than the unverified string in the paste; placed before the derivation so a refusal
    //     costs neither the code nor a phrase derivation.
    if !confirmed_mine {
        return Err(LinkRefusal::AccountNotConfirmed {
            platform,
            uid: uid_str,
        });
    }

    // 3. YOUR HALF. The phrase IS the authority for the root key; nothing about the browser's
    //    cookie is consulted, so this works on a device that has never seen this server.
    let mut phrase = normalize_typed_phrase(raw_phrase);
    let derived = derive_root_keypair(&phrase);
    phrase.zeroize();
    let (root_pubkey_hex, root_seed) =
        derived.map_err(|e| LinkRefusal::BadPhrase(phrase_detail(&e)))?;

    // 4. The custodial key, DERIVED (the bot's own `seed_for`), never pasted.
    let custodial = platform.custodial_identity(&configured.bot_secret, uid);

    // 5. The claim, signed by the root key over the canonical message.
    let (root_pubkey, signature) =
        sign_link_claim(&root_seed, platform.wire(), &uid_str, &custodial.0, chal)
            .map_err(|e| LinkRefusal::SelfCheckFailed(format!("{e:?}")))?;
    drop(root_seed); // wiped by `Zeroizing`; explicit so the wipe point is visible.

    // 6. THE SELF-CHECK. Re-runs the freshness gate and proves the bytes we are about to record are
    //    bytes the shared verifier accepts. Never a claim about the human.
    verify_link_claim(
        &account_key,
        platform.wire(),
        &uid_str,
        &custodial.0,
        &root_pubkey,
        chal,
        &signature,
        now,
    )
    .map_err(|e| LinkRefusal::SelfCheckFailed(format!("{e:?}")))?;

    // 7. Single-use. LAST gate, so a mistyped phrase never burns a code.
    if let Some((nonce, exp)) = challenge::nonce_and_exp(chal) {
        if !state.replay.consume(nonce, exp, now) {
            return Err(LinkRefusal::CodeAlreadyUsed);
        }
    }

    // 8. Record. The platform binding, then the `web` SELF-link without which the resolver hands the
    //    two keys two different join keys and the board still prints two rows.
    let mut store = FileLinkStore::new(&state.store_path);
    for record in [
        LinkRecord {
            root_pubkey_hex: root_pubkey_hex.clone(),
            platform: platform.wire().to_string(),
            platform_uid: uid_str.clone(),
            custodial_pubkey_hex: custodial.0.clone(),
            verified_at: now,
        },
        LinkRecord {
            root_pubkey_hex: root_pubkey_hex.clone(),
            platform: WEB_PLATFORM.to_string(),
            platform_uid: root_pubkey_hex.clone(),
            custodial_pubkey_hex: root_pubkey_hex.clone(),
            verified_at: now,
        },
    ] {
        store
            .record(&record)
            .map_err(|e| LinkRefusal::NotRecorded(e.to_string()))?;
    }

    Ok(Linked {
        platform,
        platform_uid: uid_str,
        custodial_pubkey_hex: custodial.0,
        root_pubkey_hex,
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// READING the links — what `/you` and this page both need.
// ─────────────────────────────────────────────────────────────────────────────

/// One platform bound to a root key, as a page shows it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinkedPlatform {
    /// `"discord"`, `"telegram"`, or [`WEB_PLATFORM`].
    pub platform: String,
    /// The platform account id (for the web self-row, the root pubkey itself).
    pub platform_uid: String,
    /// The pubkey that platform's turns are attributed under.
    pub custodial_pubkey_hex: String,
    /// When the link was proven (unix seconds).
    pub verified_at: u64,
    /// Whether that key is derivable by the OPERATOR (a bot-derived custodial key) rather than only
    /// by the phrase-holder. ⚑ This is the asymmetry, carried as DATA so a page cannot forget to
    /// say it.
    pub operator_derivable: bool,
}

/// **Every platform currently bound to a root pubkey** — the shared store's own
/// [`LinkStore::platforms_for_root`], plus the operator-derivability flag.
///
/// `root_pubkey_hex` must be an identity the CALLER can stand behind for the viewer it is rendering
/// (`/you` uses the mac-verified claim cookie's public key, never a `?user=` string). The records
/// were each signed by that root key, so returning them widens the view only to bindings the
/// phrase-holder themselves authorised.
pub fn linked_platforms_for_root(root_pubkey_hex: &str) -> Vec<LinkedPlatform> {
    linked_platforms_in(&FileLinkStore::new(default_store_path()), root_pubkey_hex)
}

/// [`linked_platforms_for_root`] over an EXPLICIT store — the seam the tests drive, so they read the
/// file they wrote rather than whatever `$DREGG_LINK_DIR` happens to hold on the machine.
fn linked_platforms_in(store: &dyn LinkStore, root_pubkey_hex: &str) -> Vec<LinkedPlatform> {
    if root_pubkey_hex.len() != 64 {
        return Vec::new();
    }
    let mut out: Vec<LinkedPlatform> = store
        .platforms_for_root(root_pubkey_hex)
        .unwrap_or_default()
        .into_iter()
        .map(|r| LinkedPlatform {
            // ⚑ NOT `platform != "web"`. That spelling was right while the web self-row was the only
            // self-held row, and became wrong the moment a browser device key could be one: it would
            // have printed "an operator can derive this key" beside the single key in the system
            // that nobody but that browser can produce. See `device_key::platform_is_self_held`.
            operator_derivable: !crate::device_key::platform_is_self_held(&r.platform),
            platform: r.platform,
            platform_uid: r.platform_uid,
            custodial_pubkey_hex: r.custodial_pubkey_hex,
            verified_at: r.verified_at,
        })
        .collect();
    out.sort_by(|a, b| {
        a.platform
            .cmp(&b.platform)
            .then_with(|| a.platform_uid.cmp(&b.platform_uid))
    });
    out
}

/// **The custodial pubkeys a viewer's own history is ALSO filed under** — every linked platform key
/// except the web self-row (which is the viewer's own identity and already counted).
///
/// This is the one function `/you` needs to union the view: hand it the viewer's claimed public key
/// and it answers "which other actor strings are provably this same human". Empty for an unlinked or
/// unclaimed viewer, so every existing path is byte-identical.
pub fn linked_actor_keys(root_pubkey_hex: &str) -> Vec<String> {
    actor_keys_of(&linked_platforms_for_root(root_pubkey_hex), root_pubkey_hex)
}

/// [`linked_actor_keys`] over an ALREADY-LOADED platform list — pure, no I/O.
///
/// ⚑ This is the form `/you` uses. The store is a file, and a page that called
/// [`linked_platforms_for_root`] for its rendering and [`linked_actor_keys`] for its joins would scan
/// that file TWICE per request; the resolver's own doc names per-row rescanning as a defect it was
/// built to fix, so this seam exists so no caller reintroduces it one level up.
pub fn actor_keys_of(links: &[LinkedPlatform], root_pubkey_hex: &str) -> Vec<String> {
    links
        .iter()
        .filter(|p| p.platform != WEB_PLATFORM)
        // The root's own key is the viewer's identity, already counted. Filtered rather than assumed
        // absent: a future platform could legitimately record a self-held key.
        .filter(|p| !p.custodial_pubkey_hex.eq_ignore_ascii_case(root_pubkey_hex))
        .map(|p| p.custodial_pubkey_hex.clone())
        .collect()
}

/// [`linked_actor_keys`] over an EXPLICIT store — the tested seam.
fn actor_keys_in(store: &dyn LinkStore, root_pubkey_hex: &str) -> Vec<String> {
    actor_keys_of(
        &linked_platforms_in(store, root_pubkey_hex),
        root_pubkey_hex,
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// Handlers.
// ─────────────────────────────────────────────────────────────────────────────

/// The link form.
#[derive(Debug, Clone, Deserialize)]
pub struct LinkForm {
    /// The code the bot handed the player — `<uid>:<challenge>`.
    pub code: String,
    /// The 24 words, however they were pasted.
    pub phrase: String,
    /// ⚑ Present only when "the account this code belongs to is mine" is ticked. See
    /// [`LinkRefusal::AccountNotConfirmed`] for the attack this exists against.
    #[serde(default)]
    pub mine: Option<String>,
}

/// `GET /identity/link?code=…` — **the one-tap phone path.**
///
/// The bot's reply carries a tappable link with the code already in it, so a player reading Discord
/// on a phone taps once and lands here with the code box filled; the only thing left to do is the 24
/// words. Copy-pasting a 117-character token between two apps on a phone was the real friction, and
/// it is now optional rather than required.
///
/// ⚑ **THE COST, and it is a real one.** A code in a URL is in a place a code should not be: browser
/// history, any `Referer` a subsequent click sends, and any access log that records query strings.
/// The code is a bearer credential inside its 15-minute window — whoever holds it can bind *their*
/// phrase to that account — so this is a genuine widening, not a free convenience. It is bounded
/// three ways and said on the page rather than hidden:
///
/// * the response carries `Referrer-Policy: no-referrer` and `Cache-Control: private, no-store`
///   ([`no_store`]), so the URL does not ride out to the next site the player clicks;
/// * a 3-line inline script rewrites the address bar to a bare `/identity/link` on load, so the code
///   does not persist in history or in a shared-screen address bar;
/// * the code is single-use and 15 minutes old at most, and it grants a display grouping — never a
///   key, never a signature, never the ability to act as the player.
///
/// The residual this does NOT fix: a reverse proxy or access log that records query strings still
/// sees it for that request. Prefer the paste box on a shared machine; the page says so.
#[derive(Debug, Clone, Default, Deserialize)]
pub struct LinkQuery {
    /// A code to prefill the box with. Never trusted: it goes through the identical
    /// [`prove_and_record`] gate order on submit, exactly as a pasted one does.
    #[serde(default)]
    pub code: Option<String>,
}

/// Strip a prefilled `?code=` out of the address bar as soon as the page loads, so a code that
/// arrived in a URL does not persist in history or sit visible on a shared screen. Pure
/// `history.replaceState` — no fetch, nothing read, and with JS off the page still works (the box is
/// already filled server-side; only the address-bar cleanup is lost).
const STRIP_CODE_SCRIPT: &str = r##"<script>
(function(){
  "use strict";
  try{
    if(window.location.search && window.history && window.history.replaceState){
      window.history.replaceState(null, "", window.location.pathname);
    }
  }catch(e){}
})();
</script>"##;

fn unix_now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// A page that must never be cached, proxied or replayed — it takes a phrase in a form.
fn no_store(body: String) -> Response {
    let mut response = Html(body).into_response();
    response.headers_mut().insert(
        header::CACHE_CONTROL,
        header::HeaderValue::from_static("private, no-store, max-age=0"),
    );
    response.headers_mut().insert(
        header::REFERRER_POLICY,
        header::HeaderValue::from_static("no-referrer"),
    );
    response
}

/// `GET /identity/link` — what a link does, what it does NOT, and the one form. A `?code=` prefills
/// the code box (see [`LinkQuery`] for the cost of that and the three bounds on it).
async fn get_link(
    State(state): State<Arc<IdentityLinkState>>,
    headers: HeaderMap,
    Query(query): Query<LinkQuery>,
) -> Response {
    let claimed =
        read_cookie(&headers, CLAIM_COOKIE).and_then(|l| seed_identity::parse_claim_label(&l));
    no_store(link_page(
        &state.kinds(),
        &state.store_path,
        claimed.as_deref(),
        None,
        None,
        query.code.as_deref(),
    ))
}

/// The step-one form: a code, and nothing else.
#[derive(Debug, Clone, Deserialize)]
pub struct CodeForm {
    /// The code the bot handed the player.
    pub code: String,
}

/// `POST /identity/link/account` — **STEP ONE: whose account is this?**
///
/// Checks the code and renders the account it is really for, beside the box that then asks for the
/// 24 words. Nothing is derived, nothing is spent, and no record is written; a player who reads
/// "this is Discord account 6913…" and does not recognise it can close the page having given up
/// nothing at all.
///
/// ⚑ Before this route the disclosure was a paragraph beside the phrase box that read the account
/// number out of the paste and said, honestly, that it was unchecked until submit. Both halves of
/// that were the weakness: the number could be anything, and by the time it was checked the words
/// had already been transmitted. Now the number is verified before it is shown, and the words are
/// asked for on the far side of the reader saying "yes, that is mine".
async fn post_link_account(
    State(state): State<Arc<IdentityLinkState>>,
    headers: HeaderMap,
    Form(form): Form<CodeForm>,
) -> Response {
    let claimed =
        read_cookie(&headers, CLAIM_COOKIE).and_then(|l| seed_identity::parse_claim_label(&l));
    // The same gate 0 the recording route runs. A cross-origin submit here writes nothing, but it
    // would render an attacker's chosen account onto the player's screen as though the player had
    // asked about it, which is the first move of the same con.
    if !seed_identity::same_origin_post(&headers) {
        let message = LinkRefusal::NotFromOurPage.message();
        return (
            LinkRefusal::NotFromOurPage.http_status(),
            no_store(link_page(
                &state.kinds(),
                &state.store_path,
                claimed.as_deref(),
                None,
                Some(&message),
                None,
            )),
        )
            .into_response();
    }
    match authenticate_code(&state, &form.code, unix_now()) {
        Ok((configured, uid)) => no_store(link_page_with(
            &state.kinds(),
            &state.store_path,
            claimed.as_deref(),
            None,
            None,
            Some(&form.code),
            Some((configured.platform, uid.as_str())),
        )),
        Err(refusal) => {
            let status = refusal.http_status();
            let message = refusal.message();
            (
                status,
                no_store(link_page(
                    &state.kinds(),
                    &state.store_path,
                    claimed.as_deref(),
                    None,
                    Some(&message),
                    // The code is handed back only when re-typing it could help. A code this
                    // server cannot authenticate is dead, and re-filling the box would invite the
                    // player to keep submitting something that can never work.
                    matches!(
                        &refusal,
                        LinkRefusal::MalformedCode | LinkRefusal::MalformedUid
                    )
                    .then_some(form.code.as_str()),
                )),
            )
                .into_response()
        }
    }
}

/// `POST /identity/link` — run the ceremony. On success re-renders the page with the new link
/// listed; on refusal re-renders with the named gate and nothing recorded.
///
/// ⚑ **The origin gate runs HERE, in the handler, and not inside [`prove_and_record`]** — which is
/// the one gate that is not in that function's numbered order. That is deliberate rather than
/// convenient: `prove_and_record` is pure over its clock and its store precisely so the whole gate
/// order is drivable from a test, and headers are not among its inputs. Threading a
/// `from_our_page: bool` through it would put the answer to a question about the TRANSPORT inside a
/// function that only knows about codes and phrases, and would let a caller pass `true`. The refusal
/// still lives in the shared [`LinkRefusal`] taxonomy, so it renders, statuses and reads like every
/// other gate — [`LinkRefusal::NotFromOurPage`] says what it is against.
async fn post_link(
    State(state): State<Arc<IdentityLinkState>>,
    headers: HeaderMap,
    Form(form): Form<LinkForm>,
) -> Response {
    let claimed =
        read_cookie(&headers, CLAIM_COOKIE).and_then(|l| seed_identity::parse_claim_label(&l));
    // GATE 0: did this come from our own page? Before the code is parsed, before the phrase is
    // touched, and before any nonce could be spent.
    let origin = seed_identity::request_origin(&headers);
    if origin != seed_identity::RequestOrigin::SameOrigin {
        tracing::warn!(
            ?origin,
            "REFUSED a POST /identity/link that could not show it came from a page on this site — \
             nothing was derived, no code was spent and NO RECORD WAS WRITTEN. A cross-origin submit \
             would otherwise bind an attacker-chosen account to this browser's identity, which the \
             player would then have to notice and undo by hand"
        );
        let message = LinkRefusal::NotFromOurPage.message();
        return (
            LinkRefusal::NotFromOurPage.http_status(),
            no_store(link_page(
                &state.kinds(),
                &state.store_path,
                claimed.as_deref(),
                None,
                Some(&message),
                // A foreign request's code is not handed back: it was never the player's to retype.
                None,
            )),
        )
            .into_response();
    }
    match prove_and_record(
        &state,
        &form.code,
        &form.phrase,
        form.mine.is_some(),
        unix_now(),
    ) {
        Ok(linked) => {
            // The audit line carries the PUBLIC halves only: the platform, the account, and the two
            // public keys. Never the code (a live bearer within its window) and never the phrase.
            tracing::info!(
                platform = linked.platform.wire(),
                platform_uid = %linked.platform_uid,
                root = %linked.root_pubkey_hex,
                custodial = %linked.custodial_pubkey_hex,
                "identity link PROVEN and recorded (display/grouping join; the platform key stays \
                 custodial)"
            );
            // Render against the ROOT the phrase named, not the browser's cookie: a player may link
            // an identity this browser is not currently acting as, and the page must show the truth.
            let root = linked.root_pubkey_hex.clone();
            no_store(link_page(
                &state.kinds(),
                &state.store_path,
                Some(root.as_str()),
                Some(&linked),
                None,
                None,
            ))
        }
        Err(refusal) => {
            let status = refusal.http_status();
            // ⚑ Hand the code back ONLY when it was not spent. A `BadPhrase` refusal leaves the code
            // live (the nonce is spent last, on purpose), so re-typing 117 characters would be pure
            // busywork; a `CodeAlreadyUsed` or `CodeNotOurs` code is dead, and re-filling the box
            // with it would invite the player to keep submitting something that can never work.
            let refusable_code = match &refusal {
                LinkRefusal::BadPhrase(_) | LinkRefusal::AccountNotConfirmed { .. } => {
                    Some(form.code.clone())
                }
                _ => None,
            };
            let message = refusal.message();
            (
                status,
                no_store(link_page(
                    &state.kinds(),
                    &state.store_path,
                    claimed.as_deref(),
                    None,
                    Some(&message),
                    // Hand the code back so a fixable refusal (a mistyped phrase) does not also cost
                    // the player their code — it was NOT spent, and re-pasting it would be busywork.
                    refusable_code.as_deref(),
                )),
            )
                .into_response()
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The page.
// ─────────────────────────────────────────────────────────────────────────────

/// Page-local styling only for the three shapes the product shell has no class for: the platform
/// list, the asymmetry box, and the code/phrase inputs.
const LINK_STYLE: &str = r##"<style>
.lk-plats{list-style:none;margin:1rem 0;padding:0;display:flex;flex-direction:column;gap:.5rem}
.lk-plats li{padding:.7rem .85rem;border:1px solid var(--line,#2a2a2a);border-left:3px solid rgba(140,160,220,.7);
 border-radius:0 4px 4px 0;background:rgba(255,255,255,.02);line-height:1.55}
.lk-plats li.self{border-left-color:rgba(120,200,150,.7)}
.lk-plats b{display:block;font-size:.95rem}
.lk-plats code{font-family:ui-monospace,Menlo,monospace;font-size:.82rem;overflow-wrap:anywhere;opacity:.85}
.lk-asym{margin:1.3rem 0;padding:.9rem 1rem;border:1px solid rgba(201,106,94,.4);
 border-left:2px solid rgba(201,106,94,.8);border-radius:0 3px 3px 0;background:rgba(201,106,94,.05);line-height:1.6}
.lk-asym h3{margin:0 0 .45rem;font-size:.95rem}
.lk-asym dt{font-weight:600;margin-top:.55rem}
.lk-asym dd{margin:.12rem 0 0;opacity:.88}
.lk-form label{display:block;margin:1rem 0 .3rem;font-size:.8rem;letter-spacing:.1em;text-transform:uppercase;opacity:.7}
.lk-form input[type=text],.lk-form textarea{width:100%;padding:.6rem .7rem;border:1px solid var(--line,#2a2a2a);
 border-radius:4px;background:rgba(0,0,0,.25);color:inherit;font-family:ui-monospace,Menlo,monospace;
 font-size:.88rem;line-height:1.6}
.lk-form textarea{min-height:5.5rem}
.lk-check{display:flex;gap:.55rem;align-items:flex-start;margin:1.1rem 0 .2rem;line-height:1.55;font-size:.92rem}
.lk-check input{margin-top:.3rem;flex:none}
.lk-steps{margin:1rem 0;padding-left:1.3rem;line-height:1.6}
.lk-steps li{margin:.35rem 0}
.lk-key{font-family:ui-monospace,Menlo,monospace;font-size:.85rem;overflow-wrap:anywhere;opacity:.8}
.lk-sep{margin:2rem 0;border:0;border-top:1px solid var(--line,#2a2a2a)}
</style>"##;

/// ⚑ **THE ASYMMETRY, ON THE PAGE.** Rendered on the link page and after a successful link, from ONE
/// source, so what a player reads while deciding and what they read afterwards cannot differ.
///
/// This is the paragraph the whole feature is judged by. Linking makes the boards treat two players
/// as one human; it does NOT make both keys yours, and it does NOT stop the operator from being able
/// to derive the platform one. `seed_identity` refuses to launder the same class of thing (it says
/// plainly that browser turns are `Asserted`, not `Signed`); this matches that register.
pub(crate) fn asymmetry_block() -> String {
    "<div class=\"lk-asym\"><h3>What a link gives you, and what it does not change</h3><dl>\
     <dt>Your two keys stay two keys.</dt>\
     <dd>Nothing is imported and nothing is re-keyed. Your web identity is still the key your 24 \
     words derive; your Discord identity is still the key the bot derives. A link is a signed \
     statement that the same human holds both, recorded so the boards can group them.</dd>\
     <dt>Your Discord identity is still CUSTODIAL, and linking does not change that.</dt>\
     <dd>The bot's key for you is <code>BLAKE3(bot_secret, your account id)</code>. Whoever operates \
     the bot holds <code>bot_secret</code>, so they can derive your Discord key and sign as you \
     there (before this link, and after it). That is what running a chat bot means, and no link \
     ceremony can take it away. Only your 24 words are self-held; only they are yours in the sense \
     that nobody else can reproduce them.</dd>\
     <dt>So the two halves of \"you\" are not equally yours.</dt>\
     <dd>If you want the version of you that <em>only</em> you can act as, that is the phrase, and \
     turns signed with it through a tool that holds it (the <code>dregg</code> CLI, on \
     <code>/act-signed</code>) are the only turns on this surface that carry a real signature. \
     Everything you press in this browser, on either side of the link, is still \
     <em>attributed</em> rather than signed.</dd>\
     <dt>What the link is actually FOR.</dt>\
     <dd>One row on the Descent board instead of two strangers, and a <a href=\"/you\">/you</a> page \
     that counts both sides' tables and runs. It is a view, and it is honest about being one.</dd>\
     <dt>Who can read the record.</dt>\
     <dd>The operator. The link is stored in plaintext as \"this key and that account are one \
     human\". The private version, proving you are one human across several platforms <em>without \
     revealing which accounts</em>, exists in the tree and is not what this page does.</dd>\
     </dl></div>"
        .to_string()
}

/// The list of platforms already bound to a root, with the per-row custody statement.
///
/// Reads the store the CEREMONY writes to (`state.store_path`), not
/// [`default_store_path`] — in production they are the same value, but a page that could read a
/// different file than the one just appended to would print a stale answer the moment they ever
/// diverged.
fn platforms_block(store_path: &std::path::Path, root_pubkey_hex: &str) -> String {
    let links = linked_platforms_in(&FileLinkStore::new(store_path), root_pubkey_hex);
    if links.is_empty() {
        return "<p class=\"prose\">This identity has no platform linked yet. Nothing is wrong: an \
                unlinked player works exactly as before, on every surface.</p>"
            .to_string();
    }
    let rows: String = links
        .iter()
        .map(|link| {
            let (cls, custody) = if link.operator_derivable {
                (
                    "",
                    "This key is <strong>custodial</strong>: the bot's operator can derive it. \
                     Linking did not change that.",
                )
            } else if link.platform == crate::device_key::DEVICE_PLATFORM {
                (
                    " class=\"self\"",
                    "This key is <strong>self-held</strong>, and more so than any other key here: \
                     the browser made it and will not give it back, so neither we nor your 24 words \
                     can reproduce it. Turns it signs are recorded as yours.",
                )
            } else {
                (
                    " class=\"self\"",
                    "This key is <strong>self-held</strong>: only your 24 words reproduce it.",
                )
            };
            format!(
                "<li{cls}><b>{platform}{uid}</b>\
                 <code>{key}</code><span>{custody}</span></li>",
                platform = esc(link.platform.as_str()),
                uid = if link.platform == WEB_PLATFORM {
                    " · this browser's identity".to_string()
                } else if link.platform == crate::device_key::DEVICE_PLATFORM {
                    format!(" · browser {}", esc(&link.platform_uid))
                } else {
                    format!(" · account {}", esc(&link.platform_uid))
                },
                key = esc(&link.custodial_pubkey_hex),
                custody = custody,
            )
        })
        .collect();
    format!("<ul class=\"lk-plats\">{rows}</ul>")
}

/// The banner shown when a code arrived in the URL — SAY that it did, and say the one place that is
/// a bad idea. A convenience whose cost is hidden is the thing this codebase refuses to ship.
fn prefilled_note(prefilled: bool) -> &'static str {
    if !prefilled {
        return "";
    }
    "<div class=\"notice ok\" role=\"status\">Your code is filled in below. Add your 24 words and \
     you are done.</div>\
     <p class=\"prose\" style=\"opacity:.75;font-size:.88rem\">That code travelled in this page's \
     address (it has been cleared from the address bar already). Inside its 15 minutes a code is a \
     bearer token (somebody else holding it could attach <em>their</em> words to your account), so \
     on a shared or public machine prefer pasting it into the box by hand, and do not forward this \
     link. It cannot be used to act as you or to reach your words either way: a code grants a \
     grouping, never a key.</p>"
}

/// ⚑ **RETIRED by the two-step flow, and kept only as the answer to "what did this used to do".**
///
/// It read the account id out of a code's PLAINTEXT uid half and printed it beside the box asking
/// for 24 words. Its own doc had to admit the number was unverified — anybody can write any number
/// before the colon — so its job was disclosure rather than proof, and the disclosure arrived on the
/// same screen as the phrase box rather than before it.
///
/// [`link_form`]'s step two does both halves properly: the account is named only after
/// [`authenticate_code`] has verified which account the code was really minted for, and there is no
/// phrase box on the page until that has happened. This function is gone rather than deprecated
/// because a page that could still call it would be a page that could still show an unchecked
/// number where a checked one belongs.
/// ⚑ **THE TWO-STEP FORM.** Step one asks for a code and nothing else; step two — reachable only
/// after [`authenticate_code`] has said which account the code is genuinely for — names that
/// account and then asks for the words.
///
/// The residual this closes was stated in this module's own list: *"The consent box and the phrase
/// ride in the SAME `POST`, so a player who was going to be fooled has already transmitted their
/// words by the time they see the account id … A two-step flow would make that structural instead
/// of advisory."* Two things changed and both matter:
///
/// * **the account named is verified**, not read out of the paste. the old note could only
///   print what the code claimed and had to admit so; the confirmation below prints an account a bot
///   this server shares a secret with actually minted a code for.
/// * **there is no phrase box until the reader has seen it.** That is the structural half. A
///   phishing prefill now spends its one shot on a screen that gives it nothing: the reader either
///   recognises the account or closes the page, and either way no words were on the wire.
///
/// The step-two form still carries the consent box. It is no longer load-bearing on its own, but a
/// reader who scrolled past the account line should still have to say the word "mine" before their
/// words go anywhere.
fn link_form(prefill_code: Option<&str>, confirm: Option<(LinkPlatform, &str)>) -> String {
    let Some((platform, uid)) = confirm else {
        // STEP ONE. No phrase box exists on this page at all.
        return format!(
            "<form class=\"lk-form\" method=\"post\" action=\"/identity/link/account\">\
             <label for=\"code\">The code the bot gave you</label>\
             <input id=\"code\" name=\"code\" type=\"text\" autocomplete=\"off\" spellcheck=\"false\" \
             autocapitalize=\"none\" placeholder=\"1234567:AbCd…\" value=\"{code}\">\
             <p class=\"prose\" style=\"opacity:.75;font-size:.88rem;margin:.9rem 0 0\">\
             Nothing here asks for your 24 words yet. We check the code first and tell you which \
             account it is really for; only then is there a box for your words. If the account we \
             name is not yours, you can close the page having given away nothing, and the code is \
             not used up.</p>\
             <div class=\"id-actions\" style=\"display:flex;gap:.6rem;flex-wrap:wrap;margin:1.1rem 0 0\">\
             <button class=\"btn btn-primary\" type=\"submit\">Check this code</button>\
             <a class=\"btn btn-ghost\" href=\"/you\">Back to your record</a></div></form>",
            code = esc(prefill_code.unwrap_or_default()),
        );
    };
    // STEP TWO. The account is checked; now, and only now, the words.
    format!(
        "<div class=\"lk-asym\" style=\"border-color:rgba(140,160,220,.45);\
         border-left-color:rgba(140,160,220,.85);background:rgba(140,160,220,.06)\">\
         <h3>This code is for {platform} account {uid}</h3>\
         <p>We checked that with {platform} itself, so this is the account the code was really \
         issued for and not just what the code says. <strong>Is that your account?</strong></p>\
         <p>If it is not, if somebody sent you this code or this link, stop here and close the \
         page. Nothing has happened yet and your words have not been asked for. Linking somebody \
         else's account would put their play on your record; you could \
         <a href=\"/identity/unlink\">undo it afterwards</a>, but not having done it is \
         better.</p></div>\
         <form class=\"lk-form\" method=\"post\" action=\"/identity/link\">\
         <input type=\"hidden\" name=\"code\" value=\"{code}\">\
         <label class=\"lk-check\"><input type=\"checkbox\" name=\"mine\" value=\"yes\">\
         <span>Yes, {platform} account {uid} is <strong>mine</strong>.</span></label>\
         <label for=\"phrase\">Your 24 words</label>\
         <textarea id=\"phrase\" name=\"phrase\" rows=\"3\" autocomplete=\"off\" \
         spellcheck=\"false\" autocapitalize=\"none\" placeholder=\"abandon ability able about …\"\
         ></textarea>\
         <p class=\"prose\" style=\"opacity:.75;font-size:.88rem;margin:.9rem 0 0\">\
         <strong>Why your words, here.</strong> The link is a signature by the key your words \
         derive, and that key exists only while the words are in hand; nothing on the server or in \
         this browser holds it. So the signing happens inside this one request: the words are turned \
         into a key, one link claim is signed, and every byte of secret material is wiped before the \
         response goes out. This is the same path <a href=\"/identity\">restoring an identity</a> \
         already takes, with the same cost: the words pass through the server once. They are never \
         written to disk or to a log.</p>\
         <div class=\"id-actions\" style=\"display:flex;gap:.6rem;flex-wrap:wrap;margin:1.1rem 0 0\">\
         <button class=\"btn btn-primary\" type=\"submit\">Prove and link</button>\
         <a class=\"btn btn-ghost\" href=\"/identity/link\">No · start over</a></div></form>",
        platform = esc(platform.display()),
        uid = esc(uid),
        code = esc(prefill_code.unwrap_or_default()),
    )
}

/// `GET`/`POST /identity/link`'s page at **step one** — the code box, and no phrase box.
///
/// Kept as a six-argument wrapper over [`link_page_with`] so that every existing caller and every
/// existing test renders the step-one page unchanged; only the route that has just AUTHENTICATED a
/// code passes the seventh argument. (A default-argument-shaped wrapper rather than seven `None`s
/// sprinkled through a dozen call sites: the sprinkling is how a new parameter silently acquires
/// the wrong value at the one site nobody re-read.)
fn link_page(
    platforms: &[LinkPlatform],
    store_path: &std::path::Path,
    root_pubkey_hex: Option<&str>,
    just_linked: Option<&Linked>,
    refusal: Option<&str>,
    prefill_code: Option<&str>,
) -> String {
    link_page_with(
        platforms,
        store_path,
        root_pubkey_hex,
        just_linked,
        refusal,
        prefill_code,
        None,
    )
}

/// The page, with the **step-two** state made explicit.
///
/// `confirm = Some((platform, uid))` means a code has been checked and names that account; the page
/// then shows the account, the consent box and the phrase box. `None` is step one: a code box and
/// nothing that asks for 24 words.
fn link_page_with(
    platforms: &[LinkPlatform],
    store_path: &std::path::Path,
    root_pubkey_hex: Option<&str>,
    just_linked: Option<&Linked>,
    refusal: Option<&str>,
    prefill_code: Option<&str>,
    confirm: Option<(LinkPlatform, &str)>,
) -> String {
    let notice = match just_linked {
        Some(linked) => notice_html(Some(&format!(
            "Linked. {} account {} and the identity {} are now recorded as one human.",
            linked.platform.display(),
            linked.platform_uid,
            short_tag(&linked.root_pubkey_hex),
        ))),
        None => notice_html(refusal),
    };
    let how = platforms
        .iter()
        .map(|platform| {
            format!(
                "<li><strong>{name}.</strong> {how}</li>",
                name = platform.display(),
                how = platform.how_to_get_a_code(),
            )
        })
        .collect::<String>();
    let names: Vec<&str> = platforms.iter().map(|p| p.display()).collect();
    // ⚑ A deployment with no platform secret CANNOT prove a link. Say that at the top and drop the
    // form entirely, rather than presenting a box whose every submission is a refusal. The page is
    // still reachable (every other page links here), and it still explains what linking is — that is
    // the whole reason it is mounted unconditionally.
    //
    // ⚑ It also renders `{notice}`. This branch COMPUTED the notice and threw it away, which meant
    // that on an unconfigured deployment every per-request refusal was swallowed and the player got
    // the standing "cannot prove a link" page instead of the one thing that had just happened to
    // their request — a cross-origin submission included. A refusal that renders nowhere is a refusal
    // nobody can act on.
    if platforms.is_empty() {
        return document_with_head(
            "Link your accounts · DreggNet",
            "",
            LINK_STYLE,
            &format!(
                "<main class=\"session\">\
                 <header class=\"page-head\"><p class=\"eyebrow\">Identity · linking</p>\
                 <h1>One player, both places</h1>\
                 <p class=\"deck\">This is where you would prove that your chat account and the \
                 identity your 24 words derive are the same human, so the boards rank you once \
                 instead of twice.</p></header>{notice}\
                 <div class=\"notice refused\" role=\"status\">Refused: this server cannot prove a \
                 link right now.</div>\
                 <h2>Why, exactly</h2>\
                 <p class=\"prose\">Linking works by a chat bot handing you a code that only a \
                 holder of that bot's identity secret could have minted. <strong>This server holds \
                 no such secret</strong>, so it has nothing to check a code against: not \
                 &ldquo;your code is wrong&rdquo;, but &ldquo;there is no bot this deployment shares \
                 an identity with&rdquo;. Nothing you could paste would change that, so there is no \
                 form here to mislead you with.</p>\
                 <p class=\"prose\">Everything else is unaffected: your 24-word identity works \
                 exactly as it does, and so does every game. You simply stay a separate player on \
                 each surface, which is what you already were.</p>\
                 <h2>For whoever runs this</h2>\
                 <p class=\"prose\">Set <code>{discord}</code> to the SAME 64-hex identity secret \
                 the Discord bot reads, and/or <code>{telegram}</code>, in this process's \
                 environment, and point <code>DREGG_LINK_DIR</code> at the same directory every \
                 dregg unit uses, so a link recorded on one surface resolves on the others.</p>\
                 {asym}</main>",
                notice = notice,
                discord = crate::discord_activity::BOT_SECRET_ENV,
                telegram = crate::telegram_miniapp::TELEGRAM_BOT_TOKEN_ENV,
                asym = asymmetry_block(),
            ),
        );
    }
    let current = match root_pubkey_hex {
        Some(root) => format!(
            "<h2>Linked to <span class=\"lk-key\">{tag}</span></h2>\
             <p class=\"prose\">Everything bound to the identity your 24 words derive \
             (<span class=\"lk-key\">{full}</span>):</p>{list}",
            tag = esc(&short_tag(root)),
            full = esc(root),
            list = platforms_block(store_path, root),
        ),
        None => "<h2>No identity on this browser yet</h2>\
             <p class=\"prose\">You can still link from here: the ceremony reads your 24 words, \
             not this browser's cookie, so it works on a device that has never seen us. If you have \
             not claimed an identity at all, <a href=\"/identity\">start there</a>: linking needs a \
             phrase to link TO.</p>"
            .to_string(),
    };
    document_with_head(
        "Link your accounts · DreggNet",
        "",
        LINK_STYLE,
        &format!(
            "<main class=\"session\">\
             <header class=\"page-head\"><p class=\"eyebrow\">Identity · linking</p>\
             <h1>One player, both places</h1>\
             <p class=\"deck\">Prove that the {names} account you play from and the identity your 24 \
             words derive are the same human. The boards then rank you once instead of twice.</p>\
             </header>{notice}{current}\
             <hr class=\"lk-sep\">\
             <h2>Link an account</h2>\
             <ol class=\"lk-steps\">{how}\
             <li><strong>On a phone, just tap the link in the bot's reply</strong>: it opens this \
             page with the code already filled in, so the only thing left is your 24 words. \
             Otherwise copy the whole code (it looks like <code>1234567:AbCd…</code>) and paste it \
             below. A code is good for {minutes} minutes and works once.</li>\
             </ol>{prefilled}{form}\
             {asym}{honest}{strip}</main>",
            names = esc(&names.join(" or ")),
            notice = notice,
            current = current,
            how = how,
            minutes = code_window_minutes(),
            prefilled = prefilled_note(prefill_code.is_some()),
            form = link_form(prefill_code, confirm),
            asym = asymmetry_block(),
            honest = honest_limits_html(),
            // Only ship the address-bar cleanup when there is something to clean. A page reached with
            // no query needs no script at all.
            strip = if prefill_code.is_some() {
                STRIP_CODE_SCRIPT
            } else {
                ""
            },
        ),
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the whole gate order driven with REAL keys, a REAL phrase, and a REAL store file.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_sdk::mnemonic::generate_mnemonic;
    use webauth_core::identity_resolve::RootResolver;
    use webauth_core::link_claim::format_link_code;

    const BOT_SECRET: [u8; 32] = [0x3cu8; 32];
    const TG_SECRET: [u8; 32] = [0xa7u8; 32];
    const NOW: u64 = 1_790_000_000;

    fn tmp_store(tag: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "dregg-identity-link-{}-{tag}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        dir.join("links.tsv")
    }

    fn state(path: std::path::PathBuf, telegram: bool) -> IdentityLinkState {
        let mut platforms = vec![ConfiguredPlatform {
            platform: LinkPlatform::Discord,
            base_key: phrase_link_challenge_key(&BOT_SECRET),
            bot_secret: Zeroizing::new(BOT_SECRET),
        }];
        if telegram {
            platforms.push(ConfiguredPlatform {
                platform: LinkPlatform::Telegram,
                base_key: phrase_link_challenge_key(&TG_SECRET),
                bot_secret: Zeroizing::new(TG_SECRET),
            });
        }
        IdentityLinkState::new(platforms, path)
    }

    /// ⚑ THE WHOLE POINT, end to end: a bot-minted code plus a real phrase produce a record under
    /// which the WEB key and the DISCORD key resolve to the SAME human — which is exactly what the
    /// Descent board's `merge_per_human` groups on.
    #[test]
    fn a_bot_code_and_a_phrase_make_one_human_on_the_boards() {
        let path = tmp_store("payoff");
        let state = state(path.clone(), false);
        let phrase = generate_mnemonic();
        let web_key = seed_identity::derive_pubkey_hex(&phrase).expect("a fresh phrase derives");
        let uid = 6_913_902_526_u64;
        let code = mint_link_code(
            &BOT_SECRET,
            LinkPlatform::Discord,
            uid,
            NOW,
            PHRASE_LINK_CODE_TTL_SECS,
        );

        let linked =
            prove_and_record(&state, &code, &phrase, true, NOW + 20).expect("the link proves");
        assert_eq!(linked.platform, LinkPlatform::Discord);
        assert_eq!(linked.platform_uid, uid.to_string());
        assert_eq!(linked.root_pubkey_hex, web_key);
        // The custodial key is the bot's OWN derivation, not something the code carried.
        let expected_custodial =
            TurnSigner::from_seed(dreggnet_discord_identity::seed_for(&BOT_SECRET, uid))
                .identity()
                .0;
        assert_eq!(linked.custodial_pubkey_hex, expected_custodial);
        assert_ne!(
            linked.custodial_pubkey_hex, web_key,
            "the two identities stay DISTINCT keys — nothing was merged"
        );

        // THE PAYOFF: one join key for both, through the resolver the boards already use.
        let resolver = RootResolver::from_store(&FileLinkStore::new(&path));
        assert_eq!(
            resolver.resolve(&web_key),
            resolver.resolve(&expected_custodial),
            "the web key and the discord key must resolve to ONE human"
        );
        // …and it is the ACCOUNT ID, not either raw key (so the future identity cell agrees).
        assert_ne!(resolver.resolve(&web_key), web_key);
        assert_eq!(
            Some(resolver.resolve(&web_key)),
            webauth_core::link_registry::account_id_of_root(&web_key)
        );

        // ⚑ THE READING SEAM `/you` UNIONS ON. It must name the Discord custodial key — and NOT the
        // web self-row, which is the viewer's own identity and already counted.
        let store = FileLinkStore::new(&path);
        assert_eq!(actor_keys_in(&store, &web_key), vec![expected_custodial]);
        let shown = linked_platforms_in(&store, &web_key);
        assert_eq!(shown.len(), 2, "the page lists web + discord: {shown:?}");
        assert!(
            shown
                .iter()
                .any(|p| p.platform == "discord" && p.operator_derivable),
            "the discord row MUST be flagged operator-derivable: {shown:?}"
        );
        assert!(
            shown
                .iter()
                .any(|p| p.platform == WEB_PLATFORM && !p.operator_derivable),
            "the web row MUST be flagged self-held: {shown:?}"
        );
        // An UNLINKED key widens nothing — every existing path stays byte-identical.
        assert!(actor_keys_in(&store, &"ff".repeat(32)).is_empty());
        assert!(actor_keys_in(&store, "too-short").is_empty());
        let _ = std::fs::remove_dir_all(path.parent().expect("a parent dir"));
    }

    /// ⚑ WITHOUT THE WEB SELF-ROW THE BOARD STILL PRINTS TWO ROWS. This is the tooth on the design
    /// decision in the module doc: a record set carrying ONLY the platform row leaves the two keys
    /// with two different join keys, so the merge cannot fire.
    #[test]
    fn the_web_self_row_is_what_makes_the_two_keys_share_a_join_key() {
        let root = "ab".repeat(32);
        let custodial = "cd".repeat(32);
        let mut store = webauth_core::link_registry::InMemoryLinkStore::default();
        store
            .record(&LinkRecord {
                root_pubkey_hex: root.clone(),
                platform: "discord".into(),
                platform_uid: "1".into(),
                custodial_pubkey_hex: custodial.clone(),
                verified_at: NOW,
            })
            .expect("records");
        let without = RootResolver::from_store(&store);
        assert_ne!(
            without.resolve(&root),
            without.resolve(&custodial),
            "platform row alone: the root key resolves to ITSELF, the custodial to the account id"
        );
        store
            .record(&LinkRecord {
                root_pubkey_hex: root.clone(),
                platform: WEB_PLATFORM.into(),
                platform_uid: root.clone(),
                custodial_pubkey_hex: root.clone(),
                verified_at: NOW,
            })
            .expect("records");
        let with = RootResolver::from_store(&store);
        assert_eq!(
            with.resolve(&root),
            with.resolve(&custodial),
            "with the self row both resolve to one human"
        );
    }

    /// ⚑ THE FORGERY TOOTH. A player cannot claim someone else's account by editing the uid: the
    /// challenge key is derived per account, so the edited code authenticates under nothing.
    #[test]
    fn editing_the_uid_in_a_code_is_refused_and_records_nothing() {
        let path = tmp_store("uid-swap");
        let state = state(path.clone(), false);
        let phrase = generate_mnemonic();
        let victim = 111_u64;
        let code = mint_link_code(
            &BOT_SECRET,
            LinkPlatform::Discord,
            victim,
            NOW,
            PHRASE_LINK_CODE_TTL_SECS,
        );
        let (_, chal) = parse_link_code(&code).expect("the mint is well-formed");
        let forged = format_link_code("222", chal).expect("re-encodes");
        assert_eq!(
            prove_and_record(&state, &forged, &phrase, true, NOW + 5),
            Err(LinkRefusal::CodeNotOurs)
        );
        assert!(
            !path.exists(),
            "a refused link must not have written a record"
        );
        // NON-VACUOUS: the untouched code links.
        assert!(prove_and_record(&state, &code, &phrase, true, NOW + 5).is_ok());
        let _ = std::fs::remove_dir_all(path.parent().expect("a parent dir"));
    }

    /// A code from a bot whose secret this server does not share is refused — and it is the SAME
    /// refusal as an expired one, so the page is not an oracle over which platforms are configured.
    #[test]
    fn a_foreign_secrets_code_and_an_expired_code_are_one_refusal() {
        let path = tmp_store("foreign");
        let state = state(path.clone(), false);
        let phrase = generate_mnemonic();
        let foreign = mint_link_code(&[0x99u8; 32], LinkPlatform::Discord, 5, NOW, 900);
        assert_eq!(
            prove_and_record(&state, &foreign, &phrase, true, NOW + 5),
            Err(LinkRefusal::CodeNotOurs)
        );
        let stale = mint_link_code(&BOT_SECRET, LinkPlatform::Discord, 5, NOW, 900);
        assert_eq!(
            prove_and_record(&state, &stale, &phrase, true, NOW + 10_000),
            Err(LinkRefusal::CodeNotOurs)
        );
        assert!(!path.exists());
        let _ = std::fs::remove_dir_all(path.parent().expect("a parent dir"));
    }

    /// A code works ONCE. The second use is refused, so somebody who read a code over the player's
    /// shoulder cannot attach their own phrase to that account afterwards.
    #[test]
    fn a_code_is_single_use() {
        let path = tmp_store("single-use");
        let state = state(path.clone(), false);
        let phrase = generate_mnemonic();
        let code = mint_link_code(&BOT_SECRET, LinkPlatform::Discord, 77, NOW, 900);
        assert!(prove_and_record(&state, &code, &phrase, true, NOW + 5).is_ok());
        assert_eq!(
            prove_and_record(&state, &code, &generate_mnemonic(), true, NOW + 6),
            Err(LinkRefusal::CodeAlreadyUsed)
        );
        let _ = std::fs::remove_dir_all(path.parent().expect("a parent dir"));
    }

    /// ⚑ A MISTYPED PHRASE MUST NOT BURN THE CODE. The phrase gate runs BEFORE the nonce is spent,
    /// so a typo costs a retry and not a trip back to Discord.
    #[test]
    fn a_bad_phrase_is_refused_without_spending_the_code() {
        let path = tmp_store("bad-phrase");
        let state = state(path.clone(), false);
        let code = mint_link_code(&BOT_SECRET, LinkPlatform::Discord, 42, NOW, 900);
        assert!(matches!(
            prove_and_record(&state, &code, "not a real phrase at all", true, NOW + 5),
            Err(LinkRefusal::BadPhrase(_))
        ));
        assert!(!path.exists(), "nothing recorded on a bad phrase");
        // The SAME code then works with the right words.
        assert!(prove_and_record(&state, &code, &generate_mnemonic(), true, NOW + 6).is_ok());
        let _ = std::fs::remove_dir_all(path.parent().expect("a parent dir"));
    }

    /// ONE-TO-MANY: one phrase links Discord AND Telegram, and all three keys resolve to one human.
    /// The platform is discovered from the code, never chosen by the player.
    #[test]
    fn one_phrase_links_two_platforms_and_all_three_keys_resolve_together() {
        let path = tmp_store("one-to-many");
        let state = state(path.clone(), true);
        let phrase = generate_mnemonic();
        let web_key = seed_identity::derive_pubkey_hex(&phrase).expect("derives");

        let d = prove_and_record(
            &state,
            &mint_link_code(&BOT_SECRET, LinkPlatform::Discord, 11, NOW, 900),
            &phrase,
            true,
            NOW + 1,
        )
        .expect("discord links");
        let t = prove_and_record(
            &state,
            &mint_link_code(&TG_SECRET, LinkPlatform::Telegram, 22, NOW, 900),
            &phrase,
            true,
            NOW + 2,
        )
        .expect("telegram links");
        assert_eq!(d.platform, LinkPlatform::Discord);
        assert_eq!(t.platform, LinkPlatform::Telegram);
        assert_ne!(d.custodial_pubkey_hex, t.custodial_pubkey_hex);

        let resolver = RootResolver::from_store(&FileLinkStore::new(&path));
        let human = resolver.resolve(&web_key);
        assert_eq!(resolver.resolve(&d.custodial_pubkey_hex), human);
        assert_eq!(resolver.resolve(&t.custodial_pubkey_hex), human);

        // A genuinely different human is NOT merged in (non-vacuity).
        let other = generate_mnemonic();
        let other_key = seed_identity::derive_pubkey_hex(&other).expect("derives");
        prove_and_record(
            &state,
            &mint_link_code(&BOT_SECRET, LinkPlatform::Discord, 33, NOW, 900),
            &other,
            true,
            NOW + 3,
        )
        .expect("a second human links");
        let resolver = RootResolver::from_store(&FileLinkStore::new(&path));
        assert_ne!(resolver.resolve(&other_key), human);

        // `platforms_for_root` sees three rows for the first human: web, discord, telegram.
        let rows = FileLinkStore::new(&path)
            .platforms_for_root(&web_key)
            .expect("reads");
        let mut kinds: Vec<String> = rows.into_iter().map(|r| r.platform).collect();
        kinds.sort();
        assert_eq!(kinds, vec!["discord", "telegram", "web"]);
        let _ = std::fs::remove_dir_all(path.parent().expect("a parent dir"));
    }

    /// A REBIND supersedes: linking the same Discord account from a NEW phrase moves it, and the old
    /// phrase stops resolving with it. Append-only, latest wins — no record is mutated.
    #[test]
    fn relinking_from_a_new_phrase_supersedes() {
        let path = tmp_store("rebind");
        let state = state(path.clone(), false);
        let first = generate_mnemonic();
        let second = generate_mnemonic();
        let first_key = seed_identity::derive_pubkey_hex(&first).expect("derives");
        let second_key = seed_identity::derive_pubkey_hex(&second).expect("derives");
        let custodial = prove_and_record(
            &state,
            &mint_link_code(&BOT_SECRET, LinkPlatform::Discord, 9, NOW, 900),
            &first,
            true,
            NOW + 1,
        )
        .expect("first link")
        .custodial_pubkey_hex;
        prove_and_record(
            &state,
            &mint_link_code(&BOT_SECRET, LinkPlatform::Discord, 9, NOW + 100, 900),
            &second,
            true,
            NOW + 200,
        )
        .expect("rebind");
        let resolver = RootResolver::from_store(&FileLinkStore::new(&path));
        assert_eq!(resolver.resolve(&custodial), resolver.resolve(&second_key));
        assert_ne!(resolver.resolve(&custodial), resolver.resolve(&first_key));
        assert_eq!(
            FileLinkStore::new(&path).all().expect("reads").len(),
            4,
            "append-only: two rows per link, nothing rewritten"
        );
        let _ = std::fs::remove_dir_all(path.parent().expect("a parent dir"));
    }

    /// Malformed codes die at the parse, and nothing is recorded.
    #[test]
    fn malformed_codes_are_named_rather_than_swallowed() {
        let path = tmp_store("malformed");
        let state = state(path.clone(), false);
        let phrase = generate_mnemonic();
        assert_eq!(
            prove_and_record(&state, "no-separator", &phrase, true, NOW),
            Err(LinkRefusal::MalformedCode)
        );
        assert_eq!(
            prove_and_record(&state, "not-a-number:whatever.abc", &phrase, true, NOW),
            Err(LinkRefusal::MalformedUid)
        );
        assert!(!path.exists());
        let _ = std::fs::remove_dir_all(path.parent().expect("a parent dir"));
    }

    /// ⚑ THE ASYMMETRY IS ON THE PAGE, in the words that matter, on BOTH the deciding view and the
    /// post-link view — and the page never tells the player their Discord key became theirs.
    #[test]
    fn the_page_states_the_custodial_asymmetry_in_both_states() {
        // A REAL store with a REAL pair of rows, so the page renders the row list it would in
        // production rather than the empty-state prose.
        let path = tmp_store("page");
        let state = state(path.clone(), false);
        let phrase = generate_mnemonic();
        let web_key = seed_identity::derive_pubkey_hex(&phrase).expect("derives");
        let linked = prove_and_record(
            &state,
            &mint_link_code(&BOT_SECRET, LinkPlatform::Discord, 42, NOW, 900),
            &phrase,
            true,
            NOW + 1,
        )
        .expect("links");

        let before = link_page(&[LinkPlatform::Discord], &path, None, None, None, None);
        let after = link_page(
            &[LinkPlatform::Discord],
            &path,
            Some(web_key.as_str()),
            Some(&linked),
            None,
            None,
        );
        // The post-link view lists BOTH rows, each with its own custody sentence.
        assert!(after.contains("Custodial"), "{after}");
        assert!(after.contains("Self-held"), "{after}");
        for page in [&before, &after] {
            assert!(page.contains("still CUSTODIAL"), "{page}");
            assert!(page.contains("bot_secret"), "{page}");
            assert!(
                page.contains("linking does not change that"),
                "the link must not be sold as changing custody: {page}"
            );
            assert!(
                page.contains("Your two keys stay two keys"),
                "the no-merge statement is missing: {page}"
            );
            assert!(
                page.contains("attributed</em> rather than signed") || page.contains("attributed"),
                "{page}"
            );
        }
        // A refusal page still carries the asymmetry (a player reading an error is still deciding).
        let refused = link_page(
            &[LinkPlatform::Discord],
            &path,
            None,
            None,
            Some(&LinkRefusal::CodeNotOurs.message()),
            None,
        );
        assert!(refused.contains("still CUSTODIAL"), "{refused}");
        assert!(refused.contains("notice refused"), "{refused}");
        // The window the page promises IS the issuer's constant, not a second number.
        assert!(
            before.contains(&format!("good for {} minutes", code_window_minutes())),
            "{before}"
        );
        let _ = std::fs::remove_dir_all(path.parent().expect("a parent dir"));
    }

    /// ⚑ THE PHONE PATH. A `?code=` prefills the box, is HTML-escaped into the `value`, ships the
    /// address-bar cleanup, and SAYS that the code travelled in a URL — a convenience whose cost is
    /// hidden is the thing this page is not allowed to be.
    #[test]
    fn a_prefilled_code_fills_the_box_and_states_what_that_cost() {
        let path = tmp_store("prefill");
        let code = mint_link_code(&BOT_SECRET, LinkPlatform::Discord, 42, NOW, 900);
        let page = link_page(
            &[LinkPlatform::Discord],
            &path,
            None,
            None,
            None,
            Some(&code),
        );
        assert!(
            page.contains(&format!("value=\"{code}\"")),
            "the code must land in the input's value: {page}"
        );
        assert!(page.contains("Your code is filled in below"), "{page}");
        assert!(
            page.contains("bearer token"),
            "the cost of a code-in-a-URL must be stated: {page}"
        );
        assert!(
            page.contains("replaceState"),
            "the address-bar cleanup must ship with a prefill: {page}"
        );
        // …and NOT ship when there is nothing to clean.
        let bare = link_page(&[LinkPlatform::Discord], &path, None, None, None, None);
        assert!(!bare.contains("replaceState"), "{bare}");
        assert!(!bare.contains("Your code is filled in below"), "{bare}");
        assert!(bare.contains("value=\"\""), "the box renders empty: {bare}");

        // ⚑ A code is attacker-supplied text on this path. It must be ESCAPED into the attribute, or
        // `?code=` would be reflected XSS on the one page that then asks for 24 words.
        let nasty = link_page(
            &[LinkPlatform::Discord],
            &path,
            None,
            None,
            None,
            Some("\"><script>alert(1)</script>"),
        );
        assert!(
            !nasty.contains("<script>alert(1)</script>"),
            "a code broke out of the value attribute: {nasty}"
        );
        assert!(nasty.contains("&lt;script&gt;"), "{nasty}");
        let _ = std::fs::remove_dir_all(path.parent().expect("a parent dir"));
    }

    /// ⚑ A DEPLOYMENT WITH NO PLATFORM SECRET SAYS SO, and serves no form. The page is still mounted
    /// (every other page links here, and a 404 teaches a player nothing), and it must blame the
    /// missing env rather than the player's code.
    #[test]
    fn an_unconfigured_deployment_says_so_and_offers_no_form() {
        let path = tmp_store("unconfigured");
        let page = link_page(&[], &path, None, None, None, None);
        assert!(
            !page.contains("<form"),
            "a box whose every submission refuses must not be shown: {page}"
        );
        assert!(page.contains("cannot prove a link"), "{page}");
        assert!(page.contains("no such secret"), "{page}");
        assert!(
            page.contains("BOT_SECRET"),
            "the env to set is named: {page}"
        );
        assert!(page.contains("DREGG_LINK_DIR"), "{page}");
        // The asymmetry is stated even here — a reader is still learning what linking would mean.
        assert!(page.contains("still CUSTODIAL"), "{page}");

        // ⚑ AND A PER-REQUEST REFUSAL STILL RENDERS HERE. This branch computed the notice and threw
        // it away, so on an unconfigured deployment every refusal — a cross-origin submission
        // included — was swallowed into the standing "cannot prove a link" page and the player never
        // learned what had just happened to their request.
        let refused = link_page(
            &[],
            &path,
            None,
            None,
            Some(&LinkRefusal::NotFromOurPage.message()),
            None,
        );
        assert!(
            refused.contains("did not come from our page"),
            "an unconfigured deployment must still render the refusal it just answered: {refused}"
        );
        // …and with nothing to say it says nothing extra (the page above is the unchanged one).
        assert!(!page.contains("did not come from our page"), "{page}");

        // And the ceremony refuses with the OPERATOR-shaped variant, not "your code expired".
        let state = IdentityLinkState::new(Vec::new(), path.clone());
        let refusal = prove_and_record(&state, "1:abc.def", &generate_mnemonic(), true, NOW)
            .expect_err("nothing can be proven");
        assert_eq!(refusal, LinkRefusal::NoPlatformConfigured);
        assert_eq!(refusal.http_status(), StatusCode::SERVICE_UNAVAILABLE);
        assert!(
            refusal.message().contains("operator setting"),
            "the refusal must not blame the player: {}",
            refusal.message()
        );
        assert!(!path.exists());
        let _ = std::fs::remove_dir_all(path.parent().expect("a parent dir"));
    }

    /// A refusal that leaves the code LIVE hands it back; one that kills the code does not. Re-typing
    /// 117 characters after a typo is busywork; re-offering a dead code is an invitation to fail again.
    #[test]
    fn only_a_still_live_code_is_handed_back_after_a_refusal() {
        assert!(matches!(
            LinkRefusal::BadPhrase("x".into()),
            LinkRefusal::BadPhrase(_)
        ));
        // The policy itself, as the handler expresses it.
        let handed_back = |r: &LinkRefusal| {
            matches!(
                r,
                LinkRefusal::BadPhrase(_) | LinkRefusal::AccountNotConfirmed { .. }
            )
        };
        assert!(handed_back(&LinkRefusal::BadPhrase("x".into())));
        assert!(
            handed_back(&LinkRefusal::AccountNotConfirmed {
                platform: LinkPlatform::Discord,
                uid: "1".into()
            }),
            "an unticked box leaves the code live, so it comes back"
        );
        for dead in [
            LinkRefusal::CodeAlreadyUsed,
            LinkRefusal::CodeNotOurs,
            LinkRefusal::MalformedCode,
            LinkRefusal::MalformedUid,
            LinkRefusal::NoPlatformConfigured,
            // A cross-origin submission's code was never the player's to retype, and reflecting it
            // back into our own page would be doing the attacker's rendering for them.
            LinkRefusal::NotFromOurPage,
        ] {
            assert!(!handed_back(&dead), "a dead code was re-offered: {dead:?}");
        }
    }

    /// ⚑ THE PHISHING TOOTH. A genuine code for SOMEBODY ELSE'S account authenticates perfectly — so
    /// the ceremony must not proceed on it silently. Without the ticked box nothing is recorded, the
    /// refusal NAMES the account so the player can see it is not theirs, and the code stays live.
    #[test]
    fn a_code_for_someone_elses_account_is_refused_until_the_player_says_it_is_theirs() {
        let path = tmp_store("consent");
        let state = state(path.clone(), false);
        let phrase = generate_mnemonic();
        // A stranger's perfectly genuine code, handed to this player.
        let code = mint_link_code(&BOT_SECRET, LinkPlatform::Discord, 999_888_777, NOW, 900);

        let refusal = prove_and_record(&state, &code, &phrase, false, NOW + 5)
            .expect_err("an unticked box must refuse");
        assert_eq!(
            refusal,
            LinkRefusal::AccountNotConfirmed {
                platform: LinkPlatform::Discord,
                uid: "999888777".to_string(),
            }
        );
        assert!(
            !path.exists(),
            "an unconfirmed link must record NOTHING: the whole point"
        );
        // The refusal NAMES the account, and tells the player what to do if it is not theirs.
        let message = refusal.message();
        assert!(message.contains("999888777"), "{message}");
        assert!(message.contains("Discord"), "{message}");
        assert!(message.contains("not YOUR account"), "{message}");
        assert!(
            message.contains("undo a link now"),
            "the refusal must point at the removal page now that one exists: {message}"
        );
        // ⚑ And the code is NOT spent — a player who ticks the box then succeeds.
        assert!(prove_and_record(&state, &code, &phrase, true, NOW + 6).is_ok());
        let _ = std::fs::remove_dir_all(path.parent().expect("a parent dir"));
    }

    /// ⚑ THE TWO-STEP TOOTH. Step one has **no phrase box at all**, and step two names an account
    /// that was CHECKED rather than read out of the paste. Both halves are the residual this
    /// replaces: the old page showed an unverified number beside the box that already had the
    /// player's words in it.
    #[test]
    fn a_prefilled_code_reaches_no_phrase_box_until_the_account_is_confirmed() {
        let path = tmp_store("whose");
        let state = state(path.clone(), false);
        let code = mint_link_code(&BOT_SECRET, LinkPlatform::Discord, 999_888_777, NOW, 900);

        // STEP ONE, even with the code prefilled off a tapped link: the code box, and nothing that
        // asks for 24 words. This is the screen a phishing prefill lands on.
        let step_one = link_page(
            &[LinkPlatform::Discord],
            &path,
            None,
            None,
            None,
            Some(&code),
        );
        assert!(step_one.contains("Check this code"), "{step_one}");
        assert!(
            !step_one.contains("name=\"phrase\""),
            "step one must not contain a phrase box: {step_one}"
        );
        assert!(
            !step_one.contains("name=\"mine\""),
            "nor the consent box, which belongs beside the account it consents to: {step_one}"
        );
        assert!(step_one.contains("given away nothing"), "{step_one}");

        // The code AUTHENTICATES, and to the account it was really minted for.
        let (configured, uid) =
            authenticate_code(&state, &code, NOW + 5).expect("a fresh bot code authenticates");
        assert_eq!(configured.platform, LinkPlatform::Discord);
        assert_eq!(uid, "999888777");

        // STEP TWO: the account is named, the consent box sits beside it, and NOW there are words.
        let step_two = link_page_with(
            &[LinkPlatform::Discord],
            &path,
            None,
            None,
            None,
            Some(&code),
            Some((LinkPlatform::Discord, "999888777")),
        );
        assert!(step_two.contains("account 999888777"), "{step_two}");
        assert!(step_two.contains("Is that your account?"), "{step_two}");
        assert!(step_two.contains("close the page"), "{step_two}");
        assert!(step_two.contains("name=\"mine\""), "{step_two}");
        assert!(step_two.contains("name=\"phrase\""), "{step_two}");
        // …and it does NOT hedge the number, because this one was checked.
        assert!(
            !step_two.contains("checked for real when you submit"),
            "a verified account must not be presented as unverified: {step_two}"
        );

        // ⚑ A code a stranger forged the uid onto never reaches step two at all.
        let spliced = format!("111222333:{}", code.split(':').nth(1).expect("a challenge"));
        assert_eq!(
            authenticate_code(&state, &spliced, NOW + 5).err(),
            Some(LinkRefusal::CodeNotOurs)
        );
        assert_eq!(
            authenticate_code(&state, "no-colon", NOW + 5).err(),
            Some(LinkRefusal::MalformedCode)
        );
        assert_eq!(
            authenticate_code(&state, "not-a-uid:abc", NOW + 5).err(),
            Some(LinkRefusal::MalformedUid)
        );
        // Step one is REACHED by an authenticate that failed, so a bad code costs no words either.
        let _ = std::fs::remove_dir_all(path.parent().expect("a parent dir"));
    }

    /// Every refusal says what happened AND that nothing was linked — never a bare status.
    #[test]
    fn every_refusal_says_nothing_was_linked() {
        use dregg_sdk::mnemonic::MnemonicError;
        // Each phrase branch renders a sentence naming the failing check, never a bare "invalid".
        assert!(phrase_detail(&MnemonicError::InvalidWordCount(6)).contains("exactly 24"));
        assert!(phrase_detail(&MnemonicError::InvalidChecksum).contains("checksum"));
        assert!(
            phrase_detail(&MnemonicError::UnknownWord("xyzzy".into())).contains("2048"),
            "an unknown word must be named"
        );
        for refusal in [
            LinkRefusal::NotFromOurPage,
            LinkRefusal::NoPlatformConfigured,
            LinkRefusal::MalformedCode,
            LinkRefusal::MalformedUid,
            LinkRefusal::CodeNotOurs,
            LinkRefusal::CodeAlreadyUsed,
            LinkRefusal::AccountNotConfirmed {
                platform: LinkPlatform::Telegram,
                uid: "7".into(),
            },
            LinkRefusal::BadPhrase(phrase_detail(&MnemonicError::InvalidChecksum)),
            LinkRefusal::SelfCheckFailed("x".into()),
            LinkRefusal::NotRecorded("y".into()),
        ] {
            let message = refusal.message();
            assert!(
                message.starts_with("Refused:"),
                "a refusal must render as one: {message}"
            );
            assert!(
                message.to_lowercase().contains("nothing")
                    || message.to_lowercase().contains("declined"),
                "a refusal must say nothing happened: {message}"
            );
            assert!(
                refusal.http_status().is_client_error() || refusal.http_status().is_server_error()
            );
        }
    }

    /// **Top-level bot commands an ordinary player CANNOT type.** `24e47322b` moved these off
    /// Discord's global surface: they are registered only inside `DREGG_LAB_GUILD_ID`, so a player in
    /// a normal server gets no autocomplete and no command.
    ///
    /// ⚑ **This is a MIRROR, and it is one on purpose.** The authority is
    /// `discord-bot/src/commands/menus.rs::SLASH_SURFACE` — its `Door::Lab` rows, plus its
    /// `Door::Offering(key)` rows whose key is off `dreggnet_catalog::SHIPPED_KEYS`. `dreggnet-web`
    /// CANNOT depend on `dregg-discord-bot` (an EXCLUDED workspace; see `Cargo.toml`), so a
    /// compile-time join is not available and the alternative was no tooth at all. The three
    /// offering-derived rows are therefore DERIVED here from the same ship list the bot derives them
    /// from ([`lab_only_bot_commands`]), and only the four pure-lab names are copied. If the copy goes
    /// stale this tooth mis-reports in BOTH directions — it would miss a newly demoted command, and it
    /// would wrongly flag copy naming a re-advertised one. It is a smoke alarm, not a proof.
    const PURE_LAB_BOT_COMMANDS: [&str; 4] = ["identity", "gallery", "federation", "leaderboard"];

    /// The lab-only set, with the offering-derived rows derived rather than copied: re-list `dungeon`,
    /// `council` or `hermes` on `dreggnet_catalog::SHIPPED_KEYS` and `/adventure`, `/govern` and
    /// `/hermes` come back off this list on their own, exactly as they come back onto the bot's menu.
    fn lab_only_bot_commands() -> Vec<&'static str> {
        let mut names: Vec<&'static str> = PURE_LAB_BOT_COMMANDS.to_vec();
        for (command, offering) in [
            ("adventure", "dungeon"),
            ("govern", "council"),
            ("hermes", "hermes"),
        ] {
            if !dreggnet_catalog::is_shipped(offering) {
                names.push(command);
            }
        }
        names
    }

    /// ⚑ **THE DEAD-COMMAND TOOTH.** No string this page shows a player may tell them to run a
    /// command that is not in their `/` menu.
    ///
    /// This is the defect it exists for: the Discord instruction said `run /identity link-web` for
    /// hours after `/identity` had been demoted to lab-only, so the one sentence whose entire job is
    /// "here is how you get a code" named a command a player could not type — a dead end on the
    /// load-bearing step of the ceremony. The bot's own copy was already correct
    /// (`/cipherclerk link-web`) and its own test already asserted the re-homing; nothing looked at
    /// the web copy, on either side of the seam.
    ///
    /// A `<code>/word` in this page's copy IS an instruction to type that command; an `href="/word"`
    /// is one of our own URLs, and is not what this checks.
    #[test]
    fn no_player_facing_copy_names_a_lab_only_bot_command() {
        let lab = lab_only_bot_commands();
        let names_a_lab_command = |copy: &str| -> Option<String> {
            lab.iter()
                .find(|name| copy.contains(&format!("<code>/{name}")))
                .map(|name| format!("/{name}"))
        };

        // NON-VACUOUS: the exact string that shipped is what this check is for.
        assert_eq!(
            names_a_lab_command(
                "In any server the bot is in, run <code>/identity link-web</code>."
            )
            .as_deref(),
            Some("/identity"),
            "the checker must flag the very sentence that shipped, or it proves nothing"
        );

        // Every player-facing string on this surface, in the states a player meets them.
        let path = tmp_store("dead-command");
        let mut copy: Vec<String> = LinkPlatform::ALL
            .iter()
            .map(|platform| platform.how_to_get_a_code().to_string())
            .collect();
        copy.push(asymmetry_block());
        copy.push(link_page(&LinkPlatform::ALL, &path, None, None, None, None));
        copy.push(link_page(&[], &path, None, None, None, None));
        copy.push(link_page(
            &LinkPlatform::ALL,
            &path,
            None,
            None,
            Some(&LinkRefusal::NotFromOurPage.message()),
            None,
        ));
        for refusal in [
            LinkRefusal::NotFromOurPage,
            LinkRefusal::NoPlatformConfigured,
            LinkRefusal::CodeNotOurs,
            LinkRefusal::CodeAlreadyUsed,
            LinkRefusal::AccountNotConfirmed {
                platform: LinkPlatform::Discord,
                uid: "1".into(),
            },
        ] {
            copy.push(refusal.message());
        }
        for text in &copy {
            assert_eq!(
                names_a_lab_command(text),
                None,
                "player-facing copy names a command a player cannot type: {text}"
            );
        }

        // …and the POSITIVE half: the Discord instruction names the command `link-web` actually
        // lives on. Asserted as well as the absence, so deleting the sentence would not go green.
        assert!(
            LinkPlatform::Discord
                .how_to_get_a_code()
                .contains("<code>/cipherclerk link-web</code>"),
            "the Discord instruction must name the ADVERTISED home of `link-web`: {}",
            LinkPlatform::Discord.how_to_get_a_code()
        );
        let _ = std::fs::remove_dir_all(path.parent().expect("a parent dir"));
    }

    /// The platform wire names are the SAME strings `/da/link` and `/tg/link` already record — a
    /// link made here and one made there are one record shape, resolved by one resolver.
    #[test]
    fn the_wire_names_match_the_existing_ceremonies() {
        assert_eq!(LinkPlatform::Discord.wire(), "discord");
        assert_eq!(LinkPlatform::Telegram.wire(), "telegram");
        assert_eq!(WEB_PLATFORM, "web");
    }
}
