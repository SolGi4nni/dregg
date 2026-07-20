//! One live capability-seated party plays across the deployed browser, Telegram
//! Mini App, and Discord Activity adapters.
//!
//! This is deliberately one shared session, not three adapter-local demos:
//!
//! - an asserted browser identity claims the leader/Tank seat;
//! - a Telegram initData-authenticated custodial signer claims Scout;
//! - a Discord OAuth-ticket-authenticated custodial signer claims Mage;
//! - a second browser identity claims Healer;
//! - all four ready, the browser leader launches, and three different platform
//!   identities cast the custody-signed target quorum;
//! - the leader resolves, Discord contributes its real role tactic, and the
//!   leader explicitly advances an enemy through the ordinary action routes;
//! - the rendered tactical state and replay verifier survive a fresh host over
//!   the same durable move-log directory.
//!
//! The Telegram and Discord requests use their production authentication
//! validators and custodial `advance_signed` paths. The browser cookie remains
//! honestly `Asserted` provenance; this test does not promote it to a signature.
//!
//! Target ballots currently fail closed when the verified ML-DSA signing core is
//! absent. A functional-only run may explicitly set
//! `DREGG_ALLOW_UNAUDITED_PQ=1`; that demonstrates adapter/game/replay behavior,
//! not the unavailable verified-PQ signing claim.

use std::fs;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use axum::Router;
use axum::body::Body;
use axum::http::{Request, StatusCode};
use dreggnet_discord_identity::seed_for as discord_seed_for;
use dreggnet_offerings::{FileResumeStore, OfferingHost, SessionId, TurnSigner};
use dreggnet_surfaces::PartyOffering;
use dreggnet_surfaces::party::{
    TURN_ACT, TURN_ADVANCE_ENEMY, TURN_CLAIM, TURN_FORK, TURN_LAUNCH, TURN_READY, TURN_RESOLVE_FORK,
};
use dreggnet_telegram::cipherclerk::TelegramCipherclerk;
use dreggnet_web::discord_activity::{
    ACTIVITY_TICKET_HEADER, DiscordActivityState, DiscordCodeExchange, DiscordTokenExchange,
    OAuthError, discord_activity_router,
};
use dreggnet_web::telegram_miniapp::{
    INIT_DATA_HEADER, TgMiniAppState, tg_miniapp_router, validate_init_data_at, webapp_secret_key,
};
use dreggnet_web::{CatalogState, catalog_router, web_identity};
use hmac::{Hmac, Mac};
use sha2::Sha256;
use tower::ServiceExt;

const KEY: &str = "party";
const SESSION: &str = "three-surface-raid";
const TG_TOKEN: &str = "123456789:test-only-party-token";
const TG_SECRET: [u8; 32] = [0x81; 32];
const DA_SECRET: [u8; 32] = [0x82; 32];
const TG_UID: u64 = 7_001;
const DA_UID: u64 = 8_002;

fn unix_now() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_secs())
        .unwrap_or(0)
}

fn hex32(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn url_encode(value: &str) -> String {
    let mut out = String::new();
    for byte in value.bytes() {
        match byte {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'_' | b'.' | b'~' => {
                out.push(byte as char);
            }
            _ => out.push_str(&format!("%{byte:02X}")),
        }
    }
    out
}

/// Mint Telegram's production initData shape under a test-only bot token.
fn telegram_init_data(uid: u64) -> String {
    type HmacSha256 = Hmac<Sha256>;

    let auth_date = unix_now();
    let user = format!(r#"{{"id":{uid},"first_name":"Scout","username":"party_scout"}}"#);
    let signature = "test-only-third-party-signature";
    let data_check_string = format!(
        "auth_date={auth_date}\nquery_id=party-cross-surface\nsignature={signature}\nuser={user}"
    );
    let secret = webapp_secret_key(TG_TOKEN);
    let mut mac = HmacSha256::new_from_slice(&secret).expect("HMAC accepts the Telegram key");
    mac.update(data_check_string.as_bytes());
    let hash: [u8; 32] = mac.finalize().into_bytes().into();
    let init_data = format!(
        "query_id=party-cross-surface&user={}&auth_date={auth_date}&signature={signature}&hash={}",
        url_encode(&user),
        hex32(&hash),
    );
    validate_init_data_at(&secret, &init_data, auth_date, 86_400)
        .expect("fixture initData passes the production validator");
    init_data
}

struct StubDiscordExchange;

impl DiscordTokenExchange for StubDiscordExchange {
    fn exchange(
        &self,
        _client_id: &str,
        _client_secret: &str,
        code: &str,
    ) -> Result<DiscordCodeExchange, OAuthError> {
        if code != "test-only-party-code" {
            return Err(OAuthError::TokenStatus(401));
        }
        Ok(DiscordCodeExchange {
            user_id: DA_UID,
            access_token: "test-only-party-access-token".to_string(),
            username: Some("party_mage".to_string()),
        })
    }
}

fn scratch_dir() -> PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static N: AtomicU64 = AtomicU64::new(0);
    let n = N.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "dreggnet-party-cross-surface-{}-{n}",
        std::process::id(),
    ));
    let _ = fs::remove_dir_all(&dir);
    dir
}

fn party_host_over(dir: PathBuf) -> OfferingHost {
    let store = FileResumeStore::open(dir).expect("durable party store opens");
    let mut host = OfferingHost::new().with_resume_store(Box::new(store));
    host.register(KEY, "DreggNet Party", PartyOffering::new());
    let resumed = host.resume_all();
    assert!(
        resumed.iter().all(|(_, result)| result.is_ok()),
        "every authentic party log resumes: {resumed:?}"
    );
    host
}

fn app_over(dir: PathBuf) -> (Router, Arc<CatalogState>) {
    let catalog = Arc::new(CatalogState::with_host(move || party_host_over(dir)));
    let tg = tg_miniapp_router(Arc::new(TgMiniAppState::new(
        Arc::clone(&catalog),
        TG_TOKEN,
        TG_SECRET,
        86_400,
    )));
    let da = discord_activity_router(Arc::new(DiscordActivityState::with_oauth(
        Arc::clone(&catalog),
        "party-client",
        "party-client-secret",
        DA_SECRET,
        86_400,
        Arc::new(StubDiscordExchange),
    )));
    let app = Router::new()
        .merge(catalog_router(Arc::clone(&catalog)))
        .merge(tg)
        .merge(da);
    (app, catalog)
}

async fn response(app: &Router, request: Request<Body>) -> (StatusCode, String) {
    let response = app.clone().oneshot(request).await.expect("router responds");
    let status = response.status();
    let body = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .expect("response body is bounded in-memory HTML");
    (
        status,
        String::from_utf8(body.to_vec()).expect("surface is utf-8"),
    )
}

fn form(turn: &str, arg: i64) -> Body {
    Body::from(format!("turn={turn}&arg={arg}"))
}

async fn web_act(app: &Router, turn: &str, arg: i64, user: &str) -> String {
    let (status, body) = response(
        app,
        Request::builder()
            .method("POST")
            .uri(format!("/offerings/{KEY}/session/{SESSION}/act"))
            .header("content-type", "application/x-www-form-urlencoded")
            .header("cookie", format!("dregg_user={user}"))
            .body(form(turn, arg))
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "web {turn} response: {body}");
    assert!(body.contains("Turn committed"), "web {turn} lands: {body}");
    body
}

async fn tg_act(app: &Router, init_data: &str, turn: &str, arg: i64) -> String {
    let (status, body) = response(
        app,
        Request::builder()
            .method("POST")
            .uri(format!("/tg/offerings/{KEY}/session/{SESSION}/act"))
            .header("content-type", "application/x-www-form-urlencoded")
            .header(INIT_DATA_HEADER, init_data)
            .body(form(turn, arg))
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "Telegram {turn} response: {body}");
    assert!(
        body.contains("Turn committed") && body.contains("Telegram-attested"),
        "Telegram {turn} crosses its signed adapter: {body}"
    );
    body
}

async fn da_act(app: &Router, ticket: &str, turn: &str, arg: i64) -> String {
    let (status, body) = response(
        app,
        Request::builder()
            .method("POST")
            .uri(format!("/da/offerings/{KEY}/session/{SESSION}/act"))
            .header("content-type", "application/x-www-form-urlencoded")
            .header(ACTIVITY_TICKET_HEADER, ticket)
            .body(form(turn, arg))
            .unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK, "Discord {turn} response: {body}");
    assert!(
        body.contains("Turn committed") && body.contains("Discord-attested"),
        "Discord {turn} crosses its signed adapter: {body}"
    );
    body
}

async fn web_get(app: &Router, suffix: &str, user: &str) -> (StatusCode, String) {
    response(
        app,
        Request::builder()
            .uri(format!("/offerings/{KEY}/session/{SESSION}{suffix}"))
            .header("cookie", format!("dregg_user={user}"))
            .body(Body::empty())
            .unwrap(),
    )
    .await
}

fn short(identity: &str) -> &str {
    &identity[..15.min(identity.len())]
}

#[tokio::test(flavor = "multi_thread")]
async fn one_party_forms_votes_fights_and_restarts_across_all_three_adapters() {
    let dir = scratch_dir();
    let (app, catalog) = app_over(dir.clone());
    let tg_init = telegram_init_data(TG_UID);

    // Drive the real Discord OAuth seam; subsequent requests carry only the
    // production-minted Activity bearer ticket.
    let (status, token_body) = response(
        &app,
        Request::builder()
            .method("POST")
            .uri("/da/token")
            .header("content-type", "application/json")
            .body(Body::from(r#"{"code":"test-only-party-code"}"#))
            .unwrap(),
    )
    .await;
    assert_eq!(
        status,
        StatusCode::OK,
        "Discord token response: {token_body}"
    );
    let token: serde_json::Value = serde_json::from_str(&token_body).unwrap();
    let da_ticket = token["ticket"].as_str().expect("ticket minted").to_string();

    // Both native-platform action routes fail closed before opening or mutating
    // the shared session when their platform proof is absent.
    for prefix in ["/tg", "/da"] {
        let (status, _) = response(
            &app,
            Request::builder()
                .method("POST")
                .uri(format!("{prefix}/offerings/{KEY}/session/{SESSION}/act"))
                .header("content-type", "application/x-www-form-urlencoded")
                .body(form(TURN_CLAIM, 1))
                .unwrap(),
        )
        .await;
        assert_eq!(status, StatusCode::UNAUTHORIZED, "{prefix} is auth-gated");
    }
    assert!(
        !catalog.is_open(KEY, &SessionId::new(SESSION)),
        "refused platform probes are anti-ghost"
    );

    // Four distinct, platform-derived identities occupy the canonical role
    // slots. The first claimant is the only launch/enemy authority.
    web_act(&app, TURN_CLAIM, 0, "browser-tank").await;
    tg_act(&app, &tg_init, TURN_CLAIM, 1).await;
    da_act(&app, &da_ticket, TURN_CLAIM, 2).await;
    web_act(&app, TURN_CLAIM, 3, "browser-healer").await;

    web_act(&app, TURN_READY, 0, "browser-tank").await;
    tg_act(&app, &tg_init, TURN_READY, 0).await;
    da_act(&app, &da_ticket, TURN_READY, 0).await;
    let roster = web_act(&app, TURN_READY, 0, "browser-healer").await;

    let web_tank = web_identity("browser-tank");
    let web_healer = web_identity("browser-healer");
    let tg_scout = TelegramCipherclerk::derive(&TG_SECRET, TG_UID).identity();
    let da_mage = TurnSigner::from_seed(discord_seed_for(&DA_SECRET, DA_UID)).identity();
    for identity in [&web_tank, &tg_scout, &da_mage, &web_healer] {
        assert!(
            roster.contains(short(&identity.0)),
            "one rendered roster contains platform actor {}: {roster}",
            identity.0,
        );
    }
    assert!(
        roster.contains("4 / 4 roles"),
        "the shared roster is full: {roster}"
    );

    let launched = web_act(&app, TURN_LAUNCH, 0, "browser-tank").await;
    assert!(
        launched.contains("LAUNCHED"),
        "the live roster enters the Arena: {launched}"
    );
    assert!(
        launched.contains("Enemy target ballot"),
        "the real fork opens: {launched}"
    );

    // Three independently authenticated seats form the quorum on Warden.
    web_act(&app, TURN_FORK, 0, "browser-tank").await;
    tg_act(&app, &tg_init, TURN_FORK, 0).await;
    let ballot = da_act(&app, &da_ticket, TURN_FORK, 0).await;
    assert!(
        ballot.contains("3 vote(s)"),
        "three custody ballots are visible: {ballot}"
    );

    let resolved = web_act(&app, TURN_RESOLVE_FORK, 0, "browser-tank").await;
    assert!(
        resolved.contains("the party concentrates on the Warden")
            && resolved.contains("Tactical Arena"),
        "quorum resolution enters the rendered tactical state: {resolved}"
    );

    // Initiative may begin on an enemy. Only the browser leader has enemy-AI
    // authority, so advance until a hero is active, then spend Discord's Mage
    // capability as a real cross-surface role tactic.
    let mut tactical = resolved;
    for _ in 0..4 {
        if !tactical.contains("active Warden") && !tactical.contains("active Hound") {
            break;
        }
        tactical = web_act(&app, TURN_ADVANCE_ENEMY, 0, "browser-tank").await;
    }
    assert!(
        tactical.contains("active Ranger") || tactical.contains("active Cleric"),
        "a hero is active before the role tactic: {tactical}"
    );
    tactical = da_act(&app, &da_ticket, TURN_ACT, 0).await;
    assert!(
        tactical.contains("Mage") && tactical.contains("contributed"),
        "Discord's claimed Mage capability changed the shared Arena: {tactical}"
    );

    // There are two heroes. If initiative stays on the second one, spend the
    // browser leader's distinct Tank contribution before advancing the enemy.
    if tactical.contains("active Ranger") || tactical.contains("active Cleric") {
        tactical = web_act(&app, TURN_ACT, 0, "browser-tank").await;
    }
    assert!(
        tactical.contains("active Warden") || tactical.contains("active Hound"),
        "an enemy is active after the role contributions: {tactical}"
    );
    let fought = web_act(&app, TURN_ADVANCE_ENEMY, 0, "browser-tank").await;
    assert!(
        fought.contains("Tactical Arena") && fought.contains("event "),
        "the explicit enemy turn re-renders committed combat: {fought}"
    );

    let (status, before_verify) = web_get(&app, "/verify", "browser-tank").await;
    assert_eq!(status, StatusCode::OK);
    let before_report: serde_json::Value = serde_json::from_str(&before_verify).unwrap();
    assert_eq!(before_report["verified"], true, "{before_verify}");
    let before_turns = before_report["turns"].as_u64().expect("turn count");
    assert!(
        before_turns >= 15,
        "formation + three ballots + fight are in the one move log: {before_verify}"
    );
    let (status, before_surface) = web_get(&app, "", "browser-tank").await;
    assert_eq!(status, StatusCode::OK);
    assert!(before_surface.contains("Tactical Arena"));

    // Simulated process restart: drop every route/state handle, then build a
    // fresh host and all three adapters over the same append-only move-log dir.
    drop(app);
    drop(catalog);
    let (restarted, restarted_catalog) = app_over(dir.clone());
    let (status, after_surface) = web_get(&restarted, "", "browser-tank").await;
    assert_eq!(status, StatusCode::OK, "resumed surface: {after_surface}");
    assert_eq!(
        after_surface, before_surface,
        "restart replay reproduces the exact viewer-specific tactical surface"
    );
    let (status, after_verify) = web_get(&restarted, "/verify", "browser-tank").await;
    assert_eq!(status, StatusCode::OK);
    let after_report: serde_json::Value = serde_json::from_str(&after_verify).unwrap();
    assert_eq!(after_report["verified"], true, "{after_verify}");
    assert_eq!(after_report["turns"].as_u64(), Some(before_turns));
    assert!(
        restarted_catalog.is_open(KEY, &SessionId::new(SESSION)),
        "the one cross-platform shared session is live after replay"
    );

    drop(restarted);
    drop(restarted_catalog);
    fs::remove_dir_all(dir).unwrap();
}
