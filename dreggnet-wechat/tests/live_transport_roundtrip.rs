//! **The DRIVEN live-transport round-trip** — proves the real outbound WeChat byte seam
//! ([`RawWeChatApi`] over an injected [`HttpPost`]) without a network or a live token:
//!
//! - **encode → wire → decode**: a rendered surface's [`CustomSendRequest`] is POSTed by
//!   `RawWeChatApi`; the recorded request body is EXACTLY the real `custom/send` JSON wire body
//!   (it decodes back to the same struct), and the URL is the real token-bearing `custom/send` URL;
//! - **envelope decode**: a scripted `{ "errcode": 0 }` is `Ok(())`, a non-zero errcode is the
//!   surfaced `Err`;
//! - **token fetch**: `fetch_access_token` GETs `cgi-bin/token` and decodes `{ access_token,
//!   expires_in }` (and the error envelope);
//! - **config fail-closed**: [`WeChatCredentials::from_lookup`] errors, naming the missing key,
//!   when a required env key is absent/empty;
//! - **connect → send end-to-end**: [`RawWeChatApi::connect`] fetches a token, then a send carries
//!   THAT fetched token in the `custom/send` URL.
//!
//! The only thing NOT exercised here is the live network edge (a real registered OA's
//! AppID/AppSecret + a public callback URL); everything up to the socket is driven.

use std::cell::RefCell;
use std::rc::Rc;

use dreggnet_offerings::dungeon::DungeonOffering;
use dreggnet_offerings::{Offering, SessionConfig};
use dreggnet_wechat::api::{CustomSendRequest, build_present_request, present_message};
use dreggnet_wechat::transport::{
    HttpPost, RawWeChatApi, Transport, WeChatCredentials, fetch_access_token,
};

/// What crossed the seam — POST (url, body) pairs and GET urls. Held behind an [`Rc`] so a test
/// keeps a handle to the recordings even after the [`StubHttp`] is moved into a [`RawWeChatApi`].
#[derive(Default)]
struct Recordings {
    posts: RefCell<Vec<(String, String)>>,
    gets: RefCell<Vec<String>>,
}

impl Recordings {
    fn last_post(&self) -> (String, String) {
        self.posts
            .borrow()
            .last()
            .cloned()
            .expect("a POST was made")
    }
    fn last_get(&self) -> String {
        self.gets.borrow().last().cloned().expect("a GET was made")
    }
}

/// A recording, scriptable [`HttpPost`] double — records every POST/GET into a shared
/// [`Recordings`] and answers with a canned body chosen by which method was called (POST = the
/// `custom/send` reply, GET = the token reply). No network; the whole `RawWeChatApi` byte path runs
/// against it.
#[derive(Clone)]
struct StubHttp {
    rec: Rc<Recordings>,
    post_reply: String,
    get_reply: String,
}

impl StubHttp {
    /// A stub scripting `post_reply` for `custom/send` and `get_reply` for `cgi-bin/token`; returns
    /// the stub and a handle to its recordings.
    fn new(post_reply: &str, get_reply: &str) -> (Self, Rc<Recordings>) {
        let rec = Rc::new(Recordings::default());
        let stub = StubHttp {
            rec: rec.clone(),
            post_reply: post_reply.to_string(),
            get_reply: get_reply.to_string(),
        };
        (stub, rec)
    }
}

impl HttpPost for StubHttp {
    fn post_json(&self, url: &str, body: &str) -> Result<String, String> {
        self.rec
            .posts
            .borrow_mut()
            .push((url.to_string(), body.to_string()));
        Ok(self.post_reply.clone())
    }
    fn get_json(&self, url: &str) -> Result<String, String> {
        self.rec.gets.borrow_mut().push(url.to_string());
        Ok(self.get_reply.clone())
    }
}

/// A real rendered `custom/send` request for the dungeon's opening surface (the encode side).
fn a_real_request() -> CustomSendRequest {
    let off = DungeonOffering::new();
    let s = off
        .open(SessionConfig::with_seed(3))
        .expect("the Keep opens");
    let message = present_message(&off.render(&s));
    build_present_request("oGZUI0egBJY1zhBYw2KaXT9abcd", &message)
}

/// send() through `RawWeChatApi`: the recorded body IS the wire body (round-trips to the same
/// struct), the URL is the real token-bearing `custom/send` URL, and `{errcode:0}` is `Ok`.
#[test]
fn send_encodes_the_real_wire_body_to_the_real_url_and_decodes_ok() {
    let req = a_real_request();
    let (stub, rec) = StubHttp::new(r#"{"errcode":0,"errmsg":"ok"}"#, "");
    let mut api = RawWeChatApi::new("TESTTOKEN", stub);

    api.send_message(&req).expect("errcode 0 → Ok(())");

    let (url, body) = rec.last_post();
    assert_eq!(
        url, "https://api.weixin.qq.com/cgi-bin/message/custom/send?access_token=TESTTOKEN",
        "the real token-bearing custom/send URL"
    );
    // encode → wire → decode: the recorded body decodes back to the SAME request.
    let decoded: CustomSendRequest =
        serde_json::from_str(&body).expect("the recorded body is the real wire JSON");
    assert_eq!(decoded, req, "encode → wire → decode round-trips exactly");
}

/// A non-zero errcode from `custom/send` is surfaced as an `Err` carrying the WeChat errmsg.
#[test]
fn send_surfaces_a_nonzero_errcode_as_error() {
    let req = a_real_request();
    let (stub, _rec) = StubHttp::new(
        r#"{"errcode":45015,"errmsg":"response out of time limit"}"#,
        "",
    );
    let mut api = RawWeChatApi::new("TESTTOKEN", stub);
    let err = api.send_message(&req).expect_err("non-zero errcode → Err");
    let msg = err.to_string();
    assert!(msg.contains("45015"), "errcode surfaced: {msg}");
    assert!(
        msg.contains("response out of time limit"),
        "errmsg surfaced: {msg}"
    );
}

/// `fetch_access_token` GETs `cgi-bin/token` and decodes `{ access_token, expires_in }`.
#[test]
fn token_fetch_decodes_access_token_and_expiry() {
    let (stub, rec) = StubHttp::new("", r#"{"access_token":"ACCESS_XYZ","expires_in":7200}"#);
    let creds = WeChatCredentials::new("wxAPPID", "SECRETVALUE");

    let token = fetch_access_token(&stub, "https://api.weixin.qq.com", &creds)
        .expect("a valid token response decodes");
    assert_eq!(token.token, "ACCESS_XYZ");
    assert_eq!(token.expires_in_secs, 7200);

    // The GET hit the real token endpoint with the client_credential grant + the AppID.
    let url = rec.last_get();
    assert!(url.contains("/cgi-bin/token"), "token endpoint: {url}");
    assert!(
        url.contains("grant_type=client_credential"),
        "client_credential grant: {url}"
    );
    assert!(url.contains("appid=wxAPPID"), "carries the AppID: {url}");
}

/// A token error envelope (bad AppID) is surfaced as an `Err`.
#[test]
fn token_fetch_surfaces_the_error_envelope() {
    let (stub, _rec) = StubHttp::new("", r#"{"errcode":40013,"errmsg":"invalid appid"}"#);
    let creds = WeChatCredentials::new("wxBAD", "SECRET");
    let err = fetch_access_token(&stub, "https://api.weixin.qq.com", &creds)
        .expect_err("an error envelope → Err");
    let msg = err.to_string();
    assert!(msg.contains("40013"), "errcode surfaced: {msg}");
    assert!(msg.contains("invalid appid"), "errmsg surfaced: {msg}");
}

/// Config is FAIL-CLOSED: an absent/empty required key errors, naming the key — never a silent
/// empty credential.
#[test]
fn credentials_fail_closed_on_absent_config() {
    // Nothing set → error names the FIRST missing key (AppID).
    let err = WeChatCredentials::from_lookup(|_| None).expect_err("absent config → Err");
    assert!(
        err.to_string().contains(WeChatCredentials::APP_ID_KEY),
        "names the missing AppID key: {err}"
    );

    // AppID present, AppSecret empty → error names the AppSecret key (empty is not present).
    let err = WeChatCredentials::from_lookup(|k| {
        if k == WeChatCredentials::APP_ID_KEY {
            Some("wxAPPID".to_string())
        } else {
            Some(String::new())
        }
    })
    .expect_err("empty AppSecret → Err");
    assert!(
        err.to_string().contains(WeChatCredentials::APP_SECRET_KEY),
        "names the missing AppSecret key: {err}"
    );

    // Both present → Ok, carrying the AppID.
    let creds = WeChatCredentials::from_lookup(|k| {
        Some(
            match k {
                k if k == WeChatCredentials::APP_ID_KEY => "wxAPPID",
                _ => "SECRETVALUE",
            }
            .to_string(),
        )
    })
    .expect("both keys present → Ok");
    assert_eq!(creds.app_id, "wxAPPID");
}

/// End-to-end: `connect` fetches a token (the GET), then a send carries THAT fetched token in the
/// `custom/send` URL (the POST) — the whole token→send flow driven, no network.
#[test]
fn connect_then_send_carries_the_fetched_token() {
    let (stub, rec) = StubHttp::new(
        r#"{"errcode":0,"errmsg":"ok"}"#,
        r#"{"access_token":"FETCHED_TOKEN_123","expires_in":7200}"#,
    );
    let creds = WeChatCredentials::new("wxAPPID", "SECRETVALUE");

    let mut api = RawWeChatApi::connect("https://api.weixin.qq.com", &creds, stub)
        .expect("connect fetches a token and builds a live client");
    api.send_message(&a_real_request())
        .expect("send over the connected client");

    // The GET was the token fetch…
    assert!(
        rec.last_get().contains("/cgi-bin/token"),
        "connect fetched the token"
    );
    // …and the subsequent POST carried exactly the fetched token.
    let (post_url, _body) = rec.last_post();
    assert_eq!(
        post_url,
        "https://api.weixin.qq.com/cgi-bin/message/custom/send?access_token=FETCHED_TOKEN_123",
        "the send carries the token connect fetched"
    );
}
