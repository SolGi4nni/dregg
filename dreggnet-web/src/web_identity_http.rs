//! HTTP bootstrap for the catalog's asserted browser identity.
//!
//! A visitor token is only a durable, pseudonymous continuity label. It is not a
//! login, a signature, or a cryptographic identity: callers can still explicitly
//! assert any `?user=` / `dregg_user` value, exactly as before.

use std::fmt::Write as _;
use std::io::Read as _;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use axum::body::Body;
use axum::extract::Query;
use axum::http::{HeaderMap, HeaderValue, Request, header};
use axum::middleware::Next;
use axum::response::Response;

use crate::WebQuery;

const COOKIE_NAME: &str = "dregg_user";
const VISITOR_PREFIX: &str = "visitor-";
const VISITOR_MAX_AGE_SECS: u64 = 365 * 24 * 60 * 60;

/// Resolve an explicitly supplied query/cookie identity, preserving the
/// catalog's established `?user=`-before-cookie precedence.
fn explicit_web_user(headers: &HeaderMap, query: &WebQuery) -> Option<String> {
    if let Some(user) = query.user.as_ref().filter(|user| !user.is_empty()) {
        return Some(user.clone());
    }
    headers
        .get(header::COOKIE)
        .and_then(|value| value.to_str().ok())
        .and_then(|cookies| {
            cookies.split(';').find_map(|part| {
                part.trim()
                    .strip_prefix("dregg_user=")
                    .filter(|value| !value.is_empty())
                    .map(str::to_string)
            })
        })
}

/// The asserted web identity for handlers that may also be mounted without the
/// bootstrap middleware. A layered browser request always has a generated
/// visitor token by this point; an unlayered request retains the old `anon`
/// sentinel so authentication-sensitive wrappers can still refuse it.
pub(crate) fn web_user(headers: &HeaderMap, query: &WebQuery) -> String {
    explicit_web_user(headers, query).unwrap_or_else(|| "anon".to_string())
}

/// Give a cookie-less browser its own durable asserted visitor label before a
/// catalog/session handler resolves the actor. Explicit query and cookie
/// identities are left byte-for-byte untouched.
pub(crate) async fn bootstrap_visitor_identity(mut request: Request<Body>, next: Next) -> Response {
    // This middleware is layered across the catalog router for the ordinary
    // browser GET/form routes. Keep the independently verified signed seam out
    // of the asserted-cookie bootstrap even though it shares that router: its
    // actor comes only from the signed envelope and no visitor cookie should be
    // minted as a side effect of a malformed/forged request.
    if request.uri().path().ends_with("/act-signed") {
        return next.run(request).await;
    }

    let query = Query::<WebQuery>::try_from_uri(request.uri())
        .map(|query| query.0)
        .unwrap_or_default();
    if explicit_web_user(request.headers(), &query).is_some() {
        return next.run(request).await;
    }

    let visitor = new_visitor_label();
    let secure = request.uri().scheme_str() == Some("https")
        || request
            .headers()
            .get("x-forwarded-proto")
            .and_then(|value| value.to_str().ok())
            .is_some_and(|proto| proto.eq_ignore_ascii_case("https"));
    inject_request_cookie(request.headers_mut(), &visitor);
    let mut response = next.run(request).await;
    let secure_attribute = if secure { "; Secure" } else { "" };
    response.headers_mut().append(
        header::SET_COOKIE,
        HeaderValue::from_str(&format!(
            "{COOKIE_NAME}={visitor}; Path=/; Max-Age={VISITOR_MAX_AGE_SECS}; HttpOnly; SameSite=Lax{secure_attribute}"
        ))
        .expect("the generated visitor cookie contains only header-safe ASCII"),
    );
    // Never let a shared cache replay one visitor's Set-Cookie response to
    // another browser. Session pages are personalized after this bootstrap.
    response.headers_mut().insert(
        header::CACHE_CONTROL,
        HeaderValue::from_static("private, no-store"),
    );
    response
}

fn inject_request_cookie(headers: &mut HeaderMap, visitor: &str) {
    let value = match headers.get(header::COOKIE).and_then(|v| v.to_str().ok()) {
        Some(existing) if !existing.is_empty() => {
            format!("{existing}; {COOKIE_NAME}={visitor}")
        }
        _ => format!("{COOKIE_NAME}={visitor}"),
    };
    headers.insert(
        header::COOKIE,
        HeaderValue::from_str(&value).expect("the generated visitor cookie is header-safe"),
    );
}

fn new_visitor_label() -> String {
    let mut bytes = [0_u8; 16];
    fill_visitor_bytes(&mut bytes);
    let mut label = String::with_capacity(VISITOR_PREFIX.len() + bytes.len() * 2);
    label.push_str(VISITOR_PREFIX);
    for byte in bytes {
        write!(&mut label, "{byte:02x}").expect("writing to a String cannot fail");
    }
    label
}

#[cfg(unix)]
fn fill_visitor_bytes(bytes: &mut [u8; 16]) {
    if std::fs::File::open("/dev/urandom")
        .and_then(|mut random| random.read_exact(bytes))
        .is_ok()
    {
        return;
    }
    fill_fallback_bytes(bytes);
}

#[cfg(not(unix))]
fn fill_visitor_bytes(bytes: &mut [u8; 16]) {
    fill_fallback_bytes(bytes);
}

/// Last-resort collision avoidance for an environment without an OS random
/// device. This is deliberately not represented as authentication entropy: the
/// resulting cookie is an asserted pseudonym either way.
fn fill_fallback_bytes(bytes: &mut [u8; 16]) {
    static NEXT: AtomicU64 = AtomicU64::new(0);

    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let sequence = NEXT.fetch_add(1, Ordering::Relaxed);
    let mut input = Vec::with_capacity(32);
    input.extend_from_slice(&now.to_le_bytes());
    input.extend_from_slice(&u64::from(std::process::id()).to_le_bytes());
    input.extend_from_slice(&sequence.to_le_bytes());
    bytes.copy_from_slice(&blake3::hash(&input).as_bytes()[..16]);
}
