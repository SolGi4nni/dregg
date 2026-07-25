//! Cookie-less catalog visitors receive distinct, durable asserted pseudonyms.
//! This is browser continuity, not authentication: explicit query/cookie actors
//! remain supported and retain their existing precedence.

use std::sync::Arc;

use axum::body::{Body, to_bytes};
use axum::http::{Request, StatusCode, header};
use dreggnet_web::{CatalogState, catalog_router};
use tower::ServiceExt as _;

mod common;

fn app() -> axum::Router {
    common::guard(catalog_router(Arc::new(CatalogState::new())))
}

async fn send(
    app: &axum::Router,
    request: Request<Body>,
) -> (StatusCode, Option<String>, Option<String>, String) {
    let response = app
        .clone()
        .oneshot(request)
        .await
        .expect("request succeeds");
    let status = response.status();
    let set_cookie = response
        .headers()
        .get(header::SET_COOKIE)
        .and_then(|value| value.to_str().ok())
        .map(str::to_string);
    let cache_control = response
        .headers()
        .get(header::CACHE_CONTROL)
        .and_then(|value| value.to_str().ok())
        .map(str::to_string);
    let body = String::from_utf8(
        to_bytes(response.into_body(), usize::MAX)
            .await
            .expect("body bytes")
            .to_vec(),
    )
    .expect("utf-8 response");
    (status, set_cookie, cache_control, body)
}

fn cookie_pair(set_cookie: &str) -> &str {
    set_cookie
        .split(';')
        .next()
        .expect("Set-Cookie starts with its cookie pair")
}

fn get(uri: &str, cookie: Option<&str>) -> Request<Body> {
    let mut request = Request::builder().uri(uri);
    if let Some(cookie) = cookie {
        request = request.header(header::COOKIE, cookie);
    }
    request.body(Body::empty()).expect("GET request")
}

/// A `{turn, arg}` POST carrying the route authority the play surface stamped into its own form.
/// `tug` is a SPINED game key, so a bare `turn=&arg=` is `409 invalid game reference` and the
/// "two visitors claim the two seats" property below would never have been exercised.
async fn act(app: &axum::Router, uri: &str, cookie: &str, turn: &str, arg: i64) -> Request<Body> {
    let body = common::act_body(app, uri, turn, arg, Some(cookie)).await;
    Request::builder()
        .method("POST")
        .uri(uri)
        .header(header::CONTENT_TYPE, "application/x-www-form-urlencoded")
        .header(header::COOKIE, cookie)
        .body(Body::from(body))
        .expect("POST request")
}

#[tokio::test]
async fn signed_route_is_not_wrapped_in_the_asserted_visitor_bootstrap() {
    let app = app();
    let request = Request::builder()
        .method("POST")
        .uri("/offerings/tug/session/signed-seam/act-signed")
        .header(header::CONTENT_TYPE, "application/json")
        .body(Body::from("{}"))
        .expect("signed request");

    let (status, set_cookie, _, _) = send(&app, request).await;
    assert_eq!(status, StatusCode::BAD_REQUEST);
    assert!(
        set_cookie.is_none(),
        "the independently verified signed seam must not mint an asserted visitor cookie"
    );
}

#[cfg(feature = "hosted-binary-operations")]
#[tokio::test]
async fn composed_private_operation_router_keeps_anonymous_uploads_unattributed() {
    use dreggnet_web::fhegg_operation;

    let catalog = Arc::new(CatalogState::new());
    let app = catalog_router(Arc::clone(&catalog)).merge(fhegg_operation::router(catalog));
    let request = Request::builder()
        .method("POST")
        .uri("/offerings/private-raid/session/not-open/operations/assign-private-raid")
        .header(header::CONTENT_TYPE, "application/octet-stream")
        .body(Body::empty())
        .expect("anonymous upload request");

    let (status, set_cookie, _, body) = send(&app, request).await;
    assert_eq!(status, StatusCode::UNAUTHORIZED, "{body}");
    assert!(
        set_cookie.is_none(),
        "merging the catalog must not extend asserted-cookie bootstrap onto private uploads"
    );
}

#[tokio::test]
async fn two_cookie_less_browsers_get_distinct_durable_actors_and_can_take_both_seats() {
    let app = app();
    let base = "/offerings/tug/session/visitor-bootstrap";

    let (status_a, set_cookie_a, cache_a, _) = send(&app, get(base, None)).await;
    let (status_b, set_cookie_b, _, _) = send(&app, get(base, None)).await;
    assert_eq!(status_a, StatusCode::OK);
    assert_eq!(status_b, StatusCode::OK);

    let set_cookie_a = set_cookie_a.expect("first browser receives a visitor cookie");
    let set_cookie_b = set_cookie_b.expect("second browser receives a visitor cookie");
    let cookie_a = cookie_pair(&set_cookie_a);
    let cookie_b = cookie_pair(&set_cookie_b);
    assert!(cookie_a.starts_with("dregg_user=visitor-"));
    assert!(cookie_b.starts_with("dregg_user=visitor-"));
    assert_ne!(cookie_a, cookie_b, "independent browsers must not collapse");
    assert_eq!(cache_a.as_deref(), Some("private, no-store"));
    for attribute in ["Path=/", "Max-Age=31536000", "HttpOnly", "SameSite=Lax"] {
        assert!(
            set_cookie_a.contains(attribute),
            "missing {attribute}: {set_cookie_a}"
        );
    }

    // Reusing the returned cookie is stable: it is accepted without rotation.
    let (_, rotated, _, _) = send(&app, get(base, Some(cookie_a))).await;
    assert!(
        rotated.is_none(),
        "an existing visitor cookie must remain stable"
    );

    // Multiway-Tug assigns the first two distinct actors seats A and B. The old
    // literal `anon` fallback made the second browser the same actor and this
    // second scheduled play was refused.
    let (_, _, _, first) = send(
        &app,
        act(&app, &format!("{base}/act"), cookie_a, "comp", 3).await,
    )
    .await;
    assert!(
        first.contains("Turn committed"),
        "first visitor claims seat A: {first}"
    );
    let (_, _, _, second) = send(
        &app,
        act(&app, &format!("{base}/act"), cookie_b, "comp", 3).await,
    )
    .await;
    assert!(
        second.contains("Turn committed"),
        "second visitor claims seat B: {second}"
    );
}

#[tokio::test]
async fn explicit_query_and_cookie_identities_are_not_replaced() {
    let app = app();
    let base = "/offerings/tug/session/explicit-identities";

    let (_, query_cookie, _, _) = send(&app, get(&format!("{base}?user=query-player"), None)).await;
    assert!(
        query_cookie.is_none(),
        "an explicit query actor is not overwritten"
    );

    let (_, cookie_cookie, _, _) = send(&app, get(base, Some("dregg_user=cookie-player"))).await;
    assert!(
        cookie_cookie.is_none(),
        "an explicit cookie actor is not overwritten"
    );

    // Query retains precedence over cookie: these are two distinct players and
    // therefore claim the two alternating seats successfully.
    let (_, _, _, first) = send(
        &app,
        act(
            &app,
            &format!("{base}/act?user=query-player"),
            "dregg_user=cookie-player",
            "comp",
            3,
        )
        .await,
    )
    .await;
    assert!(
        first.contains("Turn committed"),
        "query actor claims seat A: {first}"
    );
    let (_, _, _, second) = send(
        &app,
        act(
            &app,
            &format!("{base}/act"),
            "dregg_user=cookie-player",
            "comp",
            3,
        )
        .await,
    )
    .await;
    assert!(
        second.contains("Turn committed"),
        "cookie actor claims seat B: {second}"
    );
}
