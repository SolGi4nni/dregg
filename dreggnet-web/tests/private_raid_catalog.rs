#![cfg(feature = "hosted-binary-operations")]

//! The shared catalog's dynamic private-raid lobby reaches the ordinary web
//! renderer and graduates into the generic opaque-proof upload affordance.

use std::sync::Arc;

use axum::body::Body;
use axum::http::{Request, StatusCode, header};
use dreggnet_surfaces::private_raid::{ASSIGN_OPERATION, KEY, TURN_JOIN_RAID};
use dreggnet_web::{CatalogState, catalog_router};
use tower::ServiceExt;

mod common;

async fn response(
    app: &axum::Router,
    request: Request<Body>,
) -> (StatusCode, Option<String>, String) {
    let response = app.clone().oneshot(request).await.unwrap();
    let status = response.status();
    let set_cookie = response
        .headers()
        .get(header::SET_COOKIE)
        .and_then(|value| value.to_str().ok())
        .map(str::to_string);
    let body = axum::body::to_bytes(response.into_body(), usize::MAX)
        .await
        .unwrap();
    (
        status,
        set_cookie,
        String::from_utf8(body.to_vec()).unwrap(),
    )
}

#[tokio::test]
async fn four_pseudonymous_browsers_muster_then_the_proof_upload_becomes_discoverable() {
    let app = common::guard(catalog_router(Arc::new(CatalogState::new())));
    let base = format!("/offerings/{KEY}/session/web-raid");
    let (status, first_cookie, opening) = response(
        &app,
        Request::builder().uri(&base).body(Body::empty()).unwrap(),
    )
    .await;
    assert_eq!(status, StatusCode::OK);
    assert!(opening.contains("0 / 4 PUBLIC SEATS"));
    assert!(opening.contains(TURN_JOIN_RAID));
    assert!(!opening.contains(ASSIGN_OPERATION));

    let mut cookies = vec![first_cookie.expect("the first browser receives a visitor cookie")];
    for _ in 1..4 {
        let (status, cookie, _) = response(
            &app,
            Request::builder().uri(&base).body(Body::empty()).unwrap(),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        cookies.push(cookie.expect("each independent browser receives a visitor cookie"));
    }
    let cookies = cookies
        .into_iter()
        .map(|set_cookie| {
            set_cookie
                .split(';')
                .next()
                .expect("Set-Cookie starts with its cookie pair")
                .to_string()
        })
        .collect::<Vec<_>>();
    assert!(
        cookies
            .iter()
            .all(|cookie| cookie.starts_with("dregg_user=visitor-"))
    );
    let mut distinct = cookies.clone();
    distinct.sort();
    distinct.dedup();
    assert_eq!(distinct.len(), 4, "four browsers need four raid actors");

    let mut last = String::new();
    for (index, cookie) in cookies.iter().enumerate() {
        // `private-raid` is a SPINED game key: without the route authority the surface stamped
        // into its own form the join is `409 invalid game reference` and no visitor ever joins.
        let act_uri = format!("{base}/act");
        let request = Request::builder()
            .method("POST")
            .uri(&act_uri)
            .header("content-type", "application/x-www-form-urlencoded")
            .header(header::COOKIE, cookie.as_str())
            .body(Body::from(
                common::act_body(&app, &act_uri, TURN_JOIN_RAID, 0, Some(cookie.as_str())).await,
            ))
            .unwrap();
        let (status, rotated, body) = response(&app, request).await;
        assert_eq!(status, StatusCode::OK);
        assert!(rotated.is_none(), "an existing visitor cookie stays stable");
        assert!(
            body.contains("Turn committed"),
            "visitor {index} joins: {body}"
        );
        last = body;
    }
    assert!(last.contains("AWAITING HIDING PROOF"));
    assert!(last.contains(ASSIGN_OPERATION));
    assert!(last.contains("type=\"file\""));
    assert!(last.contains(&format!(
        "/offerings/{KEY}/session/web-raid/operations/{ASSIGN_OPERATION}"
    )));
}
