//! A CLI adapter — the OTHER driver of the ONE publish turn.
//!
//! Where [`crate::gateway`] adapts a network request into
//! [`SitePublishHandler::respond`], this adapts a command-line invocation into the
//! SAME turn: read a built bundle from a file (or bytes), present a credential, and
//! publish or unpublish. A CLI binary is a thin `main` over [`publish_bundle`] /
//! [`unpublish_site`]; the value-level logic (and its tests) live here so "one turn a
//! CLI and a gateway both drive" is a fact, not an aspiration.

use std::path::Path;

use crate::publish::{HttpMethod, SitePublishHandler, WebResponse};

/// Publish a bundle read from `bundle_path` (a serialized `SiteContent` JSON) to the
/// site `name`, presenting `credential`, at clock `now`. Drives the SAME
/// [`SitePublishHandler::respond`] turn a gateway does.
pub fn publish_bundle(
    handler: &SitePublishHandler,
    credential: &str,
    name: &str,
    bundle_path: &Path,
    now: u64,
) -> std::io::Result<WebResponse> {
    let body = std::fs::read(bundle_path)?;
    Ok(publish_bytes(handler, credential, name, &body, now))
}

/// Publish an in-memory bundle to the site `name` — the byte-level entry the CLI and
/// its tests share.
pub fn publish_bytes(
    handler: &SitePublishHandler,
    credential: &str,
    name: &str,
    body: &[u8],
    now: u64,
) -> WebResponse {
    handler.respond(
        HttpMethod::Post,
        &format!("/v1/sites/{name}/publish"),
        Some(credential),
        body,
        now,
    )
}

/// Unpublish the site `name`, presenting `credential`, at clock `now`.
pub fn unpublish_site(
    handler: &SitePublishHandler,
    credential: &str,
    name: &str,
    now: u64,
) -> WebResponse {
    handler.respond(
        HttpMethod::Delete,
        &format!("/v1/sites/{name}/publish"),
        Some(credential),
        &[],
        now,
    )
}
