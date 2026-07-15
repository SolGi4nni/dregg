//! An HTTP gateway adapter — the wire that turns a raw HTTP request (method, target,
//! headers, body) into the ONE value-level publish turn ([`SitePublishHandler::respond`]).
//!
//! This crate deliberately holds no HTTP-server types in its core (so the turn stays
//! server-agnostic and re-drivable from a CLI). This module is the thin, testable
//! adaptation layer a concrete server (hyper/axum/…) plugs into: it parses the method,
//! pulls the `dga1_` credential out of the `Authorization` / `X-Dregg-Credential`
//! header via [`bearer_credential`], and calls `respond`. The concrete network loop —
//! the socket, TLS, and body streaming with a max-bytes cap wired to
//! [`PublishLimits`](crate::limits::PublishLimits) — is the caller's, but the request
//! → response mapping is here and tested.

use crate::publish::{HttpMethod, SitePublishHandler, WebResponse, bearer_credential};

/// A value-level HTTP request a gateway hands to the publish turn: a method token,
/// the request target (path), headers (case-insensitively matched), and the body.
#[derive(Debug, Clone, Default)]
pub struct GatewayRequest {
    /// The HTTP method token (e.g. `"POST"`, `"DELETE"`).
    pub method: String,
    /// The request target (path + optional query).
    pub target: String,
    /// The request headers as `(name, value)` pairs (names matched case-insensitively).
    pub headers: Vec<(String, String)>,
    /// The request body (the built bundle for a publish; empty for a delete).
    pub body: Vec<u8>,
}

impl GatewayRequest {
    /// A `POST` publish request for `target` carrying `credential` (as a bearer token)
    /// and `body`.
    pub fn post_publish(
        target: impl Into<String>,
        credential: &str,
        body: Vec<u8>,
    ) -> GatewayRequest {
        GatewayRequest {
            method: "POST".to_string(),
            target: target.into(),
            headers: vec![("Authorization".to_string(), format!("Bearer {credential}"))],
            body,
        }
    }

    /// A `DELETE` unpublish request for `target` carrying `credential`.
    pub fn delete_publish(target: impl Into<String>, credential: &str) -> GatewayRequest {
        GatewayRequest {
            method: "DELETE".to_string(),
            target: target.into(),
            headers: vec![("Authorization".to_string(), format!("Bearer {credential}"))],
            body: Vec::new(),
        }
    }

    /// Look up a header value by case-insensitive name.
    pub fn header(&self, name: &str) -> Option<&str> {
        self.headers
            .iter()
            .find(|(k, _)| k.eq_ignore_ascii_case(name))
            .map(|(_, v)| v.as_str())
    }
}

/// Drive one gateway request through the publish turn at clock `now`. Extracts the
/// credential from the request headers and calls [`SitePublishHandler::respond`] — the
/// SAME turn the CLI drives.
pub fn handle(handler: &SitePublishHandler, req: &GatewayRequest, now: u64) -> WebResponse {
    let credential = bearer_credential(|name| req.header(name));
    handler.respond(
        HttpMethod::parse(&req.method),
        &req.target,
        credential.as_deref(),
        &req.body,
        now,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn header_lookup_is_case_insensitive() {
        let req = GatewayRequest {
            method: "POST".to_string(),
            target: "/v1/sites/blog/publish".to_string(),
            headers: vec![("AUTHORIZATION".to_string(), "Bearer dga1_x".to_string())],
            body: Vec::new(),
        };
        assert_eq!(req.header("authorization"), Some("Bearer dga1_x"));
        assert_eq!(
            bearer_credential(|n| req.header(n)).as_deref(),
            Some("dga1_x")
        );
    }
}
