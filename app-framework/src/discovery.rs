//! Nameservice auto-registration for dregg apps.
//!
//! `NameserviceClient` is an HTTP client that registers an app in the federation's
//! nameservice on startup and deregisters on clean shutdown. The nameservice
//! server endpoint is read from `DREGG_NAMESERVICE_URL` (default:
//! `http://127.0.0.1:9100`).
//!
//! This module provides the **client** contract. The nameservice app itself
//! is a separate dregg app that exposes the matching server endpoints
//! (`POST /register`, `DELETE /names/{name}`).
//!
//! # Usage
//!
//! ```ignore
//! use dregg_app_framework::discovery::{NameRegistration, NameserviceClient};
//!
//! let client = NameserviceClient::from_env();
//! client.register(&NameRegistration {
//!     name: "my-app".into(),
//!     tags: vec!["amm".into()],
//!     target_uri: "http://127.0.0.1:3001".into(),
//! }).await?;
//! ```

use serde::{Deserialize, Serialize};

/// A registration record for the nameservice.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NameRegistration {
    /// Human-readable name (e.g. "amm", "lending", "compute-exchange").
    pub name: String,
    /// Searchable tags (e.g. `["defi", "stablecoin"]`).
    pub tags: Vec<String>,
    /// The URI at which this app is reachable.
    /// May be a `dregg://` URI or an `http://` fallback.
    pub target_uri: String,
}

/// HTTP client for the dregg nameservice.
///
/// Cheap to clone — wraps an `Arc` internally.
#[derive(Clone, Debug)]
pub struct NameserviceClient {
    base_url: String,
    http: reqwest::Client,
}

/// Errors that can occur when communicating with the nameservice.
#[derive(Debug, thiserror::Error)]
pub enum DiscoveryError {
    /// An HTTP transport error (connection refused, timeout, etc.).
    #[error("nameservice request failed: {0}")]
    Http(#[from] reqwest::Error),
    /// The nameservice rejected the request (non-2xx response with a reason body).
    #[error("nameservice rejected: {0}")]
    Rejected(String),
}

impl NameserviceClient {
    /// Build a client pointed at the URL in `DREGG_NAMESERVICE_URL`, or the
    /// default `http://127.0.0.1:9100` if the variable is unset.
    pub fn from_env() -> Self {
        let base_url = std::env::var("DREGG_NAMESERVICE_URL")
            .unwrap_or_else(|_| "http://127.0.0.1:9100".into());
        Self::new(base_url)
    }

    /// Build a client pointed at `base_url`.
    pub fn new(base_url: impl Into<String>) -> Self {
        Self {
            base_url: base_url.into(),
            http: reqwest::Client::new(),
        }
    }

    /// Register an app. Calls `POST {base_url}/register` with JSON body.
    ///
    /// Returns `Ok(())` on 2xx. Any non-2xx status is mapped to
    /// [`DiscoveryError::Rejected`] with the response body as the reason.
    pub async fn register(&self, reg: &NameRegistration) -> Result<(), DiscoveryError> {
        let url = format!("{}/register", self.base_url);
        let resp = self.http.post(&url).json(reg).send().await?;
        if resp.status().is_success() {
            Ok(())
        } else {
            let body = resp.text().await.unwrap_or_default();
            Err(DiscoveryError::Rejected(body))
        }
    }

    /// Deregister an app by name. Calls `DELETE {base_url}/names/{name}`.
    ///
    /// Best-effort — callers should not fail hard if this errors on shutdown.
    pub async fn deregister(&self, name: &str) -> Result<(), DiscoveryError> {
        let url = format!("{}/names/{}", self.base_url, name);
        let resp = self.http.delete(&url).send().await?;
        if resp.status().is_success() {
            Ok(())
        } else {
            let body = resp.text().await.unwrap_or_default();
            Err(DiscoveryError::Rejected(body))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn name_registration_serde_round_trip() {
        let reg = NameRegistration {
            name: "my-service".into(),
            tags: vec!["defi".into(), "amm".into()],
            target_uri: "http://127.0.0.1:3001".into(),
        };

        let json = serde_json::to_string(&reg).unwrap();
        let decoded: NameRegistration = serde_json::from_str(&json).unwrap();

        assert_eq!(decoded.name, reg.name);
        assert_eq!(decoded.tags, reg.tags);
        assert_eq!(decoded.target_uri, reg.target_uri);
    }
}
