//! Client for the pyana devnet API.

use serde::{Deserialize, Serialize};

/// Client for communicating with the pyana devnet.
#[derive(Clone)]
pub struct DevnetClient {
    base_url: String,
    client: reqwest::Client,
}

/// An event from the devnet activity stream.
#[derive(Clone, Debug, Deserialize)]
pub struct RecentEvent {
    pub event_type: String,
    pub summary: String,
    pub timestamp: String,
    pub cell_id: Option<String>,
    pub tx_hash: Option<String>,
}

/// Response from the events endpoint.
#[derive(Clone, Debug, Deserialize)]
pub struct EventsResponse {
    pub block_height: u64,
    pub events: Vec<RecentEvent>,
}

impl DevnetClient {
    /// Create a new devnet client.
    pub fn new(base_url: &str) -> Self {
        Self {
            base_url: base_url.to_string(),
            client: reqwest::Client::new(),
        }
    }

    /// Get events since a given block height.
    pub async fn get_events_since(
        &self,
        since_height: u64,
    ) -> Result<EventsResponse, reqwest::Error> {
        let url = format!("{}/api/events?since={}", self.base_url, since_height);
        let resp = self.client.get(&url).send().await?.json().await?;
        Ok(resp)
    }
}
