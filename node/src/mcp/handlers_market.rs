//! `mcp::handlers_market` — the ENCRYPTED CALL AUCTION as MCP tools.
//!
//! These four tools are the same surface as
//! [`crate::dark_clearing_service`]'s HTTP routes, over the node's established MCP registration
//! idiom. They add no mechanism: every one of them calls
//! [`crate::dark_clearing_service::NodeDarkClearing`] and returns exactly what it returns.
//!
//! **No tool here can return an order.** The submit tool takes an opaque base64 envelope the
//! trader built and signed in its own process and returns a receipt of digests; the read tools
//! return `(p*, V*)` and digests. Nothing else crosses.
//!
//! Read `dark_clearing_service`'s module header before quoting the word "dark" at anyone: every
//! custodian and MPC party runs in THIS process, so the no-single-viewer property does not
//! survive co-location, and the disclosure string attached to every result says so.

use super::*;

use crate::dark_clearing_service::{
    CLEARING_DISCLOSURE, CLEARING_FAMILY, ClearingRefusal, ClearingRefusalWire, FAMILY_ORDERS,
    MAX_ORDER_ENVELOPE_BYTES,
};

/// Render a refusal the same way the HTTP surface does: a self-describing structured error whose
/// `dependency` flag says whether this was a fail-closed dependency refusal.
fn refusal_result(refusal: &ClearingRefusal) -> McpToolResult {
    let wire = ClearingRefusalWire::from(refusal);
    let hint = if wire.dependency {
        format!(
            "the '{}' dependency is unavailable — this is a fail-closed refusal, not a client \
             error; there is no degraded or plaintext path",
            wire.refused
        )
    } else {
        format!("refused: {}", wire.refused)
    };
    McpToolResult {
        content: vec![McpContent {
            content_type: "text",
            text: format!("{}\n  → {hint}", wire.detail),
        }],
        structured_content: Some(serde_json::to_value(&wire).unwrap_or_default()),
        is_error: Some(true),
    }
}

fn session_arg(params: &Value) -> Result<[u8; 32], McpToolResult> {
    let session = params
        .get("session")
        .and_then(|v| v.as_str())
        .ok_or_else(|| McpToolResult::error("missing required parameter: session"))?;
    hex_decode(session).map_err(|_| {
        McpToolResult::error("invalid session (expected 64 hex chars of the session nonce)")
    })
}

/// Open a clearing session: run the real Shamir BFV DKG and pin the ordered trader roster.
pub(super) async fn tool_dark_clearing_open(params: &Value, state: &NodeState) -> McpToolResult {
    let traders = match params.get("traders").and_then(|v| v.as_array()) {
        Some(t) => t,
        None => return McpToolResult::error("missing required parameter: traders (array of hex)"),
    };
    let mut roster = Vec::with_capacity(traders.len());
    for (index, entry) in traders.iter().enumerate() {
        let hex = match entry.as_str() {
            Some(h) => h,
            None => {
                return McpToolResult::error(format!("traders[{index}] must be a hex string"));
            }
        };
        match hex_decode(hex) {
            Ok(key) => roster.push(key),
            Err(_) => {
                return McpToolResult::error(format!(
                    "traders[{index}] is not 64 hex chars of an Ed25519 verifying key"
                ));
            }
        }
    }

    let mut guard = state.dark_clearing().write_owned().await;
    let opened = match tokio::task::spawn_blocking(move || guard.open_session(roster)).await {
        Ok(result) => result,
        Err(e) => return McpToolResult::error(format!("session task failed: {e}")),
    };
    match opened {
        Ok((session, receipt)) => McpToolResult::json(&serde_json::json!({
            "session": session,
            "receipt": receipt,
        })),
        Err(refusal) => refusal_result(&refusal),
    }
}

/// Submit one trader-encrypted, trader-signed order envelope (base64 of the exact
/// `SignedOrderSubmission` wire bytes). Returns a receipt; returns no order field.
pub(super) async fn tool_dark_clearing_submit(params: &Value, state: &NodeState) -> McpToolResult {
    let session = match session_arg(params) {
        Ok(s) => s,
        Err(e) => return e,
    };
    let envelope_b64 = match params.get("envelope_b64").and_then(|v| v.as_str()) {
        Some(e) => e,
        None => {
            return McpToolResult::error(
                "missing required parameter: envelope_b64 (base64 of the signed encrypted order \
                 envelope, built in YOUR process — this node never accepts a plaintext order)",
            );
        }
    };
    use base64::Engine as _;
    let envelope = match base64::engine::general_purpose::STANDARD.decode(envelope_b64) {
        Ok(bytes) => bytes,
        Err(e) => return McpToolResult::error(format!("envelope_b64 is not valid base64: {e}")),
    };
    if envelope.len() > MAX_ORDER_ENVELOPE_BYTES {
        return McpToolResult::error(format!(
            "the encrypted order envelope exceeds the {MAX_ORDER_ENVELOPE_BYTES}-byte bound"
        ));
    }

    let clearing = state.dark_clearing();
    let mut guard = clearing.write().await;
    match guard.submit_order(&session, &envelope) {
        Ok(receipt) => {
            let accepted = receipt.accepted_orders;
            McpToolResult::json(&serde_json::json!({
                "receipt": receipt,
                "accepted_orders": accepted,
                "required_orders": FAMILY_ORDERS,
                "family": CLEARING_FAMILY,
                "disclosure": CLEARING_DISCLOSURE,
            }))
        }
        Err(refusal) => refusal_result(&refusal),
    }
}

/// Clear the book: fold, open only the masked curves under the live custodian quorum, run the MPC
/// crossing, and issue a quorum-co-signed attested receipt. Reveals `(p*, V*)` and nothing else.
pub(super) async fn tool_dark_clearing_clear(params: &Value, state: &NodeState) -> McpToolResult {
    let session = match session_arg(params) {
        Ok(s) => s,
        Err(e) => return e,
    };
    let mut guard = state.dark_clearing().write_owned().await;
    let cleared = match tokio::task::spawn_blocking(move || guard.clear(&session)).await {
        Ok(result) => result,
        Err(e) => return McpToolResult::error(format!("clear task failed: {e}")),
    };
    match cleared {
        Ok((result, receipt)) => McpToolResult::json(&serde_json::json!({
            "result": result,
            "receipt": receipt,
        })),
        Err(refusal) => refusal_result(&refusal),
    }
}

/// Read a cleared result. `(p*, V*)` plus digests; nothing else exists to read.
pub(super) async fn tool_dark_clearing_result(params: &Value, state: &NodeState) -> McpToolResult {
    let session = match session_arg(params) {
        Ok(s) => s,
        Err(e) => return e,
    };
    let clearing = state.dark_clearing();
    let guard = clearing.read().await;
    match guard.cleared(&session) {
        Ok(result) => McpToolResult::json(&serde_json::to_value(&result).unwrap_or_default()),
        Err(refusal) => refusal_result(&refusal),
    }
}
