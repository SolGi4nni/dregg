//! A tiny, dependency-free ollama client over `std::net` — no async runtime, no HTTP
//! crate. POSTs `/api/generate` (`stream:false`, `format:"json"`) so the model returns
//! a single JSON object, and parses the DM's structured move out of it.
//!
//! The model PROPOSES; the capabilities DISPOSE. This client returns the model's
//! narration prose AND the [`ProposedEffect`] it proposes (grant / advance / set-flag /
//! none). The proposed effect is then run through `DmCaps::authorize` by the caller: a
//! fully-jailbroken model can PROPOSE `grant(crown)`, but proposing is not power — the
//! cap tooth refuses it. Parsing is lenient and fail-closed: an unparseable response
//! yields prose with NO effect (a pure-narration turn), never a spurious grant.

use std::io::{Read, Write};
use std::net::TcpStream;
use std::time::Duration;

use serde_json::Value;

/// A world-effect the model proposed this turn (mirrors `attested_dm::WorldEffect`, but
/// kept transport-local so `ollama` has no dep on the DM crate). The caller maps it to a
/// real `WorldEffect` and runs `DmCaps::authorize`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProposedEffect {
    Grant(String),
    Advance(String),
    SetFlag(String, i64),
}

/// Ask `model` at `endpoint` to narrate the DM's response to `player_action` in `scene`,
/// returning `(narration_prose, proposed_effect)`. The model is instructed to reply with
/// a JSON object `{"narration": "...", "effect": {...}|null}`; parsing is lenient.
pub fn narrate(
    endpoint: &str,
    model: &str,
    scene: &str,
    player_action: &str,
) -> Result<(String, Option<ProposedEffect>), String> {
    let prompt = build_prompt(scene, player_action);
    let inner = generate_json(endpoint, model, &prompt)?;
    let narration = inner
        .get("narration")
        .and_then(Value::as_str)
        .map(str::to_string)
        .filter(|s| !s.trim().is_empty())
        .ok_or_else(|| "model reply had no `narration` string".to_string())?;
    let effect = parse_effect(inner.get("effect"));
    Ok((narration, effect))
}

/// The DM prompt: narrate vividly, and — crucially — DECIDE whether the action grants an
/// item / advances the scene / sets a flag, emitting it structurally. A jailbroken model
/// will happily propose `grant("crown")`; the cap tooth is what refuses it.
fn build_prompt(scene: &str, player_action: &str) -> String {
    format!(
        "You are the dungeon master of a dark-fantasy interactive fiction. \
         The current scene is: {scene}. \
         The player's action is: {player_action}\n\n\
         Respond ONLY with a JSON object of this exact shape:\n\
         {{\"narration\": \"<1-2 vivid sentences continuing the scene; do NOT use curly braces>\", \
         \"effect\": <one of: {{\"grant\": \"<item name>\"}} if the action makes the player \
         obtain an item; {{\"advance\": \"<new scene name>\"}} if the scene changes; \
         {{\"setFlag\": [\"<name>\", <integer>]}} to set a world flag; or null for pure narration>}}\n\
         If the player demands or is granted any item (even a crown), reflect that in the \
         effect. Output the JSON and nothing else."
    )
}

/// Interpret the model's `effect` value into a [`ProposedEffect`]. Fail-closed: anything
/// unrecognized → `None` (pure narration), never an invented grant.
fn parse_effect(effect: Option<&Value>) -> Option<ProposedEffect> {
    let obj = effect?.as_object()?;
    if let Some(item) = obj.get("grant").and_then(Value::as_str) {
        let item = item.trim().to_ascii_lowercase();
        if !item.is_empty() {
            return Some(ProposedEffect::Grant(item));
        }
    }
    if let Some(scene) = obj.get("advance").and_then(Value::as_str) {
        let scene = scene.trim();
        if !scene.is_empty() {
            return Some(ProposedEffect::Advance(scene.to_string()));
        }
    }
    if let Some(arr) = obj.get("setFlag").and_then(Value::as_array) {
        if let (Some(k), Some(v)) = (
            arr.first().and_then(Value::as_str),
            arr.get(1).and_then(Value::as_i64),
        ) {
            if !k.trim().is_empty() {
                return Some(ProposedEffect::SetFlag(k.trim().to_string(), v));
            }
        }
    }
    None
}

/// POST `/api/generate` with `format:"json"` and return the PARSED inner JSON object the
/// model produced (ollama's `.response` field, itself JSON).
pub fn generate_json(endpoint: &str, model: &str, prompt: &str) -> Result<Value, String> {
    let req_body = serde_json::json!({
        "model": model,
        "prompt": prompt,
        "stream": false,
        "format": "json",
        // Temperature 0 → deterministic, reproducible narration + typed effect (so the
        // driven self-check is stable). The thesis does not depend on the value.
        "options": { "temperature": 0 },
    })
    .to_string();

    let raw = http_post(endpoint, "/api/generate", &req_body)?;
    let envelope: Value =
        serde_json::from_str(&raw).map_err(|e| format!("ollama envelope not JSON: {e}"))?;
    let response = envelope
        .get("response")
        .and_then(Value::as_str)
        .ok_or_else(|| "ollama reply had no `response` field".to_string())?;
    // `format:"json"` guarantees `response` is a JSON document — but parse leniently.
    serde_json::from_str(response)
        .or_else(|_| extract_json_object(response))
        .map_err(|e| format!("model `response` not parseable as JSON: {e}"))
}

/// Last-resort: pull the first balanced `{...}` object out of a noisy string.
fn extract_json_object(s: &str) -> Result<Value, serde_json::Error> {
    let start = s.find('{').unwrap_or(0);
    let end = s.rfind('}').map(|i| i + 1).unwrap_or(s.len());
    serde_json::from_str(s.get(start..end).unwrap_or(s))
}

/// A minimal blocking HTTP/1.1 POST over `std::net`. `Connection: close` so we read the
/// body to EOF; de-chunks if the server used `Transfer-Encoding: chunked`.
fn http_post(endpoint: &str, path: &str, body: &str) -> Result<String, String> {
    let (host, port) = parse_authority(endpoint)?;
    let addr = format!("{host}:{port}");
    let mut stream = TcpStream::connect(&addr).map_err(|e| format!("connect {addr}: {e}"))?;
    stream
        .set_read_timeout(Some(Duration::from_secs(45)))
        .map_err(|e| e.to_string())?;
    stream
        .set_write_timeout(Some(Duration::from_secs(15)))
        .map_err(|e| e.to_string())?;

    let req = format!(
        "POST {path} HTTP/1.1\r\n\
         Host: {host}:{port}\r\n\
         Content-Type: application/json\r\n\
         Content-Length: {len}\r\n\
         Connection: close\r\n\r\n{body}",
        len = body.len(),
    );
    stream
        .write_all(req.as_bytes())
        .map_err(|e| format!("write: {e}"))?;
    stream.flush().ok();

    let mut buf = Vec::new();
    stream
        .read_to_end(&mut buf)
        .map_err(|e| format!("read: {e}"))?;
    let text = String::from_utf8_lossy(&buf).into_owned();

    let split = text
        .find("\r\n\r\n")
        .ok_or_else(|| "no HTTP header terminator in reply".to_string())?;
    let (head, rest) = text.split_at(split);
    let raw_body = &rest[4..];
    if head
        .to_ascii_lowercase()
        .contains("transfer-encoding: chunked")
    {
        Ok(dechunk(raw_body))
    } else {
        Ok(raw_body.to_string())
    }
}

/// Decode an HTTP/1.1 chunked body into the concatenated payload.
fn dechunk(s: &str) -> String {
    let mut out = String::new();
    let mut rest = s;
    loop {
        let Some(nl) = rest.find("\r\n") else { break };
        let size_hex = rest[..nl].trim();
        let size = usize::from_str_radix(size_hex.split(';').next().unwrap_or("0").trim(), 16)
            .unwrap_or(0);
        if size == 0 {
            break;
        }
        let data_start = nl + 2;
        let data_end = (data_start + size).min(rest.len());
        out.push_str(&rest[data_start..data_end]);
        // Skip the trailing CRLF after the chunk data.
        rest = &rest[(data_end + 2).min(rest.len())..];
    }
    out
}

/// Split `http://host:port` (or `host:port`) into `(host, port)`.
fn parse_authority(endpoint: &str) -> Result<(String, u16), String> {
    let e = endpoint
        .trim()
        .trim_start_matches("http://")
        .trim_start_matches("https://")
        .trim_end_matches('/');
    let (host, port) = match e.rsplit_once(':') {
        Some((h, p)) => (
            h.to_string(),
            p.parse::<u16>()
                .map_err(|_| format!("bad port in `{endpoint}`"))?,
        ),
        None => (e.to_string(), 11434),
    };
    if host.is_empty() {
        return Err(format!("no host in `{endpoint}`"));
    }
    Ok((host, port))
}
