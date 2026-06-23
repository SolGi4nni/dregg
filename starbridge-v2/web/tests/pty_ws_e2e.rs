//! END-TO-END PROOF of the web cockpit's terminal backend: a real shell driven
//! over a real WebSocket — the exact byte path the in-browser `WsTransport`
//! speaks (the browser side differs only in being a `web_sys::WebSocket`).
//!
//! Two checks, both against the SAME `starbridge_web::pty_ws` server the bin runs:
//!
//!  1. `shell_over_websocket_echoes_marker` — connect, send `echo <marker>\n` as a
//!     binary frame (= PTY stdin), assert the PTY echoes the marker back over the
//!     socket as binary frames (= PTY stdout). Keystrokes in, shell output out.
//!
//!  2. `shell_over_websocket_pwd_returns_cwd` — connect, send `pwd\n`, assert the
//!     server's working directory comes back. Proves a second real command runs in
//!     the real shell, not a canned echo.
//!
//! These run the server IN-PROCESS (`bind_serve` on an ephemeral port), so there is
//! no separate spawned bin and no fixed-port race.

#![cfg(all(not(target_arch = "wasm32"), feature = "pty-ws-server"))]

use std::time::Duration;

use futures_util::{SinkExt, StreamExt};
use tokio_tungstenite::tungstenite::Message;

use starbridge_web::pty_ws::{bind_serve, Spawn};

/// Stand up the in-process WS↔PTY server on an ephemeral port, returning the URL.
async fn spawn_server() -> String {
    // A clean, rc-free POSIX shell for a deterministic prompt.
    std::env::set_var("DEOS_TERMINAL_SHELL", "/bin/sh");
    let (addr, fut) = bind_serve("127.0.0.1:0", Spawn::Shell)
        .await
        .expect("bind pty-ws server");
    tokio::spawn(fut);
    format!("ws://{addr}")
}

/// Drive the shell with `keystrokes` and read binary (PTY output) frames until
/// `needle` appears or a timeout elapses. Returns whether it was seen + the bytes.
/// Connects with a short retry loop in case the accept loop hasn't polled yet.
async fn run_and_await(
    url: &str,
    keystrokes: &str,
    needle: &str,
) -> (bool, String) {
    let mut ws = None;
    for _ in 0..50 {
        if let Ok((stream, _resp)) = tokio_tungstenite::connect_async(url).await {
            ws = Some(stream);
            break;
        }
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    let mut ws = ws.unwrap_or_else(|| panic!("could not connect to {url}"));

    ws.send(Message::Binary(keystrokes.as_bytes().to_vec().into()))
        .await
        .expect("send keystrokes");

    let mut seen = String::new();
    let deadline = tokio::time::Instant::now() + Duration::from_secs(10);
    let found = loop {
        let remaining = deadline.saturating_duration_since(tokio::time::Instant::now());
        if remaining.is_zero() {
            break false;
        }
        match tokio::time::timeout(remaining, ws.next()).await {
            Ok(Some(Ok(Message::Binary(bytes)))) => {
                seen.push_str(&String::from_utf8_lossy(&bytes));
                if seen.contains(needle) {
                    break true;
                }
            }
            Ok(Some(Ok(Message::Text(_)))) => {} // a WireMsg control frame.
            Ok(Some(Ok(Message::Close(_)))) | Ok(None) => break false,
            Ok(Some(Ok(_))) => {}
            Ok(Some(Err(_))) | Err(_) => break false,
        }
    };
    let _ = ws.close(None).await;
    (found, seen)
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn shell_over_websocket_echoes_marker() {
    let url = spawn_server().await;
    let marker = "DEOS_WEB_WS_OK_7717";
    let (found, seen) = run_and_await(&url, &format!("echo {marker}\n"), marker).await;
    assert!(
        found,
        "marker `{marker}` never came back over the WS from the PTY shell; saw:\n{seen}"
    );
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn shell_over_websocket_pwd_returns_cwd() {
    let url = spawn_server().await;
    // The server's cwd is the test's cwd (the web crate dir); assert a stable
    // tail of the absolute path comes back — proves a SECOND real command runs.
    let cwd = std::env::current_dir().expect("cwd");
    let tail = cwd
        .file_name()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| "/".to_string());
    let (found, seen) = run_and_await(&url, "pwd\n", &tail).await;
    assert!(
        found,
        "`pwd` output (expected to contain `{tail}`) never came back; saw:\n{seen}"
    );
}
