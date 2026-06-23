//! End-to-end proof of the PTY-over-WebSocket bridge: a real shell driven over a
//! real WebSocket.
//!
//! Spawn the `deos-terminal-pty-ws` server bin, dial it with a native tungstenite
//! WS client, send `echo <marker>\n` as a binary frame, and assert the PTY echoes
//! the marker back over the socket. This proves the wire end-to-end — keystrokes
//! in, shell output out — which is exactly the path the in-browser `WsTransport`
//! speaks (the browser side differs only in being a `web_sys::WebSocket`).

use std::process::{Child, Command, Stdio};
use std::time::Duration;

use futures_util::{SinkExt, StreamExt};
use tokio_tungstenite::tungstenite::Message;

/// Kill the server child on drop so a failed assert doesn't leak a process.
struct ServerGuard(Child);
impl Drop for ServerGuard {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn shell_over_websocket_echoes_a_marker() {
    // A free-ish port (high, fixed for this test; one connection only).
    let addr = "127.0.0.1:7731";

    // Boot the server bin. Cargo exports its path to the test via this env var.
    let bin = env!("CARGO_BIN_EXE_deos-terminal-pty-ws");
    let child = Command::new(bin)
        .arg(addr)
        // Force a clean, rc-free POSIX shell for a deterministic prompt.
        .env("DEOS_TERMINAL_SHELL", "/bin/sh")
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn deos-terminal-pty-ws");
    let _guard = ServerGuard(child);

    // Wait for the listener to come up (retry the connect).
    let url = format!("ws://{addr}");
    let mut ws = None;
    for _ in 0..50 {
        match tokio_tungstenite::connect_async(&url).await {
            Ok((stream, _resp)) => {
                ws = Some(stream);
                break;
            }
            Err(_) => tokio::time::sleep(Duration::from_millis(100)).await,
        }
    }
    let mut ws = ws.expect("connect to pty-ws server");

    // Send a command whose output is a unique marker (binary frame = PTY stdin).
    let marker = "DEOS_WS_OK_5151";
    ws.send(Message::Binary(format!("echo {marker}\n").into_bytes().into()))
        .await
        .expect("send keystrokes");

    // Read binary frames (PTY output) until the marker shows up, with a timeout.
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
                // The marker appears as the command's output line (and possibly as
                // the typed echo); either way, once present the bridge is proven.
                if seen.contains(marker) {
                    break true;
                }
            }
            Ok(Some(Ok(Message::Text(_)))) => {} // a WireMsg control frame.
            Ok(Some(Ok(Message::Close(_)))) | Ok(None) => break false,
            Ok(Some(Ok(_))) => {}
            Ok(Some(Err(_))) | Err(_) => break false,
        }
    };

    assert!(
        found,
        "shell did not echo {marker} over the WebSocket. Bytes seen:\n{seen}"
    );
}
