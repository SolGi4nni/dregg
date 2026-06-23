//! `starbridge-web-pty-ws` — the web cockpit's terminal backend server.
//!
//! A browser tab has no PTY, so the in-browser terminal grid drives a real shell
//! through THIS server: each WebSocket connection gets a fresh `$SHELL` on a real
//! PTY, and the server bridges bytes both ways (see `starbridge_web::pty_ws`).
//!
//!   starbridge-web-pty-ws [BIND_ADDR]      # default 127.0.0.1:7717
//!   DEOS_TERMINAL_SHELL=/bin/bash starbridge-web-pty-ws
//!
//! The wasm `WsTransport` (the browser terminal pane) connects to `ws://BIND_ADDR`.

// `required-features = ["pty-ws-server"]` gates the feature set but not the
// target; keep a wasm stub so a wasm build that leaves the feature on still
// compiles this bin (inert) there.
#[cfg(target_arch = "wasm32")]
fn main() {}

#[cfg(all(not(target_arch = "wasm32"), feature = "pty-ws-server"))]
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let bind = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "127.0.0.1:7717".to_string());
    starbridge_web::pty_ws::serve(&bind, starbridge_web::pty_ws::Spawn::Shell).await
}

// If the bin is somehow built native without the feature, give a clear message
// rather than a link error.
#[cfg(all(not(target_arch = "wasm32"), not(feature = "pty-ws-server")))]
fn main() {
    eprintln!("starbridge-web-pty-ws requires the `pty-ws-server` feature");
    std::process::exit(2);
}
