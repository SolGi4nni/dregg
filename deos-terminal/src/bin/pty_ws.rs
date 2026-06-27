//! `deos-terminal-pty-ws` — a PTY-over-WebSocket dev backend.
//!
//! A browser tab has no PTY, so the in-browser terminal grid drives a real shell
//! through THIS server: each WebSocket connection gets a fresh `$SHELL` on a real
//! PTY (`portable-pty`), and the server bridges bytes both ways —
//!
//! - PTY output bytes  → **binary** WS frames (transparent, no base64)
//! - client **binary** frames → PTY stdin (keystrokes / paste / escapes)
//! - client **text** frames → a JSON [`WireMsg`] control message (resize)
//! - child exit → a `WireMsg::Exit` text frame, then close
//!
//! One PTY per connection. This is the native resource the wasm `WsTransport`
//! (`src/transport.rs`) reaches.
//!
//! Usage:  `deos-terminal-pty-ws [BIND_ADDR]`   (default `127.0.0.1:7717`)
//!         `DEOS_TERMINAL_SHELL=/bin/bash deos-terminal-pty-ws`
//!
//! Net-cap (next wire): the bind/origin/shell this server grants is, in the end
//! state, what a firmament net-cap authorizes — not an ambient `ws://`. The seam
//! is the per-connection accept here (where a granted cap would gate origin +
//! shell + cwd); it does not have to be live in this slice.

// Native-only: a PTY + tokio + tungstenite server. `required-features` gates the
// feature set but not the target, so a wasm build that leaves `pty-ws-server` on
// would still try to compile this bin — the wasm stub `main` below keeps it
// compiling (inert) there.
#![cfg_attr(target_arch = "wasm32", allow(dead_code))]

#[cfg(target_arch = "wasm32")]
fn main() {}

#[cfg(not(target_arch = "wasm32"))]
mod imp {
    use std::io::{Read, Write};

    use anyhow::Context as _;
    use deos_terminal::transport::WireMsg;
    use futures_util::{SinkExt, StreamExt};
    use portable_pty::{CommandBuilder, NativePtySystem, PtySize, PtySystem};
    use tokio::sync::mpsc;
    use tokio_tungstenite::tungstenite::Message;

    pub async fn run() -> anyhow::Result<()> {
        let _ = env_logger_try_init();

        let bind = std::env::args()
            .nth(1)
            .unwrap_or_else(|| "127.0.0.1:7717".to_string());

        let listener = tokio::net::TcpListener::bind(&bind)
            .await
            .with_context(|| format!("binding {bind}"))?;
        log::info!("deos-terminal-pty-ws listening on ws://{bind}");
        eprintln!("deos-terminal-pty-ws listening on ws://{bind}");

        loop {
            let (stream, peer) = listener.accept().await?;
            tokio::spawn(async move {
                if let Err(e) = serve_connection(stream).await {
                    log::warn!("connection {peer} ended: {e:#}");
                }
            });
        }
    }

    /// Bridge one WebSocket connection ↔ one PTY-hosted shell.
    async fn serve_connection(stream: tokio::net::TcpStream) -> anyhow::Result<()> {
        let ws = tokio_tungstenite::accept_async(stream)
            .await
            .context("websocket handshake")?;
        let (mut ws_tx, mut ws_rx) = ws.split();

        // Spawn $SHELL on a fresh PTY.
        let pty_system = NativePtySystem::default();
        let pair = pty_system
            .openpty(PtySize {
                rows: 24,
                cols: 80,
                pixel_width: 0,
                pixel_height: 0,
            })
            .context("openpty")?;

        let mut cmd = shell_command();
        let mut child = pair
            .slave
            .spawn_command(cmd_take(&mut cmd))
            .context("spawn shell")?;
        // Drop the slave once the child holds it, so EOF propagates on child exit.
        drop(pair.slave);

        let mut reader = pair.master.try_clone_reader().context("clone reader")?;
        let mut writer = pair.master.take_writer().context("take writer")?;
        // `Box<dyn MasterPty + Send>` is `Send` (only the resize handle); keep it on
        // this task for the resize control path. (An `Arc` would add a `Sync` bound
        // the trait object lacks.)
        let master = pair.master;

        // PTY output → an mpsc the async side forwards as binary WS frames. The PTY
        // read is blocking, so it lives on a blocking thread.
        let (out_tx, mut out_rx) = mpsc::channel::<Vec<u8>>(64);
        let reader_handle = std::thread::spawn(move || {
            let mut buf = [0u8; 8192];
            loop {
                match reader.read(&mut buf) {
                    Ok(0) => break, // EOF — child exited / PTY closed.
                    Ok(n) => {
                        if out_tx.blocking_send(buf[..n].to_vec()).is_err() {
                            break; // receiver gone — connection closed.
                        }
                    }
                    Err(_) => break,
                }
            }
        });

        // Child-exit watcher → an exit signal. Blocking wait on a thread.
        let (exit_tx, mut exit_rx) = mpsc::channel::<Option<i32>>(1);
        let exit_handle = std::thread::spawn(move || {
            let code = child.wait().ok().map(|s| s.exit_code() as i32);
            let _ = exit_tx.blocking_send(code);
        });

        loop {
            tokio::select! {
                // PTY output → client (binary frame).
                maybe_out = out_rx.recv() => {
                    match maybe_out {
                        Some(bytes) => {
                            if ws_tx.send(Message::Binary(bytes)).await.is_err() {
                                break;
                            }
                        }
                        None => break, // reader thread ended.
                    }
                }

                // Child exited → tell the client, then close.
                code = exit_rx.recv() => {
                    let code = code.flatten();
                    let _ = ws_tx
                        .send(Message::Text(WireMsg::Exit { code }.to_text()))
                        .await;
                    let _ = ws_tx.send(Message::Close(None)).await;
                    break;
                }

                // Client → PTY (binary = stdin bytes; text = control).
                msg = ws_rx.next() => {
                    match msg {
                        Some(Ok(Message::Binary(bytes))) => {
                            if writer.write_all(&bytes).is_err() {
                                break;
                            }
                            let _ = writer.flush();
                        }
                        Some(Ok(Message::Text(text))) => {
                            if let Some(WireMsg::Resize { cols, rows }) = WireMsg::from_text(&text) {
                                let _ = master.resize(PtySize {
                                    rows,
                                    cols,
                                    pixel_width: 0,
                                    pixel_height: 0,
                                });
                            }
                        }
                        Some(Ok(Message::Close(_))) | None => break,
                        Some(Ok(_)) => {} // ping/pong handled by tungstenite.
                        Some(Err(_)) => break,
                    }
                }
            }
        }

        // Best-effort cleanup: the threads end when the PTY halves drop.
        let _ = reader_handle.join();
        let _ = exit_handle.join();
        Ok(())
    }

    /// `$SHELL` (or `$DEOS_TERMINAL_SHELL`) interactively, else `/bin/sh`.
    fn shell_command() -> CommandBuilder {
        let shell = std::env::var("DEOS_TERMINAL_SHELL")
            .or_else(|_| std::env::var("SHELL"))
            .unwrap_or_else(|_| "/bin/sh".to_string());
        let mut cmd = CommandBuilder::new(shell);
        cmd.arg("-i");
        if let Ok(cwd) = std::env::current_dir() {
            cmd.cwd(cwd);
        }
        // A trivial, predictable prompt keeps the wire deterministic for the e2e test.
        cmd.env("PS1", "$ ");
        cmd
    }

    /// `spawn_command` consumes the builder; move it out behind an `&mut`.
    fn cmd_take(cmd: &mut CommandBuilder) -> CommandBuilder {
        std::mem::replace(cmd, CommandBuilder::new("/bin/sh"))
    }

    /// `env_logger` is not a dep here; this is a no-op hook kept so adding it later is
    /// one line. (`log` macros still route to whatever a host installs.)
    fn env_logger_try_init() -> anyhow::Result<()> {
        Ok(())
    }
} // mod imp

#[cfg(not(target_arch = "wasm32"))]
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    imp::run().await
}
