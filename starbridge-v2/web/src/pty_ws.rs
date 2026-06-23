//! THE WEB COCKPIT'S TERMINAL BACKEND — a PTY over a WebSocket.
//!
//! The gpui-web cockpit (`cockpit_web::boot_cockpit`) runs the whole presentation
//! plane in a browser tab over the already-wasm data plane (the embedded verified
//! executor). One surface does not fit in the tab: the **terminal**. A shell is a
//! real OS process on a PTY; a browser tab has neither. So the terminal pane's
//! BACKEND must live outside the tab and be reached over a wire.
//!
//! This module is that wire, owned by the web crate so the web cockpit's terminal
//! has a backend it can actually reach:
//!
//! - **native** (`cfg(not(wasm32))`, behind the `pty-ws-server` feature): a
//!   WebSocket server ([`serve`]) that gives each connection a fresh `$SHELL` on a
//!   real PTY (`portable-pty`) and bridges bytes both ways. PTY output → **binary**
//!   WS frames (transparent, no base64); client binary frames → PTY stdin
//!   (keystrokes); client **text** frames → a JSON [`WireMsg`] control message
//!   (resize); child exit → a `WireMsg::Exit` text frame, then close. The server
//!   bin (`src/bin/pty-ws.rs`) and the e2e test (`tests/pty_ws_e2e.rs`) drive it.
//!
//! - **wasm** (`cfg(wasm32)`): [`WsTransport`] — a [`web_sys::WebSocket`] to that
//!   server. The browser terminal grid writes keystrokes through it and reads the
//!   PTY's output bytes (parsed into a small [`WasmGrid`]). This is the half the
//!   gpui-web terminal pane drives; it speaks the SAME wire the native server
//!   serves, so the e2e test (a native WS client against the same server) proves
//!   the exact byte path the browser will speak.
//!
//! One wire, two ends, one crate.
//!
//! ## Net-cap (the next wire, not this slice)
//!
//! Today the WS URL is ambient (`ws://host:port`). The intended end state is that
//! this reach is a *granted firmament net-cap*: the terminal can only open the
//! socket its cap names, and the gate attenuates which host/port + which shell the
//! grant permits. The seam is the per-connection accept in [`serve`] (where a
//! granted cap would gate origin + shell + cwd); it need not be live here.

use serde::{Deserialize, Serialize};

/// A control message on the WS wire (sent as a JSON **text** frame). Raw PTY
/// bytes are NOT a `WireMsg` — they ride as binary frames for transparency; only
/// the out-of-band control channel is JSON. The conventional ttyd/xterm.js shape.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "t", rename_all = "snake_case")]
pub enum WireMsg {
    /// The grid was resized to `cols`×`rows`; the server resizes the PTY winsize.
    Resize { cols: u16, rows: u16 },
    /// The child process exited (server → client).
    Exit { code: Option<i32> },
}

impl WireMsg {
    /// Encode as a JSON text-frame payload. The enum is tiny and total, so this
    /// cannot fail.
    pub fn to_text(&self) -> String {
        serde_json::to_string(self).expect("WireMsg serializes")
    }

    /// Decode a JSON text-frame payload. Returns `None` for anything that isn't a
    /// recognized control message (a peer ignores unknown control).
    pub fn from_text(s: &str) -> Option<Self> {
        serde_json::from_str(s).ok()
    }
}

// ── native: the WS↔PTY server behind the seam ────────────────────────────────

#[cfg(all(not(target_arch = "wasm32"), feature = "pty-ws-server"))]
mod server {
    use std::io::{Read, Write};

    use anyhow::Context as _;
    use futures_util::{SinkExt, StreamExt};
    use portable_pty::{CommandBuilder, NativePtySystem, PtySize, PtySystem};
    use tokio::sync::mpsc;
    use tokio_tungstenite::tungstenite::Message;

    use super::WireMsg;

    /// What shell a connection runs. `Shell` spawns `$DEOS_TERMINAL_SHELL`/`$SHELL`
    /// (default `/bin/sh`) interactively; `Command` runs a specific program+args
    /// (deterministic one-shots a test can drive).
    #[derive(Clone, Debug)]
    pub enum Spawn {
        /// `$SHELL -i` with a predictable prompt — the live terminal.
        Shell,
        /// A specific program + args (e.g. `("/bin/echo", ["hi"])`).
        Command(String, Vec<String>),
    }

    /// Bind a TCP listener and serve PTY-over-WebSocket connections forever. Each
    /// accepted connection gets a fresh PTY running `spawn`. Returns only on a
    /// fatal accept error.
    pub async fn serve(bind: &str, spawn: Spawn) -> anyhow::Result<()> {
        let listener = tokio::net::TcpListener::bind(bind)
            .await
            .with_context(|| format!("binding {bind}"))?;
        log::info!("starbridge-web pty-ws listening on ws://{bind}");
        eprintln!("starbridge-web pty-ws listening on ws://{bind}");
        loop {
            let (stream, peer) = listener.accept().await?;
            let spawn = spawn.clone();
            tokio::spawn(async move {
                if let Err(e) = serve_connection(stream, spawn).await {
                    log::warn!("pty-ws connection {peer} ended: {e:#}");
                }
            });
        }
    }

    /// Bind, returning the actually-bound address (so a test can ask for port 0
    /// and learn the OS-assigned port), plus a future that serves forever. The
    /// caller drives the future (e.g. `tokio::spawn`).
    pub async fn bind_serve(
        bind: &str,
        spawn: Spawn,
    ) -> anyhow::Result<(
        std::net::SocketAddr,
        impl std::future::Future<Output = anyhow::Result<()>>,
    )> {
        let listener = tokio::net::TcpListener::bind(bind)
            .await
            .with_context(|| format!("binding {bind}"))?;
        let addr = listener.local_addr()?;
        let fut = async move {
            loop {
                let (stream, peer) = listener.accept().await?;
                let spawn = spawn.clone();
                tokio::spawn(async move {
                    if let Err(e) = serve_connection(stream, spawn).await {
                        log::warn!("pty-ws connection {peer} ended: {e:#}");
                    }
                });
            }
        };
        Ok((addr, fut))
    }

    /// Bridge one WebSocket connection ↔ one PTY-hosted process.
    async fn serve_connection(
        stream: tokio::net::TcpStream,
        spawn: Spawn,
    ) -> anyhow::Result<()> {
        let ws = tokio_tungstenite::accept_async(stream)
            .await
            .context("websocket handshake")?;
        let (mut ws_tx, mut ws_rx) = ws.split();

        let pty_system = NativePtySystem::default();
        let pair = pty_system
            .openpty(PtySize {
                rows: 24,
                cols: 80,
                pixel_width: 0,
                pixel_height: 0,
            })
            .context("openpty")?;

        let cmd = build_command(&spawn);
        let mut child = pair.slave.spawn_command(cmd).context("spawn process")?;
        // Drop the slave once the child holds it, so EOF propagates on child exit.
        drop(pair.slave);

        let mut reader = pair.master.try_clone_reader().context("clone reader")?;
        let mut writer = pair.master.take_writer().context("take writer")?;
        let master = pair.master; // kept here for the resize control path.

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

        // Child-exit watcher → an exit signal (blocking wait on a thread).
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
                            if ws_tx.send(Message::Binary(bytes.into())).await.is_err() {
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
                        .send(Message::Text(WireMsg::Exit { code }.to_text().into()))
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

        let _ = reader_handle.join();
        let _ = exit_handle.join();
        Ok(())
    }

    fn build_command(spawn: &Spawn) -> CommandBuilder {
        match spawn {
            Spawn::Shell => {
                let shell = std::env::var("DEOS_TERMINAL_SHELL")
                    .or_else(|_| std::env::var("SHELL"))
                    .unwrap_or_else(|_| "/bin/sh".to_string());
                let mut cmd = CommandBuilder::new(shell);
                cmd.arg("-i");
                if let Ok(cwd) = std::env::current_dir() {
                    cmd.cwd(cwd);
                }
                // A trivial, predictable prompt keeps the wire deterministic.
                cmd.env("PS1", "$ ");
                cmd
            }
            Spawn::Command(prog, args) => {
                let mut cmd = CommandBuilder::new(prog);
                for a in args {
                    cmd.arg(a);
                }
                if let Ok(cwd) = std::env::current_dir() {
                    cmd.cwd(cwd);
                }
                cmd
            }
        }
    }
}

#[cfg(all(not(target_arch = "wasm32"), feature = "pty-ws-server"))]
pub use server::{bind_serve, serve, Spawn};

// ── wasm: the WebSocket client behind the seam ───────────────────────────────

#[cfg(target_arch = "wasm32")]
mod ws {
    use std::cell::RefCell;
    use std::rc::Rc;

    use wasm_bindgen::closure::Closure;
    use wasm_bindgen::JsCast;
    use web_sys::{BinaryType, MessageEvent, WebSocket};

    use super::WireMsg;

    /// A minimal renderable grid the browser terminal paints. The PTY byte stream
    /// is fed through a `vte` parser into this plain character cell buffer —
    /// enough for the cockpit-web terminal pane to render a live shell session
    /// structurally. (Full SGR/CSI/cursor-addressing on a wasm-clean grid is a
    /// follow-on; this carries the wired path end-to-end.)
    #[derive(Default)]
    pub struct WasmGrid {
        pub cols: usize,
        pub rows: usize,
        /// `rows * cols` cells, row-major; `' '` is blank.
        pub cells: Vec<char>,
        pub cursor_col: usize,
        pub cursor_row: usize,
    }

    impl WasmGrid {
        fn new(cols: usize, rows: usize) -> Self {
            Self {
                cols,
                rows,
                cells: vec![' '; cols.max(1) * rows.max(1)],
                cursor_col: 0,
                cursor_row: 0,
            }
        }

        fn put(&mut self, c: char) {
            if self.cursor_row < self.rows && self.cursor_col < self.cols {
                self.cells[self.cursor_row * self.cols + self.cursor_col] = c;
            }
            self.cursor_col += 1;
            if self.cursor_col >= self.cols {
                self.cursor_col = 0;
                self.newline();
            }
        }

        fn newline(&mut self) {
            self.cursor_row += 1;
            if self.cursor_row >= self.rows {
                self.cells.drain(0..self.cols);
                self.cells.extend(std::iter::repeat(' ').take(self.cols));
                self.cursor_row = self.rows.saturating_sub(1);
            }
        }

        /// Flatten the visible grid to text (for the view / a test / a probe).
        pub fn to_text(&self) -> String {
            (0..self.rows)
                .map(|r| {
                    self.cells[r * self.cols..(r + 1) * self.cols]
                        .iter()
                        .collect::<String>()
                })
                .collect::<Vec<_>>()
                .join("\n")
        }
    }

    /// A `vte::Perform` driving the [`WasmGrid`]. Handles printable characters and
    /// the few C0 controls a prompt needs (CR, LF, BS, TAB).
    struct GridPerform<'a> {
        grid: &'a mut WasmGrid,
    }

    impl<'a> vte::Perform for GridPerform<'a> {
        fn print(&mut self, c: char) {
            self.grid.put(c);
        }
        fn execute(&mut self, byte: u8) {
            match byte {
                b'\n' => self.grid.newline(),
                b'\r' => self.grid.cursor_col = 0,
                0x08 => self.grid.cursor_col = self.grid.cursor_col.saturating_sub(1),
                b'\t' => {
                    let next = (self.grid.cursor_col / 8 + 1) * 8;
                    self.grid.cursor_col = next.min(self.grid.cols.saturating_sub(1));
                }
                _ => {}
            }
        }
    }

    struct Inner {
        socket: WebSocket,
        grid: WasmGrid,
        parser: vte::Parser,
        generation: u64,
        exited: bool,
    }

    /// The browser terminal transport: a `web_sys::WebSocket` to the pty-ws
    /// server. Keystrokes go out as binary frames; PTY output arrives as binary
    /// frames and is parsed into [`Inner::grid`]; resize/exit are JSON text
    /// frames. Cloning shares one socket+grid (`Rc<RefCell<…>>`), so the gpui view
    /// can hold a handle while the `onmessage` closure mutates the same state.
    #[derive(Clone)]
    pub struct WsTransport {
        inner: Rc<RefCell<Inner>>,
        // Keep the message closure alive for the socket's lifetime.
        _on_message: Rc<Closure<dyn FnMut(MessageEvent)>>,
    }

    impl WsTransport {
        /// Open a WebSocket to `url` (e.g. `ws://127.0.0.1:7717`) and start feeding
        /// its byte stream into a `cols`×`rows` grid.
        ///
        /// NOTE (net-cap): `url` is the endpoint a granted firmament net-cap will
        /// name — see the module docs. In this slice it is dialed directly.
        pub fn connect(url: &str, cols: usize, rows: usize) -> Result<Self, wasm_bindgen::JsValue> {
            let socket = WebSocket::new(url)?;
            socket.set_binary_type(BinaryType::Arraybuffer);

            let inner = Rc::new(RefCell::new(Inner {
                socket: socket.clone(),
                grid: WasmGrid::new(cols, rows),
                parser: vte::Parser::new(),
                generation: 0,
                exited: false,
            }));

            // onmessage: binary ⇒ PTY data (feed the parser); text ⇒ a WireMsg.
            let on_message = {
                let inner = inner.clone();
                Closure::wrap(Box::new(move |ev: MessageEvent| {
                    let data = ev.data();
                    if let Ok(buf) = data.clone().dyn_into::<js_sys::ArrayBuffer>() {
                        let bytes = js_sys::Uint8Array::new(&buf).to_vec();
                        let mut inner = inner.borrow_mut();
                        let Inner {
                            grid, parser, generation, ..
                        } = &mut *inner;
                        let mut perform = GridPerform { grid };
                        parser.advance(&mut perform, &bytes);
                        *generation = generation.wrapping_add(1);
                    } else if let Some(text) = data.as_string() {
                        if let Some(msg) = WireMsg::from_text(&text) {
                            let mut inner = inner.borrow_mut();
                            match msg {
                                WireMsg::Exit { .. } => inner.exited = true,
                                WireMsg::Resize { cols, rows } => {
                                    inner.grid = WasmGrid::new(cols as usize, rows as usize);
                                }
                            }
                            inner.generation = inner.generation.wrapping_add(1);
                        }
                    }
                }) as Box<dyn FnMut(MessageEvent)>)
            };
            socket.set_onmessage(Some(on_message.as_ref().unchecked_ref()));

            Ok(Self {
                inner,
                _on_message: Rc::new(on_message),
            })
        }

        /// Send input bytes the shell reads on stdin (keystrokes / paste). Rides as
        /// a binary frame (transparent, no base64).
        pub fn write(&self, bytes: &[u8]) {
            let _ = self.inner.borrow().socket.send_with_u8_array(bytes);
        }

        /// Inform the far PTY the grid resized to `cols`×`rows` cells (JSON text
        /// control frame).
        pub fn resize(&self, cols: u16, rows: u16) {
            let msg = WireMsg::Resize { cols, rows }.to_text();
            let _ = self.inner.borrow().socket.send_with_str(&msg);
        }

        /// Whether the child process has exited (the shell is gone).
        pub fn has_exited(&self) -> bool {
            self.inner.borrow().exited
        }

        /// A monotonic counter the view diffs to decide when to re-snapshot: it
        /// advances whenever new output has changed the grid.
        pub fn generation(&self) -> u64 {
            self.inner.borrow().generation
        }

        /// A text snapshot of the grid (for the view to render / a probe).
        pub fn grid_text(&self) -> String {
            self.inner.borrow().grid.to_text()
        }
    }
}

#[cfg(target_arch = "wasm32")]
pub use ws::{WasmGrid, WsTransport};

#[cfg(test)]
mod tests {
    use super::WireMsg;

    #[test]
    fn wire_msg_roundtrips() {
        let resize = WireMsg::Resize { cols: 120, rows: 40 };
        assert_eq!(WireMsg::from_text(&resize.to_text()), Some(resize));
        let exit = WireMsg::Exit { code: Some(0) };
        assert_eq!(WireMsg::from_text(&exit.to_text()), Some(exit));
        // Unknown control is ignored, not an error.
        assert_eq!(WireMsg::from_text("{\"t\":\"bogus\"}"), None);
        // Raw PTY bytes are NOT a WireMsg (they ride as binary frames).
        assert_eq!(WireMsg::from_text("ls -la\n"), None);
    }
}
