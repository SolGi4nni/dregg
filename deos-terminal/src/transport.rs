//! The terminal byte-transport SEAM.
//!
//! A `TerminalView` is just a grid plus two byte streams: **output bytes** flow
//! IN (the shell's stdout/stderr, parsed into the grid) and **input bytes** flow
//! OUT (keystrokes the shell reads on stdin), with resize as a side channel. On
//! native that stream is a local PTY. In a browser there is no PTY — so the
//! stream must reach a PTY that lives elsewhere, over a WebSocket.
//!
//! This module is that seam: one [`TerminalTransport`] trait the view drives, and
//! two implementations behind it —
//!
//! - [`PtyTransport`] (native): the existing local PTY (`crate::model::Terminal`)
//!   — output is the alacritty grid the view already reads; input/resize go down
//!   the PTY notifier. The native path is unchanged in behaviour; it just now
//!   *names* the seam.
//! - [`WsTransport`] (wasm32): a [`web_sys::WebSocket`] to the
//!   `deos-terminal-pty-ws` server. Keystrokes go out as binary frames; the PTY's
//!   output bytes arrive as binary frames and are fed through a `vte` parser into
//!   a grid sink; resize/exit are JSON text frames.
//!
//! ## The wire ([`WireMsg`])
//!
//! Data is carried **transparently as binary WS frames** (raw PTY bytes, no
//! base64 — the conventional ttyd/xterm.js shape), and control as **JSON text
//! frames**. So a peer classifies a frame by kind: binary ⇒ PTY data, text ⇒ a
//! [`WireMsg`] control message (`resize` / `exit`). Keeping data out of JSON
//! avoids a base64 round-trip on the hot path.
//!
//! ## Net-cap (next wire)
//!
//! Today the WS URL is ambient (a `ws://host:port` the client dials). The
//! intended end state is that this reach is a *granted firmament net-cap*, not
//! ambient authority: the terminal can only open the socket its cap names, and
//! the gate attenuates which host/port (and which shell) the grant permits. That
//! gate is a sibling wire — see the crate-level note — and does not have to be
//! live in this slice; the seam here is where it will attach (the `connect` URL
//! becomes "the endpoint this net-cap authorizes").

use serde::{Deserialize, Serialize};

/// A control message on the WS wire (sent as a JSON **text** frame). Raw PTY
/// bytes are NOT a `WireMsg` — they ride as binary frames for transparency; only
/// the out-of-band control channel is JSON.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "t", rename_all = "snake_case")]
pub enum WireMsg {
    /// The grid was resized to `cols`×`rows`; the server resizes the PTY winsize.
    Resize { cols: u16, rows: u16 },
    /// The child process exited (server → client).
    Exit { code: Option<i32> },
}

impl WireMsg {
    /// Encode as a JSON text-frame payload.
    pub fn to_text(&self) -> String {
        // The enum is tiny and total; serialization cannot fail.
        serde_json::to_string(self).expect("WireMsg serializes")
    }

    /// Decode a JSON text-frame payload. Returns `None` for anything that isn't a
    /// recognized control message (a peer is free to ignore unknown control).
    pub fn from_text(s: &str) -> Option<Self> {
        serde_json::from_str(s).ok()
    }
}

/// The seam the `TerminalView` drives. The view does not know whether its bytes
/// reach a local PTY or a socket; it only `write`s input, `resize`s, and reads
/// the grid the transport keeps current from the output stream.
///
/// Output delivery is transport-specific: the native PTY transport parses output
/// into the alacritty grid the view already snapshots (`crate::model::Terminal`),
/// so it exposes no separate output hook; the WS transport parses output into its
/// own grid sink. Both satisfy this common *input/resize/liveness* contract.
pub trait TerminalTransport {
    /// Send input bytes the shell reads on its stdin (keystrokes, paste, escape
    /// sequences the key encoder produced).
    fn write(&self, bytes: &[u8]);

    /// Inform the far PTY the grid resized to `cols`×`rows` cells.
    fn resize(&self, cols: u16, rows: u16);

    /// Whether the child process has exited (the shell is gone).
    fn has_exited(&self) -> bool;

    /// A monotonically increasing counter the view diffs to decide when to
    /// re-snapshot: it advances whenever new output has changed the grid.
    fn generation(&self) -> u64;
}

// ── native: the local PTY behind the seam ────────────────────────────────────

// The native transport IS the existing local-PTY [`crate::model::Terminal`]: it
// implements [`TerminalTransport`] directly (see `model.rs`), so the view writes
// keystrokes through the SAME trait the WS transport implements. Its grid (the
// alacritty `Term`) is the output sink the view already snapshots via
// `Terminal::content()`; resize uses the model's `&mut` cell-resize path
// (`Terminal::resize`), which the trait's `&self` `resize` mirrors best-effort
// for wire symmetry.

// ── wasm: the WebSocket behind the seam ──────────────────────────────────────

#[cfg(target_arch = "wasm32")]
mod ws {
    use std::cell::RefCell;
    use std::rc::Rc;

    use wasm_bindgen::closure::Closure;
    use wasm_bindgen::JsCast;
    use web_sys::{BinaryType, MessageEvent, WebSocket};

    use super::{TerminalTransport, WireMsg};

    /// A minimal renderable grid the browser terminal paints. The native build
    /// gets a full alacritty grid (`crate::model::Terminal`); on wasm `alacritty_
    /// terminal` does not link (its `polling`/`home` deps are not wasm-clean), so
    /// the WS transport feeds the PTY byte stream through a `vte` parser into THIS
    /// grid — a plain character/SGR cell buffer sufficient for the cockpit-web
    /// view to render. (The full alacritty grid on a wasm-clean vte backend is a
    /// follow-on; this grid carries the wired path end-to-end.)
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
                cells: vec![' '; cols * rows],
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
                // Scroll up one line.
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

    /// A `vte::Perform` that drives the [`WasmGrid`]. Deliberately minimal: it
    /// handles printable characters and the few C0 controls a prompt needs (CR,
    /// LF, BS, TAB). Full SGR/CSI/OSC handling is a follow-on (the native grid has
    /// it); this is enough to render a live shell session structurally.
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
        // CSI/ESC/OSC dispatch is intentionally unimplemented in this slice's
        // minimal grid (cursor addressing, SGR colors, clears); the bytes still
        // flow and the printable stream renders.
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
        /// Open a WebSocket to `url` (e.g. `ws://127.0.0.1:7717`) and start
        /// feeding its byte stream into a `cols`×`rows` grid.
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

        /// A text snapshot of the grid (for the view to render / a probe).
        pub fn grid_text(&self) -> String {
            self.inner.borrow().grid.to_text()
        }
    }

    impl TerminalTransport for WsTransport {
        fn write(&self, bytes: &[u8]) {
            // Keystrokes ride as a binary frame (transparent, no base64).
            let _ = self.inner.borrow().socket.send_with_u8_array(bytes);
        }

        fn resize(&self, cols: u16, rows: u16) {
            let msg = WireMsg::Resize { cols, rows }.to_text();
            let _ = self.inner.borrow().socket.send_with_str(&msg);
        }

        fn has_exited(&self) -> bool {
            self.inner.borrow().exited
        }

        fn generation(&self) -> u64 {
            self.inner.borrow().generation
        }
    }
}

#[cfg(target_arch = "wasm32")]
pub use ws::{WasmGrid, WsTransport};
