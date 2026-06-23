//! THE 🌐 WEB-SHELL BROWSER surface — a general `http(s)://` browser as a cockpit
//! tab, distinct from the `dregg://` web-of-cells browser ([`super::panels_web`]).
//!
//! ## What it is
//!
//! A real address bar + back / forward / reload navigation + a content tile that
//! renders a live web page. The pieces are all genuine:
//!
//!   * **URL bar** — a real gpui-component single-line text
//!     [`gpui_component::input::InputState`] (the URL bar gpui never had before this
//!     widget landed), submitting on `↵` via the
//!     [`InputEvent::PressEnter`](gpui_component::input::InputEvent) subscription.
//!   * **Navigation** — a [`Vec<String>`](Cockpit::webshell_history) history of
//!     visited URLs with a [`cursor`](Cockpit::webshell_cursor); back / forward /
//!     reload each RE-DRIVE the render of the URL at the new cursor (genuine
//!     re-fetch, not a relabel).
//!   * **The content tile** — `Go` calls
//!     [`servo_render::webview::render_url_to_frame`] (the real
//!     `ServoBuilder → WebViewBuilder → SWGL context → spin-until-painted →
//!     read_to_image` flow) and paints the returned
//!     [`RgbaFrame`](servo_render::RgbaFrame) through the SAME
//!     [`rgba_frame_to_image`] `img()` path the web-of-cells tab uses. Fail-closed:
//!     a render error / cap refusal is shown in the status line and the previous
//!     tile is KEPT — the surface never silently blanks.
//!
//! ## The cap model — the net-cap seam, named honestly
//!
//! The page's fetch + navigation ride the genuine
//! [`CapGate`](servo_render::webview) `WebViewDelegate`, which discharges a held
//! [`SurfaceCapability`](starbridge_web_surface::SurfaceCapability) through the
//! `granted ⊆ held` allowlist (`load_web_resource` / `request_navigation`): an
//! origin the surface cap does not permit is REFUSED *at the callback*, before the
//! engine acts (the page sees the cap-denied body, never the resource). This panel
//! holds a real `SurfaceCapability` over the browser's own backing cell and renders
//! through it.
//!
//! ## The net-cap socket bind (the formerly-open wire, now wired)
//!
//! Every fetch's CONNECT DECISION is routed through
//! [`servo_render::NetcapConnector`] backed by the dregg `captp`
//! [`Netlayer::dial`](dregg_captp::netlayer::Netlayer::dial) transport — the SAME
//! audited byte-frame transport the federation dials over (no ambient OS socket). An
//! origin the held [`SurfaceCapability`] does not authorize is refused AT the
//! connector before any `dial` (the socket never opens); a cap-admitted origin's
//! connection IS a real audited `NetSession`. The status line reports which of the
//! three an origin hit (dialed / refused-by-cap / unreachable), via
//! [`render_url_to_frame_netcap`](servo_render::webview::render_url_to_frame_netcap).
//!
//! HONEST DEPTH: for `http(s)` the *bytes-on-the-wire* still ride servo's internal
//! `net` (hyper) — servo forbids embedder `ProtocolHandler`s for `http`/`https`
//! (`FORBIDDEN_SCHEMES`), so replacing the byte socket needs a fork of servo's `net`
//! crate (out of one pass's reach). What IS bound, at the depth the embedder API
//! allows, is the connect/authority decision → `Netlayer::dial`: the origin's
//! reachability is the netlayer's to grant (gated by the cap), and a cap-denied origin
//! is refused at the dial doorstep. A `dregg://` (cell) fetch — not http — rides the
//! connector end-to-end with no such ceiling.
//!
//! ## Build gating
//!
//! The address bar + navigation + the whole surface chrome compile in any windowed
//! (`gpui-ui`) build. The actual page render is gated on the cockpit `web-shell`
//! feature (→ `servo-render/libservo`): with it OFF the panel still renders (URL
//! bar + nav + a "render engine not linked" note); with it ON the `Go` button
//! drives the real `render_url_to_frame`. The frame field + the render call are
//! `#[cfg(feature = "servo")]` (the `RgbaFrame` type) / `#[cfg(feature =
//! "web-shell")]` (the `render_url_to_frame` symbol).

use super::*;

use gpui_component::input::{Input, InputEvent, InputState};

impl Cockpit {
    // === lifecycle ===========================================================

    /// Seed the URL-bar text input entity on the first render (it needs a live
    /// `&mut Window` for [`InputState::new`] + the cockpit's weak handle for the
    /// Enter subscription, neither available in the constructor). Idempotent — a
    /// no-op once seeded. The `↵` (PressEnter) subscription routes straight to
    /// [`Self::webshell_go`], so the address bar behaves like a real browser's.
    pub(crate) fn ensure_webshell_input(&mut self, window: &mut Window, cx: &mut Context<Self>) {
        if self.webshell_input.is_none() {
            let seed = self
                .webshell_history
                .get(self.webshell_cursor)
                .cloned()
                .unwrap_or_default();
            let input = cx.new(|cx| {
                let mut st = InputState::new(window, cx).placeholder("https://… or dregg://…");
                st.set_value(seed, window, cx);
                st
            });
            // ↵ in the URL bar = Go (the path the Go button + the ⌘K palette take).
            cx.subscribe(&input, |this, _input, event: &InputEvent, cx| {
                if matches!(event, InputEvent::PressEnter { .. }) {
                    this.webshell_go(cx);
                }
            })
            .detach();
            self.webshell_input = Some(input);
        }

        // Apply any pending URL-bar value (a back/forward/programmatic nav set it):
        // `set_value` needs the live `&mut Window` we only have here, on the paint
        // path. Cleared after applying so user typing is never re-stomped.
        if let Some(url) = self.webshell_input_pending.take() {
            if let Some(input) = self.webshell_input.clone() {
                input.update(cx, |st, cx| st.set_value(url, window, cx));
            }
        }
    }

    /// The URL currently typed into the address bar (the input entity's live value),
    /// falling back to the current history entry when the input is not yet seeded
    /// (the headless path) or empty.
    fn webshell_typed_url(&self, cx: &Context<Self>) -> String {
        let typed = self
            .webshell_input
            .as_ref()
            .map(|i| i.read(cx).value().to_string())
            .unwrap_or_default();
        if typed.trim().is_empty() {
            self.webshell_history
                .get(self.webshell_cursor)
                .cloned()
                .unwrap_or_default()
        } else {
            typed.trim().to_string()
        }
    }

    // === navigation ==========================================================

    /// GO — navigate to the URL in the address bar. A `dregg://` address routes to
    /// the `WebOfCells` browser (the existing web-of-cells resolution path — that is
    /// where a cell address belongs); an `http(s)://` (or scheme-less, defaulted to
    /// `https://`) address is pushed onto the history and RENDERED here. A
    /// malformed/empty address is refused in-band (the status line), the tile kept.
    pub(crate) fn webshell_go(&mut self, cx: &mut Context<Self>) {
        let raw = self.webshell_typed_url(cx);
        let url = normalize_url(&raw);
        let Some(url) = url else {
            self.webshell_status = format!("⚠ not a navigable address: {raw:?}");
            cx.notify();
            return;
        };

        // dregg:// — a cell address. Hand it to the WEB-OF-CELLS browser (the cell
        // docuverse resolution path), not the http renderer. The web-shell is the
        // http(s):// surface; the dregg:// surface is its sibling tab.
        if url.starts_with("dregg://") {
            self.webshell_status =
                format!("dregg:// address → routed to the WEB-OF-CELLS browser ({url})");
            self.set_tab(Tab::WebOfCells, cx);
            return;
        }

        // A NEW navigation truncates the forward tail (browser semantics) + pushes.
        if self.webshell_history.get(self.webshell_cursor) != Some(&url) {
            self.webshell_history.truncate(self.webshell_cursor + 1);
            self.webshell_history.push(url.clone());
            self.webshell_cursor = self.webshell_history.len() - 1;
        }
        self.sync_webshell_input(cx);
        self.webshell_render_current(cx);
    }

    /// BACK — step to the previous URL in history + re-render it (no-op at genesis).
    pub(crate) fn webshell_back(&mut self, cx: &mut Context<Self>) {
        if self.webshell_cursor == 0 {
            self.webshell_status = "← already at the start of history".to_string();
            cx.notify();
            return;
        }
        self.webshell_cursor -= 1;
        self.sync_webshell_input(cx);
        self.webshell_render_current(cx);
    }

    /// FORWARD — step to the next URL in history + re-render it (no-op at the head).
    pub(crate) fn webshell_forward(&mut self, cx: &mut Context<Self>) {
        if self.webshell_cursor + 1 >= self.webshell_history.len() {
            self.webshell_status = "→ already at the head of history".to_string();
            cx.notify();
            return;
        }
        self.webshell_cursor += 1;
        self.sync_webshell_input(cx);
        self.webshell_render_current(cx);
    }

    /// RELOAD — re-render the current history URL (re-drive the WebView render).
    pub(crate) fn webshell_reload(&mut self, cx: &mut Context<Self>) {
        self.webshell_render_current(cx);
    }

    /// Mirror the current history URL back into the address-bar input (after a
    /// back / forward / programmatic navigation), so the bar always shows the URL
    /// being viewed. The actual `set_value` (which needs a live `&mut Window`) is
    /// deferred to the next [`Self::ensure_webshell_input`] on the paint path via
    /// the [`webshell_input_pending`](Self::webshell_input_pending) field.
    fn sync_webshell_input(&mut self, _cx: &mut Context<Self>) {
        if let Some(url) = self.webshell_history.get(self.webshell_cursor).cloned() {
            self.webshell_input_pending = Some(url);
        }
    }

    /// The held [`SurfaceCapability`] this browser renders through — a real cap over
    /// the browser's own backing cell (the cockpit's `service` anchor stands in as
    /// the surface-owning principal). `AuthRequired::Either` clears a normal fetch;
    /// the genuine `granted ⊆ held` gate inside `render_url_to_frame` discharges it
    /// at every `load_web_resource` / `request_navigation` callback.
    #[cfg(feature = "web-shell")]
    fn webshell_surface_cap(&self) -> starbridge_web_surface::SurfaceCapability {
        let owner = self.anchors[1]; // the `service` anchor — the surface principal
        starbridge_web_surface::SurfaceCapability::root(owner, starbridge_web_surface::AuthRequired::Either)
    }

    /// Render the current history URL into the content tile through the real,
    /// cap-gated Servo WebView. Fail-closed: a `None` frame (no paint / cap refusal /
    /// parse failure) leaves the previous tile in place and explains itself in the
    /// status line.
    pub(crate) fn webshell_render_current(&mut self, cx: &mut Context<Self>) {
        let Some(url) = self.webshell_history.get(self.webshell_cursor).cloned() else {
            self.webshell_status = "no URL to render".to_string();
            cx.notify();
            return;
        };

        #[cfg(feature = "web-shell")]
        {
            const W: u32 = 720;
            const H: u32 = 460;
            const MAX_SPINS: usize = 4096;
            let surface = self.webshell_surface_cap();
            // The render runs under the process-wide SWGL current-context lock (the
            // global `ctx`), the same serialization the content-tile path uses. The
            // `_netcap` variant ALSO routes every fetch's connect decision through the
            // dregg captp `Netlayer::dial` connector and reports the outcome, so the
            // status line tells the truth about the transport, not just the allowlist.
            let (frame, net) = servo_render::with_gl(|| {
                servo_render::webview::render_url_to_frame_netcap(&url, surface, W, H, MAX_SPINS)
            });
            // The net-cap leg's truth: dialed through the audited netlayer, refused at
            // the socket by the held cap, or unreachable on the transport.
            let net_line = match &net {
                Some(o) => o.status_line(),
                None => "net-cap: (no socket fetch this navigation — e.g. an inline/data page)".to_string(),
            };
            match frame {
                Some(f) => {
                    self.webshell_status = format!(
                        "rendered {}×{} of {url} · {} bytes RGBA8 · digest {:#x} · {net_line}",
                        f.width,
                        f.height,
                        f.bytes.len(),
                        f.content_digest(),
                    );
                    self.webshell_frame = Some(f);
                }
                None => {
                    // FAIL-CLOSED — keep the old tile, show why. If the net-cap gate
                    // refused the origin at the socket, SAY SO explicitly (that is the
                    // most important fail-closed case: the cap bit at the transport).
                    if net.as_ref().map(|o| o.refused_by_cap()).unwrap_or(false) {
                        self.webshell_status = format!("⚠ {net_line} (tile kept)");
                    } else {
                        self.webshell_status = format!(
                            "⚠ no frame for {url} — the page did not paint within {MAX_SPINS} spins or the address is unparseable · {net_line} (tile kept)"
                        );
                    }
                }
            }
        }
        #[cfg(not(feature = "web-shell"))]
        {
            self.webshell_status = format!(
                "render engine not linked (build with --features web-shell to drive the real Servo WebView) · would render: {url}"
            );
        }
        cx.notify();
    }

    // === the panel ===========================================================

    /// THE 🌐 WEB-SHELL panel — the address bar + back/forward/reload + the content
    /// tile (+ the net-cap seam note).
    pub(crate) fn webshell_panel(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let can_back = self.webshell_cursor > 0;
        let can_fwd = self.webshell_cursor + 1 < self.webshell_history.len();
        let current = self
            .webshell_history
            .get(self.webshell_cursor)
            .cloned()
            .unwrap_or_default();

        let mut col = div()
            .id("cockpit-scroll-webshell")
            .flex()
            .flex_col()
            .size_full()
            .overflow_y_scroll()
            .p_3()
            .gap_2();

        // ── header ──
        col = col.child(section_title("🌐 WEB-SHELL — a general http(s):// browser"));
        col = col.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .child(
                    "A real Servo WebView render of a live web page, behind the net-cap \
                     allowlist (granted ⊆ held). dregg:// addresses route to the \
                     WEB-OF-CELLS browser.",
                ),
        );

        // ── the navigation toolbar: ← → ⟳ + the URL bar + Go ──
        let mut toolbar = div().flex().items_center().gap_1().mt_1();

        toolbar = toolbar.child(nav_button(
            cx,
            "←",
            "webshell-back",
            if can_back { theme::accent() } else { theme::muted() },
            Cockpit::webshell_back,
        ));
        toolbar = toolbar.child(nav_button(
            cx,
            "→",
            "webshell-forward",
            if can_fwd { theme::accent() } else { theme::muted() },
            Cockpit::webshell_forward,
        ));
        toolbar = toolbar.child(nav_button(
            cx,
            "⟳",
            "webshell-reload",
            theme::accent(),
            Cockpit::webshell_reload,
        ));

        // The URL BAR — the real gpui-component text input (Enter-to-go is wired in
        // `ensure_webshell_input`). When not yet seeded (first frame / headless) show
        // the current URL as a static field so the bar is never blank.
        if let Some(input) = self.webshell_input.as_ref() {
            toolbar = toolbar.child(
                div()
                    .flex_1()
                    .child(Input::new(input)),
            );
        } else {
            toolbar = toolbar.child(
                div()
                    .flex_1()
                    .px_2()
                    .py_1()
                    .rounded_md()
                    .border_1()
                    .border_color(theme::border())
                    .bg(theme::panel())
                    .text_sm()
                    .text_color(theme::text())
                    .child(SharedString::from(current.clone())),
            );
        }

        toolbar = toolbar.child(nav_button(
            cx,
            "Go",
            "webshell-go",
            theme::good(),
            Cockpit::webshell_go,
        ));
        col = col.child(toolbar);

        // ── the loading / status line ──
        let status_color = if self.webshell_status.starts_with('⚠') {
            theme::warn()
        } else if self.webshell_status.starts_with("rendered") {
            theme::good()
        } else {
            theme::muted()
        };
        col = col.child(
            div()
                .mt_1()
                .px_2()
                .py_1()
                .rounded_md()
                .bg(theme::panel())
                .text_xs()
                .text_color(status_color)
                .child(SharedString::from(self.webshell_status.clone())),
        );

        // ── the content tile ──
        col = col.child(self.webshell_tile());

        // ── the cap model / net-cap seam note ──
        col = col.child(
            div()
                .mt_2()
                .p_2()
                .rounded_md()
                .border_1()
                .border_color(theme::border())
                .bg(theme::panel())
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::accent())
                        .child("THE CAP MODEL"),
                )
                .child(
                    div()
                        .mt_0p5()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(
                            "Every fetch + navigation rides the CapGate WebViewDelegate: \
                             the held SurfaceCapability is discharged through the \
                             granted ⊆ held allowlist at each load_web_resource / \
                             request_navigation callback — a non-permitted origin is \
                             refused AT the callback (the page sees the cap-denied body, \
                             never the resource).",
                        ),
                )
                .child(
                    div()
                        .mt_1()
                        .text_xs()
                        .text_color(theme::good())
                        .child(
                            "NET-CAP SOCKET (wired): every fetch's connect decision routes \
                             through the dregg captp Netlayer::dial connector — a cap-denied \
                             origin is REFUSED at the socket (dial never called), a cap-admitted \
                             origin opens a real audited NetSession. The status line above reports \
                             dialed / refused-by-cap / unreachable.",
                        ),
                )
                .child(
                    div()
                        .mt_0p5()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(
                            "Depth (honest): for http(s) the bytes-on-the-wire still ride servo's \
                             internal hyper (it forbids embedder ProtocolHandlers for http/https); \
                             the CONNECT DECISION + reachability is the netlayer's, gated by the cap. \
                             A dregg:// (cell) fetch rides the connector end-to-end.",
                        ),
                ),
        );

        col
    }

    /// The content tile — the rendered page frame painted through the same `img()`
    /// path the web-of-cells tab uses, or a "no page yet / engine not linked"
    /// placeholder. Fail-closed: a kept frame stays painted even after a failing
    /// navigation (the status line carries the error).
    fn webshell_tile(&self) -> gpui::AnyElement {
        #[cfg(feature = "servo")]
        if let Some(frame) = self.webshell_frame.as_ref() {
            return div()
                .mt_2()
                .p_2()
                .rounded_md()
                .border_1()
                .border_color(theme::good())
                .bg(theme::panel())
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::good())
                        .child("PAGE — real cap-gated Servo WebView render (SWGL → glass)"),
                )
                .child(
                    gpui::img(rgba_frame_to_image(frame))
                        .w(gpui::px(frame.width as f32))
                        .h(gpui::px(frame.height as f32)),
                )
                .into_any_element();
        }

        // No frame yet (or `servo` off): a placeholder tile that names the state.
        div()
            .mt_2()
            .p_4()
            .rounded_md()
            .border_1()
            .border_color(theme::border())
            .bg(theme::panel())
            .flex()
            .items_center()
            .justify_center()
            .h(gpui::px(200.))
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(self.webshell_tile_placeholder()),
            )
            .into_any_element()
    }

    /// The placeholder text when there is no rendered frame to paint.
    fn webshell_tile_placeholder(&self) -> SharedString {
        #[cfg(feature = "web-shell")]
        {
            SharedString::from("no page rendered yet — type an http(s):// address and press ↵ Go")
        }
        #[cfg(not(feature = "web-shell"))]
        {
            SharedString::from(
                "the real WebView render engine is not linked in this build — build with \
                 --features web-shell (→ servo-render/libservo) to render live pages here",
            )
        }
    }
}

/// Normalize a raw address-bar string into a navigable URL. A `dregg://`,
/// `http://`, or `https://` URL passes through; a scheme-less, dot-bearing token
/// (e.g. `example.com`) is defaulted to `https://`; anything else (an empty or
/// space-laden non-URL) is rejected (`None`) — surfaced in-band, never silently
/// navigated.
fn normalize_url(raw: &str) -> Option<String> {
    let t = raw.trim();
    if t.is_empty() {
        return None;
    }
    if t.starts_with("dregg://") || t.starts_with("http://") || t.starts_with("https://") {
        return Some(t.to_string());
    }
    // A bare host (`example.com`, `a.b/c`) — default to https. Reject a token with
    // no dot and no slash (it is not a host), and anything with whitespace.
    if t.contains(char::is_whitespace) {
        return None;
    }
    if t.contains('.') {
        return Some(format!("https://{t}"));
    }
    None
}

/// A web-shell toolbar button (← → ⟳ Go) — a small kit `Button` running a
/// `&mut Cockpit` nav method. Mirrors [`shell_button`], with a caller-supplied
/// stable element id (the labels are glyphs, not unique strings).
fn nav_button(
    cx: &mut Context<Cockpit>,
    label: &str,
    id: &str,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    button_variant(Button::new(SharedString::from(id.to_string())).label(label.to_string()), color)
        .small()
        .on_click(cx.listener(move |this, _ev: &ClickEvent, _window, cx| {
            handler(this, cx);
        }))
}

#[cfg(test)]
mod tests {
    use super::normalize_url;

    #[test]
    fn normalize_passes_through_full_urls() {
        assert_eq!(normalize_url("https://example.com").as_deref(), Some("https://example.com"));
        assert_eq!(normalize_url("http://a.b/c").as_deref(), Some("http://a.b/c"));
        assert_eq!(normalize_url("dregg://cell/0").as_deref(), Some("dregg://cell/0"));
    }

    #[test]
    fn normalize_defaults_bare_hosts_to_https() {
        assert_eq!(normalize_url("example.com").as_deref(), Some("https://example.com"));
        assert_eq!(normalize_url("  a.b/c  ").as_deref(), Some("https://a.b/c"));
    }

    #[test]
    fn normalize_rejects_non_urls() {
        assert_eq!(normalize_url(""), None);
        assert_eq!(normalize_url("   "), None);
        assert_eq!(normalize_url("not a url"), None); // whitespace
        assert_eq!(normalize_url("noscheme"), None); // no dot, no scheme
    }
}
