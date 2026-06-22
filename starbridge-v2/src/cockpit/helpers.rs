//! Pure render helpers shared across the panels: sorted cells, the per-`PresentationBody` widgets, the badges + the clickable button factories.

use super::*;

// --- small render helpers ---------------------------------------------------

/// The sorted live cells, freshly collected from the ledger. Used ONLY to seed /
/// refresh `Cockpit.cells` (construction + `refresh_cells`); every render-hot read
/// site routes through that cached `self.cells` instead (the M1 re-sort weld), so
/// the full `HashMap` drain+sort runs once per mutating handler, not per frame.
pub(crate) fn sorted_cells(w: &World) -> Vec<CellId> {
    let mut ids: Vec<CellId> = w.ledger().iter().map(|(id, _)| *id).collect();
    ids.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    ids
}

// ===========================================================================
// THE GENERIC PER-BODY RENDER HELPERS — one widget per `PresentationBody` variant.
// Pure (they read the body data the model already computed). The Fields + Prose
// variants are rendered inline by `render_presentation_body`; these cover the
// six structural visual kinds.
// ===========================================================================

/// Graph body — reuses the GRAPH tab's drawing vocabulary (nodes + directed
/// `holder ──rights──▶ target` edges), centered on the focused cell.
pub(crate) fn render_graph_body(g: &GraphView) -> impl IntoElement {
    let mut col = div().flex().flex_col().gap_0p5();
    col = col.child(div().text_xs().text_color(theme::muted()).child(format!(
        "{} node(s) · {} edge(s){}",
        g.nodes.len(),
        g.edges.len(),
        g.focus.map(|f| format!(" · focus ⬡ {}", reflect::short_hex(f.as_bytes()))).unwrap_or_default(),
    )));
    if g.edges.is_empty() {
        col = col.child(div().text_xs().text_color(theme::muted()).child("(no capability edges)"));
    }
    for e in g.edges.iter().take(24) {
        col = col.child(
            div()
                .flex()
                .justify_between()
                .px_2()
                .py_0p5()
                .child(div().text_xs().text_color(theme::text()).child(format!(
                    "⬡ {} ──▶ {}",
                    reflect::short_hex(e.holder.as_bytes()),
                    reflect::short_hex(e.target.as_bytes()),
                )))
                .child(div().text_xs().text_color(theme::accent()).child(format!("[{}]", e.rights_label()))),
        );
    }
    col
}

/// StateMachine body — states (terminal marked) + the current readout + the
/// directed verb transitions.
pub(crate) fn render_state_machine(sm: &StateMachineView) -> impl IntoElement {
    let mut col = div().flex().flex_col().gap_0p5();
    col = col.child(div().text_xs().text_color(theme::good()).child(format!("current: {}", sm.current)));
    let mut states_row = div().flex().flex_wrap().gap_1();
    for st in &sm.states {
        let active = st.name == sm.current;
        let color = if active {
            theme::accent()
        } else if st.terminal {
            theme::warn()
        } else {
            theme::muted()
        };
        states_row = states_row.child(pill(
            if st.terminal { format!("{} ⊣", st.name) } else { st.name.clone() },
            color,
        ));
    }
    col = col.child(states_row);
    col = col.child(div().text_xs().text_color(theme::muted()).mt_1().child("transitions"));
    for t in &sm.transitions {
        col = col.child(div().text_xs().text_color(theme::text()).child(format!(
            "{} ──{}──▶ {}",
            t.from, t.verb, t.to
        )));
    }
    col
}

/// Gauge body — a bounded value (drawn / ceiling) drawn as a simple bar, with the
/// named ratchet rungs.
pub(crate) fn render_gauge(g: &GaugeView) -> impl IntoElement {
    let frac: f32 = match g.ceiling {
        Some(c) if c > 0 => (g.value as f32 / c as f32).clamp(0.0, 1.0),
        _ => 0.0,
    };
    let mut col = div().flex().flex_col().gap_0p5();
    col = col.child(div().text_xs().text_color(theme::text()).child(format!(
        "{}: {}{}",
        g.label,
        g.value,
        g.ceiling.map(|c| format!(" / {c}")).unwrap_or_else(|| " (unbounded)".into()),
    )));
    if g.ceiling.is_some() {
        col = col.child(
            div()
                .w_full()
                .h(px(8.))
                .rounded_md()
                .bg(theme::panel_hi())
                .child(
                    div()
                        .h(px(8.))
                        .w(gpui::relative(frac))
                        .rounded_md()
                        .bg(if frac > 0.9 { theme::bad() } else { theme::accent() }),
                ),
        );
    }
    if !g.rungs.is_empty() {
        let mut rungs = div().flex().flex_wrap().gap_1();
        for r in &g.rungs {
            rungs = rungs.child(pill(r.clone(), theme::muted()));
        }
        col = col.child(rungs);
    }
    col
}

/// Timeline body — ordered events (a receipt chain / epoch history / lineage), each
/// with its monotone key + an optional navigable hash.
pub(crate) fn render_timeline(t: &TimelineView) -> impl IntoElement {
    let mut col = div().flex().flex_col().gap_0p5();
    if t.events.is_empty() {
        col = col.child(div().text_xs().text_color(theme::muted()).child("(no events yet)"));
    }
    for e in t.events.iter().take(32) {
        col = col.child(
            div()
                .flex()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).min_w(px(28.)).child(format!("#{}", e.at)))
                .child(div().text_xs().text_color(theme::text()).child(e.label.clone()))
                .when(e.hash.is_some(), |d| {
                    d.child(pill(reflect::short_hex(&e.hash.unwrap()), theme::good()))
                }),
        );
    }
    col
}

/// MerkleTree body — leaves + the committed root + an optional highlighted path.
pub(crate) fn render_merkle(m: &MerkleTreeView) -> impl IntoElement {
    let mut col = div().flex().flex_col().gap_0p5();
    col = col.child(div().text_xs().text_color(theme::text()).child(format!("{} · {} leaf/leaves", m.label, m.leaves.len())));
    col = col.child(
        div()
            .flex()
            .gap_1()
            .child(div().text_xs().text_color(theme::muted()).child("root:"))
            .child(pill(reflect::short_hex(&m.root), theme::accent())),
    );
    for (i, leaf) in m.leaves.iter().take(24).enumerate() {
        let on_path = m.path.contains(leaf);
        col = col.child(div().text_xs().text_color(if on_path { theme::good() } else { theme::muted() }).child(format!(
            "{} leaf[{i}] {}",
            if on_path { "▣" } else { "·" },
            leaf
        )));
    }
    col
}

/// Lattice body — a partial order (rights tiers / finality levels), with the live
/// current element + the covering relations.
pub(crate) fn render_lattice(l: &LatticeView) -> impl IntoElement {
    let mut col = div().flex().flex_col().gap_0p5();
    let mut nodes_row = div().flex().flex_wrap().gap_1();
    for (i, n) in l.nodes.iter().enumerate() {
        let active = l.current == Some(i);
        nodes_row = nodes_row.child(pill(
            if active { format!("● {n}") } else { n.clone() },
            if active { theme::accent() } else { theme::muted() },
        ));
    }
    col = col.child(nodes_row);
    col = col.child(div().text_xs().text_color(theme::muted()).mt_1().child("⊑ covering relations"));
    for (a, b) in &l.edges {
        if let (Some(na), Some(nb)) = (l.nodes.get(*a), l.nodes.get(*b)) {
            col = col.child(div().text_xs().text_color(theme::text()).child(format!("{na} ⊑ {nb}")));
        }
    }
    col
}

/// Trace body — step-by-step evaluation (an HMAC chain / constraint eval / absorb),
/// numbered in evaluation order.
pub(crate) fn render_trace(t: &TraceView) -> impl IntoElement {
    let mut col = div().flex().flex_col().gap_0p5();
    if t.steps.is_empty() {
        col = col.child(div().text_xs().text_color(theme::muted()).child("(no steps)"));
    }
    for s in t.steps.iter().take(32) {
        col = col.child(
            div()
                .flex()
                .gap_1()
                .child(div().text_xs().text_color(theme::muted()).min_w(px(24.)).child(format!("{}.", s.index)))
                .child(div().text_xs().text_color(theme::text()).child(s.label.clone())),
        );
    }
    col
}

/// A human reason for a refused shell op (the window-manager ocap guarantee
/// firing). Surfaced in the outcome banner the same way the executor's
/// rejections are — a refusal is a feature, not an error to hide.
pub(crate) fn shell_err(e: &starbridge_v2::shell::ShellError) -> String {
    use starbridge_v2::shell::ShellError;
    match e {
        ShellError::Unauthorized => "no valid capability presented (no ambient authority)".to_string(),
        ShellError::NoSuchSurface(id) => format!("surface {} does not exist", id.as_u64()),
        ShellError::ConsoleProtected => "the system console is the trusted root (cannot close)".to_string(),
        ShellError::ShareDenied(why) => format!("widening share refused by the executor: {why}"),
        // The verified-scene tooth that bit (T1 overpaint / T2 spoof / T3
        // misroute|double-focus), surfaced for the operator log.
        ShellError::PresentRefused(p) => p.explain(),
    }
}

pub(crate) fn kind_badge(kind: ObjectKind) -> impl IntoElement {
    let (label, color) = match kind {
        ObjectKind::Cell => ("cell", theme::accent()),
        ObjectKind::Receipt => ("receipt", theme::good()),
        ObjectKind::Capability => ("capability", theme::accent()),
        ObjectKind::Image => ("image", theme::warn()),
        ObjectKind::Proof => ("proof", theme::good()),
        ObjectKind::Factory => ("factory", theme::accent()),
        ObjectKind::Nullifier => ("nullifier", theme::warn()),
        ObjectKind::Document => ("document", theme::accent()),
    };
    div().mb_2().child(pill(label, color))
}

/// A short label + color for a cell's lifecycle state (the OBJECTS panel's
/// lifecycle column). Matches the protocol's `CellLifecycle` variants.
pub(crate) fn lifecycle_badge(lc: &dregg_cell::lifecycle::CellLifecycle) -> (&'static str, Hsla) {
    use dregg_cell::lifecycle::CellLifecycle;
    match lc {
        CellLifecycle::Live => ("live", theme::good()),
        CellLifecycle::Sealed { .. } => ("sealed", theme::warn()),
        CellLifecycle::Destroyed { .. } => ("destroyed", theme::bad()),
        CellLifecycle::Migrated { .. } => ("migrated", theme::muted()),
        CellLifecycle::Archived { .. } => ("archived", theme::accent()),
    }
}

/// A compact row for a reflected object (the cipherclerk panel's identity /
/// token / delegation entries), showing its title, kind badge, and fields.
pub(crate) fn inspectable_row(ins: &Inspectable) -> impl IntoElement {
    let mut col = div()
        .flex()
        .flex_col()
        .gap_0p5()
        .px_2()
        .py_1()
        .rounded_md()
        .bg(theme::panel())
        .child(
            div()
                .flex()
                .justify_between()
                .child(div().text_xs().text_color(theme::text()).child(ins.title.clone()))
                .child(kind_badge(ins.kind)),
        )
        .child(div().text_xs().text_color(theme::muted()).child(ins.subtitle.clone()));
    for f in &ins.fields {
        col = col.child(field_row(f));
    }
    col
}

pub(crate) fn field_row(f: &Field) -> impl IntoElement {
    let (val, color): (String, Hsla) = match &f.value {
        FieldValue::Text(s) => (s.clone(), theme::text()),
        FieldValue::Balance(b) => (
            b.to_string(),
            if *b < 0 { theme::warn() } else { theme::text() },
        ),
        FieldValue::Count(c) => (c.to_string(), theme::text()),
        FieldValue::Bool(b) => (
            b.to_string(),
            if *b { theme::good() } else { theme::muted() },
        ),
        FieldValue::Id(id) => (reflect::short_hex(id), theme::accent()),
        FieldValue::Hash(h) => (reflect::short_hex(h), theme::good()),
        FieldValue::CapEdge { target, slot } => {
            (format!("→ {} (slot {slot})", reflect::short_hex(target)), theme::accent())
        }
        FieldValue::FieldSlot { hex, .. } => (reflect::short_hex_hexstr(hex), theme::muted()),
    };
    div()
        .flex()
        .justify_between()
        .py_0p5()
        .child(div().text_xs().text_color(theme::muted()).child(f.key.clone()))
        .child(div().text_xs().text_color(color).child(val))
}

/// Map a cockpit theme color onto the closest gpui-component [`Button`] semantic
/// variant. The cockpit speaks in `theme::good/warn/bad/accent/muted`; the kit
/// speaks in `.success()/.warning()/.danger()/.primary()/.ghost()`. This is the
/// ONE place the two vocabularies meet, so every migrated button reads in the
/// kit's coherent style while preserving the caller's semantic intent.
pub(crate) fn button_variant(b: Button, color: Hsla) -> Button {
    if color == theme::good() {
        b.success()
    } else if color == theme::warn() {
        b.warning()
    } else if color == theme::bad() {
        b.danger()
    } else if color == theme::accent() {
        b.primary()
    } else {
        // muted / text / anything else → the quiet ghost (a real component, not
        // a styled div), so a dimmed/disabled affordance still reads as a button.
        b.ghost()
    }
}

/// A verb button that runs a `&mut Cockpit` method through the listener — now a
/// real [`gpui_component::button::Button`] (the kit's variant + medium sizing),
/// so the COMPOSER's prominent verbs read like a component kit, not styled divs.
/// The click behavior is preserved exactly (it calls the same `&mut Cockpit`
/// method through `cx.listener`).
pub(crate) fn verb_button(
    cx: &mut Context<Cockpit>,
    label: &str,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    let id = SharedString::from(format!("verb-{label}"));
    button_variant(Button::new(id).label(label.to_string()), color).on_click(cx.listener(
        move |this, _ev: &ClickEvent, _window, cx| {
            handler(this, cx);
        },
    ))
}

/// A compact cipherclerk action button (smaller than a composer verb; the
/// clerk panel has four in a wrap row) — a small kit `Button`.
pub(crate) fn clerk_button(
    cx: &mut Context<Cockpit>,
    label: &str,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    let id = SharedString::from(format!("clerk-{label}"));
    button_variant(Button::new(id).label(label.to_string()), color)
        .small()
        .on_click(cx.listener(move |this, _ev: &ClickEvent, _window, cx| {
            handler(this, cx);
        }))
}

/// A compact action button with an EXPLICIT element id (so two buttons that share
/// a label don't collide) — the SIMULATE panel's build/run/commit verbs. A small
/// kit `Button`.
pub(crate) fn small_button(
    cx: &mut Context<Cockpit>,
    id: &'static str,
    label: &str,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    button_variant(Button::new(id).label(label.to_string()), color)
        .small()
        .on_click(cx.listener(move |this, _ev: &ClickEvent, _window, cx| {
            handler(this, cx);
        }))
}

/// A clickable "cycle" chip — the SIMULATE panel's agent/target/effect pickers
/// cycle their selection. An xsmall ghost-outline kit `Button` so it reads as a
/// compact pickable chip (lighter than the action verbs) while staying a real
/// component.
pub(crate) fn cycle_chip(
    cx: &mut Context<Cockpit>,
    id: &'static str,
    label: String,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    button_variant(Button::new(id).label(label), color)
        .xsmall()
        .outline()
        .on_click(cx.listener(move |this, _ev: &ClickEvent, _window, cx| {
            handler(this, cx);
        }))
}

/// Map a landing-portal [`Tone`](starbridge_v2::landing::Tone) (a semantic role,
/// kept gpui-free in the model) onto a theme color for the HOME render.
pub(crate) fn portal_tone_color(tone: starbridge_v2::landing::Tone) -> Hsla {
    use starbridge_v2::landing::Tone;
    match tone {
        Tone::Body => theme::text(),
        Tone::Muted => theme::muted(),
        Tone::Good => theme::good(),
        Tone::Accent => theme::accent(),
        Tone::Heading => theme::text(),
    }
}

/// A short label + color for a palette command's category badge.
pub(crate) fn category_badge(cat: Category) -> (&'static str, Hsla) {
    match cat {
        Category::Verb => (cat.label(), theme::good()),
        Category::Navigate => (cat.label(), theme::accent()),
        Category::Replay => (cat.label(), theme::warn()),
        Category::Clerk => (cat.label(), theme::accent()),
        Category::Shell => (cat.label(), theme::accent()),
        Category::Ide => (cat.label(), theme::good()),
        Category::Debug => (cat.label(), theme::warn()),
        Category::Inspect => (cat.label(), theme::muted()),
        Category::Palette => (cat.label(), theme::muted()),
    }
}

/// A short label + color for a surface's SHELL-DRAWN trusted-path lifecycle
/// badge (the anti-spoof identity chrome). Mirrors the shell's lifecycle strings.
pub(crate) fn identity_badge(lifecycle: &str) -> (&'static str, Hsla) {
    match lifecycle {
        "live" => ("live", theme::good()),
        "sealed" => ("sealed", theme::warn()),
        "destroyed" => ("destroyed", theme::bad()),
        "migrated" => ("migrated", theme::muted()),
        "archived" => ("archived", theme::accent()),
        "system" => ("system", theme::warn()),
        _ => ("missing", theme::bad()),
    }
}

/// A compact shell-toolbar button (the cap-first compositor's window ops). Same
/// shape as a clerk button; a small kit `Button` running a `&mut Cockpit` method.
pub(crate) fn shell_button(
    cx: &mut Context<Cockpit>,
    label: &str,
    color: Hsla,
    handler: fn(&mut Cockpit, &mut Context<Cockpit>),
) -> impl IntoElement {
    let id = SharedString::from(format!("shell-{label}"));
    button_variant(Button::new(id).label(label.to_string()), color)
        .small()
        .on_click(cx.listener(move |this, _ev: &ClickEvent, _window, cx| {
            handler(this, cx);
        }))
}

/// Convert a servo-render [`servo_render::RgbaFrame`] (RGBA8, row-major) into a
/// gpui [`gpui::RenderImage`] the cockpit paints with `img()`. gpui's
/// `RenderImage` holds **BGRA** frames (see `gpui::Image::to_image_data`, which
/// swaps R↔B after decode), so we swap the red/blue channels of the SWGL frame's
/// bytes the same way before wrapping them in an `image::Frame`. This is the SAME
/// raw-bytes -> `RenderImage::new(vec![Frame::new(buf)])` path the upstream
/// `repl::outputs::ImageView` uses — no parallel renderer, no re-fetch: just the
/// already-rendered cap-gated pixels handed to gpui.
#[cfg(feature = "servo")]
pub(crate) fn rgba_frame_to_image(frame: &servo_render::RgbaFrame) -> std::sync::Arc<gpui::RenderImage> {
    // Copy the RGBA8 bytes and swap R<->B in place to land in gpui's BGRA layout.
    let mut bgra = frame.bytes.clone();
    for px in bgra.chunks_exact_mut(4) {
        px.swap(0, 2);
    }
    let buffer = image::RgbaImage::from_raw(frame.width, frame.height, bgra)
        .expect("RgbaFrame carries width*height*4 RGBA8 bytes");
    std::sync::Arc::new(gpui::RenderImage::new(vec![image::Frame::new(buffer)]))
}
