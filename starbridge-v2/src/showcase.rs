//! THE SHOWCASE BAKE — one gorgeous headless render of the full working deos
//! desktop: every dev surface mounted, populated, and visibly real.
//!
//! This is the money shot. A single high-res PNG of the deos cockpit with a
//! curated multi-pane layout, every pane seeded with real demo content drawn
//! through the REAL surface code (no mockups of the surfaces — the actual
//! `deos_matrix` chat, `deos_zed` editor, `deos_terminal` grid, and `deos_hermes`
//! agent ledger, each rendered offscreen via the same gpui headless path the
//! cockpit bake uses).
//!
//! The panes (all REAL surfaces, seeded deterministically — no live PTY, no live
//! node, no network):
//!
//!   * CHAT — `deos_matrix` over `MockSource::seeded`, with the MEMBRANE CARD
//!     prominent: a chat message that carries a cap-bounded fork of the world,
//!     rehydratable, fail-closed on stitch. The thing post-urbit cannot have.
//!   * EDITOR — `deos_zed` over a seeded in-memory document: real syntax-
//!     highlighted Rust + a real `N patches · on-ledger` status, file tree over
//!     the real repo on the left.
//!   * TERMINAL — `deos_terminal` grid driven by a recorded `cargo`/`git` shell
//!     session (deterministic, no `$SHELL` race).
//!   * AGENT — `deos_hermes` `AgentPane::demo`: the confined-Hermes tool-call
//!     ledger — a green ✓ receipted call + a red ✗ refused call + the live
//!     mandate inspector.
//!
//! The chrome the showcase composes itself: a session bar (identity · height ·
//! verified · BALANCE_SUM=0), a cell-world rail (the four verified substances +
//! the conservation invariant read off the real ledger), and a dock strip. Every
//! number in the chrome is read from the real `world::demo_world` image.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use gpui::{
    div, px, App, AppContext, Context, Entity, FocusHandle, Focusable, InteractiveElement,
    IntoElement, ParentElement, Render, Styled, Window,
};

use crate::dock::chat_surface::ChatPane;
use crate::dock::editor_surface::EditorPane;
use crate::dock::hermes_surface::AgentPane;
use crate::dock::surface::CockpitSurface;
use crate::dock::terminal_surface::TerminalPane;
use crate::world::World;

/// The showcase palette — a self-contained mirror of the dock's GitHub-dark
/// values (the dock's `theme` module is private to the dock; this keeps the
/// showcase from reaching into a sibling-owned module). `gpui::rgb` isn't `const`
/// in this rev, so these are functions returning `Hsla`.
mod theme {
    use gpui::{rgb, Hsla};
    pub fn bg() -> Hsla {
        rgb(0x0e1116).into()
    }
    pub fn panel() -> Hsla {
        rgb(0x161b22).into()
    }
    pub fn panel_hi() -> Hsla {
        rgb(0x1f2630).into()
    }
    pub fn border() -> Hsla {
        rgb(0x2b3340).into()
    }
    pub fn text() -> Hsla {
        rgb(0xd7dee8).into()
    }
    pub fn muted() -> Hsla {
        rgb(0x7d8794).into()
    }
    pub fn accent() -> Hsla {
        rgb(0x6cb6ff).into()
    }
}

/// A read-off-the-real-image summary of the cell world, computed once at build
/// time from the seeded `demo_world` ledger. Every figure is a fact of the live
/// verified image, not a mock.
struct CellWorld {
    cell_count: usize,
    balance_sum: i64,
    height: u64,
}

impl CellWorld {
    fn read(world: &World) -> Self {
        let mut cell_count = 0usize;
        let mut balance_sum: i64 = 0;
        for (_, cell) in world.ledger().iter() {
            cell_count += 1;
            balance_sum += cell.state.balance();
        }
        CellWorld {
            cell_count,
            balance_sum,
            height: world.height(),
        }
    }
}

/// The showcase root view — owns the seeded surfaces + the cell-world summary and
/// lays them out as the curated desktop money shot.
pub struct ShowcaseView {
    chat: ChatPane,
    editor: EditorPane,
    terminal: TerminalPane,
    agent: AgentPane,
    cells: CellWorld,
    focus: FocusHandle,
}

impl ShowcaseView {
    /// Build the showcase over the seeded demo image. All four surfaces are
    /// constructed and seeded here (each through its real surface code), and the
    /// cell-world chrome is read off the same `world`.
    pub fn build(world: Rc<RefCell<World>>, window: &mut Window, cx: &mut App) -> Self {
        let cells = CellWorld::read(&world.borrow());

        // CHAT — the deos-pilled Matrix chat over the recorded sync. `seeded`
        // already carries the membrane conversation + the membrane-bearing
        // message (the rehydrate card renders from the real `MembraneEnvelope`).
        let source: Arc<dyn deos_matrix::source::ChatSource> =
            Arc::new(deos_matrix::source::MockSource::seeded());
        let chat = ChatPane::new(1, source, window, cx);

        // EDITOR — a seeded in-memory document: a real, highlighted Rust slice
        // with a multi-revision (on-ledger) patch history. No disk load; the file
        // tree still roots at the real repo so the left rail shows a live project.
        let repo_root = std::env::current_dir()
            .ok()
            .and_then(|d| d.parent().map(|p| p.to_path_buf()))
            .unwrap_or_else(|| std::path::PathBuf::from("."));
        let editor = EditorPane::seeded(
            2,
            deos_zed::fs::RealFs::arc(),
            repo_root,
            "showcase.rs",
            &EDITOR_REVISIONS,
            window,
            cx,
        );

        // TERMINAL — a recorded `cargo`/`git` session fed straight through the VTE
        // parser into the grid. Deterministic; no live shell.
        let terminal = TerminalPane::seeded(3, 96, 26, TERMINAL_SESSION.as_bytes(), cx);

        // AGENT — the confined-Hermes tool-call ledger: a real `HermesGateway`
        // admitting one ALLOWED+receipted call and one REFUSED call, plus the
        // rendered mandate inspector.
        let agent = AgentPane::demo(4, window, cx);

        Self {
            chat,
            editor,
            terminal,
            agent,
            cells,
            focus: cx.focus_handle(),
        }
    }

    /// The top session bar — the cockpit chrome: deos mark, the logged-in
    /// identity, the verified-image badges, the height and conservation invariant.
    fn session_bar(&self) -> impl IntoElement {
        div()
            .flex()
            .items_center()
            .gap_3()
            .px_4()
            .py_2()
            .w_full()
            .bg(theme::panel())
            .border_b_1()
            .border_color(theme::border())
            .child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .child(
                        div()
                            .text_color(theme::accent())
                            .text_lg()
                            .font_weight(gpui::FontWeight::BOLD)
                            .child("◈ deos"),
                    )
                    .child(
                        div()
                            .text_color(theme::muted())
                            .text_xs()
                            .child("the verified ocap desktop"),
                    ),
            )
            .child(div().flex_1())
            .child(badge("@ember:deos.local", theme::text()))
            .child(badge("● seL4 image", theme::accent()))
            .child(badge(
                &format!("✓ verified · height {}", self.cells.height),
                rgb_ok(),
            ))
            .child(badge(
                &format!("Σδ = {} · conserved", self.cells.balance_sum),
                rgb_ok(),
            ))
    }

    /// The left cell-world rail — the four verified substances and the
    /// conservation invariant, the Pharo-style live inspector face of the image.
    fn cell_rail(&self) -> impl IntoElement {
        let substances = [
            ("⛁ value", "the conserved fungible — Σδ=0 every turn", rgb_value()),
            ("⛃ authority", "production under non-forgeability", rgb_auth()),
            ("⛂ availability", "fresh-at-settlement liveness", rgb_avail()),
            ("⛀ knowledge", "attested reads · receipted writes", rgb_know()),
        ];
        let mut rail = div()
            .flex()
            .flex_col()
            .gap_3()
            .w(px(248.))
            .h_full()
            .p_3()
            .bg(theme::panel())
            .border_r_1()
            .border_color(theme::border())
            .child(
                div()
                    .text_color(theme::muted())
                    .text_xs()
                    .font_weight(gpui::FontWeight::SEMIBOLD)
                    .child("CELL WORLD · the live image"),
            )
            .child(
                div()
                    .flex()
                    .items_baseline()
                    .gap_2()
                    .child(
                        div()
                            .text_color(theme::text())
                            .text_2xl()
                            .font_weight(gpui::FontWeight::BOLD)
                            .child(format!("{}", self.cells.cell_count)),
                    )
                    .child(
                        div()
                            .text_color(theme::muted())
                            .text_xs()
                            .child("sovereign cells"),
                    ),
            );

        for (name, blurb, color) in substances {
            rail = rail.child(
                div()
                    .flex()
                    .flex_col()
                    .gap_1()
                    .p_2()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .border_l_2()
                    .border_color(color)
                    .child(
                        div()
                            .text_color(color)
                            .text_sm()
                            .font_weight(gpui::FontWeight::SEMIBOLD)
                            .child(name),
                    )
                    .child(div().text_color(theme::muted()).text_xs().child(blurb)),
            );
        }

        rail.child(div().flex_1()).child(
            div()
                .flex()
                .flex_col()
                .gap_1()
                .p_2()
                .rounded_md()
                .bg(theme::panel_hi())
                .child(
                    div()
                        .text_color(rgb_ok())
                        .text_sm()
                        .font_weight(gpui::FontWeight::SEMIBOLD)
                        .child(format!("BALANCE_SUM = {}", self.cells.balance_sum)),
                )
                .child(
                    div()
                        .text_color(theme::muted())
                        .text_xs()
                        .child("the executor proved it · every turn"),
                ),
        )
    }

    /// The MEMBRANE CARD — the eye-catching callout above the chat: a chat
    /// message IS a cap-bounded fork of the world. This is the deos-only thing.
    fn membrane_card(&self) -> impl IntoElement {
        div()
            .flex()
            .flex_col()
            .gap_2()
            .p_3()
            .rounded_lg()
            .bg(gpui::rgb(0x161f2e))
            .border_1()
            .border_color(theme::accent())
            .child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .child(
                        div()
                            .text_color(theme::accent())
                            .text_sm()
                            .font_weight(gpui::FontWeight::BOLD)
                            .child("⬡ deos membrane"),
                    )
                    .child(
                        div()
                            .text_color(theme::muted())
                            .text_xs()
                            .child("a cap-bounded fork of the world"),
                    ),
            )
            .child(
                div()
                    .flex()
                    .gap_4()
                    .child(membrane_stat("4 cells", "carried"))
                    .child(membrane_stat("real turns", "drives"))
                    .child(membrane_stat("fail-closed", "stitches back")),
            )
            .child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .child(
                        div()
                            .px_3()
                            .py_1()
                            .rounded_md()
                            .bg(theme::accent())
                            .text_color(gpui::rgb(0x0e1116))
                            .text_xs()
                            .font_weight(gpui::FontWeight::SEMIBOLD)
                            .child("▶ rehydrate"),
                    )
                    .child(
                        div()
                            .text_color(theme::muted())
                            .text_xs()
                            .child("open the fork · drive it · stitch the diff back"),
                    ),
            )
    }

    /// A titled surface frame: a small header strip + the surface body, so each
    /// pane reads as a distinct, labelled window in the layout.
    fn framed(
        title: &str,
        subtitle: &str,
        body: gpui::AnyElement,
    ) -> impl IntoElement {
        div()
            .flex()
            .flex_col()
            .flex_1()
            .min_h(px(0.))
            .overflow_hidden()
            .rounded_lg()
            .bg(theme::bg())
            .border_1()
            .border_color(theme::border())
            .child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .px_3()
                    .py_1()
                    .bg(theme::panel())
                    .border_b_1()
                    .border_color(theme::border())
                    .child(
                        div()
                            .text_color(theme::text())
                            .text_xs()
                            .font_weight(gpui::FontWeight::SEMIBOLD)
                            .child(title.to_string()),
                    )
                    .child(
                        div()
                            .text_color(theme::muted())
                            .text_xs()
                            .child(subtitle.to_string()),
                    ),
            )
            .child(div().flex_1().min_h(px(0.)).overflow_hidden().child(body))
    }
}

impl Focusable for ShowcaseView {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus.clone()
    }
}

impl Render for ShowcaseView {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let chat_body = self.chat.render_body(window, cx);
        let agent_body = self.agent.render_body(window, cx);
        let editor_body = self.editor.render_body(window, cx);
        let terminal_body = self.terminal.render_body(window, cx);

        // LEFT COLUMN: the social/agent loop — chat (with the membrane callout on
        // top) above the Hermes tool-call ledger.
        let left_column = div()
            .flex()
            .flex_col()
            .gap_3()
            .flex_1()
            .min_w(px(0.))
            .h_full()
            .child(self.membrane_card())
            .child(Self::framed(
                "chat · deos-matrix",
                "membrane-bearing rooms · MockSource",
                chat_body,
            ))
            .child(Self::framed(
                "agent · confined Hermes",
                "tool-call ledger · ✓ receipted / ✗ refused · mandate",
                agent_body,
            ));

        // RIGHT COLUMN: the self-hosting dev loop — the editor over a seeded
        // on-ledger document, above a recorded terminal session.
        let right_column = div()
            .flex()
            .flex_col()
            .gap_3()
            .flex_1()
            .min_w(px(0.))
            .h_full()
            .child(Self::framed(
                "editor · deos-zed",
                "syntax-highlit · on-ledger patches",
                editor_body,
            ))
            .child(Self::framed(
                "terminal · deos-terminal",
                "recorded cargo/git session",
                terminal_body,
            ));

        div()
            .key_context("Showcase")
            .track_focus(&self.focus)
            .flex()
            .flex_col()
            .size_full()
            .bg(theme::bg())
            .text_color(theme::text())
            .font_family("Menlo")
            .child(self.session_bar())
            .child(
                div()
                    .flex()
                    .flex_1()
                    .min_h(px(0.))
                    .w_full()
                    .child(self.cell_rail())
                    .child(
                        div()
                            .flex()
                            .gap_3()
                            .flex_1()
                            .min_w(px(0.))
                            .h_full()
                            .p_3()
                            .child(left_column)
                            .child(right_column),
                    ),
            )
            .child(dock_strip())
    }
}

/// Mount the showcase as a root view for the headless capture.
pub fn build_root(
    world: Rc<RefCell<World>>,
    window: &mut Window,
    cx: &mut App,
) -> Entity<ShowcaseView> {
    let view = cx.new(|cx| ShowcaseView::build(world, window, cx));
    view.update(cx, |v, cx| {
        let focus = v.focus.clone();
        focus.focus(window, cx);
    });
    view
}

// --- chrome helpers ---------------------------------------------------------

fn badge(text: &str, color: gpui::Hsla) -> impl IntoElement {
    div()
        .px_2()
        .py_1()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
        .text_color(color)
        .text_xs()
        .child(text.to_string())
}

fn membrane_stat(value: &str, label: &str) -> impl IntoElement {
    div()
        .flex()
        .flex_col()
        .child(
            div()
                .text_color(theme::text())
                .text_sm()
                .font_weight(gpui::FontWeight::SEMIBOLD)
                .child(value.to_string()),
        )
        .child(div().text_color(theme::muted()).text_xs().child(label.to_string()))
}

/// The bottom dock strip — the app shelf, a clean row of the mounted surfaces.
fn dock_strip() -> impl IntoElement {
    let apps = [
        "◈ home",
        "⬡ chat",
        "✎ editor",
        "▷ terminal",
        "✦ agent",
        "⛁ cells",
        "◷ time-travel",
        "⚙ inspector",
    ];
    let mut row = div()
        .flex()
        .items_center()
        .justify_center()
        .gap_2()
        .w_full()
        .px_4()
        .py_2()
        .bg(theme::panel())
        .border_t_1()
        .border_color(theme::border());
    for (i, app) in apps.iter().enumerate() {
        let active = i == 0;
        row = row.child(
            div()
                .px_3()
                .py_1()
                .rounded_md()
                .bg(if active { theme::panel_hi() } else { theme::panel() })
                .border_1()
                .border_color(if active { theme::accent() } else { theme::border() })
                .text_color(if active { theme::accent() } else { theme::muted() })
                .text_xs()
                .child(app.to_string()),
        );
    }
    row
}

fn rgb_ok() -> gpui::Hsla {
    gpui::rgb(0x57d97f).into()
}
fn rgb_value() -> gpui::Hsla {
    gpui::rgb(0xf2c14e).into()
}
fn rgb_auth() -> gpui::Hsla {
    gpui::rgb(0xff8b6b).into()
}
fn rgb_avail() -> gpui::Hsla {
    gpui::rgb(0x6cb6ff).into()
}
fn rgb_know() -> gpui::Hsla {
    gpui::rgb(0xc792ea).into()
}

/// The seeded editor document: successive on-ledger revisions of a small,
/// real-looking Rust slice (the LAST is shown; the priors make the patch count
/// real). Chosen to highlight well and read as genuine deos code.
const EDITOR_REVISIONS: [&str; 3] = [
    "/// A turn is the exercise of an attenuable proof-carrying token\n/// over owned state, leaving a verifiable receipt.\npub fn commit_turn(world: &mut World, turn: Turn) -> Receipt {\n    let receipt = world.execute(turn);\n    receipt\n}\n",
    "/// A turn is the exercise of an attenuable proof-carrying token\n/// over owned state, leaving a verifiable receipt.\npub fn commit_turn(world: &mut World, turn: Turn) -> Result<Receipt> {\n    world.check_authority(&turn)?;\n    let receipt = world.execute(turn)?;\n    Ok(receipt)\n}\n",
    "//! The single seam: every effect is one cap-gated, conserving turn.\n\nuse crate::{World, Turn, Receipt, Result};\n\n/// A turn is the exercise of an attenuable proof-carrying token over\n/// owned state, leaving a verifiable receipt. Authority is PRODUCTION\n/// under non-forgeability; value conserves (Σδ = 0) every turn.\npub fn commit_turn(world: &mut World, turn: Turn) -> Result<Receipt> {\n    // 1. The gate: authority + freshness + non-amplification, in-circuit.\n    world.check_authority(&turn)?;\n    world.check_conservation(&turn)?;\n\n    // 2. The exercise: run the turn through the verified executor.\n    let receipt = world.execute(turn)?;\n\n    // 3. The witness: a receipt a light client can't be fooled about.\n    debug_assert!(receipt.conserves());\n    Ok(receipt)\n}\n",
];

/// The recorded terminal session — a deterministic `cargo`/`git` run, fed
/// straight into the grid (no live shell). ANSI SGR colors a few tokens so the
/// grid reads like a real session. `\r\n` line breaks (terminal convention).
const TERMINAL_SESSION: &str = concat!(
    "\x1b[32member@deos\x1b[0m:\x1b[34m~/dev/breadstuffs\x1b[0m$ cargo build --release\r\n",
    "   \x1b[32mCompiling\x1b[0m dregg-cell v0.3.0\r\n",
    "   \x1b[32mCompiling\x1b[0m dregg-turn v0.3.0\r\n",
    "   \x1b[32mCompiling\x1b[0m starbridge-v2 v2.0.0\r\n",
    "    \x1b[32mFinished\x1b[0m `release` profile [optimized] in 41.2s\r\n",
    "\x1b[32member@deos\x1b[0m:\x1b[34m~/dev/breadstuffs\x1b[0m$ git log --oneline -3\r\n",
    "\x1b[33m2aeab36\x1b[0m deos: SESSION RESUME reopens the EXACT durable image\r\n",
    "\x1b[33m87c6ddd\x1b[0m node/channels: back the channels service on the Bus\r\n",
    "\x1b[33m8e133c3\x1b[0m deos-matrix: nheko-parity Matrix UX + dregg objects\r\n",
    "\x1b[32member@deos\x1b[0m:\x1b[34m~/dev/breadstuffs\x1b[0m$ cargo test -p dregg-turn\r\n",
    "test executor::conserves_every_turn ... \x1b[32mok\x1b[0m\r\n",
    "test circuit::light_client_unfoolable ... \x1b[32mok\x1b[0m\r\n",
    "\x1b[32mtest result: ok.\x1b[0m 312 passed; 0 failed\r\n",
    "\x1b[32member@deos\x1b[0m:\x1b[34m~/dev/breadstuffs\x1b[0m$ \x1b[5m▋\x1b[0m\r\n",
);
