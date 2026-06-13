//! Starbridge v2 — the native (gpui) dregg ocap shell.
//!
//! Opens a window and assembles the shell: a persistent left rail (node
//! status + the CellList) and a main split (the ReceiptInspector and the
//! TurnComposer). The layout mirrors the web Starbridge shell
//! (`site/src/starbridge/index.html`): you boot into one persistent frame
//! that shows who/where you are, your cells, and the node's receipt stream.
//!
//! THE NODE: by default the shell boots against an in-process MOCK
//! ([`NodeClient::mock`]) so a `cargo run` opens a populated window with no
//! running node. Pass a node base URL as the first arg to point at a real
//! node:
//!
//!   starbridge-v2 http://127.0.0.1:8080
//!
//! See `docs/STARBRIDGE-V2.md` for the architecture and the honest
//! scaffolded-vs-build-out scope.

mod client;
mod model;
mod views;

use gpui::{
    div, prelude::*, px, size, App, Bounds, Context, IntoElement, ParentElement, Render, Styled,
    TitlebarOptions, Window, WindowBounds, WindowOptions,
};
use gpui_platform::application;

use client::NodeClient;
use model::NodeStatus;
use views::cell_list::CellList;
use views::receipt_inspector::ReceiptInspector;
use views::turn_composer::TurnComposer;
use views::{pill, theme};

/// The shell root — owns the node client and the three core views.
struct Starbridge {
    client: NodeClient,
    status: Option<NodeStatus>,
    cell_list: gpui::Entity<CellList>,
    receipts: gpui::Entity<ReceiptInspector>,
    composer: gpui::Entity<TurnComposer>,
}

impl Starbridge {
    fn new(client: NodeClient, cx: &mut Context<Self>) -> Self {
        let status = client.status().ok();
        let cell_list = cx.new(|_| CellList::new(client.clone()));
        let receipts = cx.new(|_| ReceiptInspector::new(client.clone()));
        let composer = cx.new(|_| TurnComposer::new(client.clone()));
        Self {
            client,
            status,
            cell_list,
            receipts,
            composer,
        }
    }

    fn rail_header(&self) -> impl IntoElement {
        let (producer, producer_color) = match &self.status {
            Some(s) if s.lean_producer => ("lean producer", theme::good()),
            Some(_) => ("rust producer", theme::warn()),
            None => ("offline", theme::bad()),
        };
        let height = self.status.as_ref().map(|s| s.dag_height).unwrap_or(0);

        div()
            .flex()
            .flex_col()
            .gap_1()
            .p_3()
            .border_b_1()
            .border_color(theme::border())
            .child(
                div()
                    .text_lg()
                    .text_color(theme::text())
                    .child("Starbridge"),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child("the native shell of your polis"),
            )
            .child(
                div()
                    .flex()
                    .gap_2()
                    .mt_2()
                    .child(pill(producer, producer_color.into()))
                    .child(pill(format!("h{height}"), theme::accent())),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(format!("node: {}", self.client.describe())),
            )
    }
}

impl Render for Starbridge {
    fn render(&mut self, _window: &mut Window, _cx: &mut Context<Self>) -> impl IntoElement {
        div()
            .flex()
            .size_full()
            .bg(theme::bg())
            .text_color(theme::text())
            .font_family("monospace")
            // Left rail: identity/node + your cells.
            .child(
                div()
                    .flex()
                    .flex_col()
                    .w(px(300.))
                    .h_full()
                    .border_r_1()
                    .border_color(theme::border())
                    .bg(theme::panel())
                    .child(self.rail_header())
                    .child(div().flex_1().child(self.cell_list.clone())),
            )
            // Main split: receipt inspector + turn composer.
            .child(
                div()
                    .flex()
                    .flex_1()
                    .h_full()
                    .child(
                        div()
                            .flex()
                            .flex_col()
                            .w(px(420.))
                            .h_full()
                            .border_r_1()
                            .border_color(theme::border())
                            .child(self.receipts.clone()),
                    )
                    .child(div().flex_1().h_full().child(self.composer.clone())),
            )
    }
}

fn main() {
    // First arg = node base URL; absent → mock.
    let client = match std::env::args().nth(1) {
        Some(url) if url.starts_with("http") => NodeClient::http(url),
        _ => NodeClient::mock(),
    };

    application().run(move |cx: &mut App| {
        let bounds = Bounds::centered(None, size(px(1200.), px(760.)), cx);
        cx.open_window(
            WindowOptions {
                window_bounds: Some(WindowBounds::Windowed(bounds)),
                titlebar: Some(TitlebarOptions {
                    title: Some("Starbridge v2".into()),
                    ..Default::default()
                }),
                ..Default::default()
            },
            |_window, cx| cx.new(|cx| Starbridge::new(client.clone(), cx)),
        )
        .expect("failed to open window");
        cx.activate(true);
    });
}
