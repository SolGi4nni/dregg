//! CellList — the cells the connected node knows about.
//!
//! Mirrors the web shell's "your cells" rail section, expanded to a browser.
//! Each row shows id (truncated), balance (signed — issuer wells carry
//! −supply), nonce, capability count, and program/delegate badges. Selecting
//! a cell is the entry point for the ReceiptInspector / TurnComposer to scope
//! to it (wiring the selection across views is a build-out lane).

use gpui::{
    div, prelude::*, Context, Hsla, IntoElement, ParentElement, Render, SharedString, Styled,
    Window,
};

use crate::client::NodeClient;
use crate::model::{short_id, CellListEntry};
use crate::views::{section_title, theme};

pub struct CellList {
    client: NodeClient,
    cells: Vec<CellListEntry>,
    selected: Option<SharedString>,
    error: Option<SharedString>,
}

impl CellList {
    pub fn new(client: NodeClient) -> Self {
        let (cells, error) = match client.cells() {
            Ok(c) => (c, None),
            Err(e) => (Vec::new(), Some(SharedString::from(e.to_string()))),
        };
        Self {
            client,
            cells,
            selected: None,
            error,
        }
    }

    pub fn refresh(&mut self) {
        match self.client.cells() {
            Ok(c) => {
                self.cells = c;
                self.error = None;
            }
            Err(e) => self.error = Some(SharedString::from(e.to_string())),
        }
    }

    pub fn selected(&self) -> Option<&SharedString> {
        self.selected.as_ref()
    }

    fn row(&self, cell: &CellListEntry) -> impl IntoElement {
        let is_issuer = cell.balance < 0;
        let bal_color: Hsla = if is_issuer { theme::warn() } else { theme::good() }.into();
        let badges = {
            let mut b: Vec<&str> = Vec::new();
            if cell.has_program {
                b.push("program");
            }
            if cell.has_delegate {
                b.push("delegate");
            }
            b
        };

        div()
            .flex()
            .flex_col()
            .gap_1()
            .px_3()
            .py_2()
            .border_b_1()
            .border_color(theme::border())
            .hover(|s| s.bg(theme::panel_hi()))
            .child(
                div()
                    .flex()
                    .justify_between()
                    .child(
                        div()
                            .text_sm()
                            .text_color(theme::text())
                            .font_family("monospace")
                            .child(short_id(&cell.id)),
                    )
                    .child(
                        div()
                            .text_sm()
                            .text_color(bal_color)
                            .child(format!("{}", cell.balance)),
                    ),
            )
            .child(
                div()
                    .flex()
                    .gap_2()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(format!("nonce {}", cell.nonce))
                    .child(format!("{} caps", cell.capability_count))
                    .children(
                        badges
                            .into_iter()
                            .map(|b| div().text_color(theme::accent()).child(b)),
                    ),
            )
    }
}

impl Render for CellList {
    fn render(&mut self, _window: &mut Window, _cx: &mut Context<Self>) -> impl IntoElement {
        div()
            .flex()
            .flex_col()
            .h_full()
            .bg(theme::panel())
            .child(
                div()
                    .px_3()
                    .py_2()
                    .border_b_1()
                    .border_color(theme::border())
                    .child(section_title(format!("Cells · {}", self.cells.len()))),
            )
            .when_some(self.error.clone(), |this, err| {
                this.child(
                    div()
                        .px_3()
                        .py_2()
                        .text_xs()
                        .text_color(theme::bad())
                        .child(err),
                )
            })
            .child(
                div()
                    .flex()
                    .flex_col()
                    .overflow_hidden()
                    .children(self.cells.iter().map(|c| self.row(c))),
            )
    }
}
