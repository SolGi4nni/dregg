//! ReceiptInspector — the receipt stream + a per-receipt drill-in.
//!
//! Mirrors the web shell's "receipt stream" rail (SSE
//! `/api/events/stream`) plus the workbench's receipt inspector. Each row is
//! one committed turn; the inspector face shows the proof/finality/witness
//! state — the "inspector for receipts + proofs" the brief calls for.
//!
//! In the scaffold the list is a snapshot (`client.receipts()`); the LIVE SSE
//! stream that pushes new receipts is a build-out lane (it must be driven on
//! gpui's async executor and feed `cx.notify()` — see
//! docs/STARBRIDGE-V2.md §"Build-out lanes").

use gpui::{
    div, prelude::*, Context, Hsla, IntoElement, ParentElement, Render, SharedString, Styled,
    Window,
};

use crate::client::NodeClient;
use crate::model::{short_id, ReceiptEvent};
use crate::views::{pill, section_title, theme};

pub struct ReceiptInspector {
    client: NodeClient,
    receipts: Vec<ReceiptEvent>,
    selected: Option<usize>,
    error: Option<SharedString>,
}

impl ReceiptInspector {
    pub fn new(client: NodeClient) -> Self {
        let (receipts, error) = match client.receipts() {
            Ok(r) => (r, None),
            Err(e) => (Vec::new(), Some(SharedString::from(e.to_string()))),
        };
        Self {
            client,
            receipts,
            selected: receipts_default_selection(),
            error,
        }
    }

    pub fn refresh(&mut self) {
        match self.client.receipts() {
            Ok(r) => {
                self.receipts = r;
                self.error = None;
            }
            Err(e) => self.error = Some(SharedString::from(e.to_string())),
        }
    }

    fn finality_color(finality: &str) -> Hsla {
        match finality {
            "final" => theme::good(),
            "committed" => theme::accent(),
            _ => theme::muted(),
        }
    }

    fn stream_row(&self, idx: usize, r: &ReceiptEvent) -> impl IntoElement {
        let selected = self.selected == Some(idx);
        let proof = if r.has_proof { "proven" } else { "no proof" };
        let proof_color: Hsla = if r.has_proof { theme::good() } else { theme::warn() }.into();

        div()
            .flex()
            .flex_col()
            .gap_1()
            .px_3()
            .py_2()
            .border_b_1()
            .border_color(theme::border())
            .when(selected, |s| s.bg(theme::panel_hi()))
            .hover(|s| s.bg(theme::panel_hi()))
            .child(
                div()
                    .flex()
                    .justify_between()
                    .child(
                        div()
                            .text_sm()
                            .font_family("monospace")
                            .text_color(theme::text())
                            .child(format!("#{} {}", r.chain_index, short_id(&r.turn_hash))),
                    )
                    .child(pill(r.finality.clone(), Self::finality_color(&r.finality))),
            )
            .child(
                div()
                    .flex()
                    .gap_2()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(format!("h{}", r.height))
                    .child(format!("{} cells", r.cells.len()))
                    .child(div().text_color(proof_color).child(proof)),
            )
            .child(
                div()
                    .flex()
                    .gap_1()
                    .text_xs()
                    .text_color(theme::accent())
                    .children(r.kinds.iter().map(|k| div().child(k.clone()))),
            )
    }

    fn detail(&self, r: &ReceiptEvent) -> impl IntoElement {
        let kv = |k: &'static str, v: String| {
            div()
                .flex()
                .justify_between()
                .gap_3()
                .py_0p5()
                .child(div().text_xs().text_color(theme::muted()).child(k))
                .child(
                    div()
                        .text_xs()
                        .font_family("monospace")
                        .text_color(theme::text())
                        .child(v),
                )
        };
        div()
            .flex()
            .flex_col()
            .p_3()
            .border_t_1()
            .border_color(theme::border())
            .child(section_title("Inspector"))
            .child(kv("receipt", short_id(&r.receipt_hash)))
            .child(kv("turn", short_id(&r.turn_hash)))
            .child(kv("height", r.height.to_string()))
            .child(kv("finality", r.finality.clone()))
            .child(kv("proof", if r.has_proof { "attached".into() } else { "pending".into() }))
            .child(kv("effects", r.kinds.join(", ")))
            .child(kv("cells", r.cells.iter().map(|c| short_id(c)).collect::<Vec<_>>().join(" ")))
    }
}

fn receipts_default_selection() -> Option<usize> {
    None
}

impl Render for ReceiptInspector {
    fn render(&mut self, _window: &mut Window, _cx: &mut Context<Self>) -> impl IntoElement {
        let selected_receipt = self.selected.and_then(|i| self.receipts.get(i)).cloned();

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
                    .child(section_title(format!(
                        "Receipt stream · {} ({})",
                        self.receipts.len(),
                        if self.client.is_live() { "live" } else { "snapshot" }
                    ))),
            )
            .when_some(self.error.clone(), |this, err| {
                this.child(div().px_3().py_2().text_xs().text_color(theme::bad()).child(err))
            })
            .child(
                div()
                    .flex()
                    .flex_col()
                    .children(
                        self.receipts
                            .iter()
                            .enumerate()
                            .map(|(i, r)| self.stream_row(i, r)),
                    ),
            )
            .when_some(selected_receipt, |this, r| this.child(self.detail(&r)))
    }
}
