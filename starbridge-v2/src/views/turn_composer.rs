//! TurnComposer — build a turn and drive it through the node.
//!
//! This is the "drive turns through the organs" surface. The scaffold composes
//! the thin-client effect set (`SetField` / `Transfer` / `EmitEvent` /
//! `IncrementNonce` — the JSON-friendly `TurnEffectSpec`), shows the assembled
//! `SubmitTurnRequest`, and submits it through [`NodeClient::submit_turn`].
//!
//! The richer organ flows (trustline / channel / mailbox — the typed
//! signed-envelope `/turns/submit` path) and local-custody signing are
//! build-out lanes (docs/STARBRIDGE-V2.md §"Build-out lanes"). The composer's
//! structure is built so an organ flow is "another tab + another request
//! builder", not a rewrite.

use gpui::{
    div, prelude::*, Context, IntoElement, ParentElement, Render, SharedString, Styled, Window,
};

use crate::client::{mock, NodeClient};
use crate::model::{short_id, SubmitTurnRequest};
use crate::views::{section_title, theme};

pub struct TurnComposer {
    client: NodeClient,
    request: SubmitTurnRequest,
    last_result: Option<SharedString>,
}

impl TurnComposer {
    pub fn new(client: NodeClient) -> Self {
        Self {
            client,
            request: mock::sample_turn(),
            last_result: None,
        }
    }

    /// Drive the composed turn through the node. Wired for a button action in
    /// the build-out; callable directly in the scaffold.
    pub fn submit(&mut self) {
        match self.client.submit_turn(&self.request) {
            Ok(r) => self.last_result = Some(SharedString::from(r)),
            Err(e) => self.last_result = Some(SharedString::from(format!("error: {e}"))),
        }
    }

    fn action_panel(&self, i: usize) -> impl IntoElement {
        let a = &self.request.actions[i];
        div()
            .flex()
            .flex_col()
            .gap_1()
            .p_2()
            .rounded_md()
            .bg(theme::panel_hi())
            .border_1()
            .border_color(theme::border())
            .child(
                div()
                    .flex()
                    .justify_between()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(format!(
                        "action {i} · {}",
                        a.method.clone().unwrap_or_else(|| "submit".into())
                    ))
                    .child(
                        div()
                            .font_family("monospace")
                            .child(a.target.as_deref().map(short_id).unwrap_or_else(|| "self".into())),
                    ),
            )
            .children(a.effects.iter().map(|e| {
                div()
                    .text_sm()
                    .text_color(theme::accent())
                    .child(e.label())
            }))
    }
}

impl Render for TurnComposer {
    fn render(&mut self, _window: &mut Window, _cx: &mut Context<Self>) -> impl IntoElement {
        let req_json = serde_json::to_string_pretty(&self.request)
            .unwrap_or_else(|e| format!("<encode error: {e}>"));

        div()
            .flex()
            .flex_col()
            .h_full()
            .gap_3()
            .p_3()
            .bg(theme::panel())
            .child(section_title("Turn composer"))
            .child(
                div()
                    .flex()
                    .gap_3()
                    .text_xs()
                    .text_color(theme::muted())
                    .child(format!("agent {}", short_id(&self.request.agent)))
                    .child(format!("nonce {}", self.request.nonce))
                    .child(format!("fee {}", self.request.fee)),
            )
            .when_some(self.request.memo.clone(), |this, memo| {
                this.child(
                    div()
                        .text_sm()
                        .text_color(theme::text())
                        .child(format!("“{memo}”")),
                )
            })
            .child(
                div()
                    .flex()
                    .flex_col()
                    .gap_2()
                    .children((0..self.request.actions.len()).map(|i| self.action_panel(i))),
            )
            .child(section_title("Wire request"))
            .child(
                div()
                    .p_2()
                    .rounded_md()
                    .bg(theme::bg())
                    .border_1()
                    .border_color(theme::border())
                    .text_xs()
                    .font_family("monospace")
                    .text_color(theme::muted())
                    .child(req_json),
            )
            .when_some(self.last_result.clone(), |this, r| {
                this.child(
                    div()
                        .text_xs()
                        .text_color(theme::good())
                        .child(format!("submitted → {r}")),
                )
            })
    }
}
