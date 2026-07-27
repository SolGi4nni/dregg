//! The **moldable faces** rendered through the SAME gpui-component vocabulary.
//!
//! `deos.cell(id).present()` yields the moldable faces (RawFields · Graph ·
//! DomainVisual · Provenance) — each a distinct `obs`-projection of the same cell. The
//! §7 unification (docs/deos/SCRIPTING-AND-DISTRIBUTED-DOM.md): the applet's custom
//! view (the `deos.ui.*` tree) and the inspector (the faces) draw in the SAME widget
//! vocabulary. This module renders a minimal **RawFields** face — enough to show "the
//! inspector and the custom view share widgets".
//!
//! It reads the faces off the live ledger through deos-js's public
//! [`deos_js::reflect_binding::cell_present_json`] (the gpui-free projection), parses
//! the RawFields face, and renders it as a titled `v_flex` of `key: value` rows — the
//! same `Label`/`v_flex`/`h_flex` widgets the applet view uses.

use deos_js::applet::Applet;
use deos_js::reflect_binding::cell_present_json;
use gpui::{div, Context, FontWeight, IntoElement, ParentElement, Render, Styled, Window};
use gpui_component::label::Label;
use gpui_component::{h_flex, v_flex, ActiveTheme};
use serde::Deserialize;

/// One face from `present()` (`{kind,label,body}`).
#[derive(Debug, Deserialize)]
struct Face {
    kind: String,
    label: String,
    body: FaceBody,
}

#[derive(Debug, Deserialize)]
#[serde(tag = "type")]
enum FaceBody {
    #[serde(rename = "fields")]
    Fields { value: Inspectable },
    // The other face bodies (graph/stateMachine/timeline) are parsed loosely; this
    // slice renders only the RawFields face. They deserialize into Other and render as
    // a one-line kind tag.
    #[serde(other)]
    Other,
}

#[derive(Debug, Deserialize)]
struct Inspectable {
    title: String,
    subtitle: String,
    fields: Vec<Field>,
}

#[derive(Debug, Deserialize)]
struct Field {
    key: String,
    #[serde(rename = "type")]
    ty: String,
    value: serde_json::Value,
}

/// Extract the moldable faces of the applet's own cell as JSON (deos-js's gpui-free
/// projection off the live ledger).
fn faces_json(applet: &Applet) -> Option<String> {
    cell_present_json(applet.ledger(), &applet.cell(), applet.full_receipts())
}

/// A face with its display strings PRE-FORMATTED at construction (the faces are
/// immutable parsed data, so the `format!`s never change between paints). Render walks
/// these cached strings instead of re-`format!`ing every field/header each frame.
struct RenderedFace {
    /// `"[{kind}] {label}"` — the card header.
    header: String,
    body: RenderedBody,
}

enum RenderedBody {
    Fields {
        /// `"{title} · {subtitle}"`.
        summary: String,
        /// Per field: (`"{key}:"`, `render_value(ty, value)`), pre-formatted.
        rows: Vec<(String, String)>,
    },
    /// `"‹{kind} face, rendered as a tag in this slice›"`.
    Other(String),
}

impl RenderedFace {
    fn from_face(face: &Face) -> Self {
        let header = format!("[{}] {}", face.kind, face.label);
        let body = match &face.body {
            FaceBody::Fields { value } => RenderedBody::Fields {
                summary: format!("{} · {}", value.title, value.subtitle),
                rows: value
                    .fields
                    .iter()
                    .map(|f| (format!("{}:", f.key), render_value(&f.ty, &f.value)))
                    .collect(),
            },
            FaceBody::Other => RenderedBody::Other(format!(
                "‹{} face, rendered as a tag in this slice›",
                face.kind
            )),
        };
        RenderedFace { header, body }
    }
}

/// The inspector view — the moldable `present()` faces of a cell, rendered through the
/// SAME widget vocabulary the applet view uses (the §7 unification).
pub struct FacesView {
    faces: Vec<RenderedFace>,
}

impl FacesView {
    /// Build a faces view from the applet's own cell. Returns `None` if the cell has no
    /// presentable faces (it always does once minted). The faces' display strings are
    /// formatted ONCE here (they are immutable), so paint is allocation-light.
    pub fn for_applet(applet: &Applet) -> Option<Self> {
        let json = faces_json(applet)?;
        let parsed: Vec<Face> = serde_json::from_str(&json).ok()?;
        let faces = parsed.iter().map(RenderedFace::from_face).collect();
        Some(Self { faces })
    }

    /// How many faces were projected (the RawFields/Graph/DomainVisual/Provenance set).
    pub fn face_count(&self) -> usize {
        self.faces.len()
    }
}

impl Render for FacesView {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let fg = cx.theme().foreground;
        let muted = cx.theme().muted_foreground;
        let border = cx.theme().border;

        let mut root = v_flex().gap_3().p_3().size_full().bg(cx.theme().background);
        root = root.child(
            Label::new("present() · moldable faces")
                .font_weight(FontWeight::BOLD)
                .text_color(fg),
        );

        for face in &self.faces {
            let mut card = v_flex()
                .gap_1()
                .p_2()
                .border_1()
                .border_color(border)
                .child(
                    Label::new(face.header.clone())
                        .font_weight(FontWeight::BOLD)
                        .text_color(fg),
                );
            match &face.body {
                RenderedBody::Fields { summary, rows } => {
                    card = card.child(Label::new(summary.clone()).text_color(muted));
                    for (key, value) in rows {
                        card = card.child(
                            h_flex()
                                .gap_2()
                                .child(
                                    Label::new(key.clone())
                                        .font_weight(FontWeight::BOLD)
                                        .text_color(fg),
                                )
                                .child(Label::new(value.clone()).text_color(muted)),
                        );
                    }
                }
                RenderedBody::Other(tag) => {
                    card = card.child(Label::new(tag.clone()).text_color(muted));
                }
            }
            root = root.child(card);
        }

        div().size_full().child(root)
    }
}

/// A compact string for a field value (the inspector cell).
fn render_value(ty: &str, v: &serde_json::Value) -> String {
    match v {
        serde_json::Value::String(s) => format!("{s} ({ty})"),
        serde_json::Value::Number(n) => format!("{n} ({ty})"),
        serde_json::Value::Bool(b) => format!("{b} ({ty})"),
        other => format!("{other} ({ty})"),
    }
}
