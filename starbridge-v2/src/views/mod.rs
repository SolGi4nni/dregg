//! The shell's gpui views.
//!
//! Layout mirrors the web Starbridge shell (`site/src/starbridge/index.html`):
//! a persistent left rail (identity · places · your cells · receipt stream ·
//! node connection) and a main mount that swaps between places. Here the
//! three core views are:
//!
//!   * [`cell_list::CellList`] — the rail's "your cells" + the cell browser.
//!   * [`receipt_inspector::ReceiptInspector`] — the receipt stream + a
//!     drill-in inspector for one receipt's proof/finality.
//!   * [`turn_composer::TurnComposer`] — build a turn (actions + effects)
//!     and drive it through the node (the "drive turns through the organs"
//!     surface, scaffolded to the thin-client effect set).
//!
//! Each is a real gpui component (`Render`) holding a real data model from
//! [`crate::model`], bound to a [`crate::client::NodeClient`].

pub mod cell_list;
pub mod receipt_inspector;
pub mod turn_composer;

use gpui::{div, Hsla, IntoElement, ParentElement, Styled};

/// The shell's palette (a dark ocap console).
///
/// `gpui::rgb` is not `const` in this gpui rev, so these are functions
/// returning `Hsla` (the type `bg`/`text_color`/`border_color` all accept via
/// `Into<Hsla>` / `Into<Background>`).
pub mod theme {
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
    pub fn good() -> Hsla {
        rgb(0x57d977).into()
    }
    pub fn warn() -> Hsla {
        rgb(0xe3b341).into()
    }
    pub fn bad() -> Hsla {
        rgb(0xe5534b).into()
    }
}

/// A small section header used across the rail and panels.
pub fn section_title(text: impl Into<String>) -> impl IntoElement {
    div()
        .text_xs()
        .text_color(theme::muted())
        .child(text.into())
}

/// A status pill — colored by ok/warn/bad.
pub fn pill(text: impl Into<String>, color: Hsla) -> impl IntoElement {
    div()
        .px_2()
        .py_0p5()
        .rounded_md()
        .bg(theme::panel_hi())
        .text_xs()
        .text_color(color)
        .child(text.into())
}
