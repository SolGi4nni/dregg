//! The cockpit's shared gpui primitives — palette + small render helpers.
//!
//! The comprehensive master-interface views live in [`crate::cockpit`]
//! (rendering the EMBEDDED `World` directly). This module keeps only the
//! palette/pill/section-title primitives the cockpit consumes.

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

/// A small section header used across the rail and panels. Returns a `Div` so
/// callers can keep styling it (`.mb_1()` etc.).
pub fn section_title(text: impl Into<String>) -> gpui::Div {
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
