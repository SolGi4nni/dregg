//! The dock module's self-contained palette.
//!
//! Kept SELF-CONTAINED (not `crate::views::theme`) so the module compiles
//! independent of where it is mounted (lib vs bin). The values mirror the
//! cockpit's `views::theme` palette; on integration the cockpit can swap these
//! to share one source of truth, but the dock does not depend on it.
//!
//! `gpui::rgb` is not `const` in this gpui rev, so these are functions returning
//! `Hsla` (accepted by `bg`/`text_color`/`border_color` via `Into`).

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
