//! The dock's palette — **a re-export of [`crate::views::theme`], not a copy.**
//!
//! It used to be a self-contained transcription, on the rationale that "the module
//! compiles independent of where it is mounted (lib vs bin)". That rationale was
//! stale: `dock::theme` is declared under `#[cfg(any(gpui-ui, gpui-web))]` in
//! `dock/mod.rs` and `views` is declared under the SAME cfg in `lib.rs`, so there
//! has never been a configuration in which one exists and the other does not. The
//! gpui-free `process-pd` path reaches `dock::migrate`, which does not touch this
//! module.
//!
//! What the self-containment actually bought was a second place to hand-type the
//! panel hex. See the drift the fold turned up, documented on
//! `views::theme::good_mint`.

pub use crate::views::theme::{accent, bg, border, muted, panel, panel_hi, text};
