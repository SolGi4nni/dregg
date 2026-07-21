//! The web uses the same seat-claiming multiway-tug adapter as Telegram,
//! WeChat, and Discord. Keeping the ownership/refusal and hidden-hand policy in
//! one implementation is load-bearing: a refused press must not reserve a seat
//! on one frontend while another frontend correctly leaves it free.

pub use dreggnet_catalog::seated::{SeatedTug, SeatedTugSession};
