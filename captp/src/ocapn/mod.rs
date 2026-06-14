//! # OCapN interop — the Goblins-facing adapter layer.
//!
//! This module is the concrete realization of the "Goblins-interop adapter"
//! sketched in [`crate::netlayer`] (module docs, §"The Goblins-interop
//! adapter"). It is what lets a Spritely Goblins / OCapN peer hold and
//! exercise a dregg sturdy ref.
//!
//! ## Status
//!
//! - [`syrup`] — **done + tested**. The OCapN canonical serialization
//!   ([Syrup](https://github.com/ocapn/syrup)): every wire form (booleans,
//!   integers, floats, bytestrings, strings, symbols, lists, dictionaries,
//!   sets, records) with round-trip + adversarial (malformed-input rejection)
//!   coverage, including canonical-order enforcement on dictionaries and sets.
//!   This is the self-contained, fully-testable artifact.
//! - [`session`] — **sketched** (the message *shapes* and codec, not a driven
//!   handshake). The `op:start-session` / `op:abort` records and their Syrup
//!   encode/decode are present and tested as values; binding them to a live
//!   [`Netlayer`](crate::netlayer::Netlayer) connection (write the start frame,
//!   read the peer's, cross-certify the location signature, install the
//!   epoch-correct [`CapSession`](crate::session::CapSession)) is described
//!   precisely in that module's docs and left as the next bounded step — it
//!   needs a signature scheme decision (§"What remains") and is deliberately
//!   not over-built here.
//!
//! The descriptor layer (`desc:export` / `desc:import-object` /
//! `desc:answer` ↔ our session tables) and the `op:deliver` invocation
//! carriage build on exactly these two pieces; their shapes are noted in
//! [`session`] but not yet wired.

pub mod session;
pub mod syrup;

pub use session::{AbortReason, OcapnSessionError, StartSession};
pub use syrup::{Dict, Set, SyrupError, Value};
