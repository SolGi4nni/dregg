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
//! - [`session`] — **records + cross-certification done + tested**. The
//!   `op:start-session` / `op:abort` records, their Syrup encode/decode, and the
//!   Ed25519 location-signature verify ([`StartSession::verify_location_sig`])
//!   are present and tested (valid sigs admit, forged/wrong-key/tampered ones
//!   reject). What is not over-built here is binding them to a *live*
//!   [`Netlayer`](crate::netlayer::Netlayer) connection (the async drive loop /
//!   real socket netlayer that writes the start frame, reads the peer's, and
//!   installs the epoch-correct [`CapSession`](crate::session::CapSession)) —
//!   see that module's §"What remains".
//!
//! The descriptor layer (`desc:export` / `desc:import-object` /
//! `desc:answer` ↔ our session tables) and the `op:deliver` invocation
//! carriage build on exactly these two pieces; their shapes are noted in
//! [`session`] but not yet wired.

pub mod session;
pub mod syrup;

pub use session::{AbortReason, LocationVerifyError, OcapnSessionError, StartSession, desc};
pub use syrup::{Dict, Set, SyrupError, Value};
