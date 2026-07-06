//! `deos-matrix` — the protocol foundation of the native deos Matrix client.
//!
//! This crate stands on the official [`matrix_sdk`] (matrix-rust-sdk). It owns
//! its own tokio runtime and exposes a small, deos-shaped API:
//!
//! - [`MatrixClient`] — configure a homeserver, log in (password), restore a
//!   session, run an encrypted sync, list joined rooms, read a room's recent
//!   timeline.
//!
//! The async/sync boundary is the load-bearing design point. `matrix-rust-sdk`
//! is tokio-async; dregg's embedded executor is sync. So we keep ALL async I/O
//! inside this crate and expose a deos-friendly surface. The UI (gpui) and the
//! deos confinement seams (identity-cell binding, device-keys-as-caps, the
//! comms-PD) are layered ABOVE this crate later — see `README.md`.
//!
//! # Design lineage
//!
//! The worker/request-response bridge mirrors `iamb`'s `worker.rs`: a synchronous
//! caller sends a typed request over a channel; the async worker (running on the
//! tokio runtime) executes the matrix-sdk call and replies over a oneshot. That
//! is the SAME shape we will use to bridge into the sync dregg executor. The
//! headless library here is `async fn` directly (so it composes with any tokio
//! caller, including the CLI); [`worker`] sketches the sync-facing bridge that the
//! confined comms-PD will use.

pub mod cell;
// CHAT AS A HYPERDREGGMEDIA CARD — room = a cell, message = a turn, send = an
// affordance; the timeline is the cell's history. Over the gpui-free ChatSource.
pub mod chat_card;
// The chat card's VIEW-TREE projection — ChatCard as a renderer-independent
// `deos.ui.*` element-tree (pure serde_json; the shape every deos-view renderer
// parses), so the chat paints native/web/discord/seL4 from one piece of data.
pub mod chat_view;
pub mod client;
pub mod membrane;
pub mod object;
pub mod session;
pub mod source;
pub mod verification;
// The sync→async bridge owns an OS thread + a multi-thread tokio runtime and
// blocks on `oneshot::blocking_recv`. None of that exists on single-threaded
// wasm32 (no OS threads; you cannot block the browser event loop), so the worker
// is NATIVE-only. The in-browser async model is `wasm-bindgen-futures::spawn_local`
// driving the same `MatrixClient` async methods directly — the UI `await`s those
// futures on the event loop instead of blocking on a `MatrixHandle`. See the
// `worker` module docs and `client::wasm_indexeddb` for the wasm seam.
#[cfg(not(target_family = "wasm"))]
pub mod worker;

#[cfg(feature = "gui")]
pub mod chat;

#[cfg(feature = "cockpit-surface")]
pub mod cockpit_surface;

pub use cell::{CellId, IdentityCell, PersonTrust, RoomCell, SendReceipt};
pub use client::{
    EventState, MatrixClient, MessageKind, PublicRoom, Reaction, ReplyTo, RoomPower, RoomSummary,
    SpaceSummary, TimelineMessage,
};
pub use membrane::{MembraneEnvelope, MembraneHost, MockMembraneHost};
pub use object::{
    Affordance, CapabilityGrant, CellRef, DreggObject, ReceiptObject, Transclusion,
    DREGG_OBJECT_KEY, OBJECT_VERSION,
};
pub use session::StoredSession;
pub use source::{ChatSource, MockSource};
pub use verification::{SasEmoji, SasProgress, VerificationFlow, VerificationPhase};

/// Crate-wide error type.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("matrix sdk error: {0}")]
    Sdk(#[from] matrix_sdk::Error),
    #[error("matrix http error: {0}")]
    Http(#[from] matrix_sdk::HttpError),
    // Boxed: `ClientBuildError` is ~208 bytes and would otherwise dominate the
    // `Error` size, tripping `clippy::result_large_err` on every fallible fn.
    #[error("client build error: {0}")]
    ClientBuild(Box<matrix_sdk::ClientBuildError>),
    #[error("matrix id parse error: {0}")]
    IdParse(#[from] matrix_sdk::IdParseError),
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
    #[error("session (de)serialization error: {0}")]
    Session(#[from] serde_json::Error),
    /// This source holds no deos executor, so it cannot mint/rehydrate/drive/
    /// stitch a real membrane — fail-closed (NEVER a mock fallback).
    #[error("no deos executor attached to this source — the real membrane operations are unavailable here")]
    MembraneUnavailable,
    #[error("{0}")]
    Other(String),
}

impl From<matrix_sdk::ClientBuildError> for Error {
    fn from(e: matrix_sdk::ClientBuildError) -> Self {
        Error::ClientBuild(Box::new(e))
    }
}

pub type Result<T> = std::result::Result<T, Error>;
