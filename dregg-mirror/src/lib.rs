//! # dregg-mirror — THE MIRROR RESOLVER
//!
//! DREGG-QUIET-UPGRADE.md §9 item 4 is a NAMED SEAM: *"the mirror-form server view
//! (`dregg.net/d/…`, tier `server`) is not built: the mirror string parses and upgrades
//! under the extension, but the no-extension click path has no server renderer."* This
//! crate closes that seam.
//!
//! ## The situation it serves
//!
//! Someone pastes `dregg://poll/b3_7f2a…` into a post. A reader **with** the extension
//! gets a live, self-verified `<dregg-poll>` in a closed shadow root — tier `extension`.
//! A reader with **nothing** installed clicks the mirror link and lands here. This crate
//! resolves the content address, runs the same fail-closed ladder the extension's netlayer
//! runs, and renders the object through the same `deos-view` web renderer every other
//! glass in the system paints with.
//!
//! ## The one thing it must never do
//!
//! It must never let this page look like evidence. §5: *"A person must always be able to
//! tell WHO CHECKED THIS. The semantic web's failure was that an asserted claim looked
//! identical to a true one."* The reader here checked nothing. So the tier is a constant
//! ([`trust::TIER`] `= "server"`), the badge carries §5's `(trust the origin)` qualifier
//! verbatim and never the extension tier's green, the page states in plain words who
//! checked and what that does and does not buy, it prints the verification ladder gate by
//! gate — including the gates it SKIPPED — and it hands the reader the canonical
//! `dregg://…` string plus the way to a tier where they check it themselves.
//!
//! ## Shape
//!
//! | module | what it is |
//! |---|---|
//! | [`uri`] | the ONE grammar, mirrored from `extension/src/port.ts`; the mirror URL shape |
//! | [`store`] | address → bytes, and the git-style short prefix (ambiguous ⇒ refuse) |
//! | [`object`] | the object body + the four-gate ladder mirrored from `extension/src/netlayer.ts` |
//! | [`trust`] | every word of tier labelling, in one place, asserted on by the tests |
//! | [`page`] | the chrome around `deos-view`'s card; the fail-closed error pages |
//! | [`router`] | resolve → verify → render, or refuse |
//! | [`fixtures`] | builders for the `deos.ui.*` object bytes (tests + the demo seed) |
//!
//! ## Example
//!
//! ```
//! use dregg_mirror::{fixtures, store::MemoryStore, uri::Kind, Mirror, MirrorConfig};
//! use http_serve::WebRequest;
//!
//! let mut store = MemoryStore::new();
//! let addr = store.insert(Kind::Poll, fixtures::poll("ship it?", &[("yes", 3), ("no", 1)], 4));
//!
//! let mirror = Mirror::new(store, MirrorConfig::default());
//! // A truncated-but-unambiguous prefix resolves, which is what survives a post.
//! let res = mirror.handle(&WebRequest::get(&format!("/poll/{}", &addr[..8])));
//! assert_eq!(res.status, 200);
//! assert!(res.body_str().contains("(trust the origin)"));
//! ```

pub mod fixtures;
pub mod object;
pub mod page;
pub mod router;
pub mod store;
pub mod trust;
pub mod uri;

pub use object::{Committee, Envelope, MirrorObject, VerifyReport};
pub use page::PageConfig;
pub use router::{Mirror, MirrorConfig};
pub use store::{DirStore, MemoryStore, ObjectStore};
pub use uri::Kind;
