//! # deos-js — a deos-native JavaScript scripting surface.
//!
//! JS (real SpiderMonkey via [`mozjs`]) drives deos *substance* — sovereign cells +
//! cap-gated *verified turns* — with ember's factoring:
//!
//!   - a **cell** is a sovereignty/distribution boundary (one whole interactive
//!     "applet"), NOT a DOM node. It is a polynomial-functor interface: positions =
//!     the views it presents, directions = the affordances (turns) it accepts.
//!   - the applet's **model** is the cell's state; the only mutators are its
//!     affordances = cap-gated verified turns, each leaving a real `TurnReceipt`.
//!   - **ephemeral view-state** (draft text, hover) is NOT cell state and is NEVER a
//!     turn.
//!   - applets **compose via transclusion** (the cap-gated, provenanced distributed
//!     DOM) — reusing the real `WholeCellTransclusion`/`TranscludedField` primitive.
//!
//! [`applet::Applet`] is the substance binding (engine-independent, the load-bearing
//! factoring); [`js::JsRuntime`] is the genuine SpiderMonkey engine driving it.
//!
//! ## Two slices
//!
//! - **drive** ([`applet`]): `deos.applet`/`app.fire` — an affordance is a *production*
//!   (a real cap-gated verified turn). View-state is ephemeral; `transclude` composes.
//! - **crawl** ([`reflect_binding`]): `deos.world`/`deos.cell` — the fully-reflective
//!   object graph over the live image (cells · the four substances · the ocap web ·
//!   the cap-bounded frustum), via the gpui-free `deos-reflect`. Reflection is a READ
//!   that confers no authority — cap-bounded and attested, *not* omniscient.

pub mod applet;
pub mod js;
pub mod portable;
pub mod reflect_binding;

pub use applet::{Affordance, Applet, CellModel, FireError, Transclusion, TranscludeError};
pub use js::JsRuntime;
pub use portable::{AffordanceSpec, AppletManifest, ApplyOp, PortableApplet};
