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

pub mod agent_card;
pub mod applet;
pub mod attach;
pub mod card_editor;
pub mod coauthored_card;
pub mod composer_card;
pub mod dynamics_card;
pub mod graph_card;
pub mod inspector_card;
pub mod js;
pub mod layout_card;
pub mod links_card;
pub mod mailtown;
pub mod multi_cell;
pub mod objects_card;
pub mod portable;
pub mod program_doc;
pub mod reflect_binding;
pub mod signals;

pub use agent_card::{AGENT_NONCE_SLOT, AgentAction, AgentCard, MandateEdge};
pub use applet::{Affordance, Applet, CellModel, FireError, TranscludeError, Transclusion};
pub use attach::{
    AttachedAffordance, AttachedApplet, AttachedComposer, ComposeError, ComposeStep,
    LiveComposition, WorldSink, mint_id_of,
};
pub use card_editor::Author;
pub use card_editor::{CardEditor, EditError, ViewEdit, ViewPatch, ViewTree};
pub use coauthored_card::{COUNT_SLOT, CardFork, CardStitch, SharedCard};
pub use composer_card::{ComposedChild, ComposerCard, ComposerViewEdit, Role as ComposerRole};
pub use dynamics_card::{DynamicsCard, FEED_LEN_SLOT, FeedEntry};
pub use graph_card::{GRAPH_AUTHORSHIP_SLOT, GraphCard, GraphRow};
pub use inspector_card::{INSPECTOR_AUTHORSHIP_SLOT, InspectorCard};
pub use js::{
    ComposeOutcome, ComposeRunOutcome, JsRuntime, JsTarget, set_current_composer,
    set_current_editor, take_current_composer, take_current_editor, take_last_compose,
};
pub use layout_card::{LAYOUT_AUTHORSHIP_SLOT, LayoutCard, LayoutMode, LayoutModel, LayoutPatch};
pub use links_card::{BacklinkRow, LINK_COUNT_SLOT, LinksCard};
pub use objects_card::{OBJECTS_AUTHORSHIP_SLOT, ObjectRow, ObjectsCard};
pub use portable::{AffordanceSpec, AppletManifest, ApplyOp, PortableApplet};
pub use program_doc::{GadgetCite, ProgramSource, TranscludedFragment};
pub use reflect_binding::id_hex;
