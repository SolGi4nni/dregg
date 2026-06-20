//! THE PRESENTATION SPINE (L1) — the moldable inspector's framework primitive.
//!
//! `reflect.rs` gives every dregg datum ONE reflective shape: a flat
//! [`Inspectable`](crate::reflect::Inspectable) field-tree. Pharo's `gtViewsFor:`
//! instead lets a type offer a *set* of named views, each a different lens on the
//! same live object. This module generalizes the single field-tree into that
//! moldable multiplicity WITHOUT discarding `reflect.rs`: the existing
//! `Inspectable` becomes the body of the mandatory [`PresentationKind::RawFields`]
//! presentation, and a type registers additional kinds beside it.
//!
//! Everything here is pure data, projected from the live [`World`], proven by
//! `cargo test` exactly as `reflect.rs`/`wonder.rs`/`inspect_act.rs` are. No gpui
//! type crosses the boundary; a thin gpui layer maps each [`PresentationBody`]
//! variant and each [`GadgetField`] kind to a widget. The framework's three
//! pieces:
//!
//!   * [`Presentable`] — a protocol object offers its presentation *set*
//!     ([`Presentable::present`]), with the blanket invariant that
//!     [`PresentationKind::RawFields`] is ALWAYS present (the universal-coverage
//!     floor — every type at minimum gets the existing `reflect_*` projection).
//!   * [`Gadget`] / [`CommittingGadget`] — interactive value CONSTRUCTION that
//!     rides the established `IntentDraft → simulate → commit` spine
//!     (`simulate.rs`), so a gadget yields a REAL protocol value flowing through
//!     the verified executor. (L1 defines the trait shape + the field-kind model;
//!     concrete gadgets are L2/L3.)
//!   * [`Spotter`] — universal search over every live object's every presentation,
//!     indexed by [`Presentation::search_text`] and ranked with the cockpit's own
//!     `palette::fuzzy_score` (no parallel matcher).
//!   * [`Halo`] — the per-object direct-manipulation ring whose commands open
//!     presentations / arm gadgets (generalizing `wonder.rs`'s 3-command ring).
//!
//! The proof-of-shape: [`ReflectedCell`] is a real `impl Presentable` for a live
//! ledger cell that emits a five-presentation set (RawFields · Affordances ·
//! Provenance · Graph · a lifecycle DomainVisual) entirely off the real machinery
//! (`reflect_cell` · the `inspect_act` message surface · the live receipt log ·
//! `graph.rs`'s ocap edges · the real `CellLifecycle`).

use std::collections::BTreeSet;

use dregg_cell::{Cell, CellId};

use crate::graph::OcapGraph;
use crate::inspect_act::{InspectAct, InspectFocus};
use crate::reflect::{self, Inspectable, ObjectKind};
use crate::simulate::{self, IntentDraft, SimOutcome};
use crate::world::{CommitOutcome, World};

// ===========================================================================
// §1.1 — PresentationKind / Presentation / PresentationBody
// ===========================================================================

/// The named kinds of presentation a protocol object can offer. Mirrors
/// Pharo-GT's view multiplicity, molded to the dregg domain's four axes. The
/// seven kinds account for the census's whole repeated proposal vocabulary
/// (see `docs/deos/INSPECTOR-FRAMEWORK.md` §1.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PresentationKind {
    /// The existing [`Inspectable`] field-tree — the MANDATORY floor.
    RawFields,
    /// A node/edge view (ocap web, effect DAG, Merkle tree, lattice).
    Graph,
    /// A domain-specific rendering (state machine, gauge, ladder, timeline).
    DomainVisual,
    /// "The messages it understands" — the [`InspectAct`] `Message` list.
    Affordances,
    /// Time-travel / receipt-chain / lineage (the History scrubber face).
    Provenance,
    /// Conservation / commitment-binding / cost-coordination readouts.
    Invariant,
    /// The program/constraint-set/Datalog "what-is" text the object enforces.
    Source,
}

impl PresentationKind {
    /// A short stable slug (the gpui tab key / test selector).
    pub fn slug(&self) -> &'static str {
        match self {
            PresentationKind::RawFields => "raw-fields",
            PresentationKind::Graph => "graph",
            PresentationKind::DomainVisual => "domain-visual",
            PresentationKind::Affordances => "affordances",
            PresentationKind::Provenance => "provenance",
            PresentationKind::Invariant => "invariant",
            PresentationKind::Source => "source",
        }
    }
}

/// One presentation: a kind + a renderable payload + searchable text for the
/// [`Spotter`].
#[derive(Clone, Debug)]
pub struct Presentation {
    /// Which of the seven lenses this is.
    pub kind: PresentationKind,
    /// Operator-legible tab name ("Cell State", "ocap Graph").
    pub label: String,
    /// The data the thin gpui layer renders.
    pub body: PresentationBody,
    /// Flattened content the [`Spotter`] indexes (labels, hashes, hex ids, …).
    pub search_text: String,
}

/// The renderable payloads. Each variant is pure data; the gpui layer maps each
/// to a widget. New visual kinds are added here ONCE and every type that emits
/// them renders. [`PresentationBody::Fields`] reuses `reflect.rs` verbatim — no
/// parallel object model.
#[derive(Clone, Debug)]
pub enum PresentationBody {
    /// REUSES `reflect.rs` verbatim — the RawFields floor.
    Fields(Inspectable),
    /// Nodes + typed edges (reuses `graph.rs`'s [`GraphNode`]/[`GraphEdge`]).
    Graph(GraphView),
    /// States + transitions + current (lifecycle, escrow, channel epoch).
    StateMachine(StateMachineView),
    /// A bounded value: drawn/ceiling, ratchet rungs, finality tiers.
    Gauge(GaugeView),
    /// Ordered events (receipt chain, epoch history, attenuation lineage).
    Timeline(TimelineView),
    /// Leaves + path + root (nullifier set, cap-crown, MMR peaks).
    MerkleTree(MerkleTreeView),
    /// A partial order (AuthRequired, Auth rights, finality tiers).
    Lattice(LatticeView),
    /// Step-by-step evaluation (HMAC chain, constraint eval, hash absorb).
    Trace(TraceView),
    /// The Source/explain face (program text, Datalog, "what-is").
    Prose(String),
}

impl PresentationBody {
    /// The flattened searchable text this body contributes to a presentation's
    /// `search_text` (a default the builder can extend with labels/ids).
    pub fn search_text(&self) -> String {
        match self {
            PresentationBody::Fields(i) => {
                let mut s = format!("{} {}", i.title, i.subtitle);
                for f in &i.fields {
                    s.push(' ');
                    s.push_str(&f.key);
                }
                s
            }
            PresentationBody::Graph(g) => g
                .nodes
                .iter()
                .map(|n| n.short.as_str())
                .collect::<Vec<_>>()
                .join(" "),
            PresentationBody::StateMachine(sm) => {
                let mut s = sm.current.clone();
                for st in &sm.states {
                    s.push(' ');
                    s.push_str(&st.name);
                }
                s
            }
            PresentationBody::Gauge(g) => g.label.clone(),
            PresentationBody::Timeline(t) => t
                .events
                .iter()
                .map(|e| e.label.as_str())
                .collect::<Vec<_>>()
                .join(" "),
            PresentationBody::MerkleTree(m) => m.label.clone(),
            PresentationBody::Lattice(l) => l
                .nodes
                .iter()
                .map(|n| n.as_str())
                .collect::<Vec<_>>()
                .join(" "),
            PresentationBody::Trace(t) => t
                .steps
                .iter()
                .map(|s| s.label.as_str())
                .collect::<Vec<_>>()
                .join(" "),
            PresentationBody::Prose(p) => p.clone(),
        }
    }
}

// --- the view payload types: pure data the thin gpui layer renders ----------

/// A node/edge view payload. Reuses `graph.rs`'s [`GraphNode`]/[`GraphEdge`] as
/// the live primitives (the genuine ocap edges read off the ledger), plus a
/// `focus` marking the object this view is centered on.
#[derive(Clone, Debug)]
pub struct GraphView {
    /// The nodes (reuse the real graph primitive — never a parallel node model).
    pub nodes: Vec<crate::graph::GraphNode>,
    /// The directed edges (the real `CapabilityRef`-derived ocap grants).
    pub edges: Vec<crate::graph::GraphEdge>,
    /// The cell this view is centered on (the renderer highlights it), if any.
    pub focus: Option<CellId>,
}

/// One state in a [`StateMachineView`] (a lifecycle / escrow / epoch node).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SmState {
    /// The state's operator-legible name ("Live", "Sealed", "Destroyed").
    pub name: String,
    /// Whether this is a terminal (no-further-transition) state.
    pub terminal: bool,
}

/// One directed transition in a [`StateMachineView`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SmTransition {
    /// The source state name.
    pub from: String,
    /// The destination state name.
    pub to: String,
    /// The verb that drives it ("Seal", "Unseal", "Destroy").
    pub verb: String,
}

/// States + transitions + the current state — a lifecycle/escrow/epoch diagram.
#[derive(Clone, Debug)]
pub struct StateMachineView {
    /// The states, in canonical order.
    pub states: Vec<SmState>,
    /// The directed transitions between them.
    pub transitions: Vec<SmTransition>,
    /// The name of the state the object is currently IN (the live readout).
    pub current: String,
}

/// A bounded value: `drawn` of `ceiling`, with named ratchet rungs (capacity
/// gauge, finality ladder, accrual envelope).
#[derive(Clone, Debug)]
pub struct GaugeView {
    /// What the gauge measures ("balance", "drawn vs ceiling").
    pub label: String,
    /// The current value (signed — issuer wells carry −supply).
    pub value: i64,
    /// The ceiling/ratchet bound (`None` = unbounded).
    pub ceiling: Option<i64>,
    /// Named rungs along the dial (the discrete tiers, if any).
    pub rungs: Vec<String>,
}

/// One event in a [`TimelineView`] (a receipt, an epoch tick, an attenuation hop).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TimelineEvent {
    /// A monotone ordering key (height / index).
    pub at: u64,
    /// The event label (the row text).
    pub label: String,
    /// An optional navigable hash (the receipt / block this event IS).
    pub hash: Option<[u8; 32]>,
}

/// Ordered events — a receipt chain / epoch history / attenuation lineage.
#[derive(Clone, Debug)]
pub struct TimelineView {
    /// The events, in time order.
    pub events: Vec<TimelineEvent>,
}

/// Leaves + a path + a root — a nullifier set / cap-crown / MMR-peak view. Pure
/// data; the verifier gadgets (L4/L6/L9) recompute against the real machinery.
#[derive(Clone, Debug)]
pub struct MerkleTreeView {
    /// What this tree commits ("cap-crown", "nullifier set").
    pub label: String,
    /// The leaves (hex), in canonical order.
    pub leaves: Vec<String>,
    /// The root the leaves commit to (the published commitment).
    pub root: [u8; 32],
    /// An optional highlighted membership/non-membership path (leaf → root).
    pub path: Vec<String>,
}

/// A partial order — AuthRequired tiers, finality levels, rights lattice.
#[derive(Clone, Debug)]
pub struct LatticeView {
    /// The lattice elements, weakest-first.
    pub nodes: Vec<String>,
    /// The covering relations (`from ⊑ to`), as index pairs into `nodes`.
    pub edges: Vec<(usize, usize)>,
    /// The element the object currently sits at (the live readout), if any.
    pub current: Option<usize>,
}

/// One step in a [`TraceView`] (an HMAC link, a constraint-eval line, a hash absorb).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceStep {
    /// The step ordinal.
    pub index: usize,
    /// The step text.
    pub label: String,
}

/// Step-by-step evaluation — an HMAC chain / constraint eval / hash absorb.
#[derive(Clone, Debug)]
pub struct TraceView {
    /// The steps, in evaluation order.
    pub steps: Vec<TraceStep>,
}

// ===========================================================================
// §1.1 — the Presentable trait + PresentCtx
// ===========================================================================

/// The read-only context a [`Presentable::present`] reads — exactly the inputs
/// `reflect.rs` and `inspect_act.rs` already take: the live world, the viewer
/// principal (whose held authority gates the Affordances cap badges), and the
/// current block height. A `present()` reads the live ledger and builds its set;
/// it NEVER copies protocol types into a parallel schema (the `reflect.rs`
/// invariant, preserved).
pub struct PresentCtx<'w> {
    /// The live ledger + receipt log (read-only).
    pub world: &'w World,
    /// The viewer principal the Affordances presentation is projected for.
    pub viewer: CellId,
    /// The current block height (the freshness/lifecycle anchor).
    pub height: u64,
}

impl<'w> PresentCtx<'w> {
    /// Build a context from the live world. The viewer defaults to the focused
    /// object's own principal where a caller has nothing better; callers with a
    /// real viewer pass it via [`PresentCtx::for_viewer`].
    pub fn new(world: &'w World, viewer: CellId) -> Self {
        let height = world.height();
        PresentCtx { world, viewer, height }
    }

    /// A context for a specific viewer (the Affordances cap badges divide on it).
    pub fn for_viewer(world: &'w World, viewer: CellId) -> Self {
        PresentCtx::new(world, viewer)
    }
}

/// THE trait. A protocol object implements it to offer its presentation set.
///
/// The blanket invariant: [`PresentationKind::RawFields`] is ALWAYS present (the
/// floor that guarantees universal coverage — every type at minimum gets the
/// existing `reflect_*` projection). Implementors satisfy it by making the first
/// element of [`Presentable::present`] the existing `Inspectable`; the
/// [`PresentableExt::has_raw_fields_floor`] helper asserts it in tests.
pub trait Presentable {
    /// The full presentation set, built fresh off the live world in `ctx`.
    fn present(&self, ctx: &PresentCtx) -> Vec<Presentation>;
    /// What kind of dregg object this is (drives the icon / halo vocabulary).
    fn object_kind(&self) -> ObjectKind;
}

/// Convenience accessors over any [`Presentable`]'s set (the universal-coverage
/// floor check + kind lookups the Spotter/Halo lean on).
pub trait PresentableExt: Presentable {
    /// `true` iff the set contains the mandatory RawFields floor (the
    /// universal-coverage invariant — every Presentable MUST satisfy this).
    fn has_raw_fields_floor(&self, ctx: &PresentCtx) -> bool {
        self.present(ctx)
            .iter()
            .any(|p| p.kind == PresentationKind::RawFields)
    }
    /// The set of distinct presentation kinds offered (for the tab strip + tests).
    fn presentation_kinds(&self, ctx: &PresentCtx) -> Vec<PresentationKind> {
        let mut seen: Vec<PresentationKind> = Vec::new();
        for p in self.present(ctx) {
            if !seen.contains(&p.kind) {
                seen.push(p.kind);
            }
        }
        seen
    }
}

impl<T: Presentable + ?Sized> PresentableExt for T {}

// ===========================================================================
// §1.2 — the Gadget + CommittingGadget traits + the field-kind model
// ===========================================================================

/// The recursive sub-gadget tags the gpui layer routes (one widget per kind).
/// L1 defines the tag set; the concrete gadgets that fill them are L2/L3.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GadgetKind {
    /// A predicate / caveat composer → `StateConstraint` (L2).
    Predicate,
    /// A capability attenuator → `AttenuatedCap` (L4).
    CapAttenuation,
    /// An effect picker/composer → one `Effect` (L3).
    Effect,
    /// A call-tree / call-forest builder (L3).
    CallTree,
    /// A whole-turn composer (L3, a [`CommittingGadget`]).
    Turn,
}

/// The uniform field kinds the gpui layer renders generically (one widget per
/// kind). Recursive kinds (`SubGadget`/`List`) carry a [`GadgetKind`] tag so a
/// predicate composer nests inside a turn composer without a bespoke widget.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GadgetField {
    /// pubkey/token/hash/commitment input (a fixed-length hex blob).
    HexBytes { key: String, len: usize },
    /// amount/height/slot spinner (bounded unsigned).
    U64 { key: String, min: u64, max: u64 },
    /// signed balance dial (issuer wells).
    I64 { key: String },
    /// autocomplete over the live ledger's cells.
    CellPicker { key: String },
    /// AuthRequired tier / collateral mode / finality (a fixed variant set).
    Enum { key: String, variants: Vec<String> },
    /// EffectMask facets / permission matrix (a named bit set).
    BitMask { key: String, bits: Vec<String> },
    /// recursive: a nested gadget (Pred AnyOf/AllOf, a CallTree child).
    SubGadget { key: String, kind: GadgetKind },
    /// a homogeneous list of nested gadgets (`Vec<Effect>`, caveat chain).
    List { key: String, item: GadgetKind },
}

impl GadgetField {
    /// The field's key (its form label / set() selector).
    pub fn key(&self) -> &str {
        match self {
            GadgetField::HexBytes { key, .. }
            | GadgetField::U64 { key, .. }
            | GadgetField::I64 { key }
            | GadgetField::CellPicker { key }
            | GadgetField::Enum { key, .. }
            | GadgetField::BitMask { key, .. }
            | GadgetField::SubGadget { key, .. }
            | GadgetField::List { key, .. } => key,
        }
    }
}

/// A value set into one [`GadgetField`] (the edit the thin gpui layer performs).
/// Validated live by the gadget's [`Gadget::set`] / [`Gadget::validate`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GadgetInput {
    /// A raw byte blob (a HexBytes field).
    Bytes(Vec<u8>),
    /// An unsigned scalar (a U64 field).
    U64(u64),
    /// A signed scalar (an I64 field).
    I64(i64),
    /// A cell designation (a CellPicker field).
    Cell(CellId),
    /// An enum variant choice, by name (an Enum field).
    Variant(String),
    /// A bit-set selection, by name (a BitMask field).
    Bits(Vec<String>),
}

/// The live, fail-closed validation verdict a gadget exposes (the form's red/green).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GadgetValidation {
    /// The form is complete and the value is buildable.
    Ok,
    /// The form is incomplete or invalid — surfaced, never swallowed (the
    /// fail-closed discipline: an unfinished/illegal value cannot build).
    Invalid { reason: String },
}

impl GadgetValidation {
    /// `true` iff the gadget would build (the green state).
    pub fn is_ok(&self) -> bool {
        matches!(self, GadgetValidation::Ok)
    }
    /// `true` iff the gadget is fail-closed (will NOT build) — the safety read a
    /// composer's "is this an attenuation / a non-empty condition" check returns.
    pub fn is_fail_closed(&self) -> bool {
        matches!(self, GadgetValidation::Invalid { .. })
    }
}

/// Why a gadget could not materialize its value (the build-time failure).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GadgetError {
    /// The form is not yet valid (validate() would refuse).
    Incomplete { reason: String },
    /// The lowering into the protocol value failed (a domain rule).
    Lowering { reason: String },
}

/// THE construction trait. A gadget builds ONE protocol value through a uniform
/// field-form: [`Gadget::fields`] → [`Gadget::set`] → [`Gadget::validate`] →
/// [`Gadget::build`]. The thin gpui layer renders [`GadgetField`]s generically
/// and feeds [`GadgetInput`]s back through `set`. L1 defines this shape; the
/// concrete gadgets (Predicate Composer, Cap Attenuator, …) are later lanes.
pub trait Gadget {
    /// The protocol value this gadget builds (`StateConstraint`, `Effect`,
    /// `Turn`, `AttenuatedCap`, or a `VerificationResult`).
    type Output;
    /// The form the thin gpui layer renders (one widget per [`GadgetField`]).
    fn fields(&self) -> Vec<GadgetField>;
    /// Edit one field, validated live (the form's keystroke handler).
    fn set(&mut self, field: &str, v: GadgetInput);
    /// The live fail-closed check (e.g. `is_attenuation`, non-empty condition).
    fn validate(&self) -> GadgetValidation;
    /// Materialize the protocol value (fails closed if `validate` is not `Ok`).
    fn build(&self) -> Result<Self::Output, GadgetError>;
}

/// A gadget that emits a Turn additionally offers predict-then-commit — the SAME
/// `IntentDraft → simulate → commit` flow `wonder.rs`'s `DragValue` already uses.
/// This is the uniform "produces a real value that flows through the verified
/// executor" shape: every committing gadget reuses `simulate.rs` verbatim (it
/// does NOT invent a parallel construction path).
pub trait CommittingGadget: Gadget {
    /// Lower the gadget's current state into the real [`IntentDraft`] (the same
    /// draft shape the SIMULATE/COMPOSER panel and the wonder-room drag build).
    fn to_draft(&self, world: &World) -> Result<IntentDraft, GadgetError>;

    /// PREDICT the turn's consequences WITHOUT committing — reuses
    /// [`simulate::simulate`] on a fork of the live world (the live world is
    /// untouched; a bad value surfaces as a refusal here, before anything moves).
    fn predict(&self, world: &World) -> SimOutcome {
        match self.to_draft(world) {
            Ok(draft) => simulate::simulate(world, &draft),
            // An un-buildable gadget predicts a static refusal over an empty draft
            // (the same fail-closed verdict the static rail returns for a malformed
            // intent) — never a panic, never a faked commit.
            Err(_) => simulate::simulate(world, &IntentDraft::new(self.agent())),
        }
    }

    /// COMMIT the turn for real — reuses [`simulate::commit`] (the identical turn
    /// the prediction previewed, now on the live world). Fails closed if the
    /// gadget cannot lower (returns the executor's own rejection shape).
    fn commit(&self, world: &mut World) -> CommitOutcome {
        match self.to_draft(world) {
            Ok(draft) => simulate::commit(world, &draft),
            Err(e) => CommitOutcome::Rejected {
                reason: format!("gadget could not lower to a turn: {e:?}"),
                at_action: vec![],
            },
        }
    }

    /// The agent cell that authorizes this gadget's turn (the draft's principal).
    fn agent(&self) -> CellId;
}

// ===========================================================================
// §1.5 — the generalized Halo (the per-object direct-manipulation ring)
// ===========================================================================

/// One **halo command** — a single pokeable affordance in the ring the renderer
/// draws around an object. Generalized from `wonder.rs`'s 3-command ring: the
/// universal three (`Inspect`/`Grab`/`Explain`) apply to ANY [`Presentable`], and
/// per-kind commands extend the ring exactly as `Message` vocabularies extend per
/// `InspectFocus` (a receipt's halo carries `VerifyChain`; a cap's, `Attenuate`).
///
/// `Inspect` opens the object's presentation SET (the tabbed [`Presentable::present`]
/// result, generalizing today's single-`Inspectable` open); `Grab` arms a
/// [`CommittingGadget`]; `Explain` speaks from the RawFields + DomainVisual faces.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HaloCommand {
    /// Open the object's full presentation set (the tabbed inspector).
    Inspect,
    /// Arm a committing gadget (the `DragValue` intent generalizes).
    Grab,
    /// Speak a plain sentence from the RawFields + DomainVisual presentations.
    Explain,
    /// (Receipt-kind) verify the receipt chain — a read-only verifier gadget.
    VerifyChain,
    /// (Cap-kind) attenuate the held authority — a value gadget.
    Attenuate,
}

impl HaloCommand {
    /// A short label (the adept's read of the ring button).
    pub fn label(&self) -> &'static str {
        match self {
            HaloCommand::Inspect => "inspect",
            HaloCommand::Grab => "grab",
            HaloCommand::Explain => "explain",
            HaloCommand::VerifyChain => "verify-chain",
            HaloCommand::Attenuate => "attenuate",
        }
    }

    /// A wonder-first glyph (a child reads the glyph; an adept reads the label).
    pub fn glyph(&self) -> &'static str {
        match self {
            HaloCommand::Inspect => "○",
            HaloCommand::Grab => "✊",
            HaloCommand::Explain => "?",
            HaloCommand::VerifyChain => "✓",
            HaloCommand::Attenuate => "▽",
        }
    }
}

/// The per-object command ring. The universal three are on EVERY object; per-kind
/// commands are appended by [`Halo::for_kind`] (the ring is data, extended per
/// `ObjectKind`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Halo {
    /// The object kind this ring is for (drives the per-kind extension).
    pub kind: ObjectKind,
    /// The commands, in render order (the universal three first, then per-kind).
    pub commands: Vec<HaloCommand>,
}

impl Halo {
    /// The universal three commands every object carries (the `wonder.rs` ring).
    pub const UNIVERSAL: [HaloCommand; 3] =
        [HaloCommand::Inspect, HaloCommand::Grab, HaloCommand::Explain];

    /// The ring for a given object kind: the universal three plus the per-kind
    /// commands (a receipt gains `VerifyChain`; a capability gains `Attenuate`).
    pub fn for_kind(kind: ObjectKind) -> Self {
        let mut commands = Halo::UNIVERSAL.to_vec();
        match kind {
            ObjectKind::Receipt | ObjectKind::Proof => commands.push(HaloCommand::VerifyChain),
            ObjectKind::Capability => commands.push(HaloCommand::Attenuate),
            _ => {}
        }
        Halo { kind, commands }
    }

    /// Does this ring carry `cmd`?
    pub fn has(&self, cmd: HaloCommand) -> bool {
        self.commands.contains(&cmd)
    }
}

// ===========================================================================
// §1.3 + Registry — the thin-newtype dispatch to a Presentable
// ===========================================================================

/// A thin newtype wrapping a live ledger cell as a [`Presentable`] — the
/// established "reflect a foreign struct into a starbridge view" pattern
/// (`reflect.rs`'s `reflect_cell`, `organs.rs`'s `TrustlineReflection`). The
/// cell lives in the foreign `dregg_cell` crate, so we register via this wrapper
/// rather than `impl Presentable for Cell` directly.
#[derive(Clone, Debug)]
pub struct ReflectedCell {
    /// The cell's id (the navigable focus).
    pub id: CellId,
    /// A snapshot of the cell (cloned off the live ledger at build time). The
    /// presentations that need the LIVE world (Affordances, Provenance, Graph)
    /// re-read it from `ctx.world`; this snapshot carries the per-cell state.
    pub cell: Cell,
}

impl ReflectedCell {
    /// Wrap the live cell `id` if it is present in the world's ledger.
    pub fn from_world(world: &World, id: CellId) -> Option<Self> {
        world.ledger().get(&id).map(|c| ReflectedCell { id, cell: c.clone() })
    }
}

impl Presentable for ReflectedCell {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Cell
    }

    fn present(&self, ctx: &PresentCtx) -> Vec<Presentation> {
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor, the genuine reflect_cell verbatim.
        let insp = reflect::reflect_cell(&self.id, &self.cell);
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Cell State".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // (2) Affordances — "the messages it understands", the genuine InspectAct
        //     surface projected for the viewer (full vocabulary + cap badges). The
        //     viewer's authority is DERIVED off the live ledger (the membrane property:
        //     the lens divides per-viewer because the authority does) — ownership →
        //     root `None`, else the widest c-list cap reaching the cell, else the
        //     weakest `Impossible`. Never a uniform guess.
        let viewer_rights =
            crate::inspect_act::viewer_authority_over(ctx.world, ctx.viewer, self.id);
        let ia = InspectAct::build(
            ctx.world,
            InspectFocus::Cell(self.id),
            ctx.viewer,
            viewer_rights,
        );
        let aff_text = ia
            .messages
            .iter()
            .map(|m| format!("{} {}", m.name, m.effect))
            .collect::<Vec<_>>()
            .join(" ");
        out.push(Presentation {
            kind: PresentationKind::Affordances,
            label: "Messages Understood".to_string(),
            search_text: format!("affordances {aff_text}"),
            body: PresentationBody::Fields(messages_as_inspectable(&self.id, &ia)),
        });

        // (3) Provenance — the receipt chain this cell authored, off the live log.
        let timeline = cell_provenance(ctx.world, &self.id);
        let prov_text = timeline
            .events
            .iter()
            .map(|e| e.label.as_str())
            .collect::<Vec<_>>()
            .join(" ");
        out.push(Presentation {
            kind: PresentationKind::Provenance,
            label: "Receipt Lineage".to_string(),
            search_text: format!("provenance {prov_text}"),
            body: PresentationBody::Timeline(timeline),
        });

        // (4) Graph — the cell's ocap neighborhood (its outbound + inbound edges),
        //     the genuine graph.rs primitives read off the live ledger.
        let graph = cell_ocap_view(ctx.world, &self.id);
        out.push(Presentation {
            kind: PresentationKind::Graph,
            label: "ocap Graph".to_string(),
            search_text: format!(
                "graph {} edges {} nodes",
                graph.edges.len(),
                graph.nodes.len()
            ),
            body: PresentationBody::Graph(graph),
        });

        // (5) DomainVisual — the lifecycle STATE MACHINE, with the cell's current
        //     state, read off the real CellLifecycle.
        let sm = lifecycle_state_machine(&self.cell);
        out.push(Presentation {
            kind: PresentationKind::DomainVisual,
            label: "Lifecycle".to_string(),
            search_text: format!("lifecycle {}", sm.current),
            body: PresentationBody::StateMachine(sm),
        });

        out
    }
}

/// Project the genuine [`InspectAct`] message list into an [`Inspectable`] body
/// (the Affordances kind reuses the RawFields render path — each message is a
/// field whose value is its required-rights + cap badge). The MESSAGES are the
/// real `inspect_act` surface; this only re-houses them as a field tree so the
/// gpui layer renders Affordances with the existing field-tree widget.
fn messages_as_inspectable(id: &CellId, ia: &InspectAct) -> Inspectable {
    let fields = ia
        .messages
        .iter()
        .map(|m| {
            reflect::Field::text(
                m.name.clone(),
                format!(
                    "{} · requires {:?} · {}",
                    m.effect,
                    m.required,
                    if m.authorized { "you may send" } else { "refused: insufficient authority" }
                ),
            )
        })
        .collect();
    Inspectable {
        kind: ObjectKind::Cell,
        title: format!("Messages · Cell {}", reflect::short_hex(id.as_bytes())),
        subtitle: format!("{} message(s) understood", ia.messages.len()),
        fields,
    }
}

/// Build the cell's provenance [`TimelineView`] off the live receipt log: every
/// receipt this cell AUTHORED (its `agent`), in commit order. Reads the real log
/// (`world.receipts()`), never a parallel chain model.
fn cell_provenance(world: &World, id: &CellId) -> TimelineView {
    let events = world
        .receipts()
        .iter()
        .enumerate()
        .filter(|(_, r)| &r.agent == id)
        .map(|(i, r)| TimelineEvent {
            at: i as u64,
            label: format!(
                "receipt {} · {} action(s) · {} computrons",
                reflect::short_hex(&r.receipt_hash()),
                r.action_count,
                r.computrons_used
            ),
            hash: Some(r.receipt_hash()),
        })
        .collect();
    TimelineView { events }
}

/// Build the cell's ocap neighborhood as a [`GraphView`]: the whole-image ocap
/// graph (`graph.rs`) restricted to this cell's node + its inbound/outbound
/// edges. The genuine graph primitives, read off the live ledger.
fn cell_ocap_view(world: &World, id: &CellId) -> GraphView {
    let g = OcapGraph::build(world);
    // The edges touching this cell (either end).
    let edges: Vec<crate::graph::GraphEdge> = g
        .edges()
        .iter()
        .filter(|e| &e.holder == id || &e.target == id)
        .cloned()
        .collect();
    // The nodes those edges (plus this cell) span.
    let mut node_ids: BTreeSet<CellId> = BTreeSet::new();
    node_ids.insert(*id);
    for e in &edges {
        node_ids.insert(e.holder);
        node_ids.insert(e.target);
    }
    let nodes: Vec<crate::graph::GraphNode> = g
        .nodes()
        .iter()
        .filter(|n| node_ids.contains(&n.cell))
        .cloned()
        .collect();
    GraphView { nodes, edges, focus: Some(*id) }
}

/// Build the cell's lifecycle [`StateMachineView`] from the real `CellLifecycle`.
/// The four canonical states + the verb transitions between them, with the live
/// `current` read off the cell's actual lifecycle.
fn lifecycle_state_machine(cell: &Cell) -> StateMachineView {
    use dregg_cell::lifecycle::CellLifecycle;
    let states = vec![
        SmState { name: "Live".to_string(), terminal: false },
        SmState { name: "Sealed".to_string(), terminal: false },
        SmState { name: "Destroyed".to_string(), terminal: true },
        SmState { name: "Migrated".to_string(), terminal: true },
        SmState { name: "Archived".to_string(), terminal: false },
    ];
    let transitions = vec![
        SmTransition { from: "Live".to_string(), to: "Sealed".to_string(), verb: "Seal".to_string() },
        SmTransition { from: "Sealed".to_string(), to: "Live".to_string(), verb: "Unseal".to_string() },
        SmTransition { from: "Live".to_string(), to: "Destroyed".to_string(), verb: "Destroy".to_string() },
        SmTransition { from: "Live".to_string(), to: "Migrated".to_string(), verb: "Migrate".to_string() },
        SmTransition { from: "Live".to_string(), to: "Archived".to_string(), verb: "Archive".to_string() },
    ];
    let current = match cell.lifecycle {
        CellLifecycle::Live => "Live",
        CellLifecycle::Sealed { .. } => "Sealed",
        CellLifecycle::Destroyed { .. } => "Destroyed",
        CellLifecycle::Migrated { .. } => "Migrated",
        CellLifecycle::Archived { .. } => "Archived",
    }
    .to_string();
    StateMachineView { states, transitions, current }
}

// ===========================================================================
// §1.1 (registry) — focus → Presentable dispatch
// ===========================================================================

/// What the registry focuses on. Today a cell (the only Live `impl Presentable`
/// in L1); the variants extend per `ObjectKind` exactly as `InspectFocus` does
/// — the dispatch shape is identical, only the wrapper differs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FocusTarget {
    /// A live ledger cell (resolves to [`ReflectedCell`]).
    Cell(CellId),
    /// A UI **view cell** — the inspector's own `(focus, present_idx)` camera-aim,
    /// self-hosted as a real cell (`docs/deos/REFLEXIVE-MIGRATION.md` §3). Anchored
    /// on the view's backing cell id, it resolves to a
    /// [`ViewCell`](crate::view_cell::ViewCell) `impl Presentable` — so the
    /// inspector can focus on ITSELF (inspect the inspector). The keystone reflexive
    /// arm: "new object kinds add one arm."
    ViewCell(CellId),
    /// A **meta-debug frame** — a suspended/frozen world AS AN OBJECT, at a level in
    /// the reflective tower (`docs/deos/FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §2.3,
    /// `docs/deos/REFLEXIVE-MIGRATION.md` §4.2). Resolves to a
    /// [`MetaDebugView`](crate::meta_debug::MetaDebugView) `impl Presentable` looked
    /// up in the cockpit's [`MetaStack`](crate::meta_debug::MetaStack) — so
    /// "debug the debugger" is focusing the inspector on a meta-level's own view,
    /// recursion through the SAME `present()` dispatch. The fractal meta-debug arm.
    DebugFrame(crate::meta_debug::MetaLevelId),
    /// The whole live **World** AS AN OBJECT (a `ReadState` mirror over the World) —
    /// the frozen-but-live head a Suspend inspection points at. Resolves to a
    /// [`MetaDebugView`](crate::meta_debug::MetaDebugView) at the base level.
    World,
    /// The running **Cockpit** AS AN OBJECT — the desktop image reflected on itself.
    /// Resolves (like `World`) to a base meta-debug view over the live world the
    /// cockpit drives. The third meta-arm scoped in §2.3.
    Cockpit,
}

impl FocusTarget {
    /// The cell id this focus anchors on (every focus kind anchors on a cell-shaped
    /// id — a real ledger cell for `Cell`/`ViewCell`, a stable synthetic anchor for
    /// the meta arms, which are frame-objects not ledger cells). The anchor is the
    /// memo key; the meta arms' anchors are never in the ledger.
    pub fn cell(&self) -> CellId {
        match self {
            FocusTarget::Cell(id) => *id,
            FocusTarget::ViewCell(id) => *id,
            FocusTarget::DebugFrame(level) => level.debug_frame_anchor(),
            // The World/Cockpit-as-object both anchor on the base meta-level.
            FocusTarget::World | FocusTarget::Cockpit => {
                crate::meta_debug::MetaLevelId::BASE.debug_frame_anchor()
            }
        }
    }
}

/// THE REGISTRY — resolves a focused protocol object to its presentation set +
/// its halo ring. It reads the live world fresh every call (never a stale cache,
/// matching the `OcapGraph::build`/`OrganSurvey::build` "scan the live ledger
/// every render" pattern). The registry knows the dispatch from a [`FocusTarget`]
/// to the right newtype [`Presentable`]; new object kinds add one arm.
pub struct Registry<'w> {
    world: &'w World,
    /// The reflective tower the meta-debug arms ([`FocusTarget::DebugFrame`] /
    /// `::World` / `::Cockpit`) resolve through. `None` when no meta-debug session
    /// is open (the common case — the cockpit passes its live
    /// [`MetaStack`](crate::meta_debug::MetaStack) when one is). A meta arm with no
    /// stack resolves to `None` (a dangling meta-focus, surfaced honestly).
    meta_stack: Option<&'w crate::meta_debug::MetaStack>,
}

impl<'w> Registry<'w> {
    /// Build a registry over the live world (no meta-debug session — the meta arms
    /// resolve to `None`).
    pub fn new(world: &'w World) -> Self {
        Registry { world, meta_stack: None }
    }

    /// Build a registry that ALSO resolves the meta-debug arms through `meta_stack`
    /// — the fractal meta-debug dispatch. A [`FocusTarget::DebugFrame(level)`] looks
    /// the level up here and projects its [`MetaDebugView`](crate::meta_debug::MetaDebugView).
    pub fn with_meta_stack(
        world: &'w World,
        meta_stack: &'w crate::meta_debug::MetaStack,
    ) -> Self {
        Registry { world, meta_stack: Some(meta_stack) }
    }

    /// Resolve the meta arms (`DebugFrame`/`World`/`Cockpit`) to a
    /// [`MetaDebugView`](crate::meta_debug::MetaDebugView), if a meta-stack is held
    /// and the level is materialized. `World`/`Cockpit` resolve to the base level;
    /// `DebugFrame(level)` to that exact level. The shared tail of the three meta
    /// arms — pure lookup, no projection here.
    fn meta_view_for(&self, target: FocusTarget) -> Option<crate::meta_debug::MetaDebugView> {
        let stack = self.meta_stack?;
        let level = match target {
            FocusTarget::DebugFrame(level) => level,
            FocusTarget::World | FocusTarget::Cockpit => crate::meta_debug::MetaLevelId::BASE,
            _ => return None,
        };
        stack.get(level).copied()
    }

    /// Resolve `target` to its presentation set, projected for `viewer`. `None`
    /// iff the focused object is absent from the live world (a dangling focus —
    /// surfaced honestly, never faked).
    pub fn present(&self, target: FocusTarget, viewer: CellId) -> Option<Vec<Presentation>> {
        let ctx = PresentCtx::for_viewer(self.world, viewer);
        match target {
            FocusTarget::Cell(id) => {
                ReflectedCell::from_world(self.world, id).map(|c| c.present(&ctx))
            }
            // THE REFLEXIVE ARM — resolve a view cell from its WITNESSED (committed)
            // state on the live ledger, then project it. The Registry holds only
            // `&world`, so it reconstructs the `ViewCell` from the backing cell's
            // committed camera-aim (the prior-frame state the projector reads — the
            // unit-delay that breaks the self-cycle). `None` iff the backing cell is
            // absent (a dangling view focus, surfaced honestly).
            FocusTarget::ViewCell(id) => {
                let view = crate::view_cell::ViewCell::from_world(self.world, id)?;
                Some(view.present(&ctx))
            }
            // THE FRACTAL META-DEBUG ARM — resolve a meta-level from the reflective
            // tower (the MetaStack) and project the suspended world AS AN OBJECT. The
            // recursion (debug the debugger) is this SAME dispatch at a higher level.
            // `None` iff no meta-stack is held or the level is unmaterialized (a
            // dangling meta-focus, surfaced honestly).
            FocusTarget::DebugFrame(_) | FocusTarget::World | FocusTarget::Cockpit => {
                let view = self.meta_view_for(target)?;
                Some(view.present(&ctx))
            }
        }
    }

    /// The object kind a focus resolves to (drives the halo ring).
    pub fn object_kind(&self, target: FocusTarget) -> ObjectKind {
        match target {
            FocusTarget::Cell(_) => ObjectKind::Cell,
            FocusTarget::ViewCell(_) => ObjectKind::Cell,
            // A meta-debug frame is an image-shaped object (a whole world-as-object).
            FocusTarget::DebugFrame(_) | FocusTarget::World | FocusTarget::Cockpit => {
                ObjectKind::Image
            }
        }
    }

    /// The halo ring for a focus (the universal three + the per-kind commands).
    pub fn halo(&self, target: FocusTarget) -> Halo {
        Halo::for_kind(self.object_kind(target))
    }
}

// ===========================================================================
// M2 — THE PROJECTION MEMO around the UNCHANGED-pure `Registry::present`.
//
// `Registry::present(target, viewer)` is a pure function of `(target, viewer,
// world-state)`. This wraps it — it does NOT rewrite it — in a memo valid
// exactly while the live head (`WitnessCursor`) is unchanged. A new receipt
// advances the head; the cockpit's delta fold (`world.dynamics().since(cursor)`)
// drops every cell the delta named, so a cell the turn did NOT touch reuses its
// cached projection across the head advance. The ONLY way a stale entry survives
// is a state change with no naming `WorldEvent` — the cache-soundness =
// dynamics-completeness obligation closed by `world::collect_effect_events`'s
// completeness arms (`docs/deos/EFFICIENCY-WELD-PLAN.md` §4.1, §2.3).
//
// Interior mutability (`RefCell`) so the cockpit's `&self` moldable render path
// can read-through-and-fill without threading `&mut self` through the whole
// render closure (mirrors `World::state_root_memo`'s `Cell` memo, M1).
// ===========================================================================

use std::cell::RefCell;
use std::collections::HashMap;

use crate::ui_snapshot::WitnessCursor;

/// A `(focus-cell, viewer) -> projected presentation set` memo, valid while the
/// live head is unchanged. Wraps the pure [`Registry::present`].
#[derive(Default)]
pub struct PresentMemo {
    inner: RefCell<PresentMemoInner>,
}

#[derive(Default)]
struct PresentMemoInner {
    /// The live head the cached entries were projected at. When the head moves,
    /// entries the delta fold did NOT invalidate are still valid (a cell the turn
    /// didn't touch projects identically); a touched cell's entry was already
    /// dropped by the fold, so this recomputes on miss.
    cursor: Option<WitnessCursor>,
    /// (focus-cell, viewer) -> projected presentation set at `cursor`.
    entries: HashMap<(CellId, CellId), Vec<Presentation>>,
}

impl PresentMemo {
    pub fn new() -> Self {
        Self::default()
    }

    /// The memoized projector. On a head advance the cursor is recorded but
    /// entries are KEPT (the fold dropped the dirty ones). On a hit the cached set
    /// is cloned; on a miss the pure [`Registry`] recomputes and fills.
    ///
    /// `None` iff the focused object is absent from the live world (a dangling
    /// focus — surfaced honestly, never cached as `Some`).
    pub fn present(
        &self,
        world: &World,
        target: FocusTarget,
        viewer: CellId,
    ) -> Option<Vec<Presentation>> {
        let head = WitnessCursor::at_head(world);
        let key = (target.cell(), viewer);
        {
            let mut inner = self.inner.borrow_mut();
            // If the head advanced, drop the whole cache ONLY when the caller did
            // not feed deltas (defensive); normal operation: the cockpit's fold
            // already invalidated the dirty cells, so keep clean entries.
            if inner.cursor != Some(head) {
                inner.cursor = Some(head);
            }
            if let Some(hit) = inner.entries.get(&key) {
                return Some(hit.clone());
            }
        }
        let set = Registry::new(world).present(target, viewer)?;
        self.inner.borrow_mut().entries.insert(key, set.clone());
        Some(set)
    }

    /// Drop a single cell's cached projections (every viewer) — the per-cell
    /// delta invalidation the fold drives.
    pub fn invalidate_cell(&self, cell: CellId) {
        self.inner.borrow_mut().entries.retain(|(c, _), _| *c != cell);
    }

    /// Cap-edge deltas reach OTHER cells' affordance badges (viewer-non-local,
    /// §4.2): drop everything. Coarse but correct.
    pub fn invalidate_affordances_all(&self) {
        self.inner.borrow_mut().entries.clear();
    }

    /// Drop the entire cache — used when `self.cells` is rebuilt from a
    /// ZERO-sentinel `CellBorn` (a new child whose id we don't yet know).
    pub fn invalidate_all(&self) {
        self.inner.borrow_mut().entries.clear();
    }

    /// Test/instrumentation: how many entries are cached right now.
    pub fn len(&self) -> usize {
        self.inner.borrow().entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

// ===========================================================================
// §1.4 — the Spotter (universal search over the presentation index)
// ===========================================================================

/// One ranked search hit: the object it found, the presentation kind that
/// matched, a snippet, and the score (higher is better). Reuses
/// `inspect_act.rs`'s `InspectFocus` as the navigable focus (so a hit jumps
/// straight into the inspect→act loop).
#[derive(Clone, Debug)]
pub struct SpotterHit {
    /// The navigable focus the hit resolves to.
    pub focus: InspectFocus,
    /// The presentation kind whose `search_text` matched.
    pub matched_kind: PresentationKind,
    /// A short snippet (the matched presentation's label).
    pub snippet: String,
    /// The fuzzy score (from `palette::fuzzy_score`); higher ranks first.
    pub score: i32,
}

/// THE SPOTTER — universal search over every live object's every presentation,
/// indexed by [`Presentation::search_text`] and ranked with the cockpit's own
/// `palette::fuzzy_score` (no parallel matcher). The index is built lazily off
/// the live world (cells, today), never a stale cache.
pub struct Spotter<'w> {
    world: &'w World,
    viewer: CellId,
}

impl<'w> Spotter<'w> {
    /// A spotter over the live world, searching as `viewer` (the Affordances cap
    /// badges that contribute to search_text divide on it).
    pub fn new(world: &'w World, viewer: CellId) -> Self {
        Spotter { world, viewer }
    }

    /// Search every live object's every presentation. Returns ranked hits (best
    /// first), each naming the object, the presentation kind that matched, and a
    /// navigable focus. Empty query ⟹ no hits (a Spotter is search, not a list).
    pub fn search(&self, query: &str) -> Vec<SpotterHit> {
        if query.trim().is_empty() {
            return Vec::new();
        }
        let ctx = PresentCtx::for_viewer(self.world, self.viewer);
        let mut hits: Vec<SpotterHit> = Vec::new();

        // Index every live cell's every presentation (the only Live impl today).
        let mut cells: Vec<CellId> = self.world.ledger().iter().map(|(id, _)| *id).collect();
        cells.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));

        for id in cells {
            let Some(refl) = ReflectedCell::from_world(self.world, id) else {
                continue;
            };
            for p in refl.present(&ctx) {
                // Score the search_text AND the label; take the better of the two.
                let text_score = crate::palette::fuzzy_score(query, &p.search_text);
                let label_score = crate::palette::fuzzy_score(query, &p.label);
                let best = match (text_score, label_score) {
                    (Some(a), Some(b)) => Some(a.max(b)),
                    (Some(a), None) => Some(a),
                    (None, Some(b)) => Some(b),
                    (None, None) => None,
                };
                if let Some(score) = best {
                    hits.push(SpotterHit {
                        focus: InspectFocus::Cell(id),
                        matched_kind: p.kind,
                        snippet: p.label.clone(),
                        score,
                    });
                }
            }
        }

        // Best score first; ties broken by object order (stable, via id sort above).
        hits.sort_by(|a, b| b.score.cmp(&a.score));
        hits
    }

    /// The best (top-ranked) hit for a query, if any (the ⌘-Enter "jump to first").
    pub fn best(&self, query: &str) -> Option<SpotterHit> {
        self.search(query).into_iter().next()
    }
}

// ===========================================================================
// TESTS — the model, proven gpui-free (exactly as reflect.rs's tests are).
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{transfer, World};

    /// A two-cell world: a treasury (1_000) and a sink (0), no turns yet.
    fn two_cell_world() -> (World, CellId, CellId) {
        let mut w = World::new();
        let treasury = w.genesis_cell(0x11, 1_000);
        let sink = w.genesis_cell(0x22, 0);
        (w, treasury, sink)
    }

    // ── the universal-coverage floor ────────────────────────────────────────

    #[test]
    fn every_presentable_yields_a_nonempty_raw_fields_floor() {
        // THE INVARIANT: RawFields is ALWAYS present, and it is a non-empty field
        // tree (the genuine reflect_cell projection).
        let (w, treasury, _sink) = two_cell_world();
        let refl = ReflectedCell::from_world(&w, treasury).expect("the cell exists");
        let ctx = PresentCtx::new(&w, treasury);

        assert!(refl.has_raw_fields_floor(&ctx), "RawFields is the mandatory floor");

        let set = refl.present(&ctx);
        let raw = set
            .iter()
            .find(|p| p.kind == PresentationKind::RawFields)
            .expect("the floor is present");
        match &raw.body {
            PresentationBody::Fields(i) => {
                assert!(!i.fields.is_empty(), "the RawFields body is a non-empty field tree");
                assert!(i.fields.iter().any(|f| f.key == "balance"));
            }
            other => panic!("RawFields must carry a Fields body, got {other:?}"),
        }
    }

    // ── the Cell impl offers ≥4 distinct presentation kinds ─────────────────

    #[test]
    fn the_cell_impl_offers_at_least_four_distinct_presentation_kinds() {
        // The proof-of-shape: a real World cell emits a multi-presentation set
        // spanning RawFields + Affordances + Provenance + Graph + DomainVisual.
        let (w, treasury, _sink) = two_cell_world();
        let refl = ReflectedCell::from_world(&w, treasury).unwrap();
        let ctx = PresentCtx::new(&w, treasury);

        let kinds = refl.presentation_kinds(&ctx);
        assert!(
            kinds.len() >= 4,
            "the Cell impl offers ≥4 distinct presentation kinds, got {kinds:?}"
        );
        // The specific set the spec demands.
        assert!(kinds.contains(&PresentationKind::RawFields));
        assert!(kinds.contains(&PresentationKind::Affordances));
        assert!(kinds.contains(&PresentationKind::Provenance));
        assert!(kinds.contains(&PresentationKind::Graph));
        assert!(kinds.contains(&PresentationKind::DomainVisual));
    }

    #[test]
    fn the_affordances_presentation_carries_the_real_message_surface() {
        // The Affordances body is the genuine inspect_act vocabulary (peek/touch/
        // write/grant), re-housed as a field tree — not a stub.
        let (w, treasury, _sink) = two_cell_world();
        let refl = ReflectedCell::from_world(&w, treasury).unwrap();
        let ctx = PresentCtx::new(&w, treasury);
        let set = refl.present(&ctx);
        let aff = set
            .iter()
            .find(|p| p.kind == PresentationKind::Affordances)
            .expect("Affordances present");
        match &aff.body {
            PresentationBody::Fields(i) => {
                assert!(i.fields.iter().any(|f| f.key == "peek"));
                assert!(i.fields.iter().any(|f| f.key == "grant"));
            }
            other => panic!("Affordances should carry a Fields body, got {other:?}"),
        }
    }

    #[test]
    fn the_lifecycle_domain_visual_reads_the_real_lifecycle() {
        // The DomainVisual state machine reads the cell's real CellLifecycle —
        // a fresh cell is Live.
        let (w, treasury, _sink) = two_cell_world();
        let refl = ReflectedCell::from_world(&w, treasury).unwrap();
        let ctx = PresentCtx::new(&w, treasury);
        let set = refl.present(&ctx);
        let dv = set
            .iter()
            .find(|p| p.kind == PresentationKind::DomainVisual)
            .unwrap();
        match &dv.body {
            PresentationBody::StateMachine(sm) => {
                assert_eq!(sm.current, "Live", "a fresh cell is Live");
                assert!(sm.states.iter().any(|s| s.name == "Destroyed" && s.terminal));
                assert!(sm.transitions.iter().any(|t| t.verb == "Seal"));
            }
            other => panic!("Lifecycle should carry a StateMachine body, got {other:?}"),
        }
    }

    // ── a presentation's body reflects the LIVE ledger (after a real turn) ───

    #[test]
    fn a_presentation_reflects_the_live_ledger_after_a_real_turn() {
        // The set is a LIVE projection, not a snapshot of a moment: after a real
        // committed transfer, the RawFields balance + the Provenance receipt
        // lineage of the SAME cell move.
        let (mut w, treasury, sink) = two_cell_world();

        // Before: treasury balance 1_000, no provenance receipts authored by it.
        {
            let refl = ReflectedCell::from_world(&w, treasury).unwrap();
            let ctx = PresentCtx::new(&w, treasury);
            let set = refl.present(&ctx);
            let prov = set
                .iter()
                .find(|p| p.kind == PresentationKind::Provenance)
                .unwrap();
            match &prov.body {
                PresentationBody::Timeline(t) => {
                    assert!(t.events.is_empty(), "no receipts authored yet");
                }
                _ => unreachable!(),
            }
        }

        // Commit a real transfer treasury → sink.
        let turn = w.turn(treasury, vec![transfer(treasury, sink, 250)]);
        assert!(w.commit_turn(turn).is_committed());

        // After: the RawFields balance is 750 and the Provenance timeline carries
        // the receipt the treasury just authored — re-read off the live world.
        let refl = ReflectedCell::from_world(&w, treasury).unwrap();
        let ctx = PresentCtx::new(&w, treasury);
        let set = refl.present(&ctx);

        let raw = set.iter().find(|p| p.kind == PresentationKind::RawFields).unwrap();
        match &raw.body {
            PresentationBody::Fields(i) => assert!(
                i.fields.iter().any(|f| matches!(f.value, reflect::FieldValue::Balance(750))),
                "the RawFields balance reflects the committed transfer (750)"
            ),
            _ => unreachable!(),
        }
        let prov = set.iter().find(|p| p.kind == PresentationKind::Provenance).unwrap();
        match &prov.body {
            PresentationBody::Timeline(t) => {
                assert_eq!(t.events.len(), 1, "the authored receipt appears in the lineage");
                assert!(t.events[0].hash.is_some(), "the receipt is navigable");
            }
            _ => unreachable!(),
        }
    }

    // ── the registry dispatch ───────────────────────────────────────────────

    #[test]
    fn the_registry_resolves_a_focus_to_its_presentation_set() {
        let (w, treasury, _sink) = two_cell_world();
        let reg = Registry::new(&w);
        let set = reg
            .present(FocusTarget::Cell(treasury), treasury)
            .expect("the focused cell resolves");
        assert!(set.iter().any(|p| p.kind == PresentationKind::RawFields));
        assert_eq!(reg.object_kind(FocusTarget::Cell(treasury)), ObjectKind::Cell);
    }

    #[test]
    fn the_registry_surfaces_a_dangling_focus_honestly() {
        // A focus on a cell not in the ledger resolves to None (never a faked set).
        let w = World::new();
        let ghost = CellId::derive_raw(&[0xFEu8; 32], &[0u8; 32]);
        let reg = Registry::new(&w);
        assert!(reg.present(FocusTarget::Cell(ghost), ghost).is_none());
    }

    // ── the Spotter finds a cell by its presentation search_text ────────────

    #[test]
    fn the_spotter_finds_a_cell_by_its_presentation_search_text() {
        let (w, treasury, _sink) = two_cell_world();
        let spotter = Spotter::new(&w, treasury);

        // The RawFields body's search_text carries the cell's title ("Cell <hex>")
        // and field keys — searching "ocap Graph" finds the graph presentation, and
        // searching "lifecycle" finds the DomainVisual.
        let hits = spotter.search("lifecycle");
        assert!(!hits.is_empty(), "the spotter finds the lifecycle presentation");
        assert!(
            hits.iter().any(|h| h.matched_kind == PresentationKind::DomainVisual),
            "a lifecycle query matches the DomainVisual presentation"
        );
        assert_eq!(hits[0].focus, InspectFocus::Cell(treasury));

        // Search by the cell's short-hex id (carried in the RawFields title) finds
        // the cell — the universal "find any object by any presentation" promise.
        let short = reflect::short_hex(treasury.as_bytes());
        let prefix: String = short.chars().take(4).collect();
        let by_id = spotter.search(&prefix);
        assert!(
            by_id.iter().any(|h| h.focus == InspectFocus::Cell(treasury)),
            "the spotter finds the cell by its id-derived search_text"
        );

        // An empty query yields no hits (a spotter is search, not a dump).
        assert!(spotter.search("   ").is_empty());
    }

    #[test]
    fn the_spotter_ranks_and_returns_a_best_hit() {
        let (w, treasury, _sink) = two_cell_world();
        let spotter = Spotter::new(&w, treasury);
        let best = spotter.best("graph").expect("a graph presentation matches");
        // The hits are ranked best-first; the best is a real presentation hit.
        assert!(best.score > 0);
        assert!(!best.snippet.is_empty());
    }

    // ── the Halo commands resolve to real presentations/gadgets ─────────────

    #[test]
    fn the_halo_commands_resolve_to_real_presentations() {
        // The universal ring is on every object; Inspect opens the real
        // presentation set; per-kind commands extend per ObjectKind.
        let (w, treasury, _sink) = two_cell_world();
        let reg = Registry::new(&w);

        let halo = reg.halo(FocusTarget::Cell(treasury));
        // The universal three are present.
        assert!(halo.has(HaloCommand::Inspect));
        assert!(halo.has(HaloCommand::Grab));
        assert!(halo.has(HaloCommand::Explain));
        // A cell carries no per-kind extras.
        assert_eq!(halo.commands.len(), 3);

        // INSPECT resolves to the REAL presentation set (the same the registry returns).
        let set = reg.present(FocusTarget::Cell(treasury), treasury).unwrap();
        assert!(set.iter().any(|p| p.kind == PresentationKind::RawFields));
        assert!(set.iter().any(|p| p.kind == PresentationKind::Affordances));

        // A receipt's ring gains VerifyChain; a capability's gains Attenuate.
        let receipt_halo = Halo::for_kind(ObjectKind::Receipt);
        assert!(receipt_halo.has(HaloCommand::VerifyChain));
        let cap_halo = Halo::for_kind(ObjectKind::Capability);
        assert!(cap_halo.has(HaloCommand::Attenuate));
    }

    // ── the gadget field-kind model is well-formed ──────────────────────────

    #[test]
    fn the_gadget_field_model_keys_and_validation_are_well_formed() {
        // L1 defines the gadget SHAPE (the field kinds + validation); concrete
        // gadgets are L2/L3. Assert the shape is coherent.
        let f = GadgetField::U64 { key: "amount".into(), min: 0, max: 1_000 };
        assert_eq!(f.key(), "amount");
        let sub = GadgetField::SubGadget { key: "condition".into(), kind: GadgetKind::Predicate };
        assert_eq!(sub.key(), "condition");

        assert!(GadgetValidation::Ok.is_ok());
        assert!(GadgetValidation::Invalid { reason: "empty".into() }.is_fail_closed());
        assert!(!GadgetValidation::Ok.is_fail_closed());
    }

    // ── the graph presentation centers on the focused cell ──────────────────

    #[test]
    fn the_graph_presentation_centers_on_the_focused_cell() {
        // A world with a cap edge treasury → sink: the treasury's Graph presentation
        // carries the real ocap edge and focuses on the treasury.
        let mut w = World::new();
        let sink = w.genesis_cell(0xB0, 0);
        let (treasury, _slot) = w.genesis_cell_with_cap(0xA0, 1_000, sink);

        let refl = ReflectedCell::from_world(&w, treasury).unwrap();
        let ctx = PresentCtx::new(&w, treasury);
        let set = refl.present(&ctx);
        let graph = set.iter().find(|p| p.kind == PresentationKind::Graph).unwrap();
        match &graph.body {
            PresentationBody::Graph(g) => {
                assert_eq!(g.focus, Some(treasury));
                assert!(
                    g.edges.iter().any(|e| e.holder == treasury && e.target == sink),
                    "the real ocap edge treasury → sink is in the focused graph view"
                );
            }
            other => panic!("Graph should carry a Graph body, got {other:?}"),
        }
    }
}
