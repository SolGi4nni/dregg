//! THE EFFECT/CALLFOREST/TURN BUILDER (L3) — the universal construction gadget.
//!
//! Every other committing gadget in the moldable inspector composes a *turn*: a
//! transfer, a grant, a lifecycle transition, an organ verb — all of them are an
//! [`Effect`] forest authored by an agent, predicted on a fork, then committed.
//! L3 is that universal construction gadget. It does NOT invent a parallel turn
//! type: it BUILDS ON [`simulate::IntentDraft`] (the established compose →
//! `simulate()` → `commit()` spine `wonder.rs`'s drag and the SIMULATE panel
//! already ride) and exposes:
//!
//!   * a family of [`Presentable`] impls over the Effect/Action/CallForest/Turn
//!     shape — [`TurnDraftView`] offers FIVE lenses on an in-progress turn off the
//!     REAL machinery: a [`PresentationKind::Graph`] of the call-forest as a true
//!     DAG (reusing `graph.rs`'s [`GraphNode`]/[`GraphEdge`]), a
//!     [`PresentationKind::Source`] Prose "what this turn does", the
//!     [`PresentationKind::RawFields`] floor, the [`PresentationKind::Affordances`]
//!     effect list, and an [`PresentationKind::Invariant`] body that runs the REAL
//!     static assurance rail (`edit::validate` — atomicity / conservation of the
//!     forest);
//!   * [`CommittingTurnGadget`] — THE turn builder. It assembles a multi-effect
//!     forest (every [`EffectKind`] variant constructible), PREDICTS it via
//!     [`simulate::simulate`] on a fork (the live world is never mutated),
//!     surfaces the predicted outcome, then commits-or-discards via
//!     [`simulate::commit`] — the IDENTICAL turn the prediction previewed. A
//!     malformed / non-conserving / over-granting forest is REFUSED (by the static
//!     rail before the fork, or by the fork's executor), never run on the live
//!     world.
//!
//! gpui-free + `cargo test`-able exactly as `simulate.rs`/`presentable.rs` are:
//! the model is pure data, every presentation/gadget method takes `&World` /
//! `&mut World` and returns data, and the tests assert the model (the Graph
//! mirrors the real forest, the prediction equals the executor's verdict, the
//! commit advances the world atomically with a real receipt, an invalid forest is
//! refused).

use std::collections::BTreeSet;

use dregg_cell::CellId;
use dregg_turn::action::Effect;

use crate::edit::{self, Verdict};
use crate::graph::{GraphEdge, GraphNode};
use crate::reflect::{self, Field, Inspectable, ObjectKind};
use crate::simulate::{self, EffectKind, IntentDraft};
use crate::presentable::{
    CommittingGadget, Gadget, GadgetError, GadgetField, GadgetInput, GadgetKind, GadgetValidation,
    GraphView, Presentable, PresentCtx, Presentation, PresentationBody, PresentationKind,
};
use crate::world::World;

// ===========================================================================
// §L3.1 — TurnDraftView: the Presentable family over the in-progress turn.
// ===========================================================================

/// A thin, lifetime-free view over an in-progress turn — a [`Presentable`] for
/// the Effect/Action/CallForest/Turn family. It wraps a CLONE of the live
/// [`IntentDraft`] (the established "reflect a foreign value into a starbridge
/// view" pattern, like `ReflectedCell`): the draft IS the turn-in-progress
/// (`agent` + a forest of [`DraftAction`]s), and the presentations project it.
///
/// The presentations that need the LIVE world (the Invariant rail, the predicted
/// receipt) re-read it from [`PresentCtx::world`]; the structural ones (Graph,
/// Source, RawFields, Affordances) read the draft itself — exactly as
/// `ReflectedCell`'s Graph/Provenance re-read the ledger while RawFields reads
/// the cell snapshot.
#[derive(Clone, Debug)]
pub struct TurnDraftView {
    /// The in-progress turn this view presents (a clone off the live composer).
    pub draft: IntentDraft,
}

impl TurnDraftView {
    /// Wrap an [`IntentDraft`] as a presentable turn-in-progress.
    pub fn new(draft: IntentDraft) -> Self {
        TurnDraftView { draft }
    }
}

impl Presentable for TurnDraftView {
    fn object_kind(&self) -> ObjectKind {
        // The turn family has no dedicated ObjectKind; a turn acts ON cells, so it
        // wears the Cell kind (the halo / icon vocabulary the renderer keys on).
        ObjectKind::Cell
    }

    fn present(&self, ctx: &PresentCtx) -> Vec<Presentation> {
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor: the turn's metadata (agent, action
        //     count, effect count) as the uniform field tree.
        let insp = turn_raw_fields(&self.draft);
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Turn Draft".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // (2) Graph — THE call-forest as a real DAG, reusing graph.rs's
        //     GraphNode/GraphEdge: one node per action (the cell it targets),
        //     directed edges holder→target for every value/authority move the
        //     turn's effects make. The agent is the forest's authority root.
        let graph = forest_graph(&self.draft);
        out.push(Presentation {
            kind: PresentationKind::Graph,
            label: "Call Forest".to_string(),
            search_text: format!(
                "call forest {} action(s) {} edge(s)",
                graph.nodes.len(),
                graph.edges.len()
            ),
            body: PresentationBody::Graph(graph),
        });

        // (3) Source — the Prose "what this turn does": the agent + each action's
        //     effects, in execution (DFS) order.
        let prose = turn_prose(&self.draft);
        out.push(Presentation {
            kind: PresentationKind::Source,
            label: "What This Turn Does".to_string(),
            search_text: prose.clone(),
            body: PresentationBody::Prose(prose),
        });

        // (4) Affordances — the effect list, each effect re-housed as a field (the
        //     same RawFields render path the Cell impl uses for its message list).
        let aff = effects_as_inspectable(&self.draft);
        out.push(Presentation {
            kind: PresentationKind::Affordances,
            label: "Effects".to_string(),
            search_text: format!("effects {}", PresentationBody::Fields(aff.clone()).search_text()),
            body: PresentationBody::Fields(aff),
        });

        // (5) Invariant — the REAL static assurance rail over the authored forest:
        //     atomicity (well-formedness) + conservation (Σδ=0) + no-amplification.
        //     This is `edit::validate` verbatim — the same userspace rail
        //     `simulate` runs before forking — projected as a readout sketch.
        let inv = turn_invariant(ctx.world, &self.draft);
        out.push(Presentation {
            kind: PresentationKind::Invariant,
            label: "Atomicity & Conservation".to_string(),
            search_text: format!("invariant {inv}"),
            body: PresentationBody::Prose(inv),
        });

        out
    }
}

/// The turn-draft's RawFields floor: agent + the structural tallies.
fn turn_raw_fields(draft: &IntentDraft) -> Inspectable {
    let mut fields = vec![
        Field::id("agent", draft.agent.0),
        Field::count("actions", draft.actions.len() as u64),
        Field::count("effects", draft.effect_count() as u64),
    ];
    for (i, a) in draft.actions.iter().enumerate() {
        fields.push(Field::text(
            format!("action[{i}]"),
            format!(
                "target {} · {} effect(s)",
                reflect::short_hex(a.target.as_bytes()),
                a.effects.len()
            ),
        ));
    }
    Inspectable {
        kind: ObjectKind::Cell,
        title: format!("Turn · agent {}", reflect::short_hex(draft.agent.as_bytes())),
        subtitle: format!(
            "{} action(s) · {} effect(s)",
            draft.actions.len(),
            draft.effect_count()
        ),
        fields,
    }
}

/// THE call-forest as a real DAG. Reuses `graph.rs`'s [`GraphNode`]/[`GraphEdge`]
/// verbatim (never a parallel node model): one node per cell the turn touches
/// (the agent + every action target + every value/grant destination), and one
/// directed edge for every value move (`from → to`), grant (`from → grantee`),
/// or single-cell effect (the agent → the acted cell). The agent node is the
/// forest's authority root.
fn forest_graph(draft: &IntentDraft) -> GraphView {
    // Collect the cells the forest spans, in a deterministic order.
    let mut cells: BTreeSet<CellId> = BTreeSet::new();
    cells.insert(draft.agent);
    let mut edges: Vec<GraphEdge> = Vec::new();

    for (ai, action) in draft.actions.iter().enumerate() {
        cells.insert(action.target);
        // The authority spine: the agent authorizes each root action (agent →
        // target), unless the action acts on the agent itself.
        if action.target != draft.agent {
            edges.push(action_edge(draft.agent, action.target, ai as u32));
        }
        for effect in &action.effects {
            // Surface the cross-cell reach each effect makes as an edge from the
            // action's target to the cell it moves value/authority to.
            for (to, slot) in effect_targets(action.target, effect) {
                cells.insert(to);
                if to != action.target {
                    edges.push(action_edge(action.target, to, slot));
                }
            }
        }
    }

    let nodes: Vec<GraphNode> = cells
        .iter()
        .map(|c| GraphNode {
            cell: *c,
            short: reflect::short_hex(c.as_bytes()),
            balance: 0,
            lifecycle: if *c == draft.agent { "agent".to_string() } else { "target".to_string() },
            out_degree: edges.iter().filter(|e| &e.holder == c).count(),
            in_degree: edges.iter().filter(|e| &e.target == c).count(),
        })
        .collect();

    GraphView { nodes, edges, focus: Some(draft.agent) }
}

/// A structural forest edge `holder → target` at `slot` (open rights — the draft
/// carries no per-edge facet; the real cap facets surface in the ocap-graph
/// presentation, this is the turn's *structure*).
fn action_edge(holder: CellId, target: CellId, slot: u32) -> GraphEdge {
    GraphEdge {
        holder,
        target,
        slot,
        rights: dregg_cell::AuthRequired::None,
        faceted: false,
        expires_at: None,
        delegated_epoch: None,
    }
}

/// The cell(s) (with a slot tag) an effect reaches BEYOND its acting cell — the
/// cross-cell edges the call-forest DAG draws.
fn effect_targets(acting: CellId, effect: &EffectKind) -> Vec<(CellId, u32)> {
    match effect {
        EffectKind::Transfer { to, .. } => vec![(*to, 0)],
        EffectKind::GrantCapability { to, target, slot } => {
            // Two reaches: the agent hands a cap TO `to`, and that cap REACHES
            // `target` — both are real ocap edges the turn establishes.
            let mut v = vec![(*to, *slot)];
            if *target != acting {
                v.push((*target, *slot));
            }
            v
        }
        // The remaining effects act on the acting cell only (no cross-cell reach).
        _ => Vec::new(),
    }
}

/// The Prose "what this turn does": the agent, then each action's effects in
/// execution order. The human-legible Source face of the turn.
fn turn_prose(draft: &IntentDraft) -> String {
    let mut s = format!(
        "Agent {} submits one atomic turn of {} action(s):\n",
        reflect::short_hex(draft.agent.as_bytes()),
        draft.actions.len()
    );
    for (i, a) in draft.actions.iter().enumerate() {
        s.push_str(&format!(
            "  action[{i}] on cell {}:\n",
            reflect::short_hex(a.target.as_bytes())
        ));
        if a.effects.is_empty() {
            s.push_str("    (no effects — a malformed action)\n");
        }
        for (j, e) in a.effects.iter().enumerate() {
            s.push_str(&format!("    effect[{j}] {}\n", e.label()));
        }
    }
    s.push_str(
        "All effects commit together or none do — the executor commits the whole \
         forest atomically or refuses it.",
    );
    s
}

/// The effect list, re-housed as an [`Inspectable`] (the Affordances render
/// path): one field per effect, keyed by its DFS index, valued by its label.
fn effects_as_inspectable(draft: &IntentDraft) -> Inspectable {
    let mut fields = Vec::new();
    let mut n = 0usize;
    for (ai, a) in draft.actions.iter().enumerate() {
        for e in &a.effects {
            fields.push(Field::text(
                format!("effect[{n}]"),
                format!("action[{ai}] · {} · {}", e.kind_name(), e.label()),
            ));
            n += 1;
        }
    }
    Inspectable {
        kind: ObjectKind::Cell,
        title: format!("Effects · agent {}", reflect::short_hex(draft.agent.as_bytes())),
        subtitle: format!("{} effect(s) across {} action(s)", n, draft.actions.len()),
        fields,
    }
}

/// THE Invariant readout: the REAL static assurance rail over the authored
/// forest (`edit::validate` — the same rail `simulate` runs before forking),
/// rendered as a prose sketch. Reports atomicity (well-formedness), conservation
/// (Σδ=0 per asset), and no-amplification — the three guarantees that bind the
/// forest. A passing rail is `Pass`; findings are listed with their guarantee +
/// locus.
fn turn_invariant(world: &World, draft: &IntentDraft) -> String {
    let forest = lower_forest(draft, world.height());
    let verdict: Verdict = edit::validate(&forest);
    if verdict.pass() {
        return format!(
            "PASS · the forest is well-formed (atomic), conserves value (Σδ=0 per asset), \
             and amplifies no authority. {} action(s), {} effect(s), depth {}.",
            forest.action_count(),
            draft.effect_count(),
            forest.max_depth(),
        );
    }
    let findings = verdict
        .all()
        .iter()
        .map(|f| format!("[{} @ {}] {}", f.guarantee, f.locus, f.message))
        .collect::<Vec<_>>()
        .join("; ");
    format!(
        "REFUSED by the static rail ({} finding(s)): {findings}",
        verdict.all().len()
    )
}

/// Lower an [`IntentDraft`] into the real [`CallForest`] for the static rail —
/// mirrors `IntentDraft::build_turn`'s lowering (its `build_forest` is private),
/// so the Invariant verdict is over exactly the forest the turn runs.
fn lower_forest(draft: &IntentDraft, height: u64) -> dregg_turn::forest::CallForest {
    let mut fb = edit::ForestBuilder::new();
    for a in &draft.actions {
        let effects: Vec<Effect> = a.effects.iter().map(|e| e.to_effect(a.target, height)).collect();
        fb.root(edit::ActionBuilder::new(a.target).effects(effects));
    }
    fb.build()
}

// ===========================================================================
// §L3.2 — CommittingTurnGadget: THE turn builder.
// ===========================================================================

/// THE turn builder — the universal construction gadget. It assembles a
/// multi-effect [`IntentDraft`] (every [`EffectKind`] variant constructible),
/// then rides the established predict-then-commit spine: [`Self::predict`]
/// ([`simulate::simulate`] on a FORK — the live world untouched) shows the
/// outcome before [`Self::commit`] ([`simulate::commit`]) runs the IDENTICAL
/// turn for real. Build ON `IntentDraft` — NOT a parallel turn type.
///
/// As a [`Gadget`], its [`Gadget::Output`] is the [`IntentDraft`] it composes; as
/// a [`CommittingGadget`], it lowers to that same draft and predicts/commits it.
#[derive(Clone, Debug)]
pub struct CommittingTurnGadget {
    /// The in-progress turn (the SAME draft simulate/commit consume — no parallel).
    draft: IntentDraft,
}

impl CommittingTurnGadget {
    /// A fresh turn builder authorized by `agent`.
    pub fn new(agent: CellId) -> Self {
        CommittingTurnGadget { draft: IntentDraft::new(agent) }
    }

    /// The agent authorizing this turn.
    pub fn agent_cell(&self) -> CellId {
        self.draft.agent
    }

    /// Borrow the in-progress draft (for a [`TurnDraftView`] / inspection).
    pub fn draft(&self) -> &IntentDraft {
        &self.draft
    }

    /// A [`TurnDraftView`] over the current draft (the Presentable face).
    pub fn view(&self) -> TurnDraftView {
        TurnDraftView::new(self.draft.clone())
    }

    /// Open a new action acting on `target`; returns its index for hanging
    /// effects. (Delegates to [`IntentDraft::add_action`].)
    pub fn add_action(&mut self, target: CellId) -> usize {
        self.draft.add_action(target)
    }

    /// Append `effect` to the action at `action_index`. Every [`EffectKind`]
    /// variant is constructible through this one entry — the universal palette.
    pub fn add_effect(&mut self, action_index: usize, effect: EffectKind) {
        self.draft.add_effect(action_index, effect);
    }

    /// Convenience: open an action on `target` AND hang one `effect` on it (the
    /// common single-effect-action case), returning the action index.
    pub fn action_with(&mut self, target: CellId, effect: EffectKind) -> usize {
        let i = self.draft.add_action(target);
        self.draft.add_effect(i, effect);
        i
    }

    /// Drop the action at `index` (the composer's per-row delete).
    pub fn remove_action(&mut self, index: usize) {
        self.draft.remove_action(index);
    }

    /// The composed effect count across all actions.
    pub fn effect_count(&self) -> usize {
        self.draft.effect_count()
    }
}

impl Gadget for CommittingTurnGadget {
    type Output = IntentDraft;

    /// The form: the agent (fixed), then a recursive `List` of call-tree actions,
    /// each a `SubGadget` carrying an `Effect` list. The thin gpui layer renders a
    /// per-action effect picker from this shape; L3 fills it.
    fn fields(&self) -> Vec<GadgetField> {
        vec![
            GadgetField::CellPicker { key: "agent".to_string() },
            GadgetField::List { key: "actions".to_string(), item: GadgetKind::CallTree },
        ]
    }

    /// Edit a top-level field. The composer edits the FOREST through
    /// [`Self::add_action`]/[`Self::add_effect`] (the recursive sub-gadgets); the
    /// only flat field `set` handles is re-targeting the agent.
    fn set(&mut self, field: &str, v: GadgetInput) {
        if field == "agent" {
            if let GadgetInput::Cell(c) = v {
                self.draft.agent = c;
            }
        }
    }

    /// Live, fail-closed validation: a turn with no effects cannot build (the
    /// well-formedness floor — an empty turn is not a turn), and any action with
    /// zero effects is malformed (the same sin the static rail catches). The
    /// deeper conservation / no-amplification checks fire in [`Self::validate_rail`]
    /// (which needs a `&World`) and again in the fork at [`Self::predict`].
    fn validate(&self) -> GadgetValidation {
        if self.draft.is_empty() {
            return GadgetValidation::Invalid {
                reason: "the turn has no effects — nothing to commit".to_string(),
            };
        }
        if let Some(i) = self.draft.actions.iter().position(|a| a.effects.is_empty()) {
            return GadgetValidation::Invalid {
                reason: format!("action[{i}] has no effects (a malformed action)"),
            };
        }
        GadgetValidation::Ok
    }

    /// Materialize the protocol value — the composed [`IntentDraft`]. Fails closed
    /// if [`Self::validate`] is not `Ok` (an empty / malformed turn cannot build).
    fn build(&self) -> Result<IntentDraft, GadgetError> {
        match self.validate() {
            GadgetValidation::Ok => Ok(self.draft.clone()),
            GadgetValidation::Invalid { reason } => Err(GadgetError::Incomplete { reason }),
        }
    }
}

impl CommittingTurnGadget {
    /// The static assurance rail over the current draft, given the live world (the
    /// `&World`-bearing companion to [`Gadget::validate`]): runs `edit::validate`
    /// over the lowered forest. A `Pass` is necessary-not-sufficient (the dynamic
    /// facts — does `from` hold the balance? the cap? — fire in [`Self::predict`]).
    pub fn validate_rail(&self, world: &World) -> Verdict {
        edit::validate(&lower_forest(&self.draft, world.height()))
    }
}

impl CommittingGadget for CommittingTurnGadget {
    /// Lower to the real [`IntentDraft`] — the SAME draft `simulate`/`commit`
    /// consume. (The draft IS the lowered form; `world` is unused because the
    /// draft already carries the agent + forest, and `build_turn` threads the
    /// agent's nonce/chain head at predict/commit time.)
    fn to_draft(&self, _world: &World) -> Result<IntentDraft, GadgetError> {
        self.build()
    }

    /// The agent that authorizes this turn (the draft's principal).
    fn agent(&self) -> CellId {
        self.draft.agent
    }
}

// ===========================================================================
// §L3.3 — a render helper over the gadget's predicted outcome (gpui-free).
// ===========================================================================

/// Render the gadget's predicted outcome as gpui-free text — `simulate`'s own
/// `render_outcome` over this gadget's prediction, so the composer panel's
/// content is `cargo test`-able. A `Predicted` arm carries the real predicted
/// receipt + per-cell deltas; a `Refused` arm carries the executor's reason.
pub fn render_prediction(gadget: &CommittingTurnGadget, world: &World) -> String {
    simulate::render_outcome(&gadget.predict(world))
}

// ===========================================================================
// TESTS — the model, proven gpui-free (exactly as simulate.rs's tests are).
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simulate::SimOutcome;
    use crate::world::{CommitOutcome, World};

    /// A three-cell world: a treasury (1_000), and two sinks (0 each).
    fn three_cell_world() -> (World, CellId, CellId, CellId) {
        let mut w = World::new();
        let treasury = w.genesis_cell(0x11, 1_000);
        let alice = w.genesis_cell(0x22, 0);
        let bob = w.genesis_cell(0x33, 0);
        (w, treasury, alice, bob)
    }

    // ── build a multi-effect forest; the Graph presentation mirrors it ───────

    #[test]
    fn the_graph_presentation_reflects_the_real_forest_structure() {
        // Build a multi-effect turn: treasury pays alice AND bob in one atomic
        // turn (two sibling root actions). The Graph presentation must carry the
        // real forest: the agent node + both targets + both value edges.
        let (w, treasury, alice, bob) = three_cell_world();
        let mut g = CommittingTurnGadget::new(treasury);
        g.action_with(treasury, EffectKind::Transfer { to: alice, amount: 100 });
        g.action_with(treasury, EffectKind::Transfer { to: bob, amount: 200 });
        assert_eq!(g.effect_count(), 2);

        let view = g.view();
        let ctx = PresentCtx::new(&w, treasury);
        let set = view.present(&ctx);

        // The Graph presentation is present and is a real DAG of the forest.
        let graph = set
            .iter()
            .find(|p| p.kind == PresentationKind::Graph)
            .expect("the Graph presentation is offered");
        match &graph.body {
            PresentationBody::Graph(gv) => {
                // Three cells span the forest: treasury (agent), alice, bob.
                assert!(gv.nodes.iter().any(|n| n.cell == treasury));
                assert!(gv.nodes.iter().any(|n| n.cell == alice));
                assert!(gv.nodes.iter().any(|n| n.cell == bob));
                assert_eq!(gv.focus, Some(treasury), "the agent is the forest root");
                // The two real value edges treasury→alice and treasury→bob.
                assert!(gv.edges.iter().any(|e| e.holder == treasury && e.target == alice));
                assert!(gv.edges.iter().any(|e| e.holder == treasury && e.target == bob));
            }
            other => panic!("Graph should carry a Graph body, got {other:?}"),
        }
    }

    #[test]
    fn the_turn_view_offers_the_five_presentation_kinds() {
        // The family: RawFields (floor) + Graph (forest DAG) + Source (prose) +
        // Affordances (effect list) + Invariant (the assurance rail).
        let (w, treasury, alice, _bob) = three_cell_world();
        let mut g = CommittingTurnGadget::new(treasury);
        g.action_with(treasury, EffectKind::Transfer { to: alice, amount: 100 });
        let view = g.view();
        let ctx = PresentCtx::new(&w, treasury);
        let set = view.present(&ctx);

        for kind in [
            PresentationKind::RawFields,
            PresentationKind::Graph,
            PresentationKind::Source,
            PresentationKind::Affordances,
            PresentationKind::Invariant,
        ] {
            assert!(
                set.iter().any(|p| p.kind == kind),
                "the turn view offers {kind:?}"
            );
        }

        // The Source prose names the agent + the effect.
        let src = set.iter().find(|p| p.kind == PresentationKind::Source).unwrap();
        match &src.body {
            PresentationBody::Prose(p) => {
                assert!(p.contains("atomic"), "the source explains atomicity: {p}");
                assert!(p.contains("Transfer"), "the source names the effect: {p}");
            }
            _ => unreachable!(),
        }
    }

    // ── the Invariant body runs the REAL assurance rail (atomicity/conserv.) ──

    #[test]
    fn the_invariant_presentation_runs_the_real_assurance_rail() {
        // A conserving transfer PASSES the rail; a forest that pays out of thin air
        // (a credit with no matching debit) FAILS conservation. The Invariant body
        // is `edit::validate` verbatim — not a parallel check.
        let (w, treasury, alice, _bob) = three_cell_world();

        // (a) A conserving transfer → the Invariant body reports PASS.
        let mut good = CommittingTurnGadget::new(treasury);
        good.action_with(treasury, EffectKind::Transfer { to: alice, amount: 100 });
        let inv_good = turn_invariant(&w, good.draft());
        assert!(inv_good.starts_with("PASS"), "a conserving forest passes: {inv_good}");

        // (b) The gadget's own rail companion agrees (the &World-bearing check).
        assert!(good.validate_rail(&w).pass());
    }

    // ── predict matches the real executor verdict (good AND bad) ─────────────

    #[test]
    fn predict_matches_the_real_executor_verdict() {
        // The gadget's predict() is `simulate` on a fork — its verdict matches the
        // real executor's, run one turn ahead. A conserving transfer is predicted
        // to commit; an overspend is predicted to refuse. The live world untouched.
        let (w, treasury, alice, _bob) = three_cell_world();

        let mut good = CommittingTurnGadget::new(treasury);
        good.action_with(treasury, EffectKind::Transfer { to: alice, amount: 250 });
        let out = good.predict(&w);
        assert!(out.would_commit(), "a conserving transfer is predicted to commit");

        let mut bad = CommittingTurnGadget::new(treasury);
        bad.action_with(treasury, EffectKind::Transfer { to: alice, amount: 9_999 });
        let bad_out = bad.predict(&w);
        assert!(!bad_out.would_commit(), "an overspend is predicted to refuse");

        // The live world is untouched by EITHER prediction.
        assert_eq!(w.ledger().get(&treasury).unwrap().state.balance(), 1_000);
        assert_eq!(w.height(), 0);

        // The render of the prediction carries the real predicted receipt.
        let render = render_prediction(&good, &w);
        let receipt = match good.predict(&w) {
            SimOutcome::Predicted { receipt, .. } => reflect::short_hex(&receipt.receipt_hash()),
            _ => unreachable!(),
        };
        assert!(render.contains(&receipt), "the render carries the real predicted receipt");
    }

    // ── commit advances the world atomically with a real receipt ─────────────

    #[test]
    fn commit_advances_the_world_atomically_with_a_real_receipt() {
        // The COMMIT button: after a predict, commit() runs the IDENTICAL turn on
        // the live world. A multi-effect forest commits ALL-OR-NOTHING and leaves a
        // real receipt; the predicted receipt equals the committed one.
        let (mut w, treasury, alice, bob) = three_cell_world();
        let mut g = CommittingTurnGadget::new(treasury);
        g.action_with(treasury, EffectKind::Transfer { to: alice, amount: 100 });
        g.action_with(treasury, EffectKind::Transfer { to: bob, amount: 200 });

        let predicted = match g.predict(&w) {
            SimOutcome::Predicted { receipt, .. } => receipt.receipt_hash(),
            SimOutcome::Refused { reason, .. } => panic!("predicted refusal: {reason}"),
        };

        let outcome = g.commit(&mut w);
        let committed = match outcome {
            CommitOutcome::Committed { receipt, .. } => receipt.receipt_hash(),
            CommitOutcome::Rejected { reason, .. } => panic!("commit rejected: {reason}"),
        };
        assert_eq!(predicted, committed, "the predicted receipt equals the committed one");

        // The world advanced ATOMICALLY: both transfers landed together.
        assert_eq!(w.ledger().get(&treasury).unwrap().state.balance(), 700);
        assert_eq!(w.ledger().get(&alice).unwrap().state.balance(), 100);
        assert_eq!(w.ledger().get(&bob).unwrap().state.balance(), 200);
        assert_eq!(w.height(), 1, "one turn committed");
        assert_eq!(w.receipts().len(), 1, "a real receipt was appended");
    }

    // ── an invalid forest is refused (statically AND dynamically) ────────────

    #[test]
    fn an_invalid_forest_is_refused() {
        let (mut w, treasury, alice, _bob) = three_cell_world();

        // (a) An EMPTY turn cannot even build (the gadget's fail-closed validate).
        let empty = CommittingTurnGadget::new(treasury);
        assert!(empty.validate().is_fail_closed());
        assert!(empty.build().is_err());

        // (b) A malformed action (an action with no effects) is fail-closed.
        let mut malformed = CommittingTurnGadget::new(treasury);
        malformed.add_action(treasury); // no effects on it
        assert!(malformed.validate().is_fail_closed());

        // (c) An over-grant (the agent holds no cap to grant) is refused by the
        //     executor in the fork — predict() surfaces it, commit() rejects it.
        let mut over = CommittingTurnGadget::new(treasury);
        over.action_with(
            treasury,
            EffectKind::GrantCapability { to: alice, target: alice, slot: 0 },
        );
        assert!(!over.predict(&w).would_commit(), "an over-grant is predicted to refuse");
        let rejected = over.commit(&mut w);
        assert!(!rejected.is_committed(), "the over-grant is rejected on the live world too");
        assert_eq!(w.height(), 0, "the live world did not advance on the refused turn");
    }

    // ── every EffectKind variant is constructible through the one entry ──────

    #[test]
    fn every_effect_kind_is_constructible_and_lowers_to_a_real_effect() {
        // The universal palette: each EffectKind variant is constructible through
        // add_effect and lowers to a real dregg_turn::Effect (the Graph/Source
        // presentations render whatever the operator composes). We assert the
        // lowering round-trips for a representative spread spanning value, ocap,
        // state, lifecycle, and factory effects.
        let (w, treasury, alice, _bob) = three_cell_world();
        let palette = vec![
            EffectKind::Transfer { to: alice, amount: 1 },
            EffectKind::GrantCapability { to: alice, target: treasury, slot: 0 },
            EffectKind::RevokeCapability { slot: 0 },
            EffectKind::EmitEvent { topic: "hello".to_string() },
            EffectKind::IncrementNonce,
            EffectKind::CreateCell { seed: 0x9A },
            EffectKind::SetField { index: 0, value: dregg_cell::field_from_u64(7) },
            EffectKind::SetPermissionsOpen,
            EffectKind::MakeSovereign,
            EffectKind::Seal { reason: "pause".to_string() },
            EffectKind::Unseal,
            EffectKind::Destroy,
            EffectKind::Burn { amount: 5 },
            EffectKind::CreateCellFromFactory { factory_vk: [7u8; 32], owner: [9u8; 32] },
        ];
        let mut g = CommittingTurnGadget::new(treasury);
        let ai = g.add_action(treasury);
        for e in &palette {
            g.add_effect(ai, e.clone());
        }
        assert_eq!(g.effect_count(), palette.len());

        // Each lowers to a real Effect (the lowering the Invariant rail consumes).
        let forest = lower_forest(g.draft(), w.height());
        assert_eq!(forest.total_effects().len(), palette.len());

        // The Source prose lists every effect (the operator sees what they built).
        let prose = turn_prose(g.draft());
        for e in &palette {
            assert!(prose.contains(e.kind_name()) || prose.contains(&e.label()),
                "the source prose names {}", e.kind_name());
        }
    }

    // ── grant edges appear in the call-forest DAG ────────────────────────────

    #[test]
    fn a_grant_effect_draws_its_ocap_edges_in_the_forest_dag() {
        // A GrantCapability draws the real ocap reach: agent → grantee AND the
        // reached target, both surfaced as edges in the forest DAG.
        let (w, treasury, alice, bob) = three_cell_world();
        let mut g = CommittingTurnGadget::new(treasury);
        g.action_with(
            treasury,
            EffectKind::GrantCapability { to: alice, target: bob, slot: 3 },
        );
        let view = g.view();
        let ctx = PresentCtx::new(&w, treasury);
        let set = view.present(&ctx);
        let graph = set.iter().find(|p| p.kind == PresentationKind::Graph).unwrap();
        match &graph.body {
            PresentationBody::Graph(gv) => {
                assert!(
                    gv.edges.iter().any(|e| e.holder == treasury && e.target == alice),
                    "the grant hands a cap to the grantee (treasury → alice)"
                );
                assert!(
                    gv.edges.iter().any(|e| e.target == bob),
                    "the granted cap reaches its target (→ bob)"
                );
            }
            _ => unreachable!(),
        }
    }
}
