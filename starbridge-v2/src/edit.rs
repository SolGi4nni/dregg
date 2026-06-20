//! THE LIVE EDITOR — author dregg artifacts, validate them, deploy them live.
//!
//! This is the authoring surface of the master interface: the place where an
//! operator *writes* dregg artifacts (cell programs out of the guard-algebra
//! atoms, factory descriptors, multi-effect call-forests), gets a STATIC
//! ASSURANCE VERDICT before paying to submit, and — on pass — DEPLOYS them
//! through the embedded verified [`World`] so they appear live in the
//! reflective image.
//!
//! The three movements:
//!
//!   1. **Author** — typed builders ([`ProgramBuilder`], [`FactoryBuilder`],
//!      [`ForestBuilder`]) assemble the protocol types directly
//!      (`dregg_cell::CellProgram` / `StateConstraint`, `FactoryDescriptor`,
//!      `dregg_turn::CallForest`). No parallel wire schema — the editor writes
//!      exactly what the executor will run.
//!
//!   2. **Validate** — [`validate`] runs the static, userspace,
//!      pre-submission assurance checks over the authored [`CallForest`] by
//!      delegating to the REAL [`dregg_userspace_verify::analyze`]: per-asset
//!      **conservation**, delegation-edge **non-amplification**, and structural
//!      **well-formedness**. It is the editor's SAFETY RAIL — and it is
//!      **necessary, not sufficient**: a `Pass` means the artifact is
//!      statically well-shaped, NOT that the executor will accept it (the
//!      *holding* half of ocap, balance sufficiency, credential validity and
//!      the whole-state proof are dynamic — they live in the executor, which
//!      the deploy step then actually runs).
//!
//!   3. **Deploy** — [`deploy_program`] genesis-installs a cell carrying an
//!      authored program (the executor then enforces it on every transition);
//!      [`deploy_forest`] commits an authored forest's effects through the
//!      embedded executor and surfaces the real [`CommitOutcome`].
//!
//! ## The assurance toolkit
//!
//! [`validate`] calls `dregg_userspace_verify::analyze(forest, false)` — the
//! canonical `check_conservation` / `check_no_amplification` /
//! `check_wellformed` toolkit — and projects its `Assurance` onto this module's
//! [`Verdict`]/[`Finding`] panel surface. There is no parallel re-expression.

use dregg_cell::{
    factory::{CapTarget, CapTemplate, ChildVkStrategy, FactoryDescriptor},
    program::{CellProgram, SimpleStateConstraint, StateConstraint},
    AuthRequired, CapabilityRef, Cell, CellId, CellMode, FieldElement,
};
use dregg_turn::{
    action::{Action, Authorization, DelegationMode, Effect},
    forest::CallForest,
};

use crate::world::{open_permissions, World};
use crate::CommitOutcome;

// ===========================================================================
// VALIDATION — the static assurance rail (necessary, not sufficient).
//
// Delegates to the REAL `dregg_userspace_verify::analyze(forest, false)` — the
// canonical static assurance toolkit (`check_conservation` /
// `check_no_amplification` / `check_wellformed`) — never a parallel
// re-expression. The crate's `Assurance` is projected onto this module's
// `Verdict`/`Finding` (the editor's panel surface).
// ===========================================================================

/// The native value column — `Transfer` / `balance_change` move against this.
/// (Re-exported from `dregg_userspace_verify` so the editor names one constant.)
pub use dregg_userspace_verify::COMPUTRON_ASSET;

/// A located finding: which guarantee failed, where, and why. The `locus`
/// names the construction site so the editor can point the author at it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Finding {
    /// `"A (non-amplification)"` / `"B (conservation)"` / `"well-formedness"`.
    pub guarantee: String,
    /// Index-path from the forest down to the offending node (`[2,0,1]` =
    /// root 2 → child 0 → child 1), plus an optional effect index / asset.
    pub locus: String,
    /// Human-readable explanation of the violation.
    pub message: String,
}

/// The combined static verdict over an authored forest: one finding-list per
/// check plus a roll-up [`Verdict::pass`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Verdict {
    pub conservation: Vec<Finding>,
    pub no_amplification: Vec<Finding>,
    pub wellformed: Vec<Finding>,
}

impl Verdict {
    /// `true` iff every static check passed (no findings).
    pub fn pass(&self) -> bool {
        self.conservation.is_empty()
            && self.no_amplification.is_empty()
            && self.wellformed.is_empty()
    }

    /// Every finding across all checks, flattened (for rendering).
    pub fn all(&self) -> Vec<&Finding> {
        self.conservation
            .iter()
            .chain(self.no_amplification.iter())
            .chain(self.wellformed.iter())
            .collect()
    }
}

/// Run the static assurance checks over an authored forest.
///
/// **This is the editor's safety rail.** A `Pass` is **necessary, not
/// sufficient** for the executor to accept the turn: it certifies the
/// userspace-decidable shape (conservation of moves, in-forest delegation
/// attenuation, structural well-formedness) but NOT the dynamic facts (did the
/// signer HOLD the cap it grants? does `from` have the balance? is the
/// credential valid?). Those fire when [`deploy_forest`] runs the real
/// executor.
///
/// Semantics ARE `dregg_userspace_verify::analyze(forest, false)` — this calls
/// the real crate and projects its [`dregg_userspace_verify::Assurance`] onto
/// the editor's [`Verdict`]/[`Finding`] panel surface. No parallel checks.
///
/// (`treat_as_ring = false`: the editor validates ordinary authored forests;
/// ring balance is the intent-ring specialization and is `Pass` here.)
pub fn validate(forest: &CallForest) -> Verdict {
    let assurance = dregg_userspace_verify::analyze(forest, false);
    Verdict {
        conservation: project_findings(&assurance.conservation),
        no_amplification: project_findings(&assurance.no_amplification),
        wellformed: project_findings(&assurance.wellformed),
    }
}

/// Project a real `dregg_userspace_verify::Verdict`'s findings onto this
/// module's [`Finding`] list, rendering the canonical [`dregg_userspace_verify::Locus`]
/// into the editor's `forest[i][j]…` construction-site path.
fn project_findings(v: &dregg_userspace_verify::Verdict) -> Vec<Finding> {
    v.findings()
        .iter()
        .map(|f| Finding {
            guarantee: f.guarantee.clone(),
            locus: fmt_locus(&f.locus),
            message: f.message.clone(),
        })
        .collect()
}

/// Render a real [`dregg_userspace_verify::Locus`] as the editor's
/// `forest[i][j]… effect[k] asset[a]` construction-site string.
fn fmt_locus(locus: &dregg_userspace_verify::Locus) -> String {
    let mut s = String::from("forest");
    for p in &locus.node_path {
        s.push_str(&format!("[{p}]"));
    }
    if let Some(e) = locus.effect_index {
        s.push_str(&format!(" effect[{e}]"));
    }
    if let Some(a) = &locus.asset {
        s.push_str(&format!(" asset[{a}]"));
    }
    s
}

// ===========================================================================
// AUTHOR — cell programs out of the guard-algebra atoms.
// ===========================================================================

/// A typed builder for a [`CellProgram::Predicate`] — the guard-algebra
/// surface. Each `with_*` appends one [`StateConstraint`] atom; the program is
/// the implicit conjunction (all constraints must hold post-transition).
///
/// Covers the headline atoms an author reaches for: field comparisons
/// (`equals`/`gte`/`lte`), the immutability/monotonic family (`immutable`,
/// `write_once`, `monotonic`, `strict_monotonic`), and the actor-bound atom
/// (`sender_is`, via the `SimpleStateConstraint` lift). Richer atoms (heap
/// keys, witnessed, cross-cell) are reachable by pushing a raw
/// [`StateConstraint`] with [`Self::with_raw`].
#[derive(Clone, Debug, Default)]
pub struct ProgramBuilder {
    constraints: Vec<StateConstraint>,
}

impl ProgramBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    /// `new[index] == value`.
    pub fn field_equals(mut self, index: u8, value: FieldElement) -> Self {
        self.constraints.push(StateConstraint::FieldEquals { index, value });
        self
    }
    /// `new[index] >= value` (unsigned big-endian).
    pub fn field_gte(mut self, index: u8, value: FieldElement) -> Self {
        self.constraints.push(StateConstraint::FieldGte { index, value });
        self
    }
    /// `new[index] <= value` (unsigned big-endian).
    pub fn field_lte(mut self, index: u8, value: FieldElement) -> Self {
        self.constraints.push(StateConstraint::FieldLte { index, value });
        self
    }
    /// Slot is read-only after its first write (first write free, then frozen).
    pub fn immutable(mut self, index: u8) -> Self {
        self.constraints.push(StateConstraint::Immutable { index });
        self
    }
    /// Slot may only transition from zero to a non-zero value, then is frozen.
    pub fn write_once(mut self, index: u8) -> Self {
        self.constraints.push(StateConstraint::WriteOnce { index });
        self
    }
    /// `new[index] >= old[index]` (append-only counters, expiry extensions).
    pub fn monotonic(mut self, index: u8) -> Self {
        self.constraints.push(StateConstraint::Monotonic { index });
        self
    }
    /// `new[index] > old[index]` strictly (auction bids, sequence numbers).
    pub fn strict_monotonic(mut self, index: u8) -> Self {
        self.constraints.push(StateConstraint::StrictMonotonic { index });
        self
    }
    /// Actor binding: the turn's sender must equal `pk` (the per-cell
    /// controller). A `SimpleStateConstraint` atom, lifted to the outer enum
    /// via a single-element `AnyOf` (the canonical embedding — these atoms
    /// live in `SimpleStateConstraint` so they compose under `AnyOf`/`Not`).
    pub fn sender_is(mut self, pk: [u8; 32]) -> Self {
        self.constraints.push(StateConstraint::AnyOf {
            variants: vec![SimpleStateConstraint::SenderIs { pk }],
        });
        self
    }
    /// The cell's own post-turn balance must be `>= min` (solvency floor).
    /// Lifted via a single-element `AnyOf` like [`Self::sender_is`].
    pub fn balance_gte(mut self, min: u64) -> Self {
        self.constraints.push(StateConstraint::AnyOf {
            variants: vec![SimpleStateConstraint::BalanceGte { min }],
        });
        self
    }
    /// Escape hatch: push any raw [`StateConstraint`] (heap atoms, witnessed,
    /// cross-cell, `AnyOf` disjunctions, `Custom`).
    pub fn with_raw(mut self, c: StateConstraint) -> Self {
        self.constraints.push(c);
        self
    }

    /// The authored constraint list (for inspection / hashing).
    pub fn constraints(&self) -> &[StateConstraint] {
        &self.constraints
    }

    /// Finish into a [`CellProgram::Predicate`]. An empty builder yields
    /// `CellProgram::None` (no program — any authorized transition is valid).
    pub fn build(self) -> CellProgram {
        if self.constraints.is_empty() {
            CellProgram::None
        } else {
            CellProgram::Predicate(self.constraints)
        }
    }
}

// ===========================================================================
// AUTHOR — factory descriptors + slot caveats.
// ===========================================================================

/// A typed builder for a [`FactoryDescriptor`]: the child program VK, the cap
/// templates new cells may be granted, the creation-time field constraints,
/// and the PERPETUAL slot caveats (`state_constraints`) baked into every
/// child cell's program (enforced on every transition).
#[derive(Clone, Debug)]
pub struct FactoryBuilder {
    factory_vk: [u8; 32],
    child_program_vk: Option<[u8; 32]>,
    cap_templates: Vec<CapTemplate>,
    state_constraints: Vec<StateConstraint>,
    default_mode: CellMode,
    creation_budget: Option<u64>,
}

impl FactoryBuilder {
    /// A fresh factory builder identified by `factory_vk` (its own program
    /// VK hash — content-addressed identity).
    pub fn new(factory_vk: [u8; 32]) -> Self {
        Self {
            factory_vk,
            child_program_vk: None,
            cap_templates: Vec::new(),
            state_constraints: Vec::new(),
            default_mode: CellMode::Hosted,
            creation_budget: None,
        }
    }

    /// Pin the child program by its canonical VK. Use
    /// [`child_program`](Self::child_program) to derive it from an authored
    /// `CellProgram` instead.
    pub fn child_program_vk(mut self, vk: [u8; 32]) -> Self {
        self.child_program_vk = Some(vk);
        self
    }

    /// Pin the child program from an authored [`CellProgram`] — computes its
    /// canonical VK and bakes the program's constraints in as the perpetual
    /// slot caveats so child cells inherit them.
    pub fn child_program(mut self, program: &CellProgram) -> Self {
        self.child_program_vk = Some(dregg_cell::canonical_program_vk(program));
        if let CellProgram::Predicate(cs) = program {
            self.state_constraints = cs.clone();
        }
        self
    }

    /// Allow this factory to grant children a capability matching `template`.
    pub fn allow_cap(mut self, target: CapTarget, max_permissions: AuthRequired, attenuatable: bool) -> Self {
        self.cap_templates.push(CapTemplate {
            target,
            max_permissions,
            attenuatable,
        });
        self
    }

    /// Add a perpetual slot caveat (a [`StateConstraint`] enforced on every
    /// child-cell transition).
    pub fn slot_caveat(mut self, c: StateConstraint) -> Self {
        self.state_constraints.push(c);
        self
    }

    /// Created cells are sovereign rather than hosted.
    pub fn sovereign(mut self) -> Self {
        self.default_mode = CellMode::Sovereign;
        self
    }

    /// Cap how many cells this factory may create per epoch.
    pub fn creation_budget(mut self, budget: u64) -> Self {
        self.creation_budget = Some(budget);
        self
    }

    /// Finish into a [`FactoryDescriptor`] (content-addressed via its `hash()`).
    pub fn build(self) -> FactoryDescriptor {
        FactoryDescriptor {
            factory_vk: self.factory_vk,
            child_program_vk: self.child_program_vk,
            child_vk_strategy: None::<ChildVkStrategy>,
            allowed_cap_templates: self.cap_templates,
            field_constraints: Vec::new(),
            state_constraints: self.state_constraints,
            default_mode: self.default_mode,
            creation_budget: self.creation_budget,
        }
    }
}

// ===========================================================================
// AUTHOR — call-forests (multi-effect turns, with delegation edges).
// ===========================================================================

/// A builder for one node's [`Action`], carrying a real (non-`Unchecked`)
/// authorization so the authored forest passes the well-formedness rail.
/// (The embedded [`deploy_forest`] re-authorizes through the World's single-
/// custody operator path; this auth shape is what the *validation* sees.)
#[derive(Clone, Debug)]
pub struct ActionBuilder {
    target: CellId,
    effects: Vec<Effect>,
    authorization: Authorization,
    may_delegate: DelegationMode,
}

impl ActionBuilder {
    /// A node acting on `target`. Defaults to `Authorization::Signature` (a
    /// real, non-bypass auth — so the well-formedness rail is exercised
    /// honestly, not tripped by the `Unchecked` sentinel) and
    /// `DelegationMode::None`.
    pub fn new(target: CellId) -> Self {
        Self {
            target,
            effects: Vec::new(),
            authorization: Authorization::Signature([0u8; 32], [0u8; 32]),
            may_delegate: DelegationMode::None,
        }
    }

    pub fn effect(mut self, e: Effect) -> Self {
        self.effects.push(e);
        self
    }

    pub fn effects(mut self, es: impl IntoIterator<Item = Effect>) -> Self {
        self.effects.extend(es);
        self
    }

    /// Override the authorization (e.g. `Unchecked` to *deliberately* trip the
    /// well-formedness rail in a demo).
    pub fn authorization(mut self, a: Authorization) -> Self {
        self.authorization = a;
        self
    }

    /// Permit this node to delegate to its children.
    pub fn may_delegate(mut self, m: DelegationMode) -> Self {
        self.may_delegate = m;
        self
    }

    fn into_action(self) -> Action {
        Action {
            target: self.target,
            method: [0u8; 32],
            args: vec![],
            authorization: self.authorization,
            preconditions: Default::default(),
            effects: self.effects,
            may_delegate: self.may_delegate,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        }
    }
}

/// A builder for a [`CallForest`] — compose a multi-effect, multi-node turn,
/// including parent→child delegation edges (the structure the
/// non-amplification rail walks).
#[derive(Default)]
pub struct ForestBuilder {
    forest: CallForest,
}

impl ForestBuilder {
    pub fn new() -> Self {
        Self {
            forest: CallForest::new(),
        }
    }

    /// Add a root node from an [`ActionBuilder`]. Returns the root index so a
    /// caller can hang children off it via [`Self::child_of`].
    pub fn root(&mut self, action: ActionBuilder) -> usize {
        self.forest.add_root(action.into_action());
        self.forest.roots.len() - 1
    }

    /// Add a child node under the root at `root_index` (a delegation edge —
    /// the parent acts, then its child acts under the caps the parent passed).
    /// Returns the child's index within that root's `children`.
    pub fn child_of(&mut self, root_index: usize, action: ActionBuilder) -> usize {
        let root = &mut self.forest.roots[root_index];
        root.add_child(action.into_action());
        root.children.len() - 1
    }

    /// The authored forest (borrow, for validation).
    pub fn forest(&self) -> &CallForest {
        &self.forest
    }

    /// Finish into the [`CallForest`].
    pub fn build(self) -> CallForest {
        self.forest
    }
}

/// A grant effect carrying an explicit facet/expiry (so authors can compose
/// attenuation chains the non-amplification rail walks). `allowed_effects` is
/// the facet mask (`None` = unrestricted = top); `expires_at` the expiry
/// height (`None` = never).
pub fn grant_with(
    from: CellId,
    to: CellId,
    target: CellId,
    slot: u32,
    allowed_effects: Option<u32>,
    expires_at: Option<u64>,
) -> Effect {
    Effect::GrantCapability {
        from,
        to,
        cap: CapabilityRef {
            target,
            slot,
            permissions: AuthRequired::None,
            breadstuff: None,
            expires_at,
            allowed_effects,
            stored_epoch: None,
        },
    }
}

// ===========================================================================
// DEPLOY — push authored artifacts through the embedded verified World.
// ===========================================================================

/// The result of deploying a program-carrying cell: its id, and the live
/// confirmation that the cell carries the authored program.
#[derive(Clone, Debug)]
pub struct ProgramDeploy {
    pub cell: CellId,
    /// `true` iff the ledger cell now carries the authored (non-`None`) program.
    pub installed: bool,
}

/// Genesis-install a cell carrying an authored program into the live world.
///
/// The embedded executor then enforces the program's constraints on EVERY
/// state-modifying turn against this cell (a violating `SetField` is rejected —
/// see the headless tests). Returns the new cell id + a live confirmation.
///
/// (Programs are installed at cell-birth: the protocol has no `SetProgram`
/// effect — a program is part of a cell's content-addressed identity. This is
/// the genesis path, the way a node seeds program-carrying cells.)
pub fn deploy_program(world: &mut World, seed: u8, balance: i64, program: CellProgram) -> ProgramDeploy {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    let want_program = !matches!(program, CellProgram::None);
    cell.program = program;
    let id = world.genesis_install(cell);
    let installed = world
        .ledger()
        .get(&id)
        .map(|c| want_program == !matches!(c.program, CellProgram::None))
        .unwrap_or(false);
    ProgramDeploy { cell: id, installed }
}

/// The outcome of a validate-then-deploy of an authored forest.
///
/// (No `Debug` derive: it carries a [`CommitOutcome`], which is not `Debug`;
/// the editor renders it via [`describe_forest_deploy`] instead.)
pub enum ForestDeploy {
    /// The static rail FAILED — the forest was NOT submitted. Carries the
    /// verdict so the editor can show the locus.
    Refused { verdict: Verdict },
    /// The static rail passed; the forest's effects were submitted through the
    /// embedded executor, which then applied its dynamic guarantees.
    Submitted {
        verdict: Verdict,
        outcome: CommitOutcome,
    },
}

impl ForestDeploy {
    /// `true` iff the forest was actually committed by the real executor.
    pub fn committed(&self) -> bool {
        matches!(self, ForestDeploy::Submitted { outcome, .. } if outcome.is_committed())
    }
}

/// The validate-before-deploy pipeline — THE safety rail in action.
///
/// 1. [`validate`] the authored forest. On any static finding, **REFUSE** —
///    the forest is not submitted (an amplifying grant, a conservation break
///    or a malformed node is caught BEFORE paying gas).
/// 2. On a static pass, flatten the forest's effects onto a single turn from
///    `agent` and commit it through the embedded executor (which then applies
///    the *dynamic* guarantees the static rail cannot — the holding half of
///    ocap, balance sufficiency, …). The real [`CommitOutcome`] is surfaced:
///    a static `Pass` is necessary, not sufficient, and the executor may still
///    reject.
///
/// (The embedded World is single-custody — the operator is the authority — so
/// the deploy turn re-authorizes through `World::turn` rather than carrying the
/// authored node's `Token` auth across to the executor. The authored auth is
/// what the *validation* rail sees; the *deploy* runs the operator path.)
pub fn deploy_forest(world: &mut World, agent: CellId, forest: &CallForest) -> ForestDeploy {
    let verdict = validate(forest);
    if !verdict.pass() {
        return ForestDeploy::Refused { verdict };
    }
    let effects: Vec<Effect> = forest
        .roots
        .iter()
        .flat_map(|root| {
            let mut es = root.action.effects.clone();
            for child in &root.children {
                es.extend(child.action.effects.clone());
            }
            es
        })
        .collect();
    let turn = world.turn(agent, effects);
    let outcome = world.commit_turn(turn);
    ForestDeploy::Submitted { verdict, outcome }
}

/// A one-line (or few-line) human description of a [`ForestDeploy`], for the
/// editor's DEPLOY pane. (`ForestDeploy` carries a non-`Debug` `CommitOutcome`,
/// so this is the rendering surface.)
pub fn describe_forest_deploy(dep: &ForestDeploy) -> String {
    match dep {
        ForestDeploy::Refused { verdict } => format!(
            "REFUSED by the static rail — {} finding(s); NOT submitted (no gas spent)",
            verdict.all().len()
        ),
        ForestDeploy::Submitted { outcome, .. } => match outcome {
            CommitOutcome::Committed { receipt, events } => format!(
                "static PASS → executor COMMITTED: {} actions, {} computrons, {} dynamics event(s)",
                receipt.action_count,
                receipt.computrons_used,
                events.len()
            ),
            CommitOutcome::Rejected { reason, at_action } => format!(
                "static PASS but executor REJECTED (the dynamic guarantees fired): {reason} \
                 @ action {at_action:?}\n(a static Pass is necessary, NOT sufficient)"
            ),
            CommitOutcome::Queued { .. } => {
                "world suspended (meta-debug): turn queued, not committed".to_string()
            }
        },
    }
}

// ===========================================================================
// RENDER — the authoring panel (self-contained; the cockpit wires it in).
// ===========================================================================

/// What the editor panel currently presents: the authored artifact (as a
/// human description), the static verdict, and — if a deploy has run — its
/// result. The cockpit owns one of these and mutates it as the operator works;
/// [`render_panel`] turns it into the panel text.
#[derive(Clone, Debug, Default)]
pub struct EditorState {
    /// A human description of the artifact under authoring (e.g. the program's
    /// constraints, or the forest's effect summary).
    pub artifact: String,
    /// The most recent static verdict, if [`validate`] has run.
    pub verdict: Option<Verdict>,
    /// The most recent deploy result line, if a deploy has run.
    pub deploy: Option<String>,
}

impl EditorState {
    pub fn set_artifact(&mut self, s: impl Into<String>) {
        self.artifact = s.into();
    }
    pub fn set_verdict(&mut self, v: Verdict) {
        self.verdict = Some(v);
    }
    pub fn set_deploy(&mut self, s: impl Into<String>) {
        self.deploy = Some(s.into());
    }
}

/// Render the live-editor panel as text: the authoring surface, the validation
/// verdict (PASS / the located findings), and the deploy result.
///
/// This is the panel `render` fn the main loop wires into the cockpit. It is
/// deliberately string-rendering (gpui-free) so it is `cargo test`-able and the
/// visual layer can present it however it likes.
pub fn render_panel(state: &EditorState) -> String {
    let mut out = String::new();
    out.push_str("┌─ LIVE EDITOR ─ author · validate · deploy ─────────────\n");
    out.push_str("│ ARTIFACT\n");
    if state.artifact.is_empty() {
        out.push_str("│   (nothing authored yet)\n");
    } else {
        for line in state.artifact.lines() {
            out.push_str(&format!("│   {line}\n"));
        }
    }
    out.push_str("│ VALIDATION (static — necessary, NOT sufficient)\n");
    match &state.verdict {
        None => out.push_str("│   (not validated)\n"),
        Some(v) if v.pass() => out.push_str(
            "│   ✓ PASS — conservation · non-amplification · well-formed\n\
             │     (executor still applies the dynamic guarantees on deploy)\n",
        ),
        Some(v) => {
            out.push_str(&format!("│   ✗ FAIL — {} finding(s):\n", v.all().len()));
            for f in v.all() {
                out.push_str(&format!("│     [{}] @ {}\n", f.guarantee, f.locus));
                out.push_str(&format!("│       {}\n", f.message));
            }
        }
    }
    out.push_str("│ DEPLOY\n");
    match &state.deploy {
        None => out.push_str("│   (not deployed)\n"),
        Some(d) => {
            for line in d.lines() {
                out.push_str(&format!("│   {line}\n"));
            }
        }
    }
    out.push_str("└────────────────────────────────────────────────────────");
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::field_from_u64;

    // ── AUTHOR a program with a constraint → DEPLOY → the cell carries it ──

    #[test]
    fn author_program_then_deploy_carries_the_constraint() {
        let mut w = World::new();
        // Author: slot 0 is immutable after first write.
        let program = ProgramBuilder::new().immutable(0).build();
        assert!(matches!(program, CellProgram::Predicate(_)));

        let dep = deploy_program(&mut w, 0x41, 100, program);
        assert!(dep.installed, "the live cell must carry the authored program");
        let cell = w.ledger().get(&dep.cell).unwrap();
        assert!(matches!(cell.program, CellProgram::Predicate(_)));
    }

    #[test]
    fn deployed_write_once_program_gates_a_transition() {
        // The program is REAL: the executor enforces it on EVERY transition.
        // `WriteOnce` admits the first write to a zero slot, then freezes it.
        // First write to slot 0 (0→7) commits; the SECOND, differing write
        // (7→9) is rejected by the deployed program. This proves the authored
        // artifact is live, not decorative.
        let mut w = World::new();
        let program = ProgramBuilder::new().write_once(0).build();
        let dep = deploy_program(&mut w, 0x42, 100, program);
        let id = dep.cell;

        // First write: slot 0 was zero, WriteOnce admits the first write.
        let t1 = w.turn(id, vec![Effect::SetField {
            cell: id,
            index: 0,
            value: field_from_u64(7),
        }]);
        assert!(w.commit_turn(t1).is_committed(), "first write must commit");

        // Second, DIFFERING write to the now-frozen slot: the program rejects.
        let t2 = w.turn(id, vec![Effect::SetField {
            cell: id,
            index: 0,
            value: field_from_u64(9),
        }]);
        assert!(
            !w.commit_turn(t2).is_committed(),
            "the deployed WriteOnce program must freeze slot 0 — second write rejected"
        );
    }

    #[test]
    fn deployed_immutable_program_freezes_a_slot_from_birth() {
        // `Immutable` on a LEDGER cell (old_state present) freezes the slot
        // from the start — ANY change is rejected (the "register-at-genesis,
        // then read-only" shape). Authoring it and deploying it proves the
        // distinction from WriteOnce is real and enforced.
        let mut w = World::new();
        let program = ProgramBuilder::new().immutable(0).build();
        let dep = deploy_program(&mut w, 0x43, 100, program);
        let id = dep.cell;
        let t = w.turn(id, vec![Effect::SetField {
            cell: id,
            index: 0,
            value: field_from_u64(7),
        }]);
        assert!(
            !w.commit_turn(t).is_committed(),
            "Immutable freezes the slot from birth — any write rejected"
        );
    }

    // ── AUTHOR a conserving forest → VALIDATE PASS → DEPLOY commits ──

    #[test]
    fn conserving_forest_validates_pass_and_deploys() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);

        let mut fb = ForestBuilder::new();
        fb.root(ActionBuilder::new(a).effect(Effect::Transfer { from: a, to: b, amount: 250 }));
        let forest = fb.build();

        let v = validate(&forest);
        assert!(v.pass(), "a single conserving transfer must pass: {v:?}");

        let dep = deploy_forest(&mut w, a, &forest);
        assert!(dep.committed(), "a validated conserving forest must commit");
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 250);
    }

    // ── AUTHOR an AMPLIFYING grant → VALIDATE FAILS with the locus → NOT deployed ──

    #[test]
    fn amplifying_grant_fails_validation_and_is_refused() {
        // Parent grants child an ATTENUATED cap (facet 0b01) to target T.
        // The child then grants a WIDER cap (facet 0b11 ⊋ 0b01) for the same
        // target — the non-amplification rail must flag it, and deploy refuses.
        let mut w = World::new();
        let parent = w.genesis_cell(1, 0);
        let child = w.genesis_cell(2, 0);
        let target = w.genesis_cell(3, 0);

        let mut fb = ForestBuilder::new();
        let r = fb.root(
            ActionBuilder::new(parent)
                .may_delegate(DelegationMode::ParentsOwn)
                // parent → child: facet 0b01 (narrow).
                .effect(grant_with(parent, child, target, 0, Some(0b01), None)),
        );
        // child → child (re-grant): facet 0b11 (WIDER) = amplification.
        fb.child_of(
            r,
            ActionBuilder::new(child).effect(grant_with(child, child, target, 1, Some(0b11), None)),
        );
        let forest = fb.build();

        let v = validate(&forest);
        assert!(!v.pass(), "an amplifying grant must FAIL validation");
        assert!(
            !v.no_amplification.is_empty(),
            "the failure must be the non-amplification guarantee"
        );
        let f = &v.no_amplification[0];
        assert!(f.guarantee.contains("non-amplification"));
        // The locus points at the child node, effect 0 (the amplifying grant).
        assert!(f.locus.contains("forest[0][0]"), "locus must point at the child: {}", f.locus);

        // Deploy must REFUSE (not submit) on a static failure.
        let dep = deploy_forest(&mut w, parent, &forest);
        assert!(matches!(dep, ForestDeploy::Refused { .. }), "must refuse, not submit");
        assert!(!dep.committed());
        assert_eq!(w.height(), 0, "nothing was committed");
    }

    // ── A properly-ATTENUATING grant chain PASSES (the rail is not trigger-happy) ──

    #[test]
    fn attenuating_grant_chain_passes_validation() {
        let parent = CellId::from_bytes([1u8; 32]);
        let child = CellId::from_bytes([2u8; 32]);
        let target = CellId::from_bytes([3u8; 32]);

        let mut fb = ForestBuilder::new();
        let r = fb.root(
            ActionBuilder::new(parent)
                .effect(grant_with(parent, child, target, 0, Some(0b11), Some(100))),
        );
        // child grants a NARROWER facet (0b01 ⊆ 0b11) and EARLIER expiry → ok.
        fb.child_of(
            r,
            ActionBuilder::new(child).effect(grant_with(child, child, target, 1, Some(0b01), Some(50))),
        );
        let v = validate(&fb.build());
        assert!(v.no_amplification.is_empty(), "a true attenuation must pass: {v:?}");
    }

    // ── AUTHOR a malformed forest → WELL-FORMEDNESS FAILS ──

    #[test]
    fn malformed_forest_fails_wellformedness() {
        // An empty-effect node AND an Unchecked node — two well-formedness sins.
        let a = CellId::from_bytes([1u8; 32]);
        let mut fb = ForestBuilder::new();
        fb.root(ActionBuilder::new(a)); // zero effects
        fb.root(
            ActionBuilder::new(a)
                .authorization(Authorization::Unchecked)
                .effect(Effect::IncrementNonce { cell: a }),
        );
        let v = validate(&fb.build());
        assert!(!v.pass());
        assert_eq!(v.wellformed.len(), 2, "empty-effect + Unchecked = 2 findings: {:?}", v.wellformed);
        assert!(v.wellformed.iter().any(|f| f.message.contains("zero effects")));
        assert!(v.wellformed.iter().any(|f| f.message.contains("Unchecked")));
    }

    // ── AUTHOR a non-conserving forest → CONSERVATION FAILS ──

    #[test]
    fn non_conserving_balance_change_fails_conservation() {
        // A node with a +500 balance_change and no offsetting move: the
        // computron column nets to +500 (value conjured) → conservation FAIL.
        let a = CellId::from_bytes([1u8; 32]);
        let mut fb = ForestBuilder::new();
        let mut action = ActionBuilder::new(a)
            .effect(Effect::IncrementNonce { cell: a })
            .into_action();
        action.balance_change = Some(500);
        fb.forest.add_root(action);
        let v = validate(&fb.build());
        assert!(!v.conservation.is_empty(), "a +500 residue must fail conservation: {v:?}");
        assert!(v.conservation[0].message.contains("conjured"));
    }

    // ── AUTHOR a factory descriptor (state-constraint caveats baked in) ──

    #[test]
    fn factory_builder_bakes_child_program_caveats() {
        let child_program = ProgramBuilder::new().monotonic(0).write_once(1).build();
        let factory = FactoryBuilder::new([0xAB; 32])
            .child_program(&child_program)
            .allow_cap(CapTarget::SelfCell, AuthRequired::None, true)
            .creation_budget(10)
            .build();
        // The child program's constraints became the factory's perpetual slot
        // caveats (so children inherit them on every transition).
        assert_eq!(factory.state_constraints.len(), 2);
        assert!(factory.child_program_vk.is_some());
        assert_eq!(factory.allowed_cap_templates.len(), 1);
        // Content-addressed: the descriptor hashes deterministically.
        assert_eq!(factory.hash(), factory.clone().hash());
    }

    // ── RENDER the panel across the lifecycle ──

    #[test]
    fn render_panel_reflects_author_validate_deploy() {
        let mut st = EditorState::default();
        // Empty.
        let p0 = render_panel(&st);
        assert!(p0.contains("nothing authored yet"));
        assert!(p0.contains("not validated"));

        // Authored + a passing verdict.
        st.set_artifact("Transfer 250 a→b (1 root, conserving)");
        let a = CellId::from_bytes([1u8; 32]);
        let b = CellId::from_bytes([2u8; 32]);
        let mut fb = ForestBuilder::new();
        fb.root(ActionBuilder::new(a).effect(Effect::Transfer { from: a, to: b, amount: 250 }));
        st.set_verdict(validate(&fb.build()));
        st.set_deploy("Committed at height 1 (receipt logged)");
        let p1 = render_panel(&st);
        assert!(p1.contains("Transfer 250"));
        assert!(p1.contains("PASS"));
        assert!(p1.contains("Committed at height 1"));

        // A failing verdict surfaces the locus.
        let mut fb2 = ForestBuilder::new();
        fb2.root(ActionBuilder::new(a)); // empty effects → malformed
        st.set_verdict(validate(&fb2.build()));
        let p2 = render_panel(&st);
        assert!(p2.contains("FAIL"));
        assert!(p2.contains("well-formedness"));
    }
}
