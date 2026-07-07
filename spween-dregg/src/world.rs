//! # The `WorldCell` binding + the stock-runtime driver
//!
//! A spween story/world is a dregg **cell** holding the narrative vars. This module
//! implements spween's [`EffectHandler`](spween::EffectHandler) over that cell and
//! exposes the two ways a story advances:
//!
//! * [`WorldCell::apply_choice`] — the low-level primitive: a chosen `Choice` lands
//!   as **one cap-bounded turn** (its effects → cell writes, its target → the passage
//!   slot), admitted by the real [`EmbeddedExecutor`](dregg_app_framework::EmbeddedExecutor).
//!   The executor re-checks the choice's installed gate case, so an *ineligible* pick
//!   is refused in-band — nobody can take a choice they are not eligible for, and
//!   nobody can forge another's move. The collective-vote loop and the forge/gate
//!   teeth drive this path.
//! * [`Driver`] — runs the **stock `spween::Runtime`** over a [`CellHandler`]
//!   (spween's own `EffectHandler`, backed by the cell): each `select_choice` becomes
//!   a real turn and the playthrough is a receipt chain. This is single-player
//!   verifiable CYOA with the unmodified engine.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, Effect, EmbeddedExecutor, Event,
    ExecutorSubmitError, FieldElement, TurnReceipt, field_from_u64, symbol,
};
use dregg_cell::Cell;
use dregg_node_target::{NodeTarget, SubmittedTurn};
use spween::{Choice, EffectHandler, Runtime, RuntimeState, Scene, Value};
use zeroize::Zeroizing;

use crate::compiler::{
    CompileError, CompiledStory, GENESIS_METHOD, PASSAGE_ENDED, PASSAGE_SLOT, choice_method,
    compile_scene,
};
use crate::encoding::{field_to_u64, value_to_field, value_to_u64};

/// The fixed federation the world-cell's turns commit under (identity is carried by
/// the deterministic owner key, not the federation).
const WORLD_FEDERATION: [u8; 32] = [0xD6; 32];

/// Why a turn on the world-cell could not be committed.
#[derive(Clone, Debug)]
pub enum WorldError {
    /// The real executor refused the choice-turn (an ineligible gate, an unknown
    /// method, a forged/unauthorized move). The receipt-why is carried verbatim.
    Refused(String),
    /// The choice navigates to a passage not in the scene (a compile-time-checked
    /// invariant that should not occur post-[`compile_scene`]).
    UnknownTarget(String),
    /// The scene could not be compiled to a world-cell.
    Compile(CompileError),
    /// The choice-turn committed locally but a configured [`NodeTarget::Federation`]
    /// node refused it or could not confirm it landed (a rejected / unreachable /
    /// non-landing submit). Fail-closed: the caller learns the turn did not replicate.
    Federation(String),
}

impl std::fmt::Display for WorldError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WorldError::Refused(r) => write!(f, "world-cell turn refused: {r}"),
            WorldError::UnknownTarget(t) => write!(f, "unknown navigation target `{t}`"),
            WorldError::Compile(c) => write!(f, "compile error: {c}"),
            WorldError::Federation(m) => write!(f, "federation routing failed: {m}"),
        }
    }
}

impl std::error::Error for WorldError {}

impl From<ExecutorSubmitError> for WorldError {
    fn from(e: ExecutorSubmitError) -> Self {
        WorldError::Refused(e.0)
    }
}

/// **A spween world running on a dregg cell.** Owns the real executor + ledger, the
/// signing identity, the world-cell id, and the compiled story. Deterministic in the
/// scene id + seed, so a re-deploy reproduces the same cell identity and state hashes
/// (the property [`crate::verify`] leans on).
pub struct WorldCell {
    exec: EmbeddedExecutor,
    cclerk: AppCipherclerk,
    cell: CellId,
    story: Arc<CompiledStory>,
    /// Explicitly-seeded pre-play variable values (true spween `Value`s), threaded
    /// into a [`CellHandler`]'s read-overlay so the stock runtime sees them exactly
    /// as a reference in-memory handler would.
    seed_vars: BTreeMap<String, Value>,
    /// Explicitly-seeded membership atoms.
    seed_has: BTreeSet<(String, String)>,
    /// Where committed choice-turns route. [`NodeTarget::Local`] (default) keeps them on
    /// this in-process executor; [`NodeTarget::Federation`] additionally submits each to
    /// a real `DREGG_NODE_URL` node + confirms it landed.
    node_target: NodeTarget,
}

impl WorldCell {
    /// **Deploy** a spween [`Scene`] as a world-cell: compile it, birth the cell under
    /// a deterministic owner key, grant the driver a signature cap, and install the
    /// story's [`CellProgram`](dregg_app_framework::CellProgram) (the per-choice gates).
    pub fn deploy(scene: &Scene, seed: u8) -> Result<Self, WorldError> {
        let story = compile_scene(scene).map_err(WorldError::Compile)?;
        Self::from_compiled(Arc::new(story), seed)
    }

    fn from_compiled(story: Arc<CompiledStory>, seed: u8) -> Result<Self, WorldError> {
        // Deterministic identity: same scene id + seed ⇒ same owner key ⇒ same
        // world-cell id ⇒ reproducible state hashes on re-deploy (verify path).
        let mut material = story.scene_id.as_bytes().to_vec();
        material.push(seed);
        let key = blake3::derive_key("spween-dregg-world-owner-v1", &material);
        let cclerk = AppCipherclerk::new(
            AgentCipherclerk::from_key_bytes(Zeroizing::new(key)),
            WORLD_FEDERATION,
        );
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        let owner = cclerk.public_key().0;
        let token = *blake3::hash(story.scene_id.as_bytes()).as_bytes();
        let cell = CellId::derive_raw(&owner, &token);

        let agent = cclerk.cell_id();
        exec.with_ledger_mut(|ledger| {
            if ledger.get(&cell).is_none() {
                let world_cell = Cell::new(owner, token);
                let _ = ledger.insert_cell(world_cell);
            }
            if let Some(agent_cell) = ledger.get_mut(&agent) {
                agent_cell.capabilities.grant(cell, AuthRequired::Signature);
            }
        });
        exec.install_program(cell, story.program.clone());

        Ok(WorldCell {
            exec,
            cclerk,
            cell,
            story,
            seed_vars: BTreeMap::new(),
            seed_has: BTreeSet::new(),
            node_target: NodeTarget::Local,
        })
    }

    /// **Make this world federation-capable.** By default a world runs `Local` (every
    /// committed choice-turn stays on this in-process executor). Pass a
    /// [`NodeTarget::Federation`] (e.g. from [`NodeTarget::from_env`], reading
    /// `DREGG_NODE_URL`) to additionally submit each committed choice-turn to a real
    /// federation node and confirm it landed — one flip from a live federation.
    pub fn with_node_target(mut self, target: NodeTarget) -> Self {
        self.node_target = target;
        self
    }

    /// The world-cell id.
    pub fn cell_id(&self) -> CellId {
        self.cell
    }

    /// The compiled story descriptor.
    pub fn story(&self) -> &CompiledStory {
        &self.story
    }

    /// Seed a variable's pre-play value: write the cell slot directly (setup, not a
    /// turn — mirrors how flagship apps seed cell config before the game runs) AND
    /// record the true `Value` for the stock-runtime overlay. Panics-free: a var with
    /// no compiled slot is recorded in the overlay only.
    pub fn seed_var(&mut self, name: &str, value: Value) {
        if let Some(&slot) = self.story.var_slots.get(name) {
            let f = value_to_field(&value);
            self.exec.with_ledger_mut(|ledger| {
                if let Some(c) = ledger.get_mut(&self.cell) {
                    c.state.set_field(slot, f);
                }
            });
        }
        self.seed_vars.insert(name.to_string(), value);
    }

    /// Seed a membership atom (`category.key`) as present: write its slot to 1.
    pub fn seed_membership(&mut self, category: &str, key: &str) {
        if let Some(&slot) = self
            .story
            .has_slots
            .get(&(category.to_string(), key.to_string()))
        {
            self.exec.with_ledger_mut(|ledger| {
                if let Some(c) = ledger.get_mut(&self.cell) {
                    c.state.set_field(slot, field_from_u64(1));
                }
            });
        }
        self.seed_has
            .insert((category.to_string(), key.to_string()));
    }

    /// Read a variable's current numeric projection off the committed cell state.
    pub fn read_var(&self, name: &str) -> u64 {
        match self.story.var_slots.get(name) {
            Some(&slot) => self.read_slot(slot),
            None => 0,
        }
    }

    /// Read a membership atom off the committed cell state.
    pub fn read_membership(&self, category: &str, key: &str) -> bool {
        match self
            .story
            .has_slots
            .get(&(category.to_string(), key.to_string()))
        {
            Some(&slot) => self.read_slot(slot) != 0,
            None => false,
        }
    }

    /// The current passage index off the committed cell state; `None` if the scene
    /// has ended.
    pub fn read_passage(&self) -> Option<usize> {
        let p = self.read_slot(PASSAGE_SLOT);
        if p == PASSAGE_ENDED {
            None
        } else {
            Some(p as usize)
        }
    }

    fn read_slot(&self, slot: usize) -> u64 {
        self.exec
            .cell_state(self.cell)
            .map(|s| field_to_u64(&s.fields[slot]))
            .unwrap_or(0)
    }

    /// The full committed slot vector of the world-cell (all state slots) — the
    /// deterministic fingerprint the replay verifier compares (timestamp-independent,
    /// unlike a receipt hash).
    pub fn snapshot(&self) -> Vec<u64> {
        match self.exec.cell_state(self.cell) {
            Some(s) => s.fields.iter().map(field_to_u64).collect(),
            None => Vec::new(),
        }
    }

    /// **Apply a chosen `Choice` as ONE cap-bounded turn** — the world-cell binding's
    /// core primitive. The choice's effects become cell writes, its target advances
    /// the passage slot, and the whole thing is a single signed action the real
    /// executor admits IFF the choice's installed gate case passes. An ineligible or
    /// forged pick is a [`WorldError::Refused`] (nothing commits).
    ///
    /// `choice_index` is the index of the choice among its passage's choices (the same
    /// index `spween::Runtime::select_choice` uses) — it selects which gate case the
    /// turn is checked against.
    pub fn apply_choice(
        &self,
        passage_name: &str,
        choice_index: usize,
        choice: &Choice,
    ) -> Result<TurnReceipt, WorldError> {
        let method = choice_method(passage_name, choice_index);
        let mut effects = Vec::new();
        // A local accumulator so multiple Modify effects on one var compose within
        // the single turn (each reads the running value, not stale committed state).
        let mut local: BTreeMap<usize, u64> = BTreeMap::new();
        for e in &choice.effects {
            match e {
                spween::Effect::Set(s) => {
                    if let Some(&slot) = self.story.var_slots.get(s.var.as_str()) {
                        let v = value_to_u64(&s.value);
                        local.insert(slot, v);
                        effects.push(set_field(self.cell, slot, field_from_u64(v)));
                    }
                }
                spween::Effect::Modify(m) => {
                    if let Some(&slot) = self.story.var_slots.get(m.var.as_str()) {
                        let cur = *local.get(&slot).unwrap_or(&self.read_slot(slot));
                        let nv = (cur as i64 + m.delta).max(0) as u64;
                        local.insert(slot, nv);
                        effects.push(set_field(self.cell, slot, field_from_u64(nv)));
                    }
                }
                spween::Effect::Call(c) => {
                    let args: Vec<FieldElement> = c.args.iter().map(value_to_field).collect();
                    effects.push(Effect::EmitEvent {
                        cell: self.cell,
                        event: Event::new(symbol(&c.name), args),
                    });
                }
            }
        }
        let pidx = self.nav_index(choice)?;
        effects.push(set_field(self.cell, PASSAGE_SLOT, field_from_u64(pidx)));
        self.commit(&method, effects)
    }

    fn nav_index(&self, choice: &Choice) -> Result<u64, WorldError> {
        match &choice.target {
            Some(nav) if nav.is_end => Ok(PASSAGE_ENDED),
            Some(nav) => self
                .story
                .passage_index
                .get(nav.target.as_str())
                .map(|&i| i as u64)
                .ok_or_else(|| WorldError::UnknownTarget(nav.target.to_string())),
            None => Ok(PASSAGE_ENDED),
        }
    }

    /// Build, sign, and submit a turn on the world-cell under `method`.
    fn commit(&self, method: &str, effects: Vec<Effect>) -> Result<TurnReceipt, WorldError> {
        let action = self.cclerk.make_action(self.cell, method, effects);
        let receipt = self.exec.submit_action(&self.cclerk, action)?;
        // FEDERATION SEAM: in `Local` mode this is a no-op; in `Federation` mode the
        // committed choice-turn is submitted to the real node + confirmed landed, and a
        // rejected / unreachable / non-landing submit fails the choice (fail-closed).
        self.node_target
            .route(&SubmittedTurn::new(
                self.story.scene_id.clone(),
                receipt.turn_hash,
            ))
            .map_err(|e| WorldError::Federation(e.to_string()))?;
        Ok(receipt)
    }
}

/// A `SetField` effect on the world-cell.
fn set_field(cell: CellId, index: usize, value: FieldElement) -> Effect {
    Effect::SetField { cell, index, value }
}

// =============================================================================
// The stock-runtime handler: spween's own EffectHandler, backed by the cell.
// =============================================================================

/// **spween's [`EffectHandler`] over a dregg world-cell.** `get_var`/`has` read a
/// full-fidelity overlay (seeded from the world's pre-play state, updated by writes)
/// so the *stock* runtime evaluates conditions exactly as it would over an in-memory
/// handler. `set_var`/`call` BUFFER cell writes; a [`Driver`] flushes the buffer as
/// ONE verified turn per `select_choice`.
pub struct CellHandler {
    story: Arc<CompiledStory>,
    cell: CellId,
    /// The spween read model (true `Value`s, `Null` for unset) — drives conditions.
    overlay: BTreeMap<String, Value>,
    /// Membership atoms currently held.
    has: BTreeSet<(String, String)>,
    /// Cell writes buffered for the in-flight turn.
    pending: Vec<Effect>,
}

impl CellHandler {
    fn new(
        story: Arc<CompiledStory>,
        cell: CellId,
        seed_vars: &BTreeMap<String, Value>,
        seed_has: &BTreeSet<(String, String)>,
    ) -> Self {
        CellHandler {
            story,
            cell,
            overlay: seed_vars.clone(),
            has: seed_has.clone(),
            pending: Vec::new(),
        }
    }

    /// Take the buffered cell writes (clearing the buffer).
    fn take_pending(&mut self) -> Vec<Effect> {
        std::mem::take(&mut self.pending)
    }
}

impl EffectHandler for CellHandler {
    fn get_var(&self, name: &str) -> Value {
        self.overlay.get(name).cloned().unwrap_or(Value::Null)
    }

    fn set_var(&mut self, name: &str, value: Value) {
        // Buffer the cell write (numeric projection) for the turn...
        if let Some(&slot) = self.story.var_slots.get(name) {
            self.pending
                .push(set_field(self.cell, slot, value_to_field(&value)));
        }
        // ...and update the read overlay so subsequent reads in this choice see it.
        self.overlay.insert(name.to_string(), value);
    }

    fn has(&self, category: &str, key: &str) -> bool {
        self.has.contains(&(category.to_string(), key.to_string()))
    }

    fn call(&mut self, name: &str, args: &[Value]) -> Result<(), String> {
        let fields: Vec<FieldElement> = args.iter().map(value_to_field).collect();
        self.pending.push(Effect::EmitEvent {
            cell: self.cell,
            event: Event::new(symbol(name), fields),
        });
        Ok(())
    }
}

// =============================================================================
// The driver: the stock spween::Runtime, each select_choice a real turn.
// =============================================================================

/// A choice at the current passage, with its runtime-computed availability. (A
/// nameable mirror of spween's internal `AvailableChoice`, which the engine does not
/// re-export.)
#[derive(Clone, Debug)]
pub struct ChoiceView {
    /// The choice index within its passage (what [`Driver::advance`] takes).
    pub index: usize,
    /// The choice's display text.
    pub text: String,
    /// Whether the choice's condition holds against the current cell state.
    pub available: bool,
}

/// One committed step of a playthrough: the choice taken and the receipt it produced.
#[derive(Clone, Debug)]
pub struct StepReceipt {
    /// The passage the choice was taken from.
    pub passage: String,
    /// The choice index within that passage.
    pub choice_index: usize,
    /// The committed turn's receipt (turn hash + pre/post state hashes — the
    /// un-retconnable link).
    pub receipt: TurnReceipt,
    /// The world-cell's committed slot vector right after this turn — the
    /// deterministic state fingerprint the replay verifier reproduces.
    pub state: Vec<u64>,
}

/// A recorded playthrough: the genesis turn + every committed choice-step. Handed to
/// [`crate::verify`] to re-verify that these choices, in this order, reproduce exactly
/// this committed state chain (and that the receipt chain links cleanly).
#[derive(Clone, Debug)]
pub struct Playthrough {
    /// The genesis turn's receipt.
    pub genesis: TurnReceipt,
    /// The world-cell state right after genesis.
    pub genesis_state: Vec<u64>,
    /// The committed choice-steps, in order.
    pub steps: Vec<StepReceipt>,
}

impl Playthrough {
    /// The full receipt chain, genesis first.
    pub fn receipts(&self) -> Vec<&TurnReceipt> {
        let mut v = vec![&self.genesis];
        v.extend(self.steps.iter().map(|s| &s.receipt));
        v
    }
}

/// **Drives the stock `spween::Runtime` over a [`CellHandler`].** Each `advance`
/// runs the unmodified `select_choice` and flushes the resulting cell writes as one
/// verified turn, appending its receipt to the chain. The playthrough is the ordered
/// list of [`StepReceipt`]s — a provable record of which choices were made, in order.
pub struct Driver<'s> {
    world: WorldCell,
    runtime: Runtime<'s, CellHandler>,
    steps: Vec<StepReceipt>,
    genesis: Option<TurnReceipt>,
    genesis_state: Vec<u64>,
}

impl<'s> Driver<'s> {
    /// Start a playthrough over `scene` against a freshly-deployed `world`. Runs the
    /// intro passage's entry effects and commits them (plus the initial passage bind)
    /// as the genesis turn.
    pub fn start(world: WorldCell, scene: &'s Scene) -> Result<Driver<'s>, WorldError> {
        let handler = CellHandler::new(
            Arc::clone(&world.story),
            world.cell,
            &world.seed_vars,
            &world.seed_has,
        );
        let runtime = Runtime::new(scene, handler)
            .map_err(|e| WorldError::Refused(format!("runtime init: {e}")))?;
        let mut driver = Driver {
            world,
            runtime,
            steps: Vec::new(),
            genesis: None,
            genesis_state: Vec::new(),
        };
        // Commit the intro's entry effects + the initial passage bind as genesis.
        let receipt = driver.flush(GENESIS_METHOD)?;
        driver.genesis_state = driver.world.snapshot();
        driver.genesis = Some(receipt);
        Ok(driver)
    }

    /// The recorded playthrough (genesis + every committed step) — the input to
    /// [`crate::verify`].
    pub fn playthrough(&self) -> Playthrough {
        Playthrough {
            genesis: self.genesis.clone().unwrap_or_default(),
            genesis_state: self.genesis_state.clone(),
            steps: self.steps.clone(),
        }
    }

    /// The world-cell being driven.
    pub fn world(&self) -> &WorldCell {
        &self.world
    }

    /// The runtime's current prose (the passage text), if running.
    pub fn prose(&self) -> Option<String> {
        self.runtime.current_prose()
    }

    /// Whether the scene has ended.
    pub fn is_ended(&self) -> bool {
        self.runtime.is_ended()
    }

    /// The current passage name, if running.
    pub fn current_passage(&self) -> Option<String> {
        self.runtime.current_passage().map(|p| p.name.to_string())
    }

    /// The choices at the current passage (with availability, computed by the stock
    /// runtime against the cell-backed overlay).
    pub fn choices(&self) -> Vec<ChoiceView> {
        self.runtime
            .current_choices()
            .into_iter()
            .map(|c| ChoiceView {
                index: c.index,
                text: c.text.to_string(),
                available: c.available,
            })
            .collect()
    }

    /// The committed playthrough so far.
    pub fn steps(&self) -> &[StepReceipt] {
        &self.steps
    }

    /// The genesis receipt (intro entry effects + initial passage bind).
    pub fn genesis(&self) -> Option<&TurnReceipt> {
        self.genesis.as_ref()
    }

    /// **Advance the story by selecting choice `index`.** Runs the stock
    /// `select_choice` (which checks the gate, runs effects, navigates), then flushes
    /// the buffered cell writes as ONE verified turn. Returns the step's receipt.
    pub fn advance(&mut self, index: usize) -> Result<StepReceipt, WorldError> {
        let passage = self
            .current_passage()
            .ok_or_else(|| WorldError::Refused("scene already ended".into()))?;
        self.runtime
            .select_choice(index)
            .map_err(|e| WorldError::Refused(format!("runtime refused choice: {e}")))?;
        let method = choice_method(&passage, index);
        let receipt = self.flush(&method)?;
        let step = StepReceipt {
            passage,
            choice_index: index,
            receipt,
            state: self.world.snapshot(),
        };
        self.steps.push(step.clone());
        Ok(step)
    }

    /// Flush the handler's buffered writes + the current passage bind as one turn.
    fn flush(&mut self, method: &str) -> Result<TurnReceipt, WorldError> {
        let mut effects = self.runtime.handler_mut().take_pending();
        let pidx = match self.runtime.state() {
            RuntimeState::Running(i) => *i as u64,
            RuntimeState::Ended => PASSAGE_ENDED,
        };
        effects.push(set_field(
            self.world.cell,
            PASSAGE_SLOT,
            field_from_u64(pidx),
        ));
        self.world.commit(method, effects)
    }

    /// Consume the driver, returning the world-cell and the committed steps.
    pub fn finish(self) -> (WorldCell, Vec<StepReceipt>) {
        (self.world, self.steps)
    }
}
