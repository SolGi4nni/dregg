//! # The typed API — a schema deployed on a real `WorldCell`.
//!
//! [`SchemaGame::deploy`] runs the full keystone pipeline: allocate → Legal-check →
//! emit → build the `CompiledStory` → install on a real `spween_dregg::WorldCell` (the
//! deployed `EmbeddedExecutor` + ledger). A [`Turn`] builder stages typed `set`s and
//! commits them as ONE cap-bounded turn the executor admits IFF the emitted teeth pass
//! — `seed()` under the permissive genesis method, `move_()` under the gated move
//! method. [`SchemaGame::get`] reads a component back off the committed cell state.

use std::collections::BTreeMap;
use std::sync::Arc;

use dregg_app_framework::{CellId, Effect, TurnReceipt, field_from_u64};
use spween_dregg::{CompiledStory, WorldCell, WorldError};

use crate::emit::{EmitError, GENESIS_METHOD, MOVE_METHOD, emit_program};
use crate::layout::{CheckedLayout, LayoutError, Slot, allocate};
use crate::schema::Schema;

/// A schema deployed and playable on a real world-cell.
pub struct SchemaGame {
    world: WorldCell,
    layout: CheckedLayout,
    schema: Schema,
}

/// Why a schema game could not be deployed or a turn could not be built.
#[derive(Clone, Debug)]
pub enum GameError {
    /// The allocator could not produce a layout.
    Layout(LayoutError),
    /// The emitter could not lower the layout to teeth.
    Emit(EmitError),
    /// The real executor refused (or a federation route failed) — the receipt-why is
    /// carried verbatim inside the [`WorldError`].
    World(WorldError),
    /// A turn named a component not in the schema.
    UnknownComponent(String),
}

impl core::fmt::Display for GameError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            GameError::Layout(e) => write!(f, "layout: {e}"),
            GameError::Emit(e) => write!(f, "emit: {e}"),
            GameError::World(e) => write!(f, "world: {e}"),
            GameError::UnknownComponent(c) => write!(f, "unknown component `{c}`"),
        }
    }
}

impl std::error::Error for GameError {}

impl From<LayoutError> for GameError {
    fn from(e: LayoutError) -> Self {
        GameError::Layout(e)
    }
}
impl From<EmitError> for GameError {
    fn from(e: EmitError) -> Self {
        GameError::Emit(e)
    }
}
impl From<WorldError> for GameError {
    fn from(e: WorldError) -> Self {
        GameError::World(e)
    }
}

impl SchemaGame {
    /// **Deploy a schema on a real world-cell.** The full pipeline: [`allocate`] →
    /// [`CheckedLayout::new`] (Legal) → [`emit_program`] → `CompiledStory` →
    /// [`WorldCell::deploy_compiled`]. Deterministic in `(schema.name, seed)`, so a
    /// re-deploy reproduces the same cell identity and committed state hashes (the
    /// replay-verification property).
    pub fn deploy(schema: Schema, seed: u8) -> Result<Self, GameError> {
        let layout = check_layout(&schema)?;
        let story = compiled_story(&schema, &layout)?;
        let world = WorldCell::deploy_compiled(Arc::new(story), seed).map_err(GameError::World)?;

        Ok(SchemaGame {
            world,
            layout,
            schema,
        })
    }

    /// The checked layout backing this game.
    pub fn layout(&self) -> &CheckedLayout {
        &self.layout
    }

    /// The declared schema.
    pub fn schema(&self) -> &Schema {
        &self.schema
    }

    /// The world-cell id.
    pub fn cell_id(&self) -> CellId {
        self.world.cell_id()
    }

    /// The installed cell program (the emitted `CellProgram::Cases`).
    pub fn program(&self) -> &dregg_app_framework::CellProgram {
        &self.world.story().program
    }

    /// Start a **seeding** turn (permissive genesis method — sets the initial state).
    pub fn seed(&self) -> Turn<'_> {
        Turn {
            game: self,
            method: GENESIS_METHOD,
            sets: Vec::new(),
        }
    }

    /// Start a **move** turn (the gated method — the emitted teeth are re-checked by the
    /// real executor on the post-state).
    pub fn move_(&self) -> Turn<'_> {
        Turn {
            game: self,
            method: MOVE_METHOD,
            sets: Vec::new(),
        }
    }

    /// Read a component's current value off the committed cell state; `None` for an
    /// unknown component or an absent heap key.
    pub fn get(&self, component: &str) -> Option<u64> {
        match self.layout.resolve(component)? {
            Slot::Register(r) => self.world.snapshot().get(r as usize).copied(),
            Slot::Heap(k) => self.world.read_heap(k),
        }
    }

    /// The full committed register-slot vector — the deterministic fingerprint replay
    /// verification compares.
    pub fn snapshot(&self) -> Vec<u64> {
        self.world.snapshot()
    }
}

/// Allocate + Legal-check a schema — the gate every deploy passes.
pub fn check_layout(schema: &Schema) -> Result<CheckedLayout, GameError> {
    let raw = allocate(schema)?;
    // The Legal check is the gate: an ill-aligned layout is unconstructable here.
    CheckedLayout::new(raw).map_err(|e| {
        // Surface a Legal failure honestly (the allocator should never produce one).
        GameError::Layout(LayoutError::DuplicateComponent {
            name: format!("illegal-layout: {e}"),
        })
    })
}

/// **Build the deployable [`CompiledStory`] from a checked layout** — the emitted
/// one-shot-genesis + move program plus the register→var-slot map. Split out of
/// [`SchemaGame::deploy`] so a caller (the genesis-one-shot CANARY) can deploy a variant
/// program (e.g. genesis teeth emptied) on a raw `spween_dregg::WorldCell` and prove the
/// emitted guard is load-bearing.
pub fn compiled_story(schema: &Schema, layout: &CheckedLayout) -> Result<CompiledStory, GameError> {
    let program = emit_program(layout)?;

    // Register components become the `CompiledStory` var_slots (so the WorldCell's own
    // typed accessors resolve them too); collections read through the heap.
    let mut var_slots = BTreeMap::new();
    for a in layout.assignments() {
        if let Slot::Register(r) = a.slot {
            var_slots.insert(a.component.clone(), r as u64);
        }
    }

    Ok(CompiledStory {
        scene_id: schema.name.clone(),
        var_slots,
        has_slots: BTreeMap::new(),
        passage_index: BTreeMap::new(),
        program,
        fully_gated: BTreeMap::new(),
    })
}

/// A staged turn: a set of typed component writes committed as ONE cap-bounded turn.
pub struct Turn<'g> {
    game: &'g SchemaGame,
    method: &'static str,
    sets: Vec<(String, u64)>,
}

impl<'g> Turn<'g> {
    /// Stage a write of `value` to `component`.
    pub fn set(mut self, component: &str, value: u64) -> Self {
        self.sets.push((component.to_string(), value));
        self
    }

    /// Commit the staged writes as one turn. The real executor admits it IFF the
    /// installed teeth pass on the post-state; an illegal move is
    /// [`GameError::World`]`(WorldError::Refused(..))` and nothing commits (anti-ghost).
    pub fn commit(self) -> Result<TurnReceipt, GameError> {
        let cell = self.game.world.cell_id();
        let mut effects = Vec::with_capacity(self.sets.len());
        for (component, value) in &self.sets {
            let slot = self
                .game
                .layout
                .resolve(component)
                .ok_or_else(|| GameError::UnknownComponent(component.clone()))?;
            let index = match slot {
                Slot::Register(r) => u64::from(r),
                Slot::Heap(k) => k,
            };
            effects.push(Effect::SetField {
                cell,
                index,
                value: field_from_u64(*value),
            });
        }
        self.game
            .world
            .apply_raw(self.method, effects)
            .map_err(GameError::World)
    }
}
