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
    ExecutorSubmitError, FieldElement, TurnReceipt, field_from_bytes, field_from_u64, symbol,
};
use dregg_cell::program::{ProgramError, TransitionMeta};
use dregg_cell::{Cell, Ledger};
use dregg_node_target::{NodeTarget, SubmittedTurn};
use serde::{Deserialize, Serialize};
use spween::{Choice, EffectHandler, Runtime, RuntimeState, Scene, Value};
use zeroize::Zeroizing;

use crate::compiler::{
    CompileError, CompiledStory, GENESIS_DONE_EXT_KEY, GENESIS_METHOD, PASSAGE_ENDED, PASSAGE_SLOT,
    choice_method, compile_scene, program_requires_genesis_sentinel,
};
use crate::encoding::{field_to_u64, value_to_field, value_to_u64};

/// The fixed federation the world-cell's turns commit under (identity is carried by
/// the deterministic owner key, not the federation).
const WORLD_FEDERATION: [u8; 32] = [0xD6; 32];

/// The domain tag prefixing every certified-decision commitment — binds a commitment
/// to THIS scheme so a value minted elsewhere never reads as a decision binding.
const DECISION_DOMAIN: &[u8] = b"spween-dregg/collective/decision-binding-v1";

/// **The reserved certified-decision binding key.** A collective world turn
/// ([`WorldCell::apply_choice_certified`] / [`Driver::advance_certified`]) writes the
/// [`decision_commitment`] of the quorum-certified decision that authored it under THIS
/// ext-field key, in the SAME turn as the choice's passage advance — so the committed
/// turn binds "the world moved here" to "the crowd decided this". An ext key
/// (`>= dregg_cell::state::STATE_SLOTS`) lands in the committed `fields_map` /
/// `fields_root` (folded into the turn's post-state commitment, so a retcon breaks the
/// receipt chain), NOT a register slot — so it costs a scene ZERO of its 16 fixed slots
/// and can never collide with a story variable. Keyed high (`2^33`, above app ext-field
/// usage and distinct from `REFUSAL_AUDIT_EXT_KEY = 2^32`) so no application heap key
/// clashes. Absent on a single-player turn; [`WorldCell::read_decision`] reads it back
/// and [`crate::verify_collective_certified`] checks it against the certified winner.
/// Reserved collective-decision key in the high, schema-unallocated part of the
/// canonical `u64` field-index space.
pub const DECISION_EXT_KEY: u64 = 0x0000_0000_7000_0010;

const _: () = assert!(DECISION_EXT_KEY != GENESIS_DONE_EXT_KEY);

/// **The canonical commitment of a quorum-certified decision** — the value a collective
/// world turn pins into [`DECISION_EXT_KEY`] so the committed turn binds
/// to WHICH decision authored it. A commitment over the winning option, the choice it
/// resolves to, the winner's tally, and the quorum-met total: `blake3(domain ‖ winner
/// option ‖ winner choice ‖ winner tally ‖ total)`. Both the CYOA branch loop
/// ([`crate::run_collective`]) and the dungeon seam
/// (`dungeon_on_dregg::CollectiveRound::resolve_into_world`) mint it from the SAME
/// certified winner they advance the world by, and [`crate::verify_collective_certified`]
/// recomputes it from the round's certified winner to check the committed slot — an
/// operator who advanced the world by a DIFFERENT choice than the certified winner
/// leaves the slot zero / mismatched and is caught.
pub fn decision_commitment(
    winner_option: u64,
    winner_choice: u64,
    winner_tally: u64,
    total: u64,
) -> FieldElement {
    let mut h = blake3::Hasher::new();
    h.update(DECISION_DOMAIN);
    h.update(&winner_option.to_be_bytes());
    h.update(&winner_choice.to_be_bytes());
    h.update(&winner_tally.to_be_bytes());
    h.update(&total.to_be_bytes());
    field_from_bytes(h.finalize().as_bytes())
}

/// Why a turn on the world-cell could not be committed.
#[derive(Clone, Debug)]
pub enum WorldError {
    /// The real executor refused the choice-turn (an ineligible gate, an unknown
    /// method, a forged/unauthorized move). The receipt-why is carried verbatim.
    Refused(String),
    /// The choice navigates to a passage not in the scene (a compile-time-checked
    /// invariant that should not occur post-[`compile_scene`]).
    UnknownTarget(String),
    /// The choice's gate did NOT lower fully to executor constraints — its
    /// [`CompiledStory::fully_gated`] entry is `Some(false)`, so the installed
    /// `MethodIs` case carries an EMPTY (handler-only) tooth set. `apply_choice`
    /// drives the executor as the SOLE referee, so admitting such a turn would
    /// commit a choice whose condition NOTHING on this path checks (a fail-open).
    /// Refused, fail-closed: a handler-only gate must go through the `Driver`
    /// path (`select_choice`), the only path that evaluates it.
    UngatedChoice(String),
    /// The scene could not be compiled to a world-cell.
    Compile(CompileError),
    /// A durable world image or its write-ahead turn intent could not be
    /// authenticated, restored, or committed. A turn never reports success
    /// unless its post-state image is durable.
    Durability(String),
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
            WorldError::UngatedChoice(m) => write!(
                f,
                "under-gated choice refused: method `{m}` did not lower fully to \
                 executor teeth (handler-only gate; drive it through the runtime path)"
            ),
            WorldError::Compile(c) => write!(f, "compile error: {c}"),
            WorldError::Durability(message) => {
                write!(f, "world-cell durability refused: {message}")
            }
            WorldError::Federation(m) => write!(f, "federation routing failed: {m}"),
        }
    }
}

/// **What [`WorldCell::probe_choice`] can say about a choice** — the executor's own
/// admission predicate, dry-run against the committed state, with an explicit
/// "cannot decide" answer instead of a guess.
///
/// The third value is the load-bearing one. A dry run has no `EvalContext`, witness
/// bundle, or capability set, so the contextual constraint families (heights, temporal
/// gates, sender authorization, preimage reveals, witnessed predicates, the Lean oracle
/// when its archive is absent) are not decidable here. Collapsing those onto either
/// boolean would be a lie in one direction or the other: onto `Refuses` it would silently
/// delete legal moves from a game; onto `Admits` it would claim an admission this probe
/// never established. A caller that filters an offer list on this probe keeps
/// [`ChoiceAdmission::Undecided`] moves OFFERED — the executor still refuses them if they
/// are ineligible, so the cost is a wasted round-trip, not a broken gate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChoiceAdmission {
    /// The installed program's teeth accept this choice against the committed state.
    Admits,
    /// The installed teeth REFUSE it against the committed state (a violated constraint or
    /// default-deny), or [`WorldCell::apply_choice`] would refuse it for being under-gated.
    /// Carries the executor's own description.
    Refuses(String),
    /// The probe could not decide: the choice's gate reaches material only the executor
    /// holds. Treat as offered; the executor is still the referee.
    Undecided(String),
}

impl ChoiceAdmission {
    /// Whether a caller filtering an offer list should keep this choice. `Admits` and
    /// `Undecided` both stay; only a decisive refusal is dropped.
    pub fn offerable(&self) -> bool {
        !matches!(self, ChoiceAdmission::Refuses(_))
    }
}

/// ⚑ **THE PLAYER'S SENTENCE for a commit that failed on OUR side of the wire.** Not a phrase to
/// re-type at a call site: it is `dreggnet_offerings::refusal::COMMIT_FAILED_NOTHING_CHANGED`, named
/// here because this crate sits below that one and both must say the same thing. The literal is
/// duplicated by necessity (no shared crate sits below both) and pinned identical by the
/// refusal-copy gate, which asserts the two are equal.
const COMMIT_FAILED_NOTHING_CHANGED: &str =
    "Something went wrong committing that move; nothing was changed. Try again in a moment.";

impl WorldError {
    /// ⚑ **THE PLAYER HALF of this refusal.** [`Display`](std::fmt::Display) above is the OPERATOR's
    /// string and always was — it prepends the name of an internal architecture ("world-cell turn
    /// refused: …", "under-gated choice refused: method `select` did not lower fully to executor
    /// teeth (handler-only gate; drive it through the runtime path)"). That string reached players
    /// from ~12 sites, because it was the generic fallback for EVERY commit in Automatafl, Tug, the
    /// dungeon and the native Descent: `Err(e) => Outcome::Refused(e.to_string())`.
    ///
    /// The split is by audience, and it falls out of the variants cleanly:
    ///
    /// - [`WorldError::Refused`] carries the receipt's own *why*, produced by the game's rules — it
    ///   is already the sentence a player should read ("the purse is empty", "that action is already
    ///   spent this round"), and it is handed back VERBATIM. Only `Display`'s prefix was the leak.
    /// - Every other variant is about missing/broken machinery on this server and says nothing about
    ///   the move: a gate that did not lower to checkable form, a durability write that would not
    ///   land, a peer that would not confirm, a scene that would not compile, a target that is not in
    ///   the story. There is nothing the reader could have chosen differently, so they get the one
    ///   thing that changes what they do next, and the internals go to
    ///   [`operator_diagnostic`](Self::operator_diagnostic).
    ///
    /// Mirrors `cell::program::ProgramError::operator_diagnostic` — the same split, landed the same
    /// day, deliberately NOT a second pattern.
    pub fn player_message(&self) -> String {
        match self {
            WorldError::Refused(why) => why.clone(),
            WorldError::UnknownTarget(_)
            | WorldError::UngatedChoice(_)
            | WorldError::Compile(_)
            | WorldError::Durability(_)
            | WorldError::Federation(_) => COMMIT_FAILED_NOTHING_CHANGED.to_string(),
        }
    }

    /// **THE OPERATOR HALF** — `Some(detail)` exactly when [`player_message`](Self::player_message)
    /// declines to repeat the cause, `None` for a [`WorldError::Refused`] whose whole story the
    /// player already got.
    ///
    /// `Option` rather than `String` so the two halves cannot silently double up: a caller that logs
    /// `Some` beside the sentence it shows loses nothing, and never logs the same words twice.
    pub fn operator_diagnostic(&self) -> Option<String> {
        match self {
            WorldError::Refused(_) => None,
            other => Some(other.to_string()),
        }
    }
}

/// Canonical local executor image used by the file-backed durability layer.
/// Runtime caches and locks are deliberately absent; restore reconstructs them
/// from these cells plus the strictly linked receipt chain.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct WorldCellDurableState {
    pub cells: Vec<Cell>,
    pub receipts: Vec<TurnReceipt>,
    pub ledger_root: [u8; 32],
}

pub(crate) trait WorldCellDurability: Send + Sync {
    fn bind(&self, state: &WorldCellDurableState) -> Result<(), String>;
    fn prepare(
        &self,
        state: &WorldCellDurableState,
        method: &str,
        effects: &[Effect],
    ) -> Result<(), String>;
    fn commit(&self, state: &WorldCellDurableState) -> Result<(), String>;
    fn abort(&self, state: &WorldCellDurableState) -> Result<(), String>;
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
    /// Whether the INSTALLED program carries the one-shot genesis teeth (i.e. it came from
    /// [`compile_scene`]), so this world must birth [`GENESIS_DONE_EXT_KEY`] at deploy and
    /// write it `0 → 1` on the genesis turn. `false` for a HAND-BUILT story that installs
    /// its own genesis case (`dregg-multiway-tug`, the dungeon keep, test fixtures) —
    /// those worlds stay byte-identical to before. Computed once from the program, never
    /// from the method name (several consumers spell their own method `"genesis"` too).
    genesis_sentinel: bool,
    /// Optional write-ahead + atomic-image durability. Kept behind a narrow
    /// trait so ordinary browser/test worlds remain byte-for-byte in-memory.
    durability: Option<Arc<dyn WorldCellDurability>>,
}

impl WorldCell {
    /// **Deploy** a spween [`Scene`] as a world-cell: compile it, birth the cell under
    /// a deterministic owner key, grant the driver a signature cap, and install the
    /// story's [`CellProgram`](dregg_app_framework::CellProgram) (the per-choice gates).
    pub fn deploy(scene: &Scene, seed: u8) -> Result<Self, WorldError> {
        let story = compile_scene(scene).map_err(WorldError::Compile)?;
        Self::from_compiled(Arc::new(story), seed)
    }

    /// **Deploy an already-compiled (and possibly post-processed) [`CompiledStory`].**
    /// The public form of [`Self::from_compiled`]: a caller compiles a scene, AUGMENTS
    /// the resulting [`CompiledStory::program`] with extra executor teeth the v0
    /// compiler does not emit (a [`dregg_app_framework::StateConstraint::WriteOnce`] on a
    /// loot-owner slot, a `Monotonic` ratchet, a `FieldLteField` budget bound, a
    /// `HeapField` on a heap-keyed collection), and deploys that. The augmented
    /// constraints are REAL `CellProgram` cases the [`EmbeddedExecutor`] re-checks on
    /// every touching turn — identical enforcement to a compiler-emitted tooth, since
    /// the executor never distinguishes who authored a case. Additive: existing callers
    /// go through [`Self::deploy`] unchanged.
    pub fn deploy_compiled(story: Arc<CompiledStory>, seed: u8) -> Result<Self, WorldError> {
        Self::from_compiled(story, seed)
    }

    /// **DECLARE this world's per-turn computron fee** — forwarded to the embedded
    /// executor ([`EmbeddedExecutor::with_turn_fee`]), which stamps it on every turn this
    /// world commits.
    ///
    /// A world whose state is BIG needs this: `turn.fee` is the executor's computron limit
    /// for the turn, so a world-cell that writes a many-square board in one turn is
    /// refused outright under the framework's
    /// [`dregg_app_framework::DEFAULT_TURN_FEE`] — the refusal lands on the GENESIS turn,
    /// before the world can seed its opening state. The fee is also debited in full from
    /// the world agent's purse per turn, so it is a budget the world owns rather than a
    /// cap it may raise for free; declare it from the state's actual size and expect the
    /// purse to divide by it. Worlds that do not call this keep the framework default
    /// exactly.
    pub fn with_turn_fee(mut self, fee: u64) -> Self {
        // `EmbeddedExecutor` is a cheap `Arc` handle; the clone rebinds the SAME runtime
        // and ledger with the fee declared on it.
        self.exec = self.exec.clone().with_turn_fee(fee);
        self
    }

    /// **DECLARE `ceiling` as this world's per-turn computron CEILING and pay each turn's OWN
    /// price under it** ([`EmbeddedExecutor::with_metered_turn_fee`]) — what a world with a big
    /// state and a long session wants instead of [`Self::with_turn_fee`].
    ///
    /// A flat fee has to be sized to the GENESIS turn, because that is the turn that writes the
    /// whole world; and because the executor debits the fee in full on every turn, the genesis
    /// turn's price is then what a one-register `select` pays. The world agent's endowment
    /// divided by that price is a hard ceiling on session LENGTH that nobody chose — automatafl
    /// measured 51 play turns, about seven rounds, before `InsufficientBalance`
    /// (`dregg-automatafl/tests/match_length_purse.rs`).
    ///
    /// Metered, the endowment bounds total WORK instead: the genesis seed pays for its own 137
    /// writes once, a `select` pays for its two, and `ceiling` goes on doing the job worth
    /// keeping — refusing a turn that would write more than this world ever legitimately writes.
    /// Worlds that call neither method keep the framework default exactly.
    pub fn with_metered_turn_fee(mut self, ceiling: u64) -> Self {
        self.exec = self.exec.clone().with_metered_turn_fee(ceiling);
        self
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
        let ext_keys = story.ext_keys();
        // Does the INSTALLED program actually ask for the one-shot genesis sentinel? A
        // hand-built story installing its own genesis case does not — leave it untouched.
        let genesis_sentinel = program_requires_genesis_sentinel(&story.program);
        exec.with_ledger_mut(|ledger| {
            if ledger.get(&cell).is_none() {
                let world_cell = Cell::new(owner, token);
                let _ = ledger.insert_cell(world_cell);
            }
            // BIRTH the wide plane. A fixed register is born present-at-field-zero; an
            // ext key is born ABSENT, and every `HeapField` atom fails closed on an
            // absent key — so an unseeded SPILLED var would REFUSE the very gates its
            // register twin admits (`{ heals_used <= 0 }` on a never-written var), a
            // play-vs-replay split. Writing field-zero once at deploy makes the two
            // planes' initial state identical, so spilling is invisible to a scene's
            // semantics. Setup, not a turn — exactly how `seed_var` seeds a register.
            // No-op for a scene that fits the 16 registers (`ext_keys` is empty).
            if let Some(c) = ledger.get_mut(&cell) {
                for &key in &ext_keys {
                    if c.state.get_field_ext(key).is_none() {
                        c.state.set_field_ext(key, field_from_u64(0));
                    }
                }
                // BIRTH the genesis-done sentinel at field-zero — ONLY for a program that
                // carries the one-shot teeth. They (`Equals{1} ∧ DeltaEquals{1}`) and the
                // per-case `Immutable` freeze read a PRESENT pre-state — `DeltaEquals`
                // fails closed on an absent old — so the sentinel must exist at zero
                // before the first genesis turn writes it `0 → 1`. Setup, not a turn
                // (exactly how the ext keys above are born); the sentinel is NOT in
                // `snapshot()` (not a story var), so replay/state fingerprints are
                // unchanged.
                if genesis_sentinel && c.state.get_field_ext(GENESIS_DONE_EXT_KEY).is_none() {
                    c.state
                        .set_field_ext(GENESIS_DONE_EXT_KEY, field_from_u64(0));
                }
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
            genesis_sentinel,
            durability: None,
        })
    }

    pub(crate) fn restore_compiled(
        story: Arc<CompiledStory>,
        seed: u8,
        executor_signing_seed: [u8; 32],
        state: WorldCellDurableState,
    ) -> Result<Self, WorldError> {
        let mut material = story.scene_id.as_bytes().to_vec();
        material.push(seed);
        let key = blake3::derive_key("spween-dregg-world-owner-v1", &material);
        let cclerk = AppCipherclerk::new(
            AgentCipherclerk::from_key_bytes(Zeroizing::new(key)),
            WORLD_FEDERATION,
        );
        let owner = cclerk.public_key().0;
        let token = *blake3::hash(story.scene_id.as_bytes()).as_bytes();
        let cell = CellId::derive_raw(&owner, &token);
        let agent = cclerk.cell_id();

        if state.cells.is_empty() {
            return Err(WorldError::Durability(
                "restored world image has no cells".to_owned(),
            ));
        }
        let mut ledger = Ledger::new();
        for restored in state.cells {
            if !restored.verify_id_integrity() {
                return Err(WorldError::Durability(
                    "restored world image contains an invalid cell identity".to_owned(),
                ));
            }
            ledger.insert_cell(restored).map_err(|error| {
                WorldError::Durability(format!("restored world cell set is invalid: {error}"))
            })?;
        }
        if ledger.get(&cell).is_none() || ledger.get(&agent).is_none() {
            return Err(WorldError::Durability(
                "restored world image is missing its target or agent cell".to_owned(),
            ));
        }
        let installed_program = postcard::to_stdvec(&ledger.get(&cell).expect("checked").program)
            .map_err(|error| WorldError::Durability(error.to_string()))?;
        let expected_program = postcard::to_stdvec(&story.program)
            .map_err(|error| WorldError::Durability(error.to_string()))?;
        if installed_program != expected_program {
            return Err(WorldError::Durability(
                "restored target program differs from the compiled story".to_owned(),
            ));
        }
        let found_root = ledger.root();
        if found_root != state.ledger_root {
            return Err(WorldError::Durability(
                "restored world ledger root differs from its image commitment".to_owned(),
            ));
        }

        let expected_executor = dregg_sdk::executor_pubkey_from_seed(&executor_signing_seed);
        for receipt in &state.receipts {
            if receipt.agent != agent
                || receipt.federation_id != WORLD_FEDERATION
                || receipt.finality != dregg_turn::Finality::Final
                || dregg_turn::verify_receipt_signature_with_keys(receipt, &[expected_executor])
                    .is_err()
            {
                return Err(WorldError::Durability(
                    "restored world receipt failed its pinned authority checks".to_owned(),
                ));
            }
        }
        if let Some(head) = state.receipts.last()
            && head.post_state_hash != found_root
        {
            return Err(WorldError::Durability(
                "restored receipt head does not commit the restored ledger".to_owned(),
            ));
        }
        cclerk
            .shared_cipherclerk()
            .write()
            .unwrap_or_else(|error| error.into_inner())
            .restore_receipt_chain(state.receipts)
            .map_err(|error| WorldError::Durability(error.to_string()))?;
        let exec = EmbeddedExecutor::from_restored_ledger(&cclerk, "default", ledger)
            .map_err(WorldError::Durability)?;
        exec.set_executor_signing_key(executor_signing_seed);
        let genesis_sentinel = program_requires_genesis_sentinel(&story.program);
        Ok(Self {
            exec,
            cclerk,
            cell,
            story,
            seed_vars: BTreeMap::new(),
            seed_has: BTreeSet::new(),
            node_target: NodeTarget::Local,
            genesis_sentinel,
            durability: None,
        })
    }

    pub(crate) fn durable_state(&self) -> WorldCellDurableState {
        let (mut cells, ledger_root) = self.exec.with_ledger_mut(|ledger| {
            let cells = ledger
                .iter()
                .map(|(_, cell)| cell.clone())
                .collect::<Vec<_>>();
            (cells, ledger.root())
        });
        cells.sort_by_key(Cell::id);
        WorldCellDurableState {
            cells,
            receipts: self.receipt_chain_snapshot(),
            ledger_root,
        }
    }

    pub(crate) fn attach_durability(
        mut self,
        durability: Arc<dyn WorldCellDurability>,
    ) -> Result<Self, WorldError> {
        durability
            .bind(&self.durable_state())
            .map_err(WorldError::Durability)?;
        self.durability = Some(durability);
        Ok(self)
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

    /// The deterministic executor-agent cell whose nonce and receipt chain
    /// authorize this world. Durable registries bind it without receiving any
    /// signing material.
    pub fn executor_agent_cell(&self) -> CellId {
        self.cclerk.cell_id()
    }

    /// Install the deployment-owned signing key used for executor receipts.
    ///
    /// Game/application protocols which consume a receipt as portable
    /// authority must pin the corresponding [`Self::executor_pubkey`] and
    /// verify the signature.  Keeping this opt-in preserves the historical
    /// local test profile while giving cross-offering consequences an
    /// authenticated executor boundary.
    pub fn set_executor_signing_key(&self, seed: [u8; 32]) {
        self.exec.set_executor_signing_key(seed);
    }

    /// Public key for the installed executor-receipt signer, if configured.
    pub fn executor_pubkey(&self) -> Option<[u8; 32]> {
        self.exec.executor_pubkey()
    }

    /// Read one immutable receipt from the executor's authoritative chain.
    ///
    /// This is intentionally lookup-only.  Restart recovery can corroborate a
    /// prepared cross-offering operation without accepting a caller-supplied
    /// receipt or re-dispatching a turn whose commit status is unknown.
    pub fn receipt_by_hash(&self, receipt_hash: [u8; 32]) -> Option<TurnReceipt> {
        let shared = self.cclerk.shared_cipherclerk();
        let cipherclerk = shared.read().unwrap_or_else(|error| error.into_inner());
        cipherclerk
            .receipt_chain()
            .iter()
            .find(|receipt| receipt.receipt_hash() == receipt_hash)
            .cloned()
    }

    /// Snapshot the immutable receipt index for exact-effect recovery.
    pub fn receipt_chain_snapshot(&self) -> Vec<TurnReceipt> {
        let shared = self.cclerk.shared_cipherclerk();
        let cipherclerk = shared.read().unwrap_or_else(|error| error.into_inner());
        cipherclerk.receipt_chain().to_vec()
    }

    /// Federation identity bound into every receipt produced by this world.
    pub const fn federation_id(&self) -> [u8; 32] {
        WORLD_FEDERATION
    }

    /// The compiled story descriptor.
    pub fn story(&self) -> &CompiledStory {
        &self.story
    }

    /// Seed a variable's pre-play value: write the cell field directly (setup, not a
    /// turn — mirrors how flagship apps seed cell config before the game runs) AND
    /// record the true `Value` for the stock-runtime overlay. Panics-free: a var with
    /// no compiled key is recorded in the overlay only. `set_field_ext` routes by the
    /// key, so a SPILLED var seeds through the identical call.
    pub fn seed_var(&mut self, name: &str, value: Value) {
        if let Some(key) = self.story.var_key(name) {
            let f = value_to_field(&value);
            self.exec.with_ledger_mut(|ledger| {
                if let Some(c) = ledger.get_mut(&self.cell) {
                    c.state.set_field_ext(key, f);
                }
            });
        }
        self.seed_vars.insert(name.to_string(), value);
    }

    /// Seed a membership atom (`category.key`) as present: write its field to 1.
    pub fn seed_membership(&mut self, category: &str, key: &str) {
        if let Some(k) = self.story.has_key(category, key) {
            self.exec.with_ledger_mut(|ledger| {
                if let Some(c) = ledger.get_mut(&self.cell) {
                    c.state.set_field_ext(k, field_from_u64(1));
                }
            });
        }
        self.seed_has
            .insert((category.to_string(), key.to_string()));
    }

    /// Read a variable's current numeric projection off the committed cell state.
    /// Resolves BY NAME through the compiled layout, so it reads a register var and a
    /// SPILLED one the same way.
    pub fn read_var(&self, name: &str) -> u64 {
        match self.story.var_key(name) {
            Some(key) => self.read_key(key),
            None => 0,
        }
    }

    /// Read a membership atom off the committed cell state.
    pub fn read_membership(&self, category: &str, key: &str) -> bool {
        match self.story.has_key(category, key) {
            Some(k) => self.read_key(k) != 0,
            None => false,
        }
    }

    /// The current passage index off the committed cell state; `None` if the scene
    /// has ended.
    pub fn read_passage(&self) -> Option<usize> {
        let p = self.read_key(PASSAGE_SLOT as u64);
        if p == PASSAGE_ENDED {
            None
        } else {
            Some(p as usize)
        }
    }

    /// Read one compiled field by its KEY, on either plane — `get_field_ext` resolves
    /// `< STATE_SLOTS` to the register file and the rest to the committed `fields_map`.
    /// (Indexing `state.fields[key]` here would panic on a spilled key; the whole read
    /// path goes through the uniform accessor instead.)
    fn read_key(&self, key: u64) -> u64 {
        self.exec
            .cell_state(self.cell)
            .and_then(|s| s.get_field_ext(key))
            .map(|f| field_to_u64(&f))
            .unwrap_or(0)
    }

    /// The committed state fingerprint of the world-cell — the deterministic value the
    /// replay verifier compares (timestamp-independent, unlike a receipt hash): all 16
    /// register slots, then every compiled EXT var's committed value in ascending key
    /// order.
    ///
    /// The ext tail is what keeps replay honest on a wide scene: a spilled var lives in
    /// `fields_map`, not `fields`, so a registers-only fingerprint would let a >16-var
    /// playthrough diverge in its spilled state and still "reproduce". A scene that fits
    /// the registers has no ext keys, so its snapshot is the same 16-element vector as
    /// before — the `[PASSAGE_SLOT]` index and every existing comparison are unchanged.
    pub fn snapshot(&self) -> Vec<u64> {
        let Some(s) = self.exec.cell_state(self.cell) else {
            return Vec::new();
        };
        let mut out: Vec<u64> = s.fields.iter().map(field_to_u64).collect();
        for key in self.story.ext_keys() {
            out.push(s.get_field_ext(key).map(|f| field_to_u64(&f)).unwrap_or(0));
        }
        out
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
        self.require_fully_gated(&method)?;
        let effects = self.choice_effects(choice)?;
        self.commit(&method, effects)
    }

    /// **Apply a choice as ONE cap-bounded turn, BOUND to a certified decision.** Like
    /// [`apply_choice`](Self::apply_choice), but the same turn ALSO writes `commitment`
    /// (a [`decision_commitment`]) into [`DECISION_EXT_KEY`] — so the
    /// committed world turn binds "the world advanced by this choice" to "the crowd
    /// certified this decision", atomically. The collective seam
    /// (`dungeon_on_dregg::CollectiveRound::resolve_into_world`) drives THIS path with
    /// the commitment of the quorum-certified winner it resolves; a caller that instead
    /// advances the world by a different choice via the plain [`apply_choice`](Self::apply_choice)
    /// leaves the slot unwritten and is caught by [`crate::verify_collective_certified`] /
    /// [`Self::read_decision`].
    pub fn apply_choice_certified(
        &self,
        passage_name: &str,
        choice_index: usize,
        choice: &Choice,
        commitment: FieldElement,
    ) -> Result<TurnReceipt, WorldError> {
        let method = choice_method(passage_name, choice_index);
        self.require_fully_gated(&method)?;
        let mut effects = self.choice_effects(choice)?;
        effects.push(set_field(self.cell, DECISION_EXT_KEY, commitment));
        self.commit(&method, effects)
    }

    /// **Apply a choice as ONE cap-bounded turn, with EXTRA receipt-only effects riding
    /// the SAME turn.** Identical to [`apply_choice`](Self::apply_choice) in every
    /// admission respect — the same [`require_fully_gated`](Self::require_fully_gated)
    /// fail-closed check, the same [`choice_effects`](Self::choice_effects) lowering, the
    /// same `MethodIs` case — and then appends `extra` to the effect list before the turn
    /// is signed.
    ///
    /// This exists so a caller that must bind an extra fact into the turn (the narrator's
    /// narration-commitment `EmitEvent`) does not have to reach for
    /// [`apply_raw`](Self::apply_raw). `apply_raw` is BELOW the choice layer: it skips
    /// `require_fully_gated`, so a choice whose condition did not lower fully to executor
    /// teeth would commit with NOTHING on that path checking it — the exact fail-open
    /// `require_fully_gated` exists to close. Reaching it also forced callers to
    /// re-implement `choice_effects`, and a re-implementation drifts (the narrator's copy
    /// silently ended the scene on an unknown navigation target where the canonical
    /// lowering raises [`WorldError::UnknownTarget`]).
    ///
    /// `extra` is appended AFTER the choice's own effects and the passage advance, so it
    /// can never displace the move: a caller cannot use it to overwrite the navigation or
    /// re-write a var the choice just set to a different value, because the choice's write
    /// is already in the list and the executor's teeth see the whole post-state either way.
    /// What it CAN do is add a write of its own, which is why every tooth on this method's
    /// case — and every `SlotChanged` invariant case — still applies to the composed turn.
    pub fn apply_choice_with_effects(
        &self,
        passage_name: &str,
        choice_index: usize,
        choice: &Choice,
        extra: Vec<Effect>,
    ) -> Result<TurnReceipt, WorldError> {
        let method = choice_method(passage_name, choice_index);
        self.require_fully_gated(&method)?;
        let mut effects = self.choice_effects(choice)?;
        effects.extend(extra);
        self.commit(&method, effects)
    }

    /// **Would the installed program admit this choice RIGHT NOW?** — a DRY RUN of the
    /// executor's own admission predicate against the committed state, committing nothing.
    ///
    /// This is not a re-implementation of the gate: it lowers the choice through the same
    /// [`choice_effects`](Self::choice_effects) the real turn uses, applies those writes to
    /// a CLONE of the committed [`CellState`](dregg_cell::state::CellState), and hands the
    /// `(old, new)` pair to [`CellProgram::evaluate_with_meta`] — the same call
    /// `dregg_turn`'s `execute_tree` makes at admission, under a
    /// [`TransitionMeta`](dregg_cell::program::TransitionMeta) built the same way (the
    /// method symbol plus the OR of the effects' `effect_kind_mask()`). On a native build
    /// with the constraint oracle installed, that evaluator routes the Lean-decided subset
    /// to the verified `dregg_constraint_admits`, so the probe inherits the same decision
    /// procedure rather than paraphrasing it.
    ///
    /// It is deliberately THREE-valued. A dry run has no `EvalContext`, no witness bundle,
    /// and no capability set, so the contextual / witnessed / oracle-backed constraint
    /// families cannot be decided here. Those surface as
    /// [`ChoiceAdmission::Undecided`] — never as a refusal — because the only sound
    /// reading of "I could not evaluate this" is "ask the executor", and a caller that
    /// filters an offer list on this probe must keep an undecidable move OFFERED.
    ///
    /// The two decisive answers are the executor's own: a violated constraint
    /// (`ProgramError::ConstraintViolated`) and default-deny
    /// (`ProgramError::NoTransitionCaseMatched`). A method whose gate did not lower fully
    /// to executor teeth is [`ChoiceAdmission::Refuses`] too — not because the teeth refuse
    /// it, but because [`apply_choice`](Self::apply_choice) does, and this probe answers for
    /// that path.
    ///
    /// ⚠ It answers for the state as it is NOW. A later turn can flip either way, which is
    /// why it is a filter on what to OFFER and never a substitute for committing the turn.
    pub fn probe_choice(
        &self,
        passage_name: &str,
        choice_index: usize,
        choice: &Choice,
    ) -> ChoiceAdmission {
        let method = choice_method(passage_name, choice_index);
        if let Err(refusal) = self.require_fully_gated(&method) {
            return ChoiceAdmission::Refuses(refusal.to_string());
        }
        let effects = match self.choice_effects(choice) {
            Ok(effects) => effects,
            Err(refusal) => return ChoiceAdmission::Refuses(refusal.to_string()),
        };
        let Some(old) = self.exec.cell_state(self.cell) else {
            return ChoiceAdmission::Undecided(
                "the world-cell is not in the embedded ledger".to_string(),
            );
        };
        let mut new = old.clone();
        for effect in &effects {
            match effect {
                Effect::SetField { cell, index, value } if *cell == self.cell => {
                    new.set_field_ext(*index, *value);
                }
                // The choice's `Call` effects are receipt-only (they mutate no field), and
                // `choice_effects` emits nothing else. Anything unrecognised means this
                // probe does not model the post-state, so it must not answer.
                Effect::EmitEvent { .. } => {}
                other => {
                    return ChoiceAdmission::Undecided(format!(
                        "the choice lowers to an effect this probe does not model: {other:?}"
                    ));
                }
            }
        }
        let effects_mask: u32 = effects
            .iter()
            .fold(0u32, |mask, effect| mask | effect.effect_kind_mask());
        let meta = TransitionMeta::new(symbol(&method), effects_mask);
        match self
            .story
            .program
            .evaluate_with_meta(&new, Some(&old), None, &meta)
        {
            Ok(()) => ChoiceAdmission::Admits,
            Err(ProgramError::ConstraintViolated { description, .. }) => {
                ChoiceAdmission::Refuses(description)
            }
            Err(ProgramError::NoTransitionCaseMatched) => ChoiceAdmission::Refuses(
                "no installed transition case dispatches this method".to_string(),
            ),
            Err(undecidable) => ChoiceAdmission::Undecided(undecidable.to_string()),
        }
    }

    /// **Fail-closed on an under-gated choice.** `apply_choice*` drives the executor as
    /// the SOLE referee, so a choice whose gate did NOT lower fully to executor teeth
    /// (`fully_gated[method] == Some(false)`: some clause was left to the runtime/handler
    /// and its `MethodIs` case carries an EMPTY tooth set) would commit WITHOUT anything
    /// on this path ever checking its condition. Refuse it here so the executor admits a
    /// turn IFF the installed case is the WHOLE gate. The map is `Absent ⇒ no condition
    /// (trivially, correctly ungated — nothing to check)` / `Some(true) ⇒ full teeth` /
    /// `Some(false) ⇒ handler-only` — only the third is the hazard, and it must instead be
    /// driven through [`Driver::advance`]'s `select_choice`, the only path that evaluates
    /// the handler-only clause.
    fn require_fully_gated(&self, method: &str) -> Result<(), WorldError> {
        if self.story.fully_gated.get(method) == Some(&false) {
            return Err(WorldError::UngatedChoice(method.to_string()));
        }
        Ok(())
    }

    /// Read the certified-decision commitment currently pinned under
    /// [`DECISION_EXT_KEY`]. A single-player (or un-bound) turn never wrote it, so it
    /// reads field-zero (`[0u8; 32]`); a collective turn via
    /// [`apply_choice_certified`](Self::apply_choice_certified) pins its winner's
    /// [`decision_commitment`]. The certified-winner check reads THIS to confirm the
    /// world committed to the decision the crowd certified.
    pub fn read_decision(&self) -> FieldElement {
        self.exec
            .cell_state(self.cell)
            .and_then(|s| s.get_field_ext(DECISION_EXT_KEY))
            .unwrap_or([0u8; 32])
    }

    /// Build the cell-write effects of a choice (its `Set`/`Modify`/`Call` effects +
    /// the passage-slot advance) — the shared body of [`apply_choice`](Self::apply_choice)
    /// and [`apply_choice_certified`](Self::apply_choice_certified).
    fn choice_effects(&self, choice: &Choice) -> Result<Vec<Effect>, WorldError> {
        let mut effects = Vec::new();
        // A local accumulator so multiple Modify effects on one var compose within
        // the single turn (each reads the running value, not stale committed state).
        // Keyed by the compiled KEY, so a spilled var accumulates identically.
        let mut local: BTreeMap<u64, u64> = BTreeMap::new();
        for e in &choice.effects {
            match e {
                spween::Effect::Set(s) => {
                    if let Some(key) = self.story.var_key(s.var.as_str()) {
                        let v = value_to_u64(&s.value);
                        local.insert(key, v);
                        effects.push(set_field(self.cell, key, field_from_u64(v)));
                    }
                }
                spween::Effect::Modify(m) => {
                    if let Some(key) = self.story.var_key(m.var.as_str()) {
                        let cur = *local.get(&key).unwrap_or(&self.read_key(key));
                        let nv = (cur as i64 + m.delta).max(0) as u64;
                        local.insert(key, nv);
                        effects.push(set_field(self.cell, key, field_from_u64(nv)));
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
        effects.push(set_field(
            self.cell,
            PASSAGE_SLOT as u64,
            field_from_u64(pidx),
        ));
        Ok(effects)
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

    /// **Drive ONE raw cap-bounded turn** — an escape hatch below the choice/passage
    /// layer, for a move whose effects are not the shape [`compile_scene`] emits (the
    /// canonical example: writing a HEAP-keyed collection, `Effect::SetField` with
    /// `index >= dregg_cell::state::STATE_SLOTS`, which the executor routes into the
    /// cell's committed `fields_map`). The turn is signed with the world's cap and
    /// admitted by the SAME real [`EmbeddedExecutor`] IFF the installed program's case
    /// for `method` passes on the post-state — so an executor-enforced `HeapField`
    /// tooth on a heap key bites here exactly as a slot tooth bites on `apply_choice`.
    /// A refused turn commits nothing (anti-ghost). Additive to the choice API.
    pub fn apply_raw(&self, method: &str, effects: Vec<Effect>) -> Result<TurnReceipt, WorldError> {
        self.commit(method, effects)
    }

    /// **The real committed `dregg_cell::Cell`** this world advances — a CLONE of the live
    /// cell inside the executor's ledger (its real owner pubkey, balance, nonce,
    /// permissions, and the full register/heap state a play mutated). `None` if the cell is
    /// not in the embedded ledger.
    ///
    /// This is the WorldCell → prover bridge: a caller snapshots the real cell BEFORE a
    /// move and AFTER it, then feeds those two `Cell`s into the rotation-witness producer
    /// (`dregg_turn::rotation_witness::produce`) to fold over the CELL the turn actually
    /// committed — its real pk/balance/heap — not a synthetic `pk[0]=7` fixture. Every game
    /// leaf's `[old8 ‖ new8]` state-binding prefix then carries THIS cell's v9 commitment,
    /// so the deployed custom state-binding weld ties the sub-proof to the real transition
    /// (the one the installed `CellProgram` teeth — e.g. multiway-tug's win implication —
    /// already gated at admission).
    pub fn cell_snapshot(&self) -> Option<Cell> {
        self.exec
            .with_ledger_mut(|ledger| ledger.get(&self.cell).cloned())
    }

    /// Read a HEAP field off the committed cell state (`index >= STATE_SLOTS`, resolved
    /// through [`dregg_cell::state::CellState::get_field_ext`]'s committed `fields_map`).
    /// `None` if the key was never written — on the heap, absent ≠ present-zero. The
    /// heap read the multi-item collection ceiling (a >16-slot inventory) leans on.
    pub fn read_heap(&self, key: u64) -> Option<u64> {
        self.exec
            .cell_state(self.cell)
            .and_then(|s| s.get_field_ext(key))
            .map(|f| field_to_u64(&f))
    }

    /// **The committed root of the WIDE PLANE** — the cell's `fields_root`, the
    /// sorted-Poseidon2 digest over every ext key in the committed `fields_map`, as
    /// its canonical 32 wide bytes. This is the value that makes a spilled var real
    /// state rather than a side note: it is folded into the cell's canonical state
    /// commitment (v9), so a turn that moves a spilled var moves this root and the
    /// receipt chain binds it — a retcon of a >16-var scene's overflow state breaks
    /// the chain exactly as a register retcon does.
    ///
    /// Constant while no ext key is written (a scene that fits the 16 registers never
    /// moves it). Every ext write rebuilds it in FULL — O(n) Poseidon over the whole
    /// map, no incremental cache (the honest cost of the wide plane; the fast fixed
    /// registers are filled first precisely because they do not pay it).
    pub fn fields_root(&self) -> [u8; 32] {
        self.exec
            .cell_state(self.cell)
            .map(|s| s.fields_root.to_bytes32())
            .unwrap_or([0u8; 32])
    }

    /// Build, sign, and submit a turn on the world-cell under `method`.
    fn commit(&self, method: &str, mut effects: Vec<Effect>) -> Result<TurnReceipt, WorldError> {
        if self.durability.is_some() && self.node_target.is_federation() {
            return Err(WorldError::Durability(
                "durable world cells currently require local routing; federation confirmation has no recoverable outbox"
                    .to_owned(),
            ));
        }
        // The genesis turn WRITES the genesis-done sentinel `0 → 1` — the LEGIT
        // one-time deploy/seed the one-shot genesis case (`Equals{1} ∧ DeltaEquals{1}`
        // on `GENESIS_DONE_EXT_KEY`) admits. Injected at this single chokepoint so every
        // genesis commit path (today only `Driver::start`) flips it; a post-deploy
        // genesis staple re-hits `old == 1`, where the two teeth are jointly
        // unsatisfiable, and is REFUSED (the universal write-hatch, closed at the root).
        //
        // Gated on the INSTALLED PROGRAM, not the method name: a hand-built story that
        // spells its own dispatch method `"genesis"` (`dregg-multiway-tug`, the dungeon
        // keep) installs no sentinel teeth and gets no injected write — byte-identical.
        if method == GENESIS_METHOD && self.genesis_sentinel {
            effects.push(set_field(
                self.cell,
                GENESIS_DONE_EXT_KEY,
                field_from_u64(1),
            ));
        }
        if let Some(durability) = &self.durability {
            durability
                .prepare(&self.durable_state(), method, &effects)
                .map_err(WorldError::Durability)?;
        }
        // A browser cannot link the verified Lean ML-DSA core, so its in-tab executor uses the
        // framework's explicit local-only Ed25519 profile and publishes only replay material. It
        // must never route that action directly to a federation; publication is a fresh native
        // re-execution/re-authorization boundary. Native worlds keep the normal hybrid signer.
        #[cfg(target_arch = "wasm32")]
        if self.node_target.is_federation() {
            return Err(WorldError::Federation(
                "browser-local turns cannot be submitted directly to a federation; replay and re-authorize them on a verified native host"
                    .to_string(),
            ));
        }
        #[cfg(target_arch = "wasm32")]
        let action = self
            .cclerk
            .make_browser_local_action(self.cell, method, effects);
        #[cfg(not(target_arch = "wasm32"))]
        let action = self.make_choice_action(method, effects);
        let receipt = match self.exec.submit_action(&self.cclerk, action) {
            Ok(receipt) => receipt,
            Err(error) => {
                if let Some(durability) = &self.durability {
                    durability
                        .abort(&self.durable_state())
                        .map_err(WorldError::Durability)?;
                }
                return Err(error.into());
            }
        };
        // FEDERATION SEAM: in `Local` mode this is a no-op; in `Federation` mode the
        // committed choice-turn is submitted to the real node + confirmed landed, and a
        // rejected / unreachable / non-landing submit fails the choice (fail-closed).
        if let Err(error) = self.node_target.route(&SubmittedTurn::new(
            self.story.scene_id.clone(),
            receipt.turn_hash,
        )) {
            return Err(WorldError::Federation(error.to_string()));
        }
        if let Some(durability) = &self.durability {
            durability
                .commit(&self.durable_state())
                .map_err(WorldError::Durability)?;
        }
        Ok(receipt)
    }

    /// Build the signed choice-action for a native world, choosing the authorization SHAPE from
    /// where the turn is going.
    ///
    /// **`Federation` ⇒ HYBRID** (`sign_action`, ed25519 + ML-DSA-65). A turn that leaves this
    /// process is judged by a node whose target cell can carry a committed PQ identity and whose
    /// `require_pq` can be armed. That is the perimeter the hybrid flip exists for, and it is
    /// untouched: nothing that can be submitted anywhere loses its post-quantum half.
    ///
    /// **`Local` ⇒ CLASSICAL** (`sign_action_classical`, ed25519 only). Read what the PQ half
    /// actually decides on this path, in the executor rather than in its name
    /// (`TurnExecutor::verify_hybrid_signature`): the world-cell is a plain `Cell::new`, so
    /// `pq_identity()` is `None`; the embedded executor enrolls no legacy PQ identity; and
    /// `require_pq` is off. Every one of those is a fact about the code, checked at
    /// `spween-dregg/src/world.rs`'s own construction path and at `dregg-cell`'s `Cell::new`. So
    /// the verifier falls to its last arm and takes the verification key from `ml_dsa_pk` —
    /// **carried in the very action it is checking**. The PQ half is verified against a key the
    /// action supplies about itself. An adversary who rewrites the action rewrites both, and the
    /// check cannot notice; it is a self-consistency test, not an authentication.
    ///
    /// Nor does the no-cheat property lean on it. `crate::verify` is three teeth — chain linkage,
    /// the receipt-hash chain, and REPLAY on a fresh identically-seeded world — and not one of
    /// them reads an authorization. A forged choice is refused by the real executor when the
    /// replay re-drives it; an altered record diverges in state. That is what makes a board run
    /// un-retconnable, and it is untouched here.
    ///
    /// What this costs to keep, measured at the FFI boundary (a C driver against the deployed
    /// `libdregg_lean.a`): **472 ms of CPU to produce the half and 222 ms to check it**, per turn,
    /// because the ML-DSA core is the Lean-verified object rather than a crate primitive. A
    /// replayed run is nine to fifteen turns. The board paid minutes of verified-core CPU for a
    /// signature that verifies a key against itself.
    ///
    /// This is deliberately NOT a knob. The shape is a function of the destination, so the weaker
    /// profile is unreachable from any world that can submit — the same discipline the
    /// browser-local path states one branch above, now stated for the one native case that has the
    /// same standing.
    ///
    /// RESIDUAL, and it is bigger than this call: on the local path the CLASSICAL half authenticates
    /// nothing either. A world's owner key is `blake3::derive_key("spween-dregg-world-owner-v1",
    /// scene_id ‖ seed)` over material anyone reading the page already has, so both halves are
    /// derivable by anyone. The executor's signature check here is a plumbing check that the action
    /// came from the world's own clerk — worth having, worth not mistaking for authorization. Giving
    /// a world an identity that is actually secret is a separate piece of work.
    #[cfg(not(target_arch = "wasm32"))]
    fn make_choice_action(&self, method: &str, effects: Vec<Effect>) -> dregg_turn::action::Action {
        if self.node_target.is_federation() {
            return self.cclerk.make_action(self.cell, method, effects);
        }
        let shared = self.cclerk.shared_cipherclerk();
        let clerk = match shared.read() {
            Ok(clerk) => clerk,
            // A poisoned clerk lock cannot be read to sign classically; fall back to the framework
            // path, which takes the same lock and will surface the poisoning itself rather than
            // letting this branch invent a quieter failure.
            Err(_) => return self.cclerk.make_action(self.cell, method, effects),
        };
        let nonce = clerk.next_turn_nonce();
        let unsigned = dregg_sdk::raw::unsigned_action_named(self.cell, method, effects);
        clerk.sign_action_classical(unsigned, self.cclerk.federation_id(), nonce)
    }
}

/// A `SetField` effect on the world-cell.
fn set_field(cell: CellId, index: u64, value: FieldElement) -> Effect {
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
        // A full-fidelity mirror of the CELL must match what the executor reads. A var
        // the compiler gave a numeric slot reads as that slot's field value, and an
        // unwritten slot is field-ZERO — so an unseeded compiled var is `Int(0)`, the
        // exact value the executor's post-state gate compares against. Defaulting to
        // `Null` instead DIVERGES the stock runtime from the executor: an ordered
        // compare on `Null` is `false` in spween (`value_cmp` returns `None`), so a gate
        // like `{ heals_used <= 0 }` on a never-initialized var reads UNAVAILABLE on the
        // replay driver while the executor's lifted tooth (`FieldLte(heals_used, 1)`)
        // admits it on the live turn — a play-vs-replay split that refuses an honest run
        // on `verify_by_replay`. A var with NO compiled slot (never touched by any
        // condition/effect) stays `Null`, as the stock in-memory handler would read it.
        //
        // This holds on BOTH planes: a SPILLED var is born at field-zero on deploy
        // (`from_compiled`), precisely so `Int(0)` stays the value its ext-plane
        // `HeapField` tooth compares against. An ext key left absent would instead
        // REFUSE every gate — the same split, from the other side.
        match self.overlay.get(name) {
            Some(v) => v.clone(),
            None if self.story.var_slots.contains_key(name) => Value::Int(0),
            None => Value::Null,
        }
    }

    fn set_var(&mut self, name: &str, value: Value) {
        // Buffer the cell write (numeric projection) for the turn. `Effect::SetField`
        // routes on the key itself (`>= STATE_SLOTS` → the committed `fields_map`), so
        // a SPILLED var is written by the identical effect — the wide plane costs the
        // write path nothing but the O(n) `fields_root` rebuild the executor does.
        if let Some(key) = self.story.var_key(name) {
            self.pending
                .push(set_field(self.cell, key, value_to_field(&value)));
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
    /// The certified-decision commitment this turn committed to, if it was a
    /// collective turn ([`Driver::advance_certified`]). `None` for a single-player
    /// turn (nothing pinned in [`DECISION_EXT_KEY`]). The certified-winner
    /// check ([`crate::verify_collective_certified`]) reads it, and the replay verifier
    /// re-pins it so a collective playthrough reproduces its committed state.
    pub decision_commitment: Option<FieldElement>,
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
    /// The certified-decision commitment to pin in the NEXT flushed turn (set by
    /// [`Driver::advance_certified`], consumed by [`Driver::flush`]). `None` on a
    /// single-player advance / the genesis turn.
    pending_decision: Option<FieldElement>,
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
            pending_decision: None,
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
        self.advance_inner(index, None)
    }

    /// **Advance the story, BOUND to a certified decision.** Like
    /// [`advance`](Self::advance), but the flushed turn ALSO pins `commitment` (a
    /// [`decision_commitment`]) into [`DECISION_EXT_KEY`] and the resulting
    /// [`StepReceipt`] records it — so a collective playthrough's committed state binds
    /// each step to the crowd's certified winner. [`crate::run_collective`] drives THIS
    /// with the commitment of the winner it resolves; the certified-winner check
    /// ([`crate::verify_collective_certified`]) reads it back.
    pub fn advance_certified(
        &mut self,
        index: usize,
        commitment: FieldElement,
    ) -> Result<StepReceipt, WorldError> {
        self.advance_inner(index, Some(commitment))
    }

    fn advance_inner(
        &mut self,
        index: usize,
        decision: Option<FieldElement>,
    ) -> Result<StepReceipt, WorldError> {
        let passage = self
            .current_passage()
            .ok_or_else(|| WorldError::Refused("scene already ended".into()))?;
        self.runtime
            .select_choice(index)
            .map_err(|e| WorldError::Refused(format!("runtime refused choice: {e}")))?;
        let method = choice_method(&passage, index);
        self.pending_decision = decision;
        let receipt = self.flush(&method)?;
        self.pending_decision = None;
        let step = StepReceipt {
            passage,
            choice_index: index,
            receipt,
            state: self.world.snapshot(),
            decision_commitment: decision,
        };
        self.steps.push(step.clone());
        Ok(step)
    }

    /// Flush the handler's buffered writes + the current passage bind (+ any pending
    /// certified-decision commitment) as one turn.
    fn flush(&mut self, method: &str) -> Result<TurnReceipt, WorldError> {
        let mut effects = self.runtime.handler_mut().take_pending();
        let pidx = match self.runtime.state() {
            RuntimeState::Running(i) => *i as u64,
            RuntimeState::Ended => PASSAGE_ENDED,
        };
        effects.push(set_field(
            self.world.cell,
            PASSAGE_SLOT as u64,
            field_from_u64(pidx),
        ));
        // Pin the certified-decision commitment (a collective turn) in the SAME turn as
        // the passage advance — the world commits to which decision authored it.
        if let Some(commitment) = self.pending_decision {
            effects.push(set_field(self.world.cell, DECISION_EXT_KEY, commitment));
        }
        self.world.commit(method, effects)
    }

    /// Consume the driver, returning the world-cell and the committed steps.
    pub fn finish(self) -> (WorldCell, Vec<StepReceipt>) {
        (self.world, self.steps)
    }
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod choice_authorization_tests {
    //! THE SIGNING SHAPE IS A FUNCTION OF THE DESTINATION.
    //!
    //! `make_choice_action` picks HYBRID (ed25519 + ML-DSA-65) for a world that routes to a
    //! federation and CLASSICAL (ed25519) for a world that stays in this process. These pin both
    //! directions, because either one silently flipping is the bug: a Local world paying ~694 ms of
    //! verified-core CPU per turn to check a key against itself, or — far worse — a Federation
    //! world shipping a turn to a node with its post-quantum half missing.

    use super::*;
    use dregg_turn::action::Authorization;

    const SCENE: &str = r#"---
id: shape
title: Shape
weight: 1
---

=== start

A room.

* [Go]
  -> END
"#;

    fn world(seed: u8) -> WorldCell {
        let scene = crate::parse(SCENE, "shape.scene").expect("scene parses");
        WorldCell::deploy(&scene, seed).expect("deploy")
    }

    /// The method name is irrelevant to the shape; any choice method exercises the same branch.
    fn shape_of(world: &WorldCell) -> Authorization {
        world.make_choice_action("probe", vec![]).authorization
    }

    #[test]
    fn a_local_world_signs_classically() {
        let w = world(3);
        assert!(w.node_target.is_local(), "the default world routes nowhere");
        match shape_of(&w) {
            Authorization::Signature(r, s) => {
                assert!(
                    r != [0u8; 32] || s != [0u8; 32],
                    "the classical half must be a real signature, not a placeholder"
                );
            }
            other => panic!(
                "a Local world must not pay for the PQ half — it is verified against a key the \
                 action carries about itself; got {other:?}"
            ),
        }
    }

    #[test]
    fn a_federated_world_still_signs_hybrid() {
        let w =
            world(4).with_node_target(NodeTarget::federation(dregg_node_target::StubNode::new()));
        assert!(w.node_target.is_federation());
        match shape_of(&w) {
            Authorization::HybridSignature {
                ed25519, ml_dsa, ..
            } => {
                assert!(ed25519 != [0u8; 64], "the classical half must be real");
                assert!(
                    !ml_dsa.is_empty(),
                    "a turn that LEAVES this process keeps its post-quantum half — that is the \
                     perimeter the hybrid flip exists for"
                );
            }
            other => panic!("a Federation world must sign hybrid; got {other:?}"),
        }
    }
}
