//! The embedded verified world — the HEART of the master interface.
//!
//! `World` wraps the REAL embedded engine — `dregg_sdk::embed::DreggEngine`
//! (`sdk/src/embed.rs`), the SDK's no-I/O executor+ledger core that the SWAP
//! makes the federation's authoritative producer — and runs REAL verified turns
//! through it (`DreggEngine::execute_turn`, i.e. `TurnExecutor::execute` over a
//! `dregg_cell::Ledger`). It is NOT a client of a remote node, and NOT a
//! parallel re-implementation of that engine: the verified semantics run IN
//! THIS PROCESS, through the SDK's own engine.
//!
//! This module is gpui-free and `cargo test`-able: it is the engine the visual
//! layer renders, decoupled from any window. Every mutation flows through
//! `commit_turn`, which:
//!   1. threads the per-agent receipt-chain head (the executor enforces it),
//!   2. runs `executor.execute(&turn, &mut ledger)`,
//!   3. on `Committed`, records the new chain head + emits a [`WorldEvent`]
//!      stream of the state transition (the "dynamics"), and
//!   4. returns the real [`TurnReceipt`] (kept in an append-only provenance log).
//!
//! The four dregg-surpasses-Smalltalk axes are all live here:
//!   * ocap — turns are gated by the cells' `Permissions`/capabilities; an
//!     over-grant or unauthorized effect is REJECTED by the real executor.
//!   * verification — each commit carries the executor's conservation / no-
//!     amplification guarantees (the same code the verified producer runs).
//!   * provenance — every commit appends a `TurnReceipt` to `receipts`, a
//!     navigable causal chain (the local blocklace).
//!   * distribution — `state_root()` is a cryptographic commitment to the whole
//!     image; the federation view renders this image as one of many sovereign
//!     ones.

use std::collections::HashMap;

use dregg_cell::{
    lifecycle::{DeathCertificate, DeathReason},
    AuthRequired, Cell, CellId, Ledger, Permissions,
};
use dregg_sdk::embed::{DreggEngine, EmbedError, EngineConfig};
use dregg_turn::{
    action::{Action, Authorization, DelegationMode, Effect, Event},
    forest::CallForest,
    turn::{Turn, TurnReceipt},
    ComputronCosts, TurnExecutor,
};

use crate::dynamics::{Dynamics, WorldEvent};
use crate::replay::History;

/// The outcome of attempting to commit a turn against the embedded executor.
pub enum CommitOutcome {
    /// The turn committed. The real receipt + the dynamics events it produced.
    Committed {
        receipt: TurnReceipt,
        events: Vec<WorldEvent>,
    },
    /// The real executor REJECTED the turn (e.g. unauthorized effect,
    /// non-conservation, broken receipt chain). This is a FEATURE: it is the
    /// ocap/verification guarantees firing.
    Rejected { reason: String, at_action: Vec<usize> },
}

impl CommitOutcome {
    pub fn is_committed(&self) -> bool {
        matches!(self, CommitOutcome::Committed { .. })
    }
}

/// A live local dregg world: the REAL embedded engine
/// ([`dregg_sdk::embed::DreggEngine`] — the executor+ledger core the SWAP makes
/// the federation's authoritative producer) plus the provenance log, the
/// dynamics stream the views render, and the canonical replayable [`History`].
pub struct World {
    /// The REAL embedded engine: `dregg_sdk::embed::DreggEngine` wraps the same
    /// `TurnExecutor` over `dregg_cell::Ledger` pair this world runs every
    /// transition through — not a parallel re-implementation, the SDK's engine.
    engine: DreggEngine,
    /// The canonical, replayable history (genesis installs + committed turns,
    /// each carrying the post-state `Ledger::root` tooth). Maintained in
    /// lock-step with `engine` so time-travel ([`crate::replay`]) drives off the
    /// live world's REAL turn history, not a separately-recorded one.
    ///
    /// The recovery model ([`crate::replay`], `CrashRecovery.lean`) is a
    /// deterministic re-execution tape: it carries its own recording ledger +
    /// executor (`record_ledger`/`record_exec`), driven in lock-step with the
    /// authoritative `engine` under the SAME pinned config, so every recorded
    /// root tooth equals the live engine's post-state root — and replay can
    /// reconstruct + verify any past step.
    history: History,
    /// The history recorder's ledger (parallel to the engine's, kept in
    /// lock-step). NOT a second source of truth — the engine is authoritative;
    /// this is the replay tape's substrate so the recorded roots are real.
    record_ledger: Ledger,
    /// The history recorder's executor (pinned to the same timestamp/costs as
    /// the engine's), used only to re-derive the recorded receipts/roots.
    record_exec: TurnExecutor,
    /// Append-only provenance: every committed receipt, in commit order. This
    /// IS the local blocklace / receipt chain the browser navigates.
    receipts: Vec<TurnReceipt>,
    /// The dynamics: an observation stream of state transitions, decoupled from
    /// the visual layer (see [`crate::dynamics`]).
    dynamics: Dynamics,
    /// Monotonic "height" — one per committed turn (the local chain index).
    height: u64,
    /// The fixed wall-clock the engine + history share, so a recorded turn
    /// re-derives bit-identically on replay (the debugger's re-execution and the
    /// replayer's reconstruction must use the SAME timestamp the live engine did).
    timestamp: i64,
    /// The fee stamped onto every turn built by [`World::turn`] /
    /// [`World::forest_turn`]. `0` for [`World::new`] (free metering — the demo
    /// path). For a METERED world ([`World::with_costs`]) the executor rejects a
    /// turn whose `computrons_used` exceeds its `fee`, so a metered world stamps a
    /// fee that covers the per-turn cost (the agent pays it — conservation-real).
    /// This is what lets the SWARM BUDGET METER (N1) observe non-zero metered spend
    /// on committed turns without every turn being rejected for under-fee.
    turn_fee: u64,
}

impl Default for World {
    fn default() -> Self {
        Self::new()
    }
}

impl World {
    /// A fresh, empty world with the real embedded engine (free metering, so the
    /// demo world isn't gated on a fee economy).
    pub fn new() -> Self {
        Self::with_costs(ComputronCosts::zero())
    }

    /// A fresh, empty world with the real embedded engine metering at `costs`.
    ///
    /// [`World::new`] pins `ComputronCosts::zero()` so the demo flows aren't gated
    /// on a fee economy. The SWARM BUDGET METER (N1) needs a world where committed
    /// turns actually accrue metered computrons, so a member's `spent` GROWS and a
    /// ceiling can bite — that is what this constructor is for. The metering is the
    /// REAL executor's (`ComputronCosts` is the production cost model the federation
    /// producer configures), just non-zero; the swarm budget then sums the genuine
    /// `receipt.computrons_used`, never a re-derived estimate.
    pub fn with_costs(costs: ComputronCosts) -> Self {
        // A real wall-clock so temporal preconditions behave; harmless for the
        // demo flows that don't use them. PINNED for the world's life so the
        // engine and the replay history stay bit-deterministic together.
        Self::with_costs_and_timestamp(costs, now_unix())
    }

    /// A fresh, empty world metering at `costs` with the wall-clock PINNED to
    /// `timestamp` (rather than `now_unix()`).
    ///
    /// The timestamp is folded into every `TurnReceipt` (`receipt_hash` binds it),
    /// so two worlds that must produce BYTE-IDENTICAL receipts for the same turns
    /// — e.g. the direct executor and the semihosted executor-PD
    /// ([`SemihostCockpit`]) in a determinism/equivalence test — must share it.
    /// This is the "houyhnhnm clock as a recorded, replayable input" the semihost
    /// makes natural (`docs/DREGG-DESKTOP-OS.md §3`): construction-time determinism,
    /// not the host wall-clock. [`World::with_costs`] pins `now_unix()`; this lets
    /// a caller pin any instant.
    pub fn with_costs_and_timestamp(costs: ComputronCosts, timestamp: i64) -> Self {
        let config = EngineConfig {
            costs: costs.clone(),
            federation_id: [0u8; 32],
            block_height: 0,
            timestamp,
            max_proof_age_secs: 0,
        };
        let history = History::with_costs(timestamp, costs.clone());
        let record_exec = history.fresh_executor();
        World {
            engine: DreggEngine::new(config),
            history,
            record_ledger: Ledger::new(),
            record_exec,
            receipts: Vec::new(),
            dynamics: Dynamics::new(),
            height: 0,
            timestamp,
            turn_fee: 0,
        }
    }

    /// The wall-clock this world pinned at construction (folded into every
    /// receipt). Exposed so a second world can be pinned to the SAME instant for a
    /// byte-for-byte equivalence check (e.g. direct vs. semihost executor-PD).
    pub fn timestamp(&self) -> i64 {
        self.timestamp
    }

    /// Set the fee stamped onto every turn built by [`World::turn`] /
    /// [`World::forest_turn`]. In a METERED world ([`World::with_costs`]) this must
    /// cover the per-turn `computrons_used` or the executor rejects the turn for
    /// under-fee; the agent pays it from its balance (conservation-real). Returns
    /// `self` for builder-style construction. The default is `0` (free metering).
    pub fn with_turn_fee(mut self, fee: u64) -> Self {
        self.turn_fee = fee;
        self
    }

    // --- read surface (what the reflective object model + views consume) ----

    pub fn ledger(&self) -> &Ledger {
        self.engine.ledger()
    }

    /// The canonical, replayable history of this world (genesis installs +
    /// committed turns, each with its post-state `Ledger::root` tooth). The
    /// time-travel panel ([`crate::replay`]) drives off THIS — the live world's
    /// real turn history — rather than a separately re-recorded one.
    pub fn recorded_turns(&self) -> &History {
        &self.history
    }

    /// A fresh `TurnExecutor` configured IDENTICALLY to this world's live engine
    /// (same zero-cost metering, same pinned wall-clock, same federation id, and
    /// `agent`'s current receipt-chain head). The turn debugger
    /// ([`crate::debug`]) re-executes prefixes against this so its replay cannot
    /// drift from the live executor's configuration.
    ///
    /// (`TurnExecutor` is not `Clone` — it carries `Mutex`/`RefCell` side-tables
    /// and a `Box<dyn ProofVerifier>` — so this hands back a fresh executor
    /// matching the live config, sourced from `World` so the config lives in ONE
    /// place and the debugger can't diverge from it.)
    pub fn debug_executor(&self, agent: &CellId) -> TurnExecutor {
        let mut exec = TurnExecutor::new(ComputronCosts::zero());
        exec.set_timestamp(self.timestamp);
        exec.set_block_height(self.engine.executor().block_height);
        exec.set_local_federation_id(self.engine.executor().local_federation_id);
        if let Some(head) = self.chain_head(agent) {
            exec.set_last_receipt_hash(*agent, head);
        }
        exec
    }

    pub fn receipts(&self) -> &[TurnReceipt] {
        &self.receipts
    }

    pub fn dynamics(&self) -> &Dynamics {
        &self.dynamics
    }

    /// Emit a [`WorldEvent`] onto the dynamics stream directly (an observation a
    /// view-layer model records about a transition the executor already made).
    ///
    /// This does NOT bypass the commit path — it is for transitions whose AUTHORITY
    /// the executor decided (a committed turn) but whose VIEW-LAYER meaning a model
    /// adds (e.g. the verified compositor's `SurfaceDamaged`, emitted only after a
    /// `present()`'s `SetField` turn COMMITTED through `commit_turn`). The state
    /// change itself always went through the real executor; this records the
    /// observation for the feed.
    pub fn emit_dynamics(&mut self, event: WorldEvent) {
        self.dynamics.emit(event);
    }

    pub fn height(&self) -> u64 {
        self.height
    }

    /// The fee stamped onto every turn this world builds (`0` for the free-
    /// metering demo world; non-zero for a [`World::with_costs`] world). This is
    /// the turn's DECLARED computron budget — the executor rejects a turn whose
    /// metered `computrons_used` exceeds it — so it is a conservative upper bound
    /// on a dispatch's cost, usable as the fail-closed pre-check amount for a
    /// shared budget gate (the SDK's `set_budget_gate` gates on exactly this
    /// declared fee, before the turn runs).
    pub fn turn_fee(&self) -> u64 {
        self.turn_fee
    }

    pub fn cell_count(&self) -> usize {
        self.engine.ledger().len()
    }

    /// A cryptographic commitment to the WHOLE image — the distribution axis.
    /// (BLAKE3 over the canonical postcard of every cell, sorted by id, folded
    /// with the height + receipt-chain head so the root advances with history.)
    pub fn state_root(&self) -> [u8; 32] {
        let mut cells: Vec<(&CellId, &Cell)> = self.engine.ledger().iter().collect();
        cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"starbridge-v2-image-root-v1");
        hasher.update(&self.height.to_le_bytes());
        for (id, cell) in cells {
            hasher.update(id.as_bytes());
            if let Ok(bytes) = postcard::to_stdvec(cell) {
                hasher.update(&(bytes.len() as u64).to_le_bytes());
                hasher.update(&bytes);
            }
        }
        if let Some(head) = self.receipts.last() {
            hasher.update(&head.receipt_hash());
        }
        *hasher.finalize().as_bytes()
    }

    /// The per-agent receipt-chain head the executor enforces — exposed so
    /// callers (and the composer) can construct chained turns.
    pub fn chain_head(&self, agent: &CellId) -> Option<[u8; 32]> {
        self.engine.executor().get_last_receipt_hash(agent)
    }

    // --- genesis / cell creation (out-of-band, like a node's genesis block) -

    /// Install a cell directly into the ledger (genesis path — bypasses the
    /// executor, the way a node seeds its genesis cells). Emits a `CellBorn`
    /// dynamics event so the visual layer sees it appear. Returns its id.
    pub fn genesis_cell(&mut self, seed: u8, balance: i64) -> CellId {
        let cell = make_open_cell(seed, balance);
        self.install_genesis(cell, balance)
    }

    /// The single genesis install path: inserts `cell` into the live engine's
    /// ledger, records it in the replayable [`History`] (so the post-state root
    /// tooth is captured), and emits the `CellBorn` dynamics. Returns the id.
    fn install_genesis(&mut self, cell: Cell, balance: i64) -> CellId {
        let id = cell.id();
        // Install into the AUTHORITATIVE engine ledger.
        self.engine
            .ledger_mut()
            .insert_cell(cell.clone())
            .expect("genesis insert is into a fresh slot");
        // Mirror into the replay tape (its own ledger), capturing the root
        // tooth. Same cell, same order → the recorded root equals the engine's.
        self.history.record_genesis(&mut self.record_ledger, cell);
        self.dynamics.emit(WorldEvent::CellBorn {
            cell: id,
            balance,
            genesis: true,
        });
        id
    }

    /// Install the genesis cell for an identity at its REAL derived id.
    ///
    /// `public_key` + `token_id` are the exact pair `Cell::with_balance` (and
    /// `AgentCipherclerk::cell_id`) derive the id over, so the installed cell's
    /// id equals the identity's `cell_id`. The cell carries `open_permissions`
    /// (single-custody operator authority). Returns the derived [`CellId`].
    ///
    /// This is the real home for "embody an identity": the cipherclerk panel
    /// hands `World` the identity's `(public_key, token_id, balance)` and `World`
    /// builds + installs the genesis cell (rather than the panel building the
    /// `Cell` itself).
    pub fn embody(&mut self, public_key: [u8; 32], token_id: [u8; 32], balance: i64) -> CellId {
        let mut cell = Cell::with_balance(public_key, token_id, balance);
        cell.permissions = open_permissions();
        self.install_genesis(cell, balance)
    }

    /// Install a genesis cell that already HOLDS a capability reaching
    /// `cap_target` (so a later `GrantCapability` from it is legitimate — the
    /// executor's no-amplification rule means you can only grant what you hold).
    /// Returns `(id, slot)` of the seeded capability.
    pub fn genesis_cell_with_cap(
        &mut self,
        seed: u8,
        balance: i64,
        cap_target: CellId,
    ) -> (CellId, u32) {
        let mut cell = make_open_cell(seed, balance);
        let slot = cell
            .capabilities
            .grant(cap_target, AuthRequired::None)
            .expect("fresh c-list has a free slot");
        let id = self.install_genesis(cell, balance);
        (id, slot)
    }

    /// Install a fully-specified cell (genesis path). For richer fixtures (a
    /// cell with a program, an issuer well carrying −supply, …).
    pub fn genesis_install(&mut self, cell: Cell) -> CellId {
        let balance = cell.state.balance();
        self.install_genesis(cell, balance)
    }

    /// Re-program a cell's [`CellProgram`] in place (a GENESIS-PATH update, like
    /// seeding the cell — for the trusted window manager that OWNS a cell and
    /// installs its caveats). Used by the verified compositor
    /// ([`crate::scene::VerifiedScene`]) to bake the scene-authority admit-table
    /// onto a compositor cell before a `present()` so the EXECUTOR'S program-check
    /// gates the frame advance (the Lean `compositorSpec.caveats` closed over the
    /// live scene). Mirrored into the replay-recorder's ledger so the recorded
    /// post-state roots stay in lock-step with the live engine (a later present's
    /// `SetField` re-executes against the SAME program on both ledgers).
    ///
    /// This installs AUTHORITY (a slot caveat), it does not move value or commit a
    /// turn; it is the trusted root's prerogative over a cell it owns, exactly as
    /// `genesis_install` seeds a cell's initial program. Returns `true` if the
    /// cell existed (in the live engine ledger) and was re-programmed.
    pub fn set_cell_program(&mut self, cell: &CellId, program: dregg_cell::CellProgram) -> bool {
        let existed = if let Some(c) = self.engine.ledger_mut().get_mut(cell) {
            c.program = program.clone();
            true
        } else {
            false
        };
        // Keep the replay tape's ledger in lock-step so its recorded roots match
        // the live engine's (the compositor cell carries the SAME program on both).
        if let Some(c) = self.record_ledger.get_mut(cell) {
            c.program = program;
        }
        existed
    }

    /// Grant `holder` a capability reaching `target` via the GENESIS PATH (the
    /// trusted window manager installing an owner-grant — the way `surface.rs`
    /// documents the shell handing the surface cap back when a surface opens). The
    /// installed cap is unrestricted (`AuthRequired::None`); the executor's
    /// no-amplification rule still gates any later *delegation* of it. Mirrored
    /// into the replay-recorder's ledger so the recorded roots stay in lock-step.
    /// Returns the granted slot (in the live engine ledger), or `None` if the
    /// holder cell does not exist or its c-list is full.
    ///
    /// This is the authority leg of a `present()`: the presenter holds a surface
    /// cap on the compositor cell (the Lean `compositorState`'s `[.endpoint cell …]`),
    /// so the executor's cross-cell authority check passes and the SCENE CAVEAT —
    /// not the cap — is the load-bearing admission gate (faithful to the Lean §10:
    /// even an authorized-to-present cell cannot overpaint/spoof/steal-focus).
    pub fn genesis_grant_cap(&mut self, holder: &CellId, target: CellId) -> Option<u32> {
        let slot = self
            .engine
            .ledger_mut()
            .get_mut(holder)?
            .capabilities
            .grant(target, AuthRequired::None);
        // Mirror into the replay tape's ledger (same holder, same target) so the
        // recorded roots match the live engine's after a present's SetField.
        if let Some(c) = self.record_ledger.get_mut(holder) {
            let _ = c.capabilities.grant(target, AuthRequired::None);
        }
        slot
    }

    /// Open `cell`'s [`Permissions`] to the single-custody operator set
    /// (`open_permissions`, gating nothing) via the GENESIS PATH — the minter/owner
    /// endowing a cell it owns, exactly as [`genesis_grant_cap`] installs an
    /// owner-grant or [`set_cell_program`] seeds a program. Used by the headline demo
    /// ([`crate::demo`]) after a factory-birth: a factory-born child carries the
    /// factory's default permissions (which require a signature to send FROM it), so
    /// the minter opens its freshly-minted budget cell's permissions the way a node
    /// seeds a genesis cell's authority. Mirrored into the replay tape's ledger so the
    /// recorded roots stay in lock-step. Returns `true` if the cell existed.
    ///
    /// This installs AUTHORITY (a permissions set) on a cell the caller owns; it does
    /// not move value or commit a turn — the trusted root's prerogative over its own
    /// cell, NOT a bypass of the executor (a later spend FROM the cell still runs
    /// through the real executor; this only sets what that executor gates against).
    pub fn genesis_open_permissions(&mut self, cell: &CellId) -> bool {
        let existed = if let Some(c) = self.engine.ledger_mut().get_mut(cell) {
            c.permissions = open_permissions();
            true
        } else {
            false
        };
        if let Some(c) = self.record_ledger.get_mut(cell) {
            c.permissions = open_permissions();
        }
        existed
    }

    /// Deploy a [`FactoryDescriptor`] into the embedded executor's factory
    /// registry (the out-of-band genesis path — a node registers its factories
    /// the way it seeds genesis cells). Returns the factory's content-addressed
    /// VK, against which a later [`create_cell_from_factory`] effect is
    /// validated by the real executor. The descriptor is also mirrored into the
    /// replay tape's executor so factory-births re-derive on replay.
    pub fn deploy_factory(&mut self, descriptor: dregg_cell::FactoryDescriptor) -> [u8; 32] {
        let vk = self.engine.executor_mut().deploy_factory(descriptor.clone());
        // Keep the replay recorder's executor in lock-step so a factory-birth
        // committed below re-derives identically on replay.
        let _ = self.record_exec.deploy_factory(descriptor);
        vk
    }

    // --- THE COMMIT PATH (every real state transition goes through here) -----

    /// Commit a turn against the embedded verified executor.
    ///
    /// Threads the receipt-chain head for `turn.agent` automatically (so callers
    /// don't have to), runs the REAL executor, and — on commit — records the new
    /// head, advances the height, appends the receipt to the provenance log, and
    /// derives + emits the dynamics events for the transition.
    pub fn commit_turn(&mut self, mut turn: Turn) -> CommitOutcome {
        // Thread the chain head the engine's executor will check.
        turn.previous_receipt_hash = self.engine.executor().get_last_receipt_hash(&turn.agent);

        // Snapshot the pre-state balances of touched cells so we can describe
        // the flow in the dynamics stream.
        let touched = touched_cells(&turn);
        let pre: HashMap<CellId, i64> = touched
            .iter()
            .filter_map(|id| self.engine.ledger().get(id).map(|c| (*id, c.state.balance())))
            .collect();

        // Run the turn through the REAL embedded engine (the SDK's DreggEngine,
        // which owns the executor+ledger borrow internally).
        match self.engine.execute_turn(&turn) {
            Ok(receipt) => {
                // Advance the engine's per-agent chain head (DreggEngine's
                // execute_turn does not rebind it; do it here as the live path).
                self.engine
                    .executor()
                    .set_last_receipt_hash(receipt.agent, receipt.receipt_hash());
                // Mirror the commit onto the replay tape (re-executes against the
                // recorder's own ledger/executor, capturing the post-state root).
                self.history.record_commit(&self.record_exec, &mut self.record_ledger, turn.clone());
                self.height += 1;

                let mut events = Vec::new();
                events.push(WorldEvent::TurnCommitted {
                    height: self.height,
                    agent: receipt.agent,
                    receipt_hash: receipt.receipt_hash(),
                    turn_hash: receipt.turn_hash,
                    action_count: receipt.action_count,
                    computrons: receipt.computrons_used,
                });
                // Derive per-effect dynamics from the post-state delta.
                for id in &touched {
                    if let Some(cell) = self.engine.ledger().get(id) {
                        let before = pre.get(id).copied().unwrap_or(0);
                        let after = cell.state.balance();
                        if before != after {
                            events.push(WorldEvent::BalanceFlowed {
                                cell: *id,
                                before,
                                after,
                            });
                        }
                    }
                }
                // Surface the effect kinds (caps granted, cells born, fields set).
                for tree in &turn.call_forest.roots {
                    collect_effect_events(&tree.action, &mut events);
                    for child in &tree.children {
                        collect_effect_events(&child.action, &mut events);
                    }
                }

                for ev in &events {
                    self.dynamics.emit(ev.clone());
                }
                self.receipts.push(receipt.clone());
                CommitOutcome::Committed { receipt, events }
            }
            Err(EmbedError::TurnRejected { reason, at_action }) => {
                self.dynamics.emit(WorldEvent::TurnRejected {
                    agent: turn.agent,
                    reason: reason.clone(),
                });
                CommitOutcome::Rejected { reason, at_action }
            }
            Err(other) => {
                let reason = other.to_string();
                self.dynamics.emit(WorldEvent::TurnRejected {
                    agent: turn.agent,
                    reason: reason.clone(),
                });
                CommitOutcome::Rejected { reason, at_action: vec![] }
            }
        }
    }

    // --- ergonomic turn constructors (the typed verbs, embedded-local) -------

    /// Build a single-action, `Unchecked`-authorized turn carrying `effects`.
    /// (`Unchecked` is honest here: the embedded world is single-custody — the
    /// OPERATOR is the authority. The cells' `Permissions` still gate every
    /// effect; an effect a cell forbids is rejected regardless of auth.)
    pub fn turn(&self, agent: CellId, effects: Vec<Effect>) -> Turn {
        let mut t = bare_turn(agent, self.next_nonce(&agent), effects);
        t.fee = self.turn_fee;
        t
    }

    /// Build a MULTI-ACTION turn: one `Action` per `(target, effects)` entry,
    /// all gathered into the agent's call-forest as sibling roots and submitted
    /// as ONE atomic verified turn (the executor commits the whole forest or
    /// rejects it — there is no partial commit). This is the surface the
    /// cockpit's multi-action composer drives: several effects, several target
    /// cells, one turn, one receipt.
    ///
    /// Each action carries `Authorization::Unchecked` (honest for the single-
    /// custody embedded world — the operator is the authority; the cells'
    /// `Permissions` + the executor's whole-turn guarantees still gate every
    /// effect). Lifecycle verbs (seal/unseal/destroy/burn) require the action's
    /// `target` to equal the effect's target, so each composed action acts on
    /// its own cell.
    pub fn forest_turn(&self, agent: CellId, actions: Vec<(CellId, Vec<Effect>)>) -> Turn {
        let nonce = self.next_nonce(&agent);
        let mut forest = CallForest::new();
        for (target, effects) in actions {
            forest.add_root(bare_action(target, effects));
        }
        let mut t = wrap_turn(agent, nonce, forest);
        t.fee = self.turn_fee;
        t
    }

    fn next_nonce(&self, agent: &CellId) -> u64 {
        self.engine.ledger().get(agent).map(|c| c.state.nonce()).unwrap_or(0)
    }
}

/// Best-effort unix timestamp (seconds).
fn now_unix() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

fn push_unique(ids: &mut Vec<CellId>, id: CellId) {
    if !ids.contains(&id) {
        ids.push(id);
    }
}

/// All cell ids a turn's effects touch (for pre/post balance diffing).
fn touched_cells(turn: &Turn) -> Vec<CellId> {
    let mut ids = Vec::new();
    for tree in &turn.call_forest.roots {
        push_unique(&mut ids, tree.action.target);
        collect_touched(&tree.action, &mut ids);
        for child in &tree.children {
            push_unique(&mut ids, child.action.target);
            collect_touched(&child.action, &mut ids);
        }
    }
    ids
}

fn collect_touched(action: &Action, ids: &mut Vec<CellId>) {
    fn push(id: CellId, ids: &mut Vec<CellId>) {
        push_unique(ids, id);
    }
    for e in &action.effects {
        match e {
            Effect::Transfer { from, to, .. } => {
                push(*from, ids);
                push(*to, ids);
            }
            Effect::SetField { cell, .. }
            | Effect::IncrementNonce { cell }
            | Effect::EmitEvent { cell, .. }
            | Effect::RevokeCapability { cell, .. } => push(*cell, ids),
            Effect::GrantCapability { from, to, .. } => {
                push(*from, ids);
                push(*to, ids);
            }
            Effect::Burn { target, .. }
            | Effect::CellSeal { target, .. }
            | Effect::CellUnseal { target }
            | Effect::CellDestroy { target, .. }
            | Effect::MakeSovereign { cell: target } => push(*target, ids),
            _ => {}
        }
    }
}

/// Translate an action's effects into human-meaningful dynamics events.
fn collect_effect_events(action: &Action, out: &mut Vec<WorldEvent>) {
    for e in &action.effects {
        match e {
            Effect::GrantCapability { from, to, .. } => {
                out.push(WorldEvent::CapabilityGranted {
                    from: *from,
                    to: *to,
                });
            }
            Effect::RevokeCapability { cell, slot } => {
                out.push(WorldEvent::CapabilityRevoked { cell: *cell, slot: *slot });
            }
            Effect::CreateCell { balance, .. } => {
                out.push(WorldEvent::CellBorn {
                    // The id isn't known here without re-deriving; views render
                    // the freshly-appeared ledger cell. Use ZERO as a sentinel
                    // (the BalanceFlowed/ledger refresh carries the real one).
                    cell: CellId::ZERO,
                    balance: *balance as i64,
                    genesis: false,
                });
            }
            Effect::SetField { cell, index, .. } => {
                out.push(WorldEvent::FieldSet {
                    cell: *cell,
                    index: *index,
                });
            }
            Effect::CellSeal { target, .. } => {
                out.push(WorldEvent::CellSealed { cell: *target });
            }
            Effect::CellUnseal { target } => {
                out.push(WorldEvent::CellUnsealed { cell: *target });
            }
            Effect::CellDestroy { target, .. } => {
                out.push(WorldEvent::CellDestroyed { cell: *target });
            }
            Effect::Burn { target, amount, .. } => {
                out.push(WorldEvent::Burned { cell: *target, amount: *amount });
            }
            Effect::CreateCellFromFactory { .. } => {
                out.push(WorldEvent::CellBorn {
                    cell: CellId::ZERO,
                    balance: 0,
                    genesis: false,
                });
            }
            // THE NOTIFY EDGE: an EmitEvent is the sender's committed receipt
            // that the swarm coordinator reads to wake the recipient's next turn.
            // The recipient drains it in its OWN future turn (async, not joint).
            Effect::EmitEvent { cell, event, .. } => {
                // The topic hash is the event's 32-byte symbol (Blake3 of the
                // topic string, as hashed by `emit_event()`).
                let topic_hash = event.topic;
                let data_len = event.data.len() * 32; // each FieldElement is 32 B
                // `action.target` is the cell acting (the sender); `cell` is the
                // cell the event is emitted ON (the notify recipient). When the
                // sender emits to itself, sender == cell (a self-notification,
                // valid and useful for checkpointing). The swarm coordinator uses
                // this distinction to route the wake signal to `cell`'s inbox.
                out.push(WorldEvent::EventEmitted {
                    sender: action.target,
                    cell: *cell,
                    topic_hash,
                    data_len,
                });
            }
            _ => {}
        }
    }
}

// ===========================================================================
// Construction helpers — the genesis fixtures + the bare turn shape.
//
// These mirror `turn/tests/integration_lifecycle.rs` (the canonical happy-path
// template): an `open_permissions` cell + an `Authorization::Unchecked` action.
// ===========================================================================

/// A permissions set that gates nothing — for the operator's own cells in the
/// single-custody embedded world. (Real federation cells carry real gates; this
/// is the local image's owner authority, made explicit.)
pub fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

/// A deterministic open cell from a one-byte seed (test/genesis fixture).
pub fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// A bare `Unchecked` action on `target` carrying `effects` (the executor-test
/// template shape). The building block both `bare_turn` and `forest_turn` use.
pub fn bare_action(target: CellId, effects: Vec<Effect>) -> Action {
    Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    }
}

/// The bare single-action turn shape (matches the executor test template).
pub fn bare_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(bare_action(agent, effects));
    wrap_turn(agent, nonce, forest)
}

/// Wrap a built call-forest into the bare `Turn` shape (no proofs/witnesses —
/// the single-custody embedded world's operator path).
fn wrap_turn(agent: CellId, nonce: u64, forest: CallForest) -> Turn {
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// Convenience: a transfer effect.
pub fn transfer(from: CellId, to: CellId, amount: u64) -> Effect {
    Effect::Transfer { from, to, amount }
}

/// Convenience: grant `to` a capability reaching `cap_target` (the ocap edge).
/// Installs an unrestricted (`AuthRequired::None`) cap at `slot` — the cockpit's
/// "grant" verb. The real executor enforces no-amplification on delegation.
pub fn grant_capability(from: CellId, to: CellId, cap_target: CellId, slot: u32) -> Effect {
    Effect::GrantCapability {
        from,
        to,
        cap: dregg_cell::CapabilityRef {
            target: cap_target,
            slot,
            permissions: AuthRequired::None,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    }
}

/// Convenience: revoke the capability at `slot` on `cell`.
pub fn revoke_capability(cell: CellId, slot: u32) -> Effect {
    Effect::RevokeCapability { cell, slot }
}

/// Convenience: create a new cell (the `createCell` verb).
///
/// Created cells are born with ZERO balance: the verified executor enforces
/// value conservation (`CreateCellNonZeroBalance`), so a cell cannot be birthed
/// holding value — value only ever *moves*. Fund it afterward with a transfer.
pub fn create_cell(seed: u8) -> Effect {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    Effect::CreateCell {
        public_key: pk,
        token_id: [0u8; 32],
        balance: 0,
    }
}

/// Convenience: write `value` into state slot `index` of `cell`.
pub fn set_field(cell: CellId, index: usize, value: dregg_cell::FieldElement) -> Effect {
    Effect::SetField { cell, index, value }
}

/// Convenience: an emit-event effect with a topic symbol (the topic string is
/// BLAKE3'd to the 32-byte symbol the protocol uses).
pub fn emit_event(cell: CellId, topic: &str, data: Vec<dregg_cell::FieldElement>) -> Effect {
    let sym = *blake3::hash(topic.as_bytes()).as_bytes();
    Effect::EmitEvent {
        cell,
        event: Event::new(sym, data),
    }
}

// --- the lifecycle verbs (seal · unseal · destroy · burn) ------------------
//
// The verified executor enforces that each lifecycle effect's `target` MATCHES
// the action target (so `agent` must BE the cell being sealed/destroyed/burned;
// the cockpit composes these as self-acting turns). The `make_*_turn`
// constructors below bake that in so callers can't compose an ill-targeted one.

/// Convenience: seal `target` with a 32-byte commitment to `reason` (the
/// cleartext lives off-chain). After sealing, the cell rejects new effects
/// until [`unseal`] — the executor enforces this lifecycle gate.
pub fn seal(target: CellId, reason: &str) -> Effect {
    Effect::CellSeal {
        target,
        reason: *blake3::hash(reason.as_bytes()).as_bytes(),
    }
}

/// Convenience: reverse a seal — transition `target` from `Sealed` back to
/// `Live`. Rejected by the executor if the cell is not currently sealed.
pub fn unseal(target: CellId) -> Effect {
    Effect::CellUnseal { target }
}

/// Convenience: permanently retire `target`, binding a [`DeathCertificate`]
/// whose `cell_id` matches (the only field the executor checks against the
/// cell). Once destroyed the cell `is_terminal()` — every later effect is
/// rejected. `reason` distinguishes a voluntary retirement from a forced one.
pub fn destroy(target: CellId, height: u64, reason: DeathReason) -> Effect {
    Effect::CellDestroy {
        target,
        certificate: DeathCertificate {
            cell_id: target,
            last_receipt_hash: [0u8; 32],
            final_state_commitment: [0u8; 32],
            destroyed_at_height: height,
            reason,
        },
    }
}

/// Convenience: provably reduce `target`'s balance by `amount` (slot 0 = the
/// canonical balance slot — the only burnable slot in Silver-Vision). Unlike a
/// transfer there is no credited destination; with a registered issuer well the
/// executor routes the burn as a conserving move toward the well.
pub fn burn(target: CellId, amount: u64) -> Effect {
    Effect::Burn {
        target,
        slot: 0,
        amount,
    }
}

/// Convenience: birth a child cell from a deployed factory (the
/// `CreateCellFromFactory` verb). The executor validates the creation `params`
/// against the named factory's descriptor before installing the child.
pub fn create_cell_from_factory(
    factory_vk: [u8; 32],
    owner_pubkey: [u8; 32],
    token_id: [u8; 32],
    params: dregg_cell::factory::FactoryCreationParams,
) -> Effect {
    Effect::CreateCellFromFactory {
        factory_vk,
        owner_pubkey,
        token_id,
        params,
    }
}

/// Build a populated demo world: three cells (a treasury, a service, a user),
/// an issuer well carrying −supply, and a handful of committed turns so the
/// cockpit boots into a LIVE image with real provenance — not a mock. Returns
/// the world and the (treasury, service, user) ids for the views to anchor on.
///
/// This runs the demo's five seed TURNS eagerly (the `--headless` self-check +
/// every `cargo test` path want the fully-populated image up front). The gpui
/// cockpit instead opens the window on the INSTANT genesis ([`demo_genesis`])
/// and drives [`DemoSeed::next`] AFTER first paint, so the window is alive
/// immediately and the cells fill in live — same content, just not on the paint
/// path. Both routes run the SAME real executor turns; nothing is faked.
pub fn demo_world() -> (World, [CellId; 3]) {
    let (mut w, anchors, mut seed) = demo_genesis();
    // Run every seed turn now (the eager, headless/test path).
    while seed.next(&mut w).is_some() {}
    (w, anchors)
}

/// The INSTANT half of [`demo_world`]: install the three anchor cells (treasury,
/// service, user) and the issuer well via the GENESIS PATH (which bypasses the
/// executor — no turns run), and return a [`DemoSeed`] that will commit the five
/// demo turns on demand. This is sub-millisecond: no `commit_turn` runs here, so
/// the cockpit can open its window on this image immediately and seed the turns
/// afterward (cells appear live as each commits). Returns `(world, anchors, seed)`.
pub fn demo_genesis() -> (World, [CellId; 3], DemoSeed) {
    let mut w = World::new();
    let treasury = w.genesis_cell(0x11, 1_000_000);
    let user = w.genesis_cell(0x33, 5_000);
    // The service is born already holding a capability reaching the user (so it
    // can legitimately re-grant it later — the no-amplification rule).
    let (service, user_cap_slot) = w.genesis_cell_with_cap(0x22, 0, user);

    // An issuer well carrying −supply (THE EPOCH: wells hold negative balance).
    let mut well = make_open_cell(0xEE, 0);
    let _ = well.state.well_debit_balance(1_000_000);
    w.genesis_install(well);

    let seed = DemoSeed {
        anchors: [treasury, service, user],
        user_cap_slot,
        step: 0,
    };
    (w, [treasury, service, user], seed)
}

/// The seed-turn plan for the demo image: the five real executor turns that give
/// the cockpit its provenance, played ONE AT A TIME via [`DemoSeed::next`].
///
/// [`demo_world`] drains it eagerly; the gpui cockpit drives it from a foreground
/// async task after the window is already painted, calling `cx.notify()` between
/// steps so each committed turn shows up live. Each step runs the SAME real
/// `commit_turn` the eager path does — the asynchrony is purely about WHEN, never
/// about WHETHER the verified turn ran.
pub struct DemoSeed {
    anchors: [CellId; 3],
    user_cap_slot: u32,
    /// The index of the NEXT seed turn to commit (0..=5; `5` = done).
    step: usize,
}

impl DemoSeed {
    /// The total number of seed turns (the five that populate the demo image).
    pub const TOTAL: usize = 5;

    /// How many seed turns are still pending (0 once fully seeded).
    pub fn remaining(&self) -> usize {
        Self::TOTAL.saturating_sub(self.step)
    }

    /// Whether every seed turn has been committed.
    pub fn is_done(&self) -> bool {
        self.step >= Self::TOTAL
    }

    /// Commit the NEXT seed turn against `w` (the real executor), advancing the
    /// plan. Returns a short human label for the committed step (for a status/log
    /// line), or `None` once the plan is exhausted. Each call runs exactly ONE
    /// real verified turn — so a caller can drive it from a paint-friendly async
    /// loop, one turn per yield.
    pub fn next(&mut self, w: &mut World) -> Option<&'static str> {
        let [treasury, service, user] = self.anchors;
        let label = match self.step {
            0 => {
                let t = w.turn(treasury, vec![transfer(treasury, service, 250_000)]);
                let _ = w.commit_turn(t);
                "treasury → service (250,000)"
            }
            1 => {
                let t = w.turn(treasury, vec![transfer(treasury, user, 50_000)]);
                let _ = w.commit_turn(t);
                "treasury → user (50,000)"
            }
            2 => {
                let t = w.turn(user, vec![transfer(user, service, 1_000)]);
                let _ = w.commit_turn(t);
                "user → service (1,000)"
            }
            3 => {
                // An ocap grant: the service re-grants its user-capability back to
                // itself at a fresh slot (legitimate — it holds the cap at
                // `user_cap_slot`).
                let t = w.turn(
                    service,
                    vec![grant_capability(service, service, user, self.user_cap_slot + 1)],
                );
                let _ = w.commit_turn(t);
                "service re-grants its user-cap (ocap)"
            }
            4 => {
                // A state-field write on the service cell.
                let t = w.turn(service, vec![set_field(service, 0, [7u8; 32])]);
                let _ = w.commit_turn(t);
                "service state-field write"
            }
            _ => return None,
        };
        self.step += 1;
        Some(label)
    }
}

// ===========================================================================
// THE SEMIHOSTED COCKPIT — the executor-PD running UNDERNEATH, over the
// EmulatedKernel (`docs/SEMIHOST-COCKPIT.md`; `docs/FIRMAMENT.md §2` L3;
// `docs/DREGG-DESKTOP-OS.md §3` the KEYSTONE payoff).
//
// `World::commit_turn` runs a turn through the embedded verified executor
// DIRECTLY in-process. `SemihostCockpit` runs the SAME turn through the SAME
// verified executor, but DISPATCHED THROUGH THE SEMIHOST executor-PD: the turn
// is staged into the PD's `turn_in` region, the cockpit (an app-PD) signals the
// executor-PD over an `EmulatedKernel` Endpoint (the `ingress→executor` edge),
// the executor-PD reads `turn_in`, runs the cockpit's REAL `World` commit path,
// writes the `TurnReceipt` into `commit_out`, and replies — and the cockpit
// reads the receipt back out of `commit_out`. This proves the sel4 PD world is
// running underneath: the SAME `World` semantics, now reached through the
// firmament's `turn_in → step → commit_out` cap partition over the n=1
// microkernel — the SAME code path a real seL4 boot would take (only the launch
// mechanism, an in-process server vs. a real PD, differs).
// ===========================================================================

/// The cockpit's `World` driven as the executor-PD's [`TurnRunner`] — the
/// verified semantics behind the Endpoint.
///
/// It OWNS the real [`World`] (the embedded `DreggEngine` + the provenance log +
/// the dynamics + the replayable history) and, on a staged turn, decodes the
/// postcard [`Turn`] and runs it through the FULL real [`World::commit_turn`]
/// path (chain-head threading, history recording, dynamics emission, receipt
/// append — NOT a bypass). On commit it returns the postcard-encoded
/// [`TurnReceipt`] for the executor-PD to write into `commit_out`; on a rejected
/// turn it returns the reason (the ocap/verification guarantee firing,
/// fail-closed). A malformed/undecodable stage is a rejection too.
pub struct WorldRunner {
    world: World,
}

impl WorldRunner {
    /// Wrap a `World` as the executor-PD's turn runner.
    pub fn new(world: World) -> Self {
        WorldRunner { world }
    }

    /// Read access to the hosted world (for the harness / the cockpit to inspect
    /// the post-state the executor-PD advanced — the ledger, receipts, height).
    pub fn world(&self) -> &World {
        &self.world
    }

    /// Mutable access to the hosted world (e.g. to seed genesis cells before
    /// turns flow through the PD wire — the out-of-band genesis path, exactly as
    /// for a directly-driven `World`).
    pub fn world_mut(&mut self) -> &mut World {
        &mut self.world
    }
}

impl dregg_firmament::TurnRunner for WorldRunner {
    fn run_turn_bytes(&mut self, turn_bytes: &[u8]) -> Result<Vec<u8>, String> {
        // Decode the staged turn (the wire carries a postcard `Turn`, exactly as
        // `DreggEngine::execute_turn_bytes` and the node ingress decode it).
        let turn: Turn = postcard::from_bytes(turn_bytes)
            .map_err(|e| format!("turn decode failed: {e}"))?;
        // Run it through the FULL real cockpit commit path — chain-head threading,
        // history, dynamics, receipt append. NOT a bypass: the semihost path runs
        // the IDENTICAL `World` logic, just reached through the PD wire.
        match self.world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => postcard::to_stdvec(&receipt)
                .map_err(|e| format!("receipt encode failed: {e}")),
            CommitOutcome::Rejected { reason, .. } => Err(reason),
        }
    }
}

/// THE SEMIHOSTED COCKPIT — the cockpit's `World` hosted inside the firmament's
/// [`ExecutorPd`](dregg_firmament::ExecutorPd) on the semihost
/// [`EmulatedKernel`](dregg_firmament::EmulatedKernel).
///
/// This is "the sel4 PD world running underneath" made concrete and runnable: a
/// turn the cockpit issues flows app-PD → `turn_in` → executor-PD (over the n=1
/// microkernel's Endpoint) → the verified `World` → `commit_out` → receipt. The
/// SAME `World` semantics, reached through the firmament cap partition — the
/// SAME code path a real seL4 executor-PD boot would take.
pub struct SemihostCockpit {
    /// The executor-PD hosting the cockpit's `World` (the verified heart), over a
    /// fresh n=1 [`EmulatedKernel`](dregg_firmament::EmulatedKernel).
    executor: dregg_firmament::ExecutorPd<WorldRunner>,
    /// The run-turn Endpoint the cockpit (app-PD) `pp_call`s to signal a staged
    /// turn (the `ingress→executor` edge — channel 1 in the real assembly).
    run_endpoint: dregg_firmament::emulated_kernel::ObjectId,
    /// The shared kernel (so the cockpit can build a `Channel` to the executor;
    /// kept for the cross-PD path / future multi-PD wiring).
    kernel: dregg_firmament::emulated_kernel::EmulatedKernel,
}

impl SemihostCockpit {
    /// Boot the semihosted cockpit: a fresh n=1 [`EmulatedKernel`], an
    /// [`ExecutorPd`](dregg_firmament::ExecutorPd) hosting `world` (the cockpit's
    /// real verified `World`), and the run-turn Endpoint the cockpit signals. The
    /// `turn_in`/`commit_out` regions are sized for a real turn + receipt (the
    /// executor-stub's `0x100000`/`0x400000`).
    pub fn boot(world: World) -> Self {
        let kernel = dregg_firmament::emulated_kernel::EmulatedKernel::new();
        let run_endpoint = kernel.create_endpoint();
        let executor = dregg_firmament::ExecutorPd::boot(
            kernel.clone(),
            WorldRunner::new(world),
            0x100000, // turn_in : 1 MiB (the executor-stub's turn_in size)
            0x400000, // commit_out: 4 MiB (the executor-stub's commit_out size)
        );
        SemihostCockpit { executor, run_endpoint, kernel }
    }

    /// The hosted world (read-only) — for the cockpit / harness to inspect the
    /// post-state the executor-PD advanced (ledger, receipts, height, dynamics).
    pub fn world(&self) -> &World {
        self.executor.runner().world()
    }

    /// Seed the hosted world out-of-band (the genesis path) — e.g. install the
    /// cells a turn will act on, BEFORE turns flow through the PD wire. This is
    /// the firmament minting genesis cells at boot, exactly as for a
    /// directly-driven `World`; it does not move value or run a turn.
    pub fn with_world_mut<T>(&mut self, f: impl FnOnce(&mut World) -> T) -> T {
        f(self.executor.runner_mut().world_mut())
    }

    /// **COMMIT A TURN THROUGH THE SEMIHOST executor-PD.**
    ///
    /// The cockpit (app-PD) stages the postcard turn into the executor-PD's
    /// `turn_in` region, then drives the executor-PD's protected-procedure body
    /// (`turn_in → step → commit_out`) — reading `turn_in`, running the cockpit's
    /// REAL `World` commit path, writing the receipt/reason into `commit_out`. The
    /// cockpit then reads the receipt back out of `commit_out` and decodes it.
    ///
    /// Returns the real [`TurnReceipt`] on commit (decoded from `commit_out` — it
    /// genuinely round-tripped through the PD wire), or the rejection reason (the
    /// ocap/verification guarantee firing, fail-closed). This is the SAME outcome
    /// `World::commit_turn` produces in-process — but reached through the
    /// firmament's executor-PD over the n=1 microkernel.
    ///
    /// (The inline drive runs the executor-PD's body on the calling thread — the
    /// `EmulatedKernel::call_served_by` single-thread collapse of the rendezvous.
    /// The two-thread Endpoint form — a real PD's `protected` body on its own
    /// thread — is exercised by the firmament's `executor_pd_boot` test; the
    /// cockpit uses the inline drive so a turn commits deterministically with no
    /// thread timing.)
    pub fn commit_turn_via_semihost(&mut self, turn: Turn) -> CommitOutcome {
        // Encode + STAGE the turn into the executor-PD's turn_in region (the
        // app-PD's turn_in write before it signals the heart).
        let turn_bytes = match postcard::to_stdvec(&turn) {
            Ok(b) => b,
            Err(e) => {
                return CommitOutcome::Rejected {
                    reason: format!("turn encode failed: {e}"),
                    at_action: vec![],
                }
            }
        };
        if self.executor.stage_turn(&turn_bytes).is_none() {
            return CommitOutcome::Rejected {
                reason: format!(
                    "turn ({} bytes) does not fit the executor-PD turn_in region",
                    turn_bytes.len()
                ),
                at_action: vec![],
            };
        }
        // DRIVE the executor-PD's protected-procedure body (read turn_in + step +
        // write commit_out). This is the heart running the turn over the
        // EmulatedKernel; on the cross-PD path this is a `serve_turn` off the
        // Endpoint, here the inline single-thread collapse.
        let served = self.executor.step_staged_turn();
        match served {
            dregg_firmament::ServedTurn::Committed { .. } => {
                // Read the receipt back out of commit_out and decode it — proving
                // it genuinely round-tripped through the PD wire (not returned
                // in-band). This is the app-PD's commit_out read.
                let receipt_bytes = match self.executor.commit_out_read() {
                    Some(b) => b,
                    None => {
                        return CommitOutcome::Rejected {
                            reason: "executor-PD committed but commit_out was empty".into(),
                            at_action: vec![],
                        }
                    }
                };
                match postcard::from_bytes::<TurnReceipt>(&receipt_bytes) {
                    // `events` is empty here ON PURPOSE: the dynamics events were
                    // emitted into the HOSTED world's dynamics stream by the
                    // runner's real `commit_turn` (read them via
                    // `self.world().dynamics()`), not re-marshalled across the PD
                    // wire — the wire carries the RECEIPT (the executor-PD's
                    // commit_out), the dynamics live with the world the heart owns.
                    Ok(receipt) => CommitOutcome::Committed { receipt, events: Vec::new() },
                    Err(e) => CommitOutcome::Rejected {
                        reason: format!("receipt decode from commit_out failed: {e}"),
                        at_action: vec![],
                    },
                }
            }
            dregg_firmament::ServedTurn::Rejected { reason } => {
                CommitOutcome::Rejected { reason, at_action: vec![] }
            }
        }
    }

    /// The run-turn Endpoint id (for the cross-PD `serve_turn` path / future
    /// multi-PD wiring) — the executor's PP channel.
    pub fn run_endpoint(&self) -> dregg_firmament::emulated_kernel::ObjectId {
        self.run_endpoint
    }

    /// The shared n=1 kernel (for building a `Channel` to the executor on the
    /// cross-PD path).
    pub fn kernel(&self) -> &dregg_firmament::emulated_kernel::EmulatedKernel {
        &self.kernel
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_world_is_empty() {
        let w = World::new();
        assert_eq!(w.cell_count(), 0);
        assert_eq!(w.height(), 0);
        assert!(w.receipts().is_empty());
    }

    #[test]
    fn genesis_then_transfer_commits_and_conserves() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        assert_eq!(w.cell_count(), 2);

        let total_before =
            w.ledger().get(&a).unwrap().state.balance() + w.ledger().get(&b).unwrap().state.balance();

        let turn = w.turn(a, vec![transfer(a, b, 250)]);
        let outcome = w.commit_turn(turn);
        assert!(outcome.is_committed(), "transfer should commit");

        let ba = w.ledger().get(&a).unwrap().state.balance();
        let bb = w.ledger().get(&b).unwrap().state.balance();
        assert_eq!(ba, 750);
        assert_eq!(bb, 250);
        // Conservation: the embedded VERIFIED executor preserves total value.
        assert_eq!(ba + bb, total_before);

        // Provenance: a real receipt was logged and the chain head advanced.
        assert_eq!(w.receipts().len(), 1);
        assert_eq!(w.height(), 1);
        assert!(w.chain_head(&a).is_some());

        // Dynamics: the transition was observed (a TurnCommitted + a flow each).
        let evs = w.dynamics().since(0);
        assert!(evs.iter().any(|e| matches!(e, WorldEvent::TurnCommitted { .. })));
        assert!(evs.iter().any(|e| matches!(e, WorldEvent::BalanceFlowed { .. })));
    }

    #[test]
    fn overspend_transfer_is_rejected_by_the_real_executor() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let b = w.genesis_cell(2, 0);

        // Transfer MORE than `a` holds: the verified executor must reject it
        // (conservation / non-negativity), and the ledger must be unchanged.
        let turn = w.turn(a, vec![transfer(a, b, 1_000)]);
        let outcome = w.commit_turn(turn);
        assert!(!outcome.is_committed(), "overspend must be rejected");

        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 100);
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 0);
        assert_eq!(w.receipts().len(), 0);
        assert_eq!(w.height(), 0);
    }

    #[test]
    fn receipt_chain_advances_across_two_turns() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);

        let t1 = w.turn(a, vec![transfer(a, b, 100)]);
        assert!(w.commit_turn(t1).is_committed());
        let head1 = w.chain_head(&a).unwrap();

        let t2 = w.turn(a, vec![transfer(a, b, 100)]);
        assert!(w.commit_turn(t2).is_committed());
        let head2 = w.chain_head(&a).unwrap();

        assert_ne!(head1, head2, "chain head must advance");
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 200);
        assert_eq!(w.receipts().len(), 2);
        // The second receipt links to the first.
        assert_eq!(w.receipts()[1].previous_receipt_hash, Some(head1));
    }

    #[test]
    fn state_root_changes_when_state_changes() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        let r0 = w.state_root();

        let turn = w.turn(a, vec![transfer(a, b, 1)]);
        assert!(w.commit_turn(turn).is_committed());
        let r1 = w.state_root();
        assert_ne!(r0, r1, "the image commitment must move with history");
    }

    #[test]
    fn emit_event_commits() {
        let mut w = World::new();
        let a = w.genesis_cell(7, 10);
        let turn = w.turn(a, vec![emit_event(a, "greeting", vec![])]);
        assert!(w.commit_turn(turn).is_committed());
        assert_eq!(w.receipts().len(), 1);
    }

    #[test]
    fn grant_capability_grows_the_ocap_graph() {
        let mut w = World::new();
        let b = w.genesis_cell(2, 0);
        // `a` is born holding a cap to `b`; it re-grants to a fresh slot.
        let (a, slot) = w.genesis_cell_with_cap(1, 100, b);
        let turn = w.turn(a, vec![grant_capability(a, a, b, slot + 1)]);
        assert!(w.commit_turn(turn).is_committed());
        let cell_a = w.ledger().get(&a).unwrap();
        assert!(cell_a.capabilities.has_access(&b), "a should reach b");
    }

    #[test]
    fn over_grant_is_rejected_by_the_real_executor() {
        // The ocap no-amplification guarantee: a cell that holds NO capability
        // to `b` cannot grant one. The verified executor must reject it.
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let b = w.genesis_cell(2, 0);
        let turn = w.turn(a, vec![grant_capability(a, a, b, 0)]);
        assert!(!w.commit_turn(turn).is_committed(), "over-grant must reject");
    }

    #[test]
    fn create_cell_grows_the_ledger() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let before = w.cell_count();
        let turn = w.turn(a, vec![create_cell(9)]);
        assert!(w.commit_turn(turn).is_committed());
        assert_eq!(w.cell_count(), before + 1);
    }

    #[test]
    fn set_field_writes_state() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let turn = w.turn(a, vec![set_field(a, 3, [9u8; 32])]);
        assert!(w.commit_turn(turn).is_committed());
        assert_eq!(w.ledger().get(&a).unwrap().state.fields[3], [9u8; 32]);
    }

    #[test]
    fn seal_then_unseal_round_trips_the_lifecycle() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        // Seal: the cell's lifecycle transitions to Sealed (agent == target).
        let t1 = w.turn(a, vec![seal(a, "maintenance window")]);
        assert!(w.commit_turn(t1).is_committed(), "seal must commit");
        assert!(
            w.ledger().get(&a).unwrap().lifecycle.is_sealed(),
            "the cell's lifecycle must be Sealed"
        );

        // Unseal: the lifecycle returns to Live.
        let t2 = w.turn(a, vec![unseal(a)]);
        assert!(w.commit_turn(t2).is_committed(), "unseal must commit");
        assert!(
            !w.ledger().get(&a).unwrap().lifecycle.is_sealed(),
            "the cell must be Live again after unseal"
        );

        // NOTE (real protocol finding): the verified executor records the
        // Sealed lifecycle but does NOT yet GATE ordinary effects on it
        // (`CellLifecycle::accepts_effects()` exists on the cell type but the
        // executor's apply path does not consult it before non-lifecycle
        // effects). So seal is a recorded-disclosure today, not an enforced
        // effect-freeze. The cockpit surfaces the lifecycle state honestly; the
        // enforcement gate is an executor lane, not this surface's to fake.
    }

    #[test]
    fn unseal_of_a_live_cell_is_rejected() {
        // The executor enforces NotSealed: unsealing a non-sealed cell rejects.
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let t = w.turn(a, vec![unseal(a)]);
        assert!(!w.commit_turn(t).is_committed(), "unseal of a live cell must reject");
    }

    #[test]
    fn destroy_retires_a_cell_terminally() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 0);
        let t = w.turn(a, vec![destroy(a, w.height(), DeathReason::Voluntary)]);
        assert!(w.commit_turn(t).is_committed(), "destroy must commit");
        let cell = w.ledger().get(&a).unwrap();
        assert!(cell.lifecycle.is_terminal(), "a destroyed cell's lifecycle is terminal");

        // The lifecycle gate: a SECOND destroy IS rejected — `Cell::destroy`
        // returns `Terminal` for an already-terminal cell, so the lifecycle
        // verbs themselves DO enforce terminality (even though ordinary effects
        // are not yet gated on it — see the seal/lifecycle note in
        // `seal_then_unseal_round_trips_the_lifecycle`).
        let again = w.turn(a, vec![destroy(a, w.height(), DeathReason::Voluntary)]);
        assert!(
            !w.commit_turn(again).is_committed(),
            "a destroyed cell cannot be destroyed again (the lifecycle verb enforces terminality)"
        );
    }

    #[test]
    fn burn_reduces_supply_without_a_credit() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let t = w.turn(a, vec![burn(a, 250)]);
        assert!(w.commit_turn(t).is_committed(), "burn must commit");
        assert_eq!(
            w.ledger().get(&a).unwrap().state.balance(),
            750,
            "the burned amount left the cell with no destination"
        );
        // The receipt records the burn disclosure (bound into the hash).
        assert!(w.receipts().last().unwrap().was_burn, "the receipt must flag the burn");
    }

    #[test]
    fn burn_exceeding_balance_is_rejected() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let t = w.turn(a, vec![burn(a, 1_000)]);
        assert!(!w.commit_turn(t).is_committed(), "over-burn must reject");
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 100);
    }

    #[test]
    fn forest_turn_commits_several_actions_atomically() {
        // A multi-action turn: agent transfers to two different cells in ONE
        // turn (two sibling roots), committed atomically with one receipt.
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        let c = w.genesis_cell(3, 0);

        let t = w.forest_turn(
            a,
            vec![
                (a, vec![transfer(a, b, 100)]),
                (a, vec![transfer(a, c, 200)]),
            ],
        );
        let outcome = w.commit_turn(t);
        assert!(outcome.is_committed(), "the multi-action forest must commit");
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 100);
        assert_eq!(w.ledger().get(&c).unwrap().state.balance(), 200);
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 700);
        // ONE receipt for the whole forest, with two actions.
        assert_eq!(w.receipts().len(), 1);
        assert_eq!(w.receipts()[0].action_count, 2);
    }

    #[test]
    fn forest_turn_is_atomic_all_or_nothing() {
        // If ANY action in the forest is invalid, the WHOLE turn rejects and
        // no partial effect lands (atomic commit).
        let mut w = World::new();
        let a = w.genesis_cell(1, 150);
        let b = w.genesis_cell(2, 0);

        let t = w.forest_turn(
            a,
            vec![
                (a, vec![transfer(a, b, 100)]),     // would be fine alone
                (a, vec![transfer(a, b, 1_000)]),   // overspends → rejects the turn
            ],
        );
        assert!(!w.commit_turn(t).is_committed(), "an invalid sibling must reject the whole turn");
        // Atomicity: the first transfer did NOT land.
        assert_eq!(w.ledger().get(&a).unwrap().state.balance(), 150);
        assert_eq!(w.ledger().get(&b).unwrap().state.balance(), 0);
        assert_eq!(w.height(), 0);
    }

    #[test]
    fn deploy_factory_then_birth_a_child_cell() {
        use dregg_cell::factory::{FactoryCreationParams, FactoryDescriptor};
        use dregg_cell::CellMode;

        let mut w = World::new();
        let agent = w.genesis_cell(1, 0);

        // Deploy a minimal Hosted factory (no pinned child program) into the
        // real executor's registry; get its content-addressed VK back.
        let descriptor = FactoryDescriptor {
            factory_vk: [0xF0; 32],
            child_program_vk: None,
            child_vk_strategy: None,
            allowed_cap_templates: vec![],
            field_constraints: vec![],
            state_constraints: vec![],
            default_mode: CellMode::Hosted,
            creation_budget: Some(4),
        };
        let vk = w.deploy_factory(descriptor);

        let owner = {
            let mut pk = [0u8; 32];
            pk[0] = 0xC1;
            pk
        };
        let before = w.cell_count();
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: None,
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: owner,
        };
        let turn = w.turn(agent, vec![create_cell_from_factory(vk, owner, [0u8; 32], params)]);
        let outcome = w.commit_turn(turn);
        assert!(outcome.is_committed(), "factory-birth must commit through the real executor");
        assert_eq!(w.cell_count(), before + 1, "the factory birthed a child cell");
    }

    #[test]
    fn factory_birth_against_an_unregistered_factory_is_rejected() {
        use dregg_cell::factory::FactoryCreationParams;
        use dregg_cell::CellMode;
        let mut w = World::new();
        let agent = w.genesis_cell(1, 0);
        let owner = [0xC2u8; 32];
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: None,
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: owner,
        };
        // No factory deployed at this VK → the executor rejects the birth.
        let turn = w.turn(agent, vec![create_cell_from_factory([0x99; 32], owner, [0u8; 32], params)]);
        assert!(!w.commit_turn(turn).is_committed(), "birth from an unregistered factory must reject");
    }

    #[test]
    fn demo_world_boots_with_real_history() {
        let (w, [treasury, service, user]) = demo_world();
        // 4 cells: treasury, user, service, issuer well.
        assert_eq!(w.cell_count(), 4);
        // 5 committed turns of real provenance.
        assert_eq!(w.receipts().len(), 5);
        assert!(w.height() >= 5);
        // The flows landed: service got 250_000 (treasury) + 1_000 (user).
        assert_eq!(w.ledger().get(&service).unwrap().state.balance(), 251_000);
        assert!(w.ledger().get(&user).unwrap().state.balance() > 0);
        let _ = treasury;
        // The ocap grant landed (service reaches user).
        assert!(w.ledger().get(&service).unwrap().capabilities.has_access(&user));
    }

    #[test]
    fn demo_genesis_is_instant_and_unseeded_but_alive() {
        // THE FIRST-PAINT IMAGE: genesis installs the cells (no executor turns),
        // so the cockpit can open its window on THIS immediately. It is "alive but
        // at rest" — the four cells exist, but NO seed turn has run yet.
        let (w, [treasury, service, user], seed) = demo_genesis();
        assert_eq!(w.cell_count(), 4, "the four cells are installed at genesis");
        assert_eq!(w.receipts().len(), 0, "NO seed turn has run on the first-paint image");
        assert_eq!(w.height(), 0, "the at-rest image is at height 0");
        assert_eq!(seed.remaining(), DemoSeed::TOTAL, "all five seed turns are still pending");
        assert!(!seed.is_done());
        // The anchors are real, installed cells already (so the cockpit's panels
        // have their treasury/service/user the moment the window opens).
        assert!(w.ledger().get(&treasury).is_some());
        assert!(w.ledger().get(&service).is_some());
        assert!(w.ledger().get(&user).is_some());
    }

    #[test]
    fn demo_seed_reaches_the_same_image_as_demo_world() {
        // Driving the seed plan one turn at a time (the async/paint-friendly path)
        // converges to the EXACT image `demo_world` builds eagerly — same cells,
        // same receipts, same balances, same ocap edge. The asynchrony is purely
        // about WHEN each verified turn runs, never WHETHER.
        let (mut w, [_t, service, user], mut seed) = demo_genesis();
        let mut steps: usize = 0;
        while let Some(_label) = seed.next(&mut w) {
            steps += 1;
            // Each `next` commits exactly ONE real turn (height + receipts grow by 1).
            assert_eq!(w.height() as usize, steps, "one committed turn per seed step");
            assert_eq!(w.receipts().len(), steps);
        }
        assert_eq!(steps, DemoSeed::TOTAL, "all five seed turns ran");
        assert!(seed.is_done());
        assert_eq!(seed.remaining(), 0);
        // The fully-seeded image equals the eager `demo_world` image's invariants.
        assert_eq!(w.cell_count(), 4);
        assert_eq!(w.receipts().len(), 5);
        assert_eq!(w.ledger().get(&service).unwrap().state.balance(), 251_000);
        assert!(w.ledger().get(&user).unwrap().state.balance() > 0);
        assert!(w.ledger().get(&service).unwrap().capabilities.has_access(&user));
    }

    // ── THE SEMIHOSTED COCKPIT — a turn flowing through the executor-PD over the
    //    EmulatedKernel (the sel4 PD world running underneath) ──────────────────

    #[test]
    fn cockpit_turn_flows_through_the_semihost_executor_pd() {
        // Boot the semihosted cockpit: the cockpit's REAL `World` hosted inside
        // the firmament's executor-PD over a fresh n=1 EmulatedKernel.
        let mut w = World::new();
        let a = w.genesis_cell(1, 1_000);
        let b = w.genesis_cell(2, 0);
        let mut cockpit = SemihostCockpit::boot(w);

        // The agent's first-turn shape: build the transfer turn against the hosted
        // world (so the nonce/fee match the executor-PD's ledger). We build it via
        // the hosted world's typed constructor, then dispatch THROUGH the PD wire.
        let turn = cockpit.world().turn(a, vec![transfer(a, b, 250)]);

        // COMMIT IT THROUGH THE SEMIHOST executor-PD: staged into turn_in →
        // signalled → run through the verified `World` → receipt written to
        // commit_out → read back + decoded. The sel4 PD path, end to end.
        let outcome = cockpit.commit_turn_via_semihost(turn);
        assert!(outcome.is_committed(), "the cockpit turn committed THROUGH the semihost executor-PD");

        // The receipt genuinely round-tripped through commit_out (decoded from the
        // PD's RW region, not returned in-band).
        let receipt = match outcome {
            CommitOutcome::Committed { receipt, .. } => receipt,
            CommitOutcome::Rejected { reason, .. } => panic!("unexpected reject: {reason}"),
        };
        assert_eq!(receipt.action_count, 1, "the receipt the executor-PD wrote describes the turn");

        // THE POST-STATE: the executor-PD advanced the hosted world's ledger — the
        // transfer landed (250 moved a→b), conservation held, the chain advanced.
        let world = cockpit.world();
        assert_eq!(world.ledger().get(&a).unwrap().state.balance(), 750);
        assert_eq!(world.ledger().get(&b).unwrap().state.balance(), 250);
        assert_eq!(world.height(), 1, "the heart advanced the height");
        assert_eq!(world.receipts().len(), 1, "the receipt was appended (full World path ran)");
        assert!(world.chain_head(&a).is_some(), "the per-agent chain head advanced through the PD");
    }

    #[test]
    fn semihost_executor_pd_rejects_an_overspend_fail_closed() {
        // The ocap/verification guarantee fires AT THE HEART, through the PD wire:
        // an overspend is rejected and no state advances (fail-closed). The cockpit
        // reads the reason back, exactly as it would a receipt.
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let b = w.genesis_cell(2, 0);
        let mut cockpit = SemihostCockpit::boot(w);

        let turn = cockpit.world().turn(a, vec![transfer(a, b, 1_000)]); // overspend
        let outcome = cockpit.commit_turn_via_semihost(turn);
        assert!(!outcome.is_committed(), "an overspend is REJECTED at the heart (through the PD wire)");

        // No state advanced — the ledger the executor-PD holds is unchanged.
        let world = cockpit.world();
        assert_eq!(world.ledger().get(&a).unwrap().state.balance(), 100);
        assert_eq!(world.ledger().get(&b).unwrap().state.balance(), 0);
        assert_eq!(world.height(), 0, "no turn committed");
        assert_eq!(world.receipts().len(), 0);
    }

    #[test]
    fn semihost_path_matches_the_direct_path_byte_for_byte() {
        // THE EQUIVALENCE: the SAME turn yields the SAME receipt whether run
        // DIRECTLY in-process (`World::commit_turn`) or THROUGH the semihost
        // executor-PD (`SemihostCockpit::commit_turn_via_semihost`). The PD wire is
        // a faithful conduit for the verified semantics, not a re-implementation.
        //
        // Both worlds are pinned to the SAME timestamp (the receipt folds it), so
        // the byte-for-byte claim is DETERMINISTIC — it tests the semantics, not a
        // wall-clock coincidence (the houyhnhnm-clock determinism, §3).
        const PINNED_TS: i64 = 1_700_000_000;
        let mk = || {
            let mut w = World::with_costs_and_timestamp(ComputronCosts::zero(), PINNED_TS);
            let a = w.genesis_cell(1, 1_000);
            let b = w.genesis_cell(2, 0);
            (w, a, b)
        };

        // Direct path.
        let (mut direct, a, b) = mk();
        let t_direct = direct.turn(a, vec![transfer(a, b, 250)]);
        let direct_receipt = match direct.commit_turn(t_direct) {
            CommitOutcome::Committed { receipt, .. } => receipt,
            CommitOutcome::Rejected { reason, .. } => panic!("direct reject: {reason}"),
        };

        // Semihost path (a fresh, identically-seeded world).
        let (semi_world, a2, b2) = mk();
        assert_eq!(a, a2, "deterministic genesis ids");
        let mut cockpit = SemihostCockpit::boot(semi_world);
        let t_semi = cockpit.world().turn(a2, vec![transfer(a2, b2, 250)]);
        let semi_receipt = match cockpit.commit_turn_via_semihost(t_semi) {
            CommitOutcome::Committed { receipt, .. } => receipt,
            CommitOutcome::Rejected { reason, .. } => panic!("semihost reject: {reason}"),
        };

        // The receipt hashes match — the heart over the EmulatedKernel produced
        // the BYTE-IDENTICAL verified receipt the direct executor did.
        assert_eq!(
            direct_receipt.receipt_hash(),
            semi_receipt.receipt_hash(),
            "the semihost executor-PD produces the SAME verified receipt as the direct path"
        );
        // And the post-state ledgers agree.
        assert_eq!(
            direct.state_root(),
            cockpit.world().state_root(),
            "the semihost path advances the SAME image the direct path does"
        );
    }
}
