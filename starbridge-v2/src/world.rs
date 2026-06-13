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
        // A real wall-clock so temporal preconditions behave; harmless for the
        // demo flows that don't use them. PINNED for the world's life so the
        // engine and the replay history stay bit-deterministic together.
        let timestamp = now_unix();
        let config = EngineConfig {
            costs: ComputronCosts::zero(),
            federation_id: [0u8; 32],
            block_height: 0,
            timestamp,
            max_proof_age_secs: 0,
        };
        let history = History::new(timestamp);
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
        }
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

    pub fn height(&self) -> u64 {
        self.height
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
        bare_turn(agent, self.next_nonce(&agent), effects)
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

/// The bare single-action turn shape (matches the executor test template).
pub fn bare_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
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

/// Build a populated demo world: three cells (a treasury, a service, a user),
/// an issuer well carrying −supply, and a handful of committed turns so the
/// cockpit boots into a LIVE image with real provenance — not a mock. Returns
/// the world and the (treasury, service, user) ids for the views to anchor on.
pub fn demo_world() -> (World, [CellId; 3]) {
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

    // Seed some real history through the embedded executor.
    let t1 = w.turn(treasury, vec![transfer(treasury, service, 250_000)]);
    let _ = w.commit_turn(t1);
    let t2 = w.turn(treasury, vec![transfer(treasury, user, 50_000)]);
    let _ = w.commit_turn(t2);
    let t3 = w.turn(user, vec![transfer(user, service, 1_000)]);
    let _ = w.commit_turn(t3);
    // An ocap grant: the service re-grants its user-capability back to itself at
    // a fresh slot (legitimate — it holds the cap at `user_cap_slot`).
    let t4 = w.turn(
        service,
        vec![grant_capability(service, service, user, user_cap_slot + 1)],
    );
    let _ = w.commit_turn(t4);
    // A state-field write on the service cell.
    let t5 = w.turn(service, vec![set_field(service, 0, [7u8; 32])]);
    let _ = w.commit_turn(t5);

    (w, [treasury, service, user])
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
}
