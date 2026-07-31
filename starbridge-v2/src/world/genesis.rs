//! **THE OUT-OF-BAND GENESIS-PATH MUTATORS** — ledger writes that do NOT ride a turn.
//!
//! Extracted verbatim from `world/mod.rs` so the reactivity track owns a file rather than
//! a line-range. No behaviour change. A CHILD module, so it keeps private access to
//! `World`'s fields and helpers (`durable_regenesis`, `genesis_mutation_would_break_reopen`,
//! `ensure_record_ledger`) exactly as it had inline.
//!
//! ⚑ THESE FOUR MUTATE THE LEDGER AND EMIT NO `WorldEvent`. That is the M2 cache-soundness
//! hole: `commit_turn`'s write-set completeness pass tops up events from the executor
//! journal, but these never run `commit_turn` at all, so a memoized projection of a cell
//! they touch goes silently stale. Today the desktop 250 ms poll papers over it.
//!
//! ⚠ `set_cell_heap` is the SHIPPING desktop document editor's persist path
//! (`deos_desktop/mod.rs::commit_doc_to_umem_heap`) — and on a DURABLE image it refuses
//! from save #2 onward, because `genesis_mutation_would_break_reopen` sees the doc cell was
//! touched by save #1's own `SetField` turn. The caller then short-circuits on `&&`, so the
//! revision turn does not run either: no heap write, no receipt, no event, and the JSON
//! sidecar becomes the only copy of the prose. Closing that needs an ordered
//! `Effect::SetHeap`; until it exists the sidecar CANNOT be deleted.
//!
//! ⚠ When these learn to emit, the event must go AFTER the reopen guard, on the success
//! leg only — `persistence.rs`'s guard tests assert the early-return leg.

use super::*;

impl World {
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
        // FAIL-FAST guard (HORIZONLOG persist bug): a genesis-path mutation on a cell
        // a committed turn already touched would make the DURABLE image non-reopenable
        // (the genesis-mirror-after-turn bug — the post-mutation cell, recorded as
        // timeless "genesis", poisons recovery's re-execution of that turn). REFUSE
        // it here rather than silently corrupt the image on reopen. Genesis-SETUP
        // mutations (before the cell's first turn) and ephemeral worlds pass through.
        // (The sound full fix — ordered pre/post-chain genesis events — is HORIZONLOG'd.)
        if self.genesis_mutation_would_break_reopen(cell) {
            return false;
        }
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
        // Durable genesis re-record (SEAM §2): the in-place program change carries
        // no `CommitRecord`, so persist the cell's new post-state for reopen.
        if existed {
            self.durable_regenesis(cell);
        }
        // Genesis-path ledger mutation without a height bump — bust the memo.
        self.state_root_memo.set(None);
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
        // FAIL-FAST guard (HORIZONLOG persist bug): refuse a genesis-path c-list
        // mutation that would make the durable image non-reopenable (the holder was
        // already touched by a committed turn). Same class as `set_cell_program`.
        if self.genesis_mutation_would_break_reopen(holder) {
            return None;
        }
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
        // Durable genesis re-record (SEAM §2): the in-place cap grant carries no
        // `CommitRecord`, so persist the holder's new post-state for reopen.
        if slot.is_some() {
            self.durable_regenesis(holder);
        }
        // Genesis-path ledger mutation without a height bump — bust the memo.
        self.state_root_memo.set(None);
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
        // FAIL-FAST guard (HORIZONLOG persist bug): refuse a genesis-path permissions
        // mutation that would make the durable image non-reopenable (the cell was
        // already touched by a committed turn). Same class as `set_cell_program`.
        if self.genesis_mutation_would_break_reopen(cell) {
            return false;
        }
        let existed = if let Some(c) = self.engine.ledger_mut().get_mut(cell) {
            c.permissions = open_permissions();
            true
        } else {
            false
        };
        if let Some(c) = self.record_ledger.get_mut(cell) {
            c.permissions = open_permissions();
        }
        // Durable genesis re-record (SEAM §2): the in-place permissions change
        // carries no `CommitRecord`, so persist the cell's new post-state.
        if existed {
            self.durable_regenesis(cell);
        }
        // Genesis-path ledger mutation without a height bump — bust the memo.
        self.state_root_memo.set(None);
        existed
    }

    /// **Write a cell's universal-memory heap out-of-band and reseal its
    /// committed `heap_root`** — the per-cell umem boundary (`UMEM-PRIMITIVE` §2,
    /// §8; `cell/src/state.rs`: `set_heap` / `reseal_heap_root`). Replaces the
    /// cell's `heap_map` wholesale (so a dropped leaf simply vanishes from the
    /// boundary) and recomputes `heap_root` = sorted-Poseidon2 over the present
    /// leaves, so the resealed boundary IS the cell's committed commitment.
    ///
    /// This is the document-on-umem ride ([`dregg_doc::DocHeapCell`]): the desktop
    /// projects a document into its cell's umem-heap and reseals, so the
    /// document's commitment IS that `heap_root`. The heap register is orthogonal
    /// to `fields_map`/`fields_root` (a later `SetField` turn re-executes against,
    /// and preserves, the written heap). Like [`Self::set_cell_program`] /
    /// [`Self::genesis_grant_cap`], it installs committed state on a cell without
    /// moving value or running a turn — there is no kernel heap effect, the writes
    /// are ordinary heap writes the substrate already commits. Mirrored into the
    /// replay-recorder's ledger so the recorded roots stay in lock-step.
    ///
    /// FAIL-FAST on a DURABLE image whose cell a committed turn already touched
    /// (the genesis-mirror-after-turn bug): returns `false` rather than poison
    /// reopen. The desktop's demo world is ephemeral, so this passes; a durable
    /// runtime heap write awaits an ordered heap effect (HORIZONLOG seam). Returns
    /// `true` if the cell existed and its boundary was resealed.
    pub fn set_cell_heap(
        &mut self,
        cell: &CellId,
        heap_map: std::collections::BTreeMap<(u32, u32), dregg_cell::FieldElement>,
    ) -> bool {
        if self.genesis_mutation_would_break_reopen(cell) {
            return false;
        }
        let existed = if let Some(c) = self.engine.ledger_mut().get_mut(cell) {
            c.state.heap_map = heap_map.clone();
            c.state.reseal_heap_root();
            true
        } else {
            false
        };
        // Keep the replay tape's ledger in lock-step so its recorded roots match
        // the live engine's (the document cell carries the SAME umem boundary).
        if let Some(c) = self.record_ledger.get_mut(cell) {
            c.state.heap_map = heap_map;
            c.state.reseal_heap_root();
        }
        // Durable genesis re-record (SEAM §2): the in-place heap write carries no
        // `CommitRecord`, so persist the cell's new post-state for reopen.
        if existed {
            self.durable_regenesis(cell);
        }
        // Genesis-path ledger mutation without a height bump — bust the memo.
        self.state_root_memo.set(None);
        existed
    }

    /// Deploy a [`FactoryDescriptor`] into the embedded executor's factory
    /// registry (the out-of-band genesis path — a node registers its factories
    /// the way it seeds genesis cells). Returns the factory's content-addressed
    /// VK, against which a later [`create_cell_from_factory`] effect is
    /// validated by the real executor. The descriptor is also mirrored into the
    /// replay tape's executor so factory-births re-derive on replay.
    pub fn deploy_factory(&mut self, descriptor: dregg_cell::FactoryDescriptor) -> [u8; 32] {
        let vk = self
            .engine
            .executor_mut()
            .deploy_factory(descriptor.clone());
        // Keep the replay recorder's executor in lock-step so a factory-birth
        // committed below re-derives identically on replay.
        let _ = self.record_exec.deploy_factory(descriptor.clone());
        // Retain the descriptor so a fork can replay it onto its throwaway
        // executor (the live registry isn't enumerable; this is our own record).
        self.deployed_factories.push(descriptor);
        vk
    }
}
