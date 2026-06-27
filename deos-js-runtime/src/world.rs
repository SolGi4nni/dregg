//! The **multi-cell substance** a native-JS *app* drives — the upgrade from a single
//! [`crate::applet::CellApplet`] to a whole **cap table of cells** one JS program
//! orchestrates.
//!
//! A starbridge-app is not one cell behaving; it is a JS program *coordinating* several
//! cells — set state here, move value there, invoke a service over there. [`CellWorld`]
//! is the engine-independent substance for exactly that: ONE embedded [`DreggEngine`]
//! holding several cells, and a **cap table** recording, per cell the JS holds a cap to,
//! the held authority (the cap tooth's left side) + that cell's affordance surface.
//!
//! Every host capability the JS gets is bounded by this table:
//!
//!   - [`CellWorld::fire_on`] (the `tCell`/`t` host fns) — fire a named cell's affordance
//!     as a REAL cap-gated verified turn. The `is_attenuation` tooth runs in-band against
//!     the held cap for THAT cell; an over-reach commits nothing.
//!   - [`CellWorld::transfer`] (the `transfer` host fn) — move value between two cells the
//!     JS holds caps to, conservation enforced by the executor.
//!   - [`CellWorld::view_patch`] (the `viewPatch` host fn) — a receipted self-edit of the
//!     home cell's committed view-tree blob (moves `heap_root` + leaves a receipt).
//!   - [`CellWorld::get_slot`] (the `get`/`getCell` host fns) — a witnessed read.
//!
//! **The confinement keystone.** The JS references cells only by the *string handles* the
//! host installed in the cap table — there are no ambient cell ids in the sandbox, exactly
//! as there are no ambient host functions. A name absent from the table resolves to
//! [`FireError::NoCapability`]: the cell it would have pointed at is never touched. A name
//! present but whose held cap does not satisfy the affordance's `required` resolves to
//! [`FireError::Unauthorized`]: the same cap tooth `deos-js` already runs. A JS app can
//! therefore touch only the cells it holds caps to, and only at the authority it holds.

use std::collections::BTreeMap;

use dregg_cell::{AuthRequired, Cell, Permissions};
use dregg_sdk::embed::{DreggEngine, EngineConfig};
use dregg_turn::builder::{ActionBuilder, TurnBuilder};
use dregg_turn::TurnReceipt;
use dregg_types::CellId;

use crate::applet::{pack_u64, unpack_u64, Affordance, FireError, Slot};

/// The committed-heap collection the home cell's view-tree blob lives under — the SAME
/// `VIEWTREE_COLL` `deos-view::mount` chunks the hosted view-tree into, so a `viewPatch`
/// self-edit here moves `heap_root` the way the renderer's edits do.
pub const VIEWTREE_COLL: u32 = 0x1E4F;
/// Payload bytes per `FieldElement` leaf (byte 0 = fill length) — the proven chunked
/// heap-blob codec (31 bytes/leaf, key 0 = the u64 length header).
const CHUNK_BYTES: usize = 31;
/// The model slot the home cell's **view version** counter lives in. A `viewPatch` bumps
/// it through a real `SetField` turn — the receipt that witnesses the self-edit (mirroring
/// `deos-js::card_editor`'s provenance turn), independent of any app model slot. The top of
/// the fixed 16-slot field array (`STATE_SLOTS - 1`), reserved for the runtime's own
/// provenance so an app's low slots stay free.
pub const VIEW_VERSION_SLOT: Slot = 15;

fn open_permissions() -> Permissions {
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

/// One cell the JS app holds a cap to — a row of the cap table.
struct CellEntry {
    /// The cell on the shared embedded ledger.
    id: CellId,
    /// The authority the JS app holds toward this cell (the cap tooth's left side). A
    /// fire/self-edit succeeds only if this satisfies the affordance's `required`.
    held: AuthRequired,
    /// The cell's affordance surface (the directions of its interface).
    affordances: Vec<Affordance>,
}

/// What a successful fire produced — the receipt that joined the audit tape and the new
/// value of the written slot (the witnessed read a host fn hands back to JS).
#[derive(Clone, Debug)]
pub struct Fired {
    /// The committed receipt hash (its place on the audit tape).
    pub receipt_hash: [u8; 32],
    /// The new value of the affordance's written slot, read off the live ledger.
    pub value: i64,
}

/// A **multi-cell world** on one embedded verified executor — the substance a native-JS
/// *app* orchestrates. Cells are addressed by string handle; the handle IS the capability
/// (an absent handle is an unreachable cell). One designated **home** cell carries the
/// app's surface (its `t`/`get`/`viewPatch` default target).
pub struct CellWorld {
    engine: DreggEngine,
    cells: BTreeMap<String, CellEntry>,
    home: Option<String>,
    /// The home cell's view-tree (a `{kind,props,children}` node) — `viewPatch` appends to
    /// it, serializes it into the home heap, and bumps the view version via a real turn.
    view_tree: serde_json::Value,
    /// Every committed receipt hash, in order — the app's audit tape.
    receipts: Vec<[u8; 32]>,
    /// The per-agent authority head (`previous_receipt_hash`). The executor advances this
    /// ONLY for the submitting agent, so EACH acting cell chains its own turns; a global
    /// head would mis-link a second cell's first turn.
    heads: BTreeMap<CellId, [u8; 32]>,
}

impl Default for CellWorld {
    fn default() -> Self {
        Self::new()
    }
}

impl CellWorld {
    /// Boot an empty world on a fresh embedded executor in `Symbolic` witness mode (the
    /// cheap local end — the state transition + every gate run identically; only the
    /// publishable Merkle commitment is deferred), exactly as `deos-js::applet`.
    pub fn new() -> Self {
        let engine = DreggEngine::new(EngineConfig::for_testing());
        engine
            .executor()
            .set_witness_mode(dregg_turn::collapse::WitnessMode::Symbolic);
        CellWorld {
            engine,
            cells: BTreeMap::new(),
            home: None,
            view_tree: serde_json::json!({ "kind": "column", "props": {}, "children": [] }),
            receipts: Vec::new(),
            heads: BTreeMap::new(),
        }
    }

    /// Mint a cell onto the shared ledger AND record a cap-table row for it under `name`:
    /// the JS app holds `held` toward this cell and may fire its `affordances`. Returns the
    /// minted cell id.
    pub fn add_cell(
        &mut self,
        name: &str,
        public_key: [u8; 32],
        token_id: [u8; 32],
        balance: i64,
        seed_fields: &[(Slot, u64)],
        affordances: Vec<Affordance>,
        held: AuthRequired,
    ) -> CellId {
        let id = self.mint_cell(public_key, token_id, balance, seed_fields);
        self.cells.insert(
            name.to_string(),
            CellEntry {
                id,
                held,
                affordances,
            },
        );
        id
    }

    /// Mint a cell onto the shared ledger but record **no** cap-table row: the JS app holds
    /// NO capability to it, so it is unreachable from the sandbox (no handle names it).
    /// Used to prove confinement — the cell exists and stays untouched. Returns its id.
    pub fn add_uncapped_cell(
        &mut self,
        public_key: [u8; 32],
        token_id: [u8; 32],
        balance: i64,
        seed_fields: &[(Slot, u64)],
    ) -> CellId {
        self.mint_cell(public_key, token_id, balance, seed_fields)
    }

    fn mint_cell(
        &mut self,
        public_key: [u8; 32],
        token_id: [u8; 32],
        balance: i64,
        seed_fields: &[(Slot, u64)],
    ) -> CellId {
        let mut cell = Cell::with_balance(public_key, token_id, balance);
        cell.permissions = open_permissions();
        for (slot, value) in seed_fields {
            cell.state.set_field(*slot, pack_u64(*value));
        }
        let id = cell.id();
        self.engine
            .ledger_mut()
            .insert_cell(cell)
            .expect("seed a world cell onto the embedded ledger");
        id
    }

    /// Designate the home cell (the `t`/`get`/`viewPatch` default target). Must already be
    /// a capped cell.
    pub fn set_home(&mut self, name: &str) {
        debug_assert!(self.cells.contains_key(name), "home cell must be capped");
        self.home = Some(name.to_string());
    }

    /// The home cell's name, if set.
    pub fn home(&self) -> Option<&str> {
        self.home.as_deref()
    }

    /// The committed receipt tape (what the JS app left on the ledger), in order.
    pub fn receipts(&self) -> &[[u8; 32]] {
        &self.receipts
    }

    /// The home cell's current view-tree node.
    pub fn view_tree(&self) -> &serde_json::Value {
        &self.view_tree
    }

    /// Resolve a cell handle — the ocap gate. An absent handle is a cell the JS holds no
    /// capability to: [`FireError::NoCapability`].
    fn entry(&self, name: &str) -> Result<&CellEntry, FireError> {
        self.cells
            .get(name)
            .ok_or_else(|| FireError::NoCapability(name.to_string()))
    }

    fn id_of(&self, name: &str) -> Result<CellId, FireError> {
        self.entry(name).map(|e| e.id)
    }

    /// The live nonce of a cell (chains its next turn).
    fn nonce(&self, id: CellId) -> u64 {
        self.engine
            .ledger()
            .get(&id)
            .map(|c| c.state.nonce())
            .unwrap_or(0)
    }

    /// Witnessed read of `slot` on the cell named `name`, as a `u64`, off the live ledger.
    /// `NoCapability` if the JS holds no handle to that cell.
    pub fn get_slot(&self, name: &str, slot: Slot) -> Result<u64, FireError> {
        let id = self.id_of(name)?;
        Ok(self
            .engine
            .ledger()
            .get(&id)
            .and_then(|c| c.state.get_field(slot).copied())
            .map(|fe| unpack_u64(&fe))
            .unwrap_or(0))
    }

    /// Witnessed read of `slot` on the **home** cell.
    pub fn get_home_slot(&self, slot: Slot) -> Result<u64, FireError> {
        let home = self
            .home
            .clone()
            .ok_or_else(|| FireError::NoCapability("<home>".into()))?;
        self.get_slot(&home, slot)
    }

    /// The biased computron balance of the cell named `name`.
    pub fn balance(&self, name: &str) -> Result<i64, FireError> {
        let id = self.id_of(name)?;
        Ok(self
            .engine
            .ledger()
            .get(&id)
            .map(|c| c.state.balance())
            .unwrap_or(0))
    }

    /// Read a cell directly off the shared ledger by id — including cells the JS holds NO
    /// cap to. The host uses this to PROVE an uncapped cell stayed untouched; it is not a
    /// capability the sandbox can reach (the JS has no cell ids).
    pub fn cell_on_ledger(&self, id: CellId) -> Option<&Cell> {
        self.engine.ledger().get(&id)
    }

    /// The home cell's committed view-tree blob (what a renderer reads), if any — the
    /// witness side of [`CellWorld::view_patch`].
    pub fn home_view_blob(&self) -> Option<Vec<u8>> {
        let home = self.home.as_ref()?;
        let id = self.cells.get(home)?.id;
        read_view_blob(self.engine.ledger().get(&id)?)
    }

    /// **Fire an affordance on the home cell** (the `t(turn,arg)` host fn).
    pub fn fire_home(&mut self, affordance: &str, arg: i64) -> Result<Fired, FireError> {
        let home = self
            .home
            .clone()
            .ok_or_else(|| FireError::NoCapability("<home>".into()))?;
        self.fire_on(&home, affordance, arg)
    }

    /// **Fire an affordance on ANOTHER cell** (the `tCell(cell,turn,arg)` host fn) — the
    /// keystone of multi-cell coordination. Goes through the SAME path a home fire does:
    ///
    /// 1. resolve the cell handle (absent ⇒ [`FireError::NoCapability`], the cell is never
    ///    touched);
    /// 2. resolve the affordance (unknown ⇒ no turn);
    /// 3. **cap tooth, in-band**: the held cap for THIS cell must satisfy the affordance's
    ///    `required` (`dregg_cell::is_attenuation`) — an over-reach commits NOTHING;
    /// 4. compute the write as a pure function of the live model;
    /// 5. build + `execute_turn` the verified turn, AS the target cell (single-custody
    ///    embedded world — the JS holds the cap, acts as the cell), chaining that cell's
    ///    own authority head.
    pub fn fire_on(
        &mut self,
        cell_name: &str,
        affordance: &str,
        arg: i64,
    ) -> Result<Fired, FireError> {
        let entry = self.entry(cell_name)?;
        let id = entry.id;
        let aff = entry
            .affordances
            .iter()
            .find(|a| a.name == affordance)
            .cloned()
            .ok_or_else(|| FireError::UnknownAffordance(affordance.to_string()))?;

        // (3) the REAL cap tooth, in-band, against the cap held FOR THIS cell.
        if !dregg_cell::is_attenuation(&entry.held, &aff.required) {
            return Err(FireError::Unauthorized(affordance.to_string()));
        }

        // (4) write = pure function of the live model.
        let slot = aff.op.slot();
        let current = self.get_slot(cell_name, slot)?;
        let (slot, value) = aff.op.write(current, arg);

        // (5) build + execute the verified turn AS the target cell.
        let action = ActionBuilder::new_unchecked_for_tests(id, affordance, id)
            .effect_set_field(id, slot, value)
            .effect_increment_nonce(id)
            .build();
        let receipt = self.commit(id, action)?;
        let rh = receipt.receipt_hash();
        Ok(Fired {
            receipt_hash: rh,
            value: self.get_slot(cell_name, slot)? as i64,
        })
    }

    /// **Move value between two cells the JS holds caps to** (the `transfer` host fn). Both
    /// the spender `from` and the recipient `to` must be capped handles (you cannot move
    /// value into or out of a cell you hold no cap to). The turn is submitted AS `from`;
    /// the executor enforces conservation (sufficient balance, the balance net change sums
    /// to zero across the moved value, the fee paid by `from`). Returns `from`'s new
    /// balance.
    pub fn transfer(&mut self, from: &str, to: &str, amount: u64) -> Result<i64, FireError> {
        let from_id = self.id_of(from)?;
        let to_id = self.id_of(to)?;
        let action = ActionBuilder::new_unchecked_for_tests(from_id, "transfer", from_id)
            .effect_transfer(from_id, to_id, amount)
            .effect_increment_nonce(from_id)
            .build();
        self.commit(from_id, action)?;
        self.balance(from)
    }

    /// **A receipted self-edit of the home cell's view-tree** (the `viewPatch` host fn).
    /// Appends `node` to the home view-tree's children, serializes the tree into the home
    /// cell's committed heap (the chunked `VIEWTREE_COLL` blob — so `heap_root` moves), and
    /// bumps [`VIEW_VERSION_SLOT`] through a real `SetField` turn (the receipt that
    /// witnesses the edit). A light client sees the surface evolve exactly as it sees the
    /// model evolve. Returns the new view version.
    pub fn view_patch(&mut self, node: serde_json::Value) -> Result<u64, FireError> {
        let home = self
            .home
            .clone()
            .ok_or_else(|| FireError::NoCapability("<home>".into()))?;
        let id = self.id_of(&home)?;

        // Append the node to the home view-tree's children.
        if let Some(children) = self
            .view_tree
            .get_mut("children")
            .and_then(|c| c.as_array_mut())
        {
            children.push(node);
        }

        // Serialize the tree into the home cell's committed heap (the chunked blob the
        // renderer reads), in place on the ledger — this moves `heap_root`.
        let blob = serde_json::to_vec(&self.view_tree).expect("the view-tree serializes");
        write_view_blob(&mut self.engine, id, &blob);

        // Bump the view version through a real verified turn — the receipt that witnesses
        // the self-edit (mirroring `card_editor`'s provenance turn).
        let next = self.get_slot(&home, VIEW_VERSION_SLOT)? + 1;
        let action = ActionBuilder::new_unchecked_for_tests(id, "__view_patch__", id)
            .effect_set_field(id, VIEW_VERSION_SLOT, pack_u64(next))
            .effect_increment_nonce(id)
            .build();
        self.commit(id, action)?;
        Ok(next)
    }

    /// Build + execute a verified turn submitted AS `agent`, chaining that agent's own
    /// authority head, and record the receipt on the tape.
    fn commit(
        &mut self,
        agent: CellId,
        action: dregg_turn::Action,
    ) -> Result<TurnReceipt, FireError> {
        let nonce = self.nonce(agent);
        let mut tb = TurnBuilder::new(agent, nonce);
        tb.set_fee(10_000);
        if let Some(prev) = self.heads.get(&agent) {
            tb.set_previous_receipt_hash(*prev);
        }
        tb.add_action(action);
        let turn = tb.build();
        let receipt = self
            .engine
            .execute_turn(&turn)
            .map_err(|e| FireError::Executor(e.to_string()))?;
        let rh = receipt.receipt_hash();
        self.heads.insert(agent, rh);
        self.receipts.push(rh);
        Ok(receipt)
    }
}

/// Write a view-tree blob into a cell's committed heap (collection [`VIEWTREE_COLL`]) — key
/// 0 = the u64 length header, keys `1..` = the 31-byte payload chunks. The SAME codec
/// `deos-view::mount` and `deos-js::portable` use. Mutating the heap re-seals `heap_root`,
/// so the view-tree is part of the cell's committed state.
fn write_view_blob(engine: &mut DreggEngine, id: CellId, blob: &[u8]) {
    let cell = engine
        .ledger_mut()
        .get_mut(&id)
        .expect("the home cell is present on its own ledger");
    let mut header = [0u8; 32];
    header[..8].copy_from_slice(&(blob.len() as u64).to_le_bytes());
    cell.state.set_heap(VIEWTREE_COLL, 0, header);
    for (i, chunk) in blob.chunks(CHUNK_BYTES).enumerate() {
        let mut leaf = [0u8; 32];
        leaf[0] = chunk.len() as u8;
        leaf[1..1 + chunk.len()].copy_from_slice(chunk);
        cell.state.set_heap(VIEWTREE_COLL, (i + 1) as u32, leaf);
    }
}

/// Read a view-tree blob back out of a cell's committed heap. `None` if no header leaf is
/// present (the cell carries no view-tree). The witness side of [`write_view_blob`].
pub fn read_view_blob(cell: &Cell) -> Option<Vec<u8>> {
    let header = cell.state.get_heap(VIEWTREE_COLL, 0)?;
    let mut len_bytes = [0u8; 8];
    len_bytes.copy_from_slice(&header[..8]);
    let total = u64::from_le_bytes(len_bytes) as usize;
    let mut out = Vec::with_capacity(total);
    let mut key: u32 = 1;
    while out.len() < total {
        let leaf = cell.state.get_heap(VIEWTREE_COLL, key)?;
        let fill = leaf[0] as usize;
        out.extend_from_slice(&leaf[1..1 + fill]);
        key += 1;
    }
    out.truncate(total);
    Some(out)
}
