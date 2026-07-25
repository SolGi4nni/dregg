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

use dregg_cell::interface::{method_symbol, InterfaceDescriptor, Semantics};
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
    /// The cell's affordance surface (the directions of its interface) — the *execution
    /// bodies* (each [`Affordance::op`] computes the write). When a typed `interface` is
    /// published, the affordance is found by the method name the interface routed to.
    affordances: Vec<Affordance>,
    /// The cell's **published, typed interface** (the same content-addressed
    /// [`InterfaceDescriptor`] the real kvstore/escrow cells publish). When present, a
    /// `tCell(cell, "method", ..)` resolves the method through the verified DFA
    /// `route_method` — the SAME dispatch path `invoke()` speaks — so the JS names a TYPED
    /// METHOD (cap + replayable-vs-serviced semantics come from the published `MethodSig`),
    /// not a bare local affordance. Absent ⇒ the legacy affordance-name path.
    interface: Option<InterfaceDescriptor>,
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

/// The **guard** of a compound turn — the state precondition the WHOLE action is gated
/// on. The compound commits only if the actor cell's `slot` currently equals `value`,
/// enforced as a real kernel `require_field_equals` precondition: it is checked BEFORE any
/// effect runs (so a failed guard refuses the whole action — no partial), and it binds into
/// the action commitment (`Action::hash` folds preconditions in, the anti-downgrade hash),
/// so a LIGHT CLIENT — not just a re-executing validator — witnesses the guard that gated
/// the move. This is the escrow's missing "only-if-SETTLED" link, made a single witnessed
/// turn.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BatchGuard {
    /// The actor cell's state slot the guard reads.
    pub slot: Slot,
    /// The value that slot must currently hold for the compound to commit.
    pub value: u64,
}

/// One leg of a compound atomic turn — a single effect that commits with the others or not
/// at all. Both lower to ordinary effects the executor already enforces and a light client
/// already witnesses; the *atomicity* (all-or-none) is the executor's per-action journal —
/// "if any action fails, ALL effects are rolled back via journal replay".
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BatchOp {
    /// Move value from the actor to a capped recipient (e.g. escrow -> seller). The
    /// recipient must be a capped handle; a leg naming an unheld cell refuses the WHOLE
    /// batch ([`FireError::NoCapability`]) before any effect — the ocap gate, all-or-none.
    Transfer {
        /// The recipient handle (must be in the cap table).
        to: String,
        /// The value moved.
        amount: u64,
    },
    /// Write a fixed value to one of the actor's own slots (e.g. flip a state machine to
    /// SETTLED). Lowers to `Effect::SetField` on the actor cell.
    SetSlot {
        /// The actor slot written.
        slot: Slot,
        /// The value written.
        value: u64,
    },
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
                interface: None,
            },
        );
        id
    }

    /// **Publish a typed [`InterfaceDescriptor`] on a capped cell** — the route_method
    /// bridge. After this, a `tCell(name, "method", ..)` resolves the method through the
    /// cell's published interface via the verified DFA [`InterfaceDescriptor::route_method`]
    /// (the SAME dispatch `invoke()` speaks), so the JS names a TYPED METHOD: the cap gate
    /// and the replayable-vs-serviced bit come from the published `MethodSig`, and a method
    /// absent from the interface is fail-closed [`FireError::MethodNotRouted`]. The
    /// descriptor mirrors what the cell commits as its `InterfaceRef`, exactly the
    /// kvstore/escrow shape. Panics in debug if `name` is not a capped cell.
    pub fn publish_interface(&mut self, name: &str, descriptor: InterfaceDescriptor) {
        debug_assert!(
            self.cells.contains_key(name),
            "publish_interface: {name} must be a capped cell"
        );
        if let Some(entry) = self.cells.get_mut(name) {
            entry.interface = Some(descriptor);
        }
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

    /// Resolve the cap requirement for a `method` on a capped cell — the SAME routing the
    /// `tCell` fire path uses, factored out so the commit-reveal primitives gate identically.
    /// With a published [`InterfaceDescriptor`] the requirement comes from the typed
    /// `MethodSig` via the verified DFA `route_method` (an undeclared method is fail-closed
    /// [`FireError::MethodNotRouted`], a [`Semantics::Serviced`] method is
    /// [`FireError::ServicedSeam`]); without one, from the bare affordance's own `required`.
    fn required_for(&self, entry: &CellEntry, method: &str) -> Result<AuthRequired, FireError> {
        match &entry.interface {
            Some(iface) => {
                let sym = method_symbol(method);
                let m = iface
                    .route_method(&sym)
                    .ok_or_else(|| FireError::MethodNotRouted(method.to_string()))?;
                if m.semantics == Semantics::Serviced {
                    return Err(FireError::ServicedSeam(method.to_string()));
                }
                Ok(m.auth_required.clone())
            }
            None => entry
                .affordances
                .iter()
                .find(|a| a.name == method)
                .map(|a| a.required.clone())
                .ok_or_else(|| FireError::UnknownAffordance(method.to_string())),
        }
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

    /// Witnessed read of the **full 32-byte field** at `slot` on the cell named `name` — the
    /// sealed-commitment reader. A cell-state field is a whole [`FieldElement`] even at a low
    /// slot index, so a 256-bit sealed commitment lives in ONE slot with NO truncation (the
    /// full BLAKE3 digest, not a folded u64). An absent field reads back all-zero, which the
    /// reveal-binding check treats as "no commitment sealed here". `NoCapability` if the JS
    /// holds no handle to that cell.
    pub fn get_seal(&self, name: &str, slot: Slot) -> Result<[u8; 32], FireError> {
        let id = self.id_of(name)?;
        Ok(self
            .engine
            .ledger()
            .get(&id)
            .and_then(|c| c.state.get_field(slot).copied())
            .unwrap_or([0u8; 32]))
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

    /// **Fire an affordance on the home cell** (the `t(turn, ...args)` host fn).
    pub fn fire_home(&mut self, affordance: &str, args: &[i64]) -> Result<Fired, FireError> {
        let home = self
            .home
            .clone()
            .ok_or_else(|| FireError::NoCapability("<home>".into()))?;
        self.fire_on(&home, affordance, args)
    }

    /// **Fire an affordance/method on ANOTHER cell** (the `tCell(cell, method, ...args)`
    /// host fn) — the keystone of multi-cell coordination. Goes through the SAME path a home
    /// fire does:
    ///
    /// 1. resolve the cell handle (absent ⇒ [`FireError::NoCapability`], the cell is never
    ///    touched);
    /// 2. **typed-method routing (the bridge)**: if the cell publishes an
    ///    [`InterfaceDescriptor`], `affordance` must route through it via the verified DFA
    ///    [`InterfaceDescriptor::route_method`] (the same dispatch `invoke()` speaks) — an
    ///    undeclared method is [`FireError::MethodNotRouted`], a
    ///    [`Semantics::Serviced`] method is [`FireError::ServicedSeam`] (a read, not a
    ///    turn), and the cap requirement comes from the published `MethodSig`. With no
    ///    published interface, `affordance` is resolved as a bare local affordance name and
    ///    the cap requirement is the affordance's own `required` (the legacy path);
    /// 3. resolve the execution body (the [`Affordance`] named by the method, unknown ⇒ no
    ///    turn);
    /// 4. **cap tooth, in-band**: the held cap for THIS cell must satisfy the resolved
    ///    requirement (`dregg_cell::is_attenuation`) — an over-reach commits NOTHING;
    /// 5. compute the write as a pure function of the live model + the JS args;
    /// 6. build + `execute_turn` the verified turn, AS the target cell (single-custody
    ///    embedded world — the JS holds the cap, acts as the cell), chaining that cell's
    ///    own authority head.
    pub fn fire_on(
        &mut self,
        cell_name: &str,
        affordance: &str,
        args: &[i64],
    ) -> Result<Fired, FireError> {
        let entry = self.entry(cell_name)?;
        let id = entry.id;

        // (2) typed-method routing: resolve the cap requirement either from the published
        //     interface (the route_method bridge) or the bare affordance (legacy path).
        let required = self.required_for(entry, affordance)?;

        // (3) resolve the execution body — the affordance the method name maps to.
        let aff = entry
            .affordances
            .iter()
            .find(|a| a.name == affordance)
            .cloned()
            .ok_or_else(|| FireError::UnknownAffordance(affordance.to_string()))?;

        // (4) the REAL cap tooth, in-band, against the cap held FOR THIS cell.
        if !dregg_cell::is_attenuation(&entry.held, &required) {
            return Err(FireError::Unauthorized(affordance.to_string()));
        }

        // (5) write = pure function of the live model + the JS args.
        let slot = aff.op.slot();
        let current = self.get_slot(cell_name, slot)?;
        let (slot, value) = aff.op.write(current, args);

        // (6) build + execute the verified turn AS the target cell.
        let action = ActionBuilder::new_unchecked_for_tests(id, affordance, id)
            .effect_set_field(id, slot as u64, value)
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

    /// **Fire an ATOMIC, STATE-GUARDED, COMPOUND turn** (the `batch` host fn) — the
    /// compound/conditional-turn power-up. ONE verified turn, submitted AS `actor`, that
    /// carries an OPTIONAL [`BatchGuard`] (a kernel `require_field_equals` precondition on
    /// the actor's own state) and a list of [`BatchOp`] legs (transfers + slot writes). The
    /// kernel commits it WHOLE or refuses it whole:
    ///
    ///   - **the guard is checked BEFORE any effect** ([`crate::world`] →
    ///     `executor::check_preconditions`, run ahead of effect application). If the actor's
    ///     guarded slot does not equal the guard value, the turn is refused
    ///     ([`FireError::Executor`] carrying `PreconditionFailed`) — NO transfer, NO slot
    ///     write, NO partial release;
    ///   - **the legs commit atomically** — multiple effects in one action are all-or-none
    ///     ("if any action fails, ALL effects are rolled back via journal replay"); if any
    ///     leg would fail (insufficient balance, an unheld recipient), NOTHING commits;
    ///   - **confinement holds** — every transfer recipient must be a capped handle; a leg
    ///     naming an unheld cell is [`FireError::NoCapability`] and refuses the whole batch
    ///     before it is built (the ocap gate, you cannot even name what you do not hold);
    ///   - **a light client witnesses the guard** — preconditions fold into `Action::hash`
    ///     (the anti-downgrade commitment), so the "only-if-SETTLED" link between the state
    ///     cell and the value move is part of what the turn proves, not an off-chain
    ///     ordering the JS happened to choose.
    ///
    /// This is the escrow's "release = check SETTLED ∧ transfer to seller, atomically" as a
    /// SINGLE witnessed turn. Returns the committed receipt hash.
    ///
    /// NAMED SEAM (honest): the kernel primitive used here is `Preconditions` +
    /// per-action atomicity — STRONGER than a bolt-on `Effect::ConditionalBatch` would be,
    /// because both are already kernel-enforced AND already in the action commitment. The
    /// one limit is that the guard reads the ACTOR's own state (the precondition evaluates
    /// against `action.target`, which is the actor): a cross-cell guard (commit on cell B's
    /// state, act on cell A) is not expressible through this single-actor action and would
    /// need a `witnessed`-clause precondition or a multi-party atomic turn. For the escrow
    /// the guard cell and the value-source are the same cell (the escrow), so the release is
    /// fully covered.
    pub fn guarded_batch(
        &mut self,
        actor: &str,
        guard: Option<BatchGuard>,
        ops: &[BatchOp],
    ) -> Result<[u8; 32], FireError> {
        let actor_id = self.id_of(actor)?;

        // Build the single compound action AS the actor (target = actor, so the guard
        // precondition evaluates against the actor's own committed state).
        let mut builder = ActionBuilder::new_unchecked_for_tests(actor_id, "batch", actor_id);

        // The guard becomes a real kernel precondition (checked ahead of every effect, and
        // bound into the action commitment — the light-client-witnessed "only-if").
        if let Some(g) = guard {
            builder = builder.require_field_equals(g.slot, pack_u64(g.value));
        }

        // Lower each leg to an ordinary effect. A transfer to an unheld cell refuses the
        // WHOLE batch here (the ocap gate — confinement, all-or-none) before it is built.
        for op in ops {
            builder = match op {
                BatchOp::Transfer { to, amount } => {
                    let to_id = self.id_of(to)?;
                    builder.effect_transfer(actor_id, to_id, *amount)
                }
                BatchOp::SetSlot { slot, value } => {
                    builder.effect_set_field(actor_id, *slot as u64, pack_u64(*value))
                }
            };
        }

        // One nonce bump per turn, then commit ONE atomic verified turn.
        let action = builder.effect_increment_nonce(actor_id).build();
        let receipt = self.commit(actor_id, action)?;
        Ok(receipt.receipt_hash())
    }

    /// **Commit a SEALED bid** (the `commitSeal` host fn) — the commit half of the
    /// commit-reveal power-up. Writes the 256-bit `seal` (a full [`FieldElement`], the BLAKE3
    /// digest the runtime-owned [`seal_commitment`] produced) into `slot` on the auction
    /// cell as ONE cap-gated verified turn, AS the auction cell. Three teeth:
    ///
    ///   - **cap gate, in-band**: the held cap toward the auction must satisfy the `commit`
    ///     method's published requirement (the SAME `is_attenuation` tooth / `route_method`
    ///     bridge `tCell` uses) — an over-reach commits NOTHING;
    ///   - **anti-front-running (WRITE-ONCE), in-band**: a non-zero field already at `slot`
    ///     means a bid is already sealed there — the commit is refused
    ///     ([`FireError::CommitmentMismatch`]) BEFORE any turn, so a committed bid can never
    ///     be overwritten (the sealed board is append-only, the front-running tooth);
    ///   - **phase gate (optional, light-client-witnessed)**: a `guard` lowers to a kernel
    ///     `require_field_equals` precondition (e.g. phase == COMMIT) folded into the action
    ///     commitment, so "no commit after the commit phase closes" is part of what the turn
    ///     proves, not an ordering the JS chose.
    ///
    /// The sealed digest HIDES the bid (the blinding nonce gives hiding even for a
    /// low-entropy value) and BINDS the bidder to exactly one bid — opened only at reveal.
    pub fn commit_seal(
        &mut self,
        auction: &str,
        slot: Slot,
        seal: [u8; 32],
        guard: Option<BatchGuard>,
    ) -> Result<[u8; 32], FireError> {
        let entry = self.entry(auction)?;
        let id = entry.id;
        let required = self.required_for(entry, "commit")?;
        if !dregg_cell::is_attenuation(&entry.held, &required) {
            return Err(FireError::Unauthorized("commit".to_string()));
        }

        // Anti-front-running WRITE-ONCE: a sealed bid is FROZEN the instant it is committed.
        // A non-zero field already at this slot is a committed bid — refuse in-band (free,
        // no fee), the sealed board is append-only.
        if self.get_seal(auction, slot)? != [0u8; 32] {
            return Err(FireError::CommitmentMismatch(format!(
                "a bid is already sealed at slot {slot} (write-once: no overwriting a committed bid)"
            )));
        }

        let mut builder = ActionBuilder::new_unchecked_for_tests(id, "commit", id);
        if let Some(g) = guard {
            builder = builder.require_field_equals(g.slot, pack_u64(g.value));
        }
        let action = builder
            .effect_set_field(id, slot as u64, seal)
            .effect_increment_nonce(id)
            .build();
        let receipt = self.commit(id, action)?;
        Ok(receipt.receipt_hash())
    }

    /// **Reveal a sealed bid** (the `revealBid` host fn) — the reveal half, and the keystone
    /// BINDING tooth. The runtime OWNS the seal function ([`seal_commitment`]), so a reveal
    /// binds to EXACTLY its commitment:
    ///
    ///   1. **cap gate, in-band**: the held cap must satisfy the published `reveal` method's
    ///      requirement (the same `is_attenuation` tooth);
    ///   2. **binding, in-band**: the committed seal is read back off `seal_slot`; the
    ///      runtime RE-HASHES the supplied `(bidder, value, nonce)` and compares all 256
    ///      bits. A mismatch — a switched value (peeking-then-switching), a wrong bidder, or
    ///      an absent (all-zero) commitment (a non-committed party) — is
    ///      [`FireError::CommitmentMismatch`], refused BEFORE any turn (nothing commits,
    ///      never reaches the executor); only a faithful opening proceeds;
    ///   3. **phase gate (optional, light-client-witnessed)**: a `guard` lowers to a kernel
    ///      `require_field_equals` precondition (e.g. phase == REVEAL) folded into the action
    ///      commitment, so "no reveal before the commit phase closes" is part of what the
    ///      turn proves;
    ///   4. the revealed `value` is written into `reveal_slot` as a verified turn — the bid
    ///      is now public AND provably bound to its earlier commitment (`winner_was_committed`
    ///      follows: only a faithfully-revealed bid carries a value to win on).
    #[allow(clippy::too_many_arguments)]
    pub fn reveal_bid(
        &mut self,
        auction: &str,
        seal_slot: Slot,
        reveal_slot: Slot,
        bidder: u64,
        value: u64,
        nonce: u64,
        guard: Option<BatchGuard>,
    ) -> Result<[u8; 32], FireError> {
        let entry = self.entry(auction)?;
        let id = entry.id;
        let required = self.required_for(entry, "reveal")?;
        if !dregg_cell::is_attenuation(&entry.held, &required) {
            return Err(FireError::Unauthorized("reveal".to_string()));
        }

        // (2) THE BINDING TOOTH: re-hash the opening and compare to the frozen seal. An
        // absent (all-zero) seal — a non-committed party — never matches; a switched value or
        // a wrong bidder never matches. Refused in-band before any turn.
        let committed = self.get_seal(auction, seal_slot)?;
        if committed == [0u8; 32] {
            return Err(FireError::CommitmentMismatch(format!(
                "no bid was sealed at slot {seal_slot} (a non-committed party cannot reveal)"
            )));
        }
        if seal_commitment(bidder, value, nonce) != committed {
            return Err(FireError::CommitmentMismatch(format!(
                "the opening (bidder={bidder}, value={value}, nonce={nonce}) does not match the sealed commitment at slot {seal_slot}"
            )));
        }

        let mut builder = ActionBuilder::new_unchecked_for_tests(id, "reveal", id);
        if let Some(g) = guard {
            builder = builder.require_field_equals(g.slot, pack_u64(g.value));
        }
        let action = builder
            .effect_set_field(id, reveal_slot as u64, pack_u64(value))
            .effect_increment_nonce(id)
            .build();
        let receipt = self.commit(id, action)?;
        Ok(receipt.receipt_hash())
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
            .effect_set_field(id, VIEW_VERSION_SLOT as u64, pack_u64(next))
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

/// The **runtime-owned sealed commitment** — `BLAKE3(bidder || value || nonce)`, the SAME
/// derive-key construction the real `starbridge-apps/sealed-auction` `Bid::seal` uses (and
/// the Rust image of the Lean `SealedAuction.sealOf`). The runtime owns this function so the
/// reveal-binding check ([`CellWorld::reveal_bid`]) and the commit a JS app publishes use the
/// IDENTICAL hash: under collision-resistance a sealed commitment opens to EXACTLY its bid
/// (binding), and the nonce blinds even a low-entropy value (hiding).
///
/// The digest is the full 32-byte BLAKE3 output stored in ONE cell-state field with NO
/// truncation, so the binding is the hash's full 256-bit second-preimage resistance — not a
/// folded u64. (The all-zero digest is treated by the reveal check as "no commitment"; a
/// genuine BLAKE3 output is all-zero with negligible probability.)
pub fn seal_commitment(bidder: u64, value: u64, nonce: u64) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-sealed-auction bid v1");
    hasher.update(&bidder.to_le_bytes());
    hasher.update(&value.to_le_bytes());
    hasher.update(&nonce.to_le_bytes());
    *hasher.finalize().as_bytes()
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
