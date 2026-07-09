//! THE NODE AS A CELL — the reflexive image (the first Hearth step).
//!
//! The node already wraps an operator cell + a ledger and already serves its own
//! runtime status piecemeal (`GET /api/node/identity`, `GET /api/node/producer`,
//! `GET /status`). "self-as-cell" was UNDER-NAMED, not absent. This module
//! *collects* that already-tracked self-status onto ONE cell-shaped view so the
//! node stops being an opaque server and becomes an inspectable cell: deos-js (or
//! anything holding the gpui-free [`deos_reflect`]) can `reflect()` the node the
//! same way it reflects any sovereign cell.
//!
//! ## What this is (and is NOT)
//!
//! - It is a LIVE projection: every field comes from the live [`NodeStateInner`]
//!   (and the blocklace DAG passed alongside), read under the same lock the HTTP
//!   handlers read. Re-project after a turn and the cell view moves — `ledger_height`,
//!   `peer_count`, the operator balance/nonce, the producer mode all track the
//!   running node. It is NOT a static stub.
//! - It is Reading A of `docs/NODE-REFRAME-SCOPE.md §2.3`: the node is the world's
//!   *representative* cell (identity + federation status + a commitment to the ledger
//!   it serves). It does NOT nest a sub-ledger (Reading B), which the flat ledger
//!   does not support today.
//!
//! ## The reflexive read-path (end-to-end)
//!
//! [`NodeSelfCell::to_ledger`] produces a real `dregg_cell::Ledger` carrying ONE
//! cell — the node-self-cell — whose state slots hold the live status (packed
//! `u64`s, the SAME little-endian low-8-byte shape deos-js's `applet::pack_u64`
//! uses, so a deos-js `bind(() => s[LEDGER_HEIGHT_SLOT])` reads the height back
//! verbatim). [`NodeSelfCell::reflect_json`] renders it through the EXACT
//! `deos_reflect::reflect_cell` the deos-js crawl (`reflect_binding::cell_json`)
//! calls — so what this module yields IS what deos-js would render.
//!
//! ## The `(cell, slot)` reactive surface
//!
//! The slot layout below is the binding key surface: a deos-js binding on
//! `(node_self_cell_id(), LEDGER_HEIGHT_SLOT)` wakes precisely when the height
//! moves (`deos-js/src/signals.rs`'s `BindingRegistry::invalidate`). The node's
//! commit path names the changed `(cell, slot)` when it re-projects; wiring that
//! emit into a live deos-js `BindingRegistry` is the remaining reactive-subscribe
//! step (the read-path here is what makes the node VISIBLE as a cell first).

use dregg_cell::state::{CellState, FieldElement};
use dregg_cell::{Cell, CellId, Ledger};

use crate::state::NodeStateInner;

// ─── The node-self-cell slot layout ───────────────────────────────────────────
//
// The state slots the live status is packed into. These are the `(cell, slot)`
// binding keys a deos-js reactive view subscribes to — naming them here is what
// makes the reactive surface stable across re-projections.

/// Slot 0 — the ledger height (the latest attested-root height the node serves).
pub const LEDGER_HEIGHT_SLOT: usize = 0;
/// Slot 1 — the blocklace DAG height (consensus tip).
pub const DAG_HEIGHT_SLOT: usize = 1;
/// Slot 2 — the number of finalized blocks the DAG has produced.
pub const BLOCK_COUNT_SLOT: usize = 2;
/// Slot 3 — the peer count (size of the configured federation peer set).
pub const PEER_COUNT_SLOT: usize = 3;
/// Slot 4 — the committee epoch (rotates with key rotations).
pub const COMMITTEE_EPOCH_SLOT: usize = 4;
/// Slot 5 — `1` when the verified Lean executor is the authoritative producer, else `0`.
pub const LEAN_PRODUCER_SLOT: usize = 5;
/// Slot 6 — `1` when a full-turn STARK is generated + verified per committed turn.
pub const FULL_TURN_PROVING_SLOT: usize = 6;
/// Slot 7 — `1` when consensus is live (the blocklace task is running), else `0`.
pub const CONSENSUS_LIVE_SLOT: usize = 7;
/// Slot 8 — `1` when the node is healthy (store reachable + consensus live + producing).
pub const HEALTHY_SLOT: usize = 8;
/// Slot 9 — `1` when the node runs solo (committee of one), else `0` (full federation).
pub const SOLO_SLOT: usize = 9;

/// Pack a `u64` into a [`FieldElement`] — little-endian low 8 bytes. This is the
/// SAME encoding `deos-js`'s `applet::pack_u64` uses, so a deos-js model read of a
/// node-self-cell slot (`field_u64`) decodes the live status verbatim.
fn pack_u64(v: u64) -> FieldElement {
    let mut fe = [0u8; 32];
    fe[..8].copy_from_slice(&v.to_le_bytes());
    fe
}

/// Pack a `bool` as `1`/`0` (so a deos-js `bind(() => s[slot] === 1)` reads it).
fn pack_bool(b: bool) -> FieldElement {
    pack_u64(b as u64)
}

/// The node's live runtime status, COLLECTED onto one struct from the fields the
/// node already serves piecemeal (`/api/node/identity`, `/api/node/producer`,
/// `/status`). This is the cell-shaped view's source of truth — every field is a
/// live read, nothing is fabricated.
// Reflexive node-as-cell view; some fields are informational and not yet read in the binary path.
#[derive(Clone, Debug)]
pub struct NodeSelfStatus {
    /// The operator's Ed25519 public key (the node's identity key).
    pub operator_public_key: [u8; 32],
    /// The operator's derived agent cell id (`derive_raw(public_key, H("default"))`)
    /// — the cell `/turn/submit` acts on by default. This IS the node-self-cell's id.
    pub operator_cell: CellId,
    /// The operator agent cell's live balance, if it exists in the ledger.
    pub operator_balance: i64,
    /// The operator agent cell's live nonce, if it exists in the ledger.
    pub operator_nonce: u64,
    /// The canonical ledger root the node currently serves (a commitment to the
    /// whole ledger this node hosts — the "self-as-host" evidence).
    pub ledger_root: [u8; 32],
    /// The latest attested-root height the node serves.
    pub ledger_height: u64,
    /// The blocklace DAG height (consensus tip).
    pub dag_height: u64,
    /// The number of finalized blocks the DAG has produced.
    pub block_count: u64,
    /// Whether consensus is live (the blocklace task is running).
    pub consensus_live: bool,
    /// The configured federation peer count.
    pub peer_count: u64,
    /// The canonical federation id (bound to the committee).
    pub federation_id: [u8; 32],
    /// The current committee epoch.
    pub committee_epoch: u64,
    /// Whether the verified Lean executor is the authoritative state producer.
    pub lean_producer: bool,
    /// Whether a full-turn STARK proof is generated + verified per committed turn.
    pub full_turn_proving: bool,
    /// Whether the node runs solo (committee of one) vs. full federation.
    pub is_solo: bool,
    /// Whether the node is healthy (store reachable + consensus live + producing).
    pub healthy: bool,
}

impl NodeSelfStatus {
    /// COLLECT the live self-status off a read-locked [`NodeStateInner`] plus the
    /// blocklace DAG facts (passed alongside because the blocklace handle sits
    /// behind its own async lock — the same split `api::get_status` makes).
    ///
    /// Every value here is the EXACT value the existing endpoints serve:
    /// `operator_*` mirrors `get_node_identity`, `lean_producer`/`full_turn_proving`
    /// mirror `get_producer_status`/`get_status`, `dag_height`/`block_count`/
    /// `consensus_live` are the DAG facts `get_status` reads.
    pub fn project(inner: &NodeStateInner, dag: BlocklaceFacts) -> Self {
        let operator_public_key = inner.cclerk.public_key().0;
        let default_token_id = *blake3::hash(b"default").as_bytes();
        let operator_cell = CellId::derive_raw(&operator_public_key, &default_token_id);

        let (operator_balance, operator_nonce) = match inner.ledger.get(&operator_cell) {
            Some(cell) => (cell.state.balance(), cell.state.nonce()),
            None => (0, 0),
        };

        let ledger_root = crate::blocklace_sync::canonical_ledger_root(&inner.ledger);

        let ledger_height = inner
            .store
            .latest_attested_root()
            .ok()
            .flatten()
            .map(|r| r.height)
            .unwrap_or(0);

        let store_ok = inner.store.latest_attested_root().is_ok();
        let is_solo = inner.solo_consensus.as_ref().is_some_and(|s| s.is_solo);
        let healthy = store_ok && dag.consensus_live && dag.block_count > 0;

        NodeSelfStatus {
            operator_public_key,
            operator_cell,
            operator_balance,
            operator_nonce,
            ledger_root,
            ledger_height,
            dag_height: dag.dag_height,
            block_count: dag.block_count,
            consensus_live: dag.consensus_live,
            peer_count: inner.peers.len() as u64,
            federation_id: inner.federation_id,
            committee_epoch: inner.committee_epoch,
            lean_producer: inner.lean_producer_enabled,
            full_turn_proving: inner.full_turn_proving_enabled,
            is_solo,
            healthy,
        }
    }
}

/// The blocklace DAG facts the self-status needs but which live behind the
/// blocklace handle's own async lock (not in [`NodeStateInner`]). The caller reads
/// these from `state.blocklace()` exactly as `api::get_status` does, then hands
/// them in so the projection is one synchronous fold.
#[derive(Clone, Copy, Debug, Default)]
pub struct BlocklaceFacts {
    pub dag_height: u64,
    pub block_count: u64,
    pub consensus_live: bool,
}

/// The node projected AS A CELL — the reflexive image. Holds the node-self-cell id
/// and a one-cell [`Ledger`] carrying it, so the node can be reflected by the SAME
/// `deos_reflect::reflect_cell` deos-js's crawl uses.
pub struct NodeSelfCell {
    id: CellId,
    ledger: Ledger,
    status: NodeSelfStatus,
}

impl NodeSelfCell {
    /// Build the node-self-cell from the collected live status.
    ///
    /// The cell's identity IS the operator agent cell (so reflecting the node and
    /// reflecting its operator cell name the same sovereign id — the node is its
    /// operator cell, surfaced with its host status). Its `balance`/`nonce` are the
    /// operator cell's live value/nonce substances; its state slots carry the host
    /// status per the slot layout above. The cell is `Sovereign` and `Live`.
    pub fn from_status(status: NodeSelfStatus) -> Self {
        let default_token_id = *blake3::hash(b"default").as_bytes();
        let mut cell = Cell::new(status.operator_public_key, default_token_id);

        // VALUE substance — the operator cell's live balance/nonce.
        let mut state = CellState::new(status.operator_balance);
        state.set_nonce(status.operator_nonce);

        // STATE substance — the host status, packed per the slot layout (so a
        // deos-js binding reads it back through `field_u64`).
        state.set_field(LEDGER_HEIGHT_SLOT, pack_u64(status.ledger_height));
        state.set_field(DAG_HEIGHT_SLOT, pack_u64(status.dag_height));
        state.set_field(BLOCK_COUNT_SLOT, pack_u64(status.block_count));
        state.set_field(PEER_COUNT_SLOT, pack_u64(status.peer_count));
        state.set_field(COMMITTEE_EPOCH_SLOT, pack_u64(status.committee_epoch));
        state.set_field(LEAN_PRODUCER_SLOT, pack_bool(status.lean_producer));
        state.set_field(FULL_TURN_PROVING_SLOT, pack_bool(status.full_turn_proving));
        state.set_field(CONSENSUS_LIVE_SLOT, pack_bool(status.consensus_live));
        state.set_field(HEALTHY_SLOT, pack_bool(status.healthy));
        state.set_field(SOLO_SLOT, pack_bool(status.is_solo));

        cell.state = state;
        let id = cell.id();

        let mut ledger = Ledger::new();
        // A fresh one-cell ledger: this insert cannot collide.
        let _ = ledger.insert_cell(cell);

        NodeSelfCell { id, ledger, status }
    }

    /// COLLECT + project + build in one step from a read-locked node state.
    pub fn project(inner: &NodeStateInner, dag: BlocklaceFacts) -> Self {
        Self::from_status(NodeSelfStatus::project(inner, dag))
    }

    /// The node-self-cell id (== the operator agent cell id). The `(cell, _)` half
    /// of every reactive binding key on the node.
    pub fn id(&self) -> CellId {
        self.id
    }

    /// The collected status (the live source the cell view was built from).
    pub fn status(&self) -> &NodeSelfStatus {
        &self.status
    }

    /// The one-cell ledger carrying the node-self-cell — the `WorldSink`-shaped
    /// READ surface. A deos-js `WorldSink::with_ledger` over the node hands back
    /// exactly this; deos-js's `world_cells_json` lists the node-self-cell and
    /// `cell_json(ledger, id)` reflects it.
    pub fn ledger(&self) -> &Ledger {
        &self.ledger
    }

    /// `WorldSink::with_ledger`-shaped read: run `f` over a borrow of the one-cell
    /// ledger. This is the precise closure-passing shape the deos-js
    /// [`WorldSink`](../../../deos-js/src/attach.rs) trait requires for the crawl —
    /// the node implements the read leg of the seam here (no SpiderMonkey pulled in:
    /// the trait's read contract is satisfied structurally).
    pub fn with_ledger(&self, f: &mut dyn FnMut(&Ledger)) {
        f(&self.ledger);
    }

    /// REFLECT the node-self-cell to JSON through `deos_reflect::reflect_cell` — the
    /// EXACT reflector deos-js's `reflect_binding::cell_json` calls. The string this
    /// returns IS what deos-js's `deos.cell(node_id).reflect()` would render against
    /// a `WorldSink` backed by [`Self::with_ledger`]. The reflexive image, end-to-end.
    ///
    /// Reflection is an attested READ that confers no authority (committed slots
    /// surface their commitment, never the value) — here every host-status slot is
    /// public, so it renders as a revealed `FieldSlot`.
    // Consumed by the `GET /api/node/self` route + the dregg-mcp reflect surface,
    // both of which live in `api.rs` (a parallel lane); exercised here by the tests.
    pub fn reflect_json(&self) -> String {
        let cell = self
            .ledger
            .get(&self.id)
            .expect("node-self-cell is present in its own one-cell ledger");
        let insp = deos_reflect::reflect_cell(&self.id, cell);
        inspectable_to_json(&insp)
    }
}

/// Serialize a [`deos_reflect::Inspectable`] to JSON. Mirrors the shape deos-js's
/// `reflect_binding::inspectable_json` emits (kind/title/subtitle/fields) so the
/// node's reflexive render is wire-shaped like every other deos-js cell reflection.
fn inspectable_to_json(insp: &deos_reflect::Inspectable) -> String {
    use deos_reflect::substance::{FieldValue, hex_encode};

    fn esc(s: &str) -> String {
        let mut out = String::with_capacity(s.len() + 2);
        for c in s.chars() {
            match c {
                '"' => out.push_str("\\\""),
                '\\' => out.push_str("\\\\"),
                '\n' => out.push_str("\\n"),
                _ => out.push(c),
            }
        }
        out
    }

    fn field_value_json(v: &FieldValue) -> (&'static str, String) {
        match v {
            FieldValue::Text(s) => ("text", format!("\"{}\"", esc(s))),
            FieldValue::Balance(b) => ("balance", b.to_string()),
            FieldValue::Count(c) => ("count", c.to_string()),
            FieldValue::Bool(b) => ("bool", b.to_string()),
            FieldValue::Id(id) => ("id", format!("\"{}\"", hex_encode(id))),
            FieldValue::Hash(h) => ("hash", format!("\"{}\"", hex_encode(h))),
            FieldValue::CapEdge { target, slot } => (
                "capEdge",
                format!(
                    "{{\"target\":\"{}\",\"slot\":{}}}",
                    hex_encode(target),
                    slot
                ),
            ),
            FieldValue::FieldSlot { index, hex } => (
                "fieldSlot",
                format!("{{\"index\":{},\"hex\":\"{}\"}}", index, esc(hex)),
            ),
            FieldValue::CommittedSlot { index, commitment } => (
                "committedSlot",
                format!(
                    "{{\"index\":{},\"commitment\":\"{}\",\"redacted\":true}}",
                    index,
                    hex_encode(commitment)
                ),
            ),
        }
    }

    let fields: Vec<String> = insp
        .fields
        .iter()
        .map(|f| {
            let (ty, val) = field_value_json(&f.value);
            format!(
                "{{\"key\":\"{}\",\"type\":\"{}\",\"value\":{}}}",
                esc(&f.key),
                ty,
                val
            )
        })
        .collect();
    format!(
        "{{\"kind\":\"{:?}\",\"title\":\"{}\",\"subtitle\":\"{}\",\"fields\":[{}]}}",
        insp.kind,
        esc(&insp.title),
        esc(&insp.subtitle),
        fields.join(","),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A status fixture with distinct, recognizable values per field.
    fn fixture() -> NodeSelfStatus {
        NodeSelfStatus {
            operator_public_key: [7u8; 32],
            operator_cell: CellId::derive_raw(&[7u8; 32], blake3::hash(b"default").as_bytes()),
            operator_balance: 4242,
            operator_nonce: 9,
            ledger_root: [3u8; 32],
            ledger_height: 100,
            dag_height: 105,
            block_count: 101,
            consensus_live: true,
            peer_count: 4,
            federation_id: [5u8; 32],
            committee_epoch: 2,
            lean_producer: true,
            full_turn_proving: false,
            is_solo: false,
            healthy: true,
        }
    }

    /// Read a node-self-cell slot back as a u64 the SAME way deos-js's
    /// `CellModel::field_u64` would (little-endian low 8 bytes) — the bridge that
    /// makes a deos-js `bind(() => s[slot])` read the live status verbatim.
    fn slot_u64(cell: &Cell, slot: usize) -> u64 {
        let fe = cell.state.get_field(slot).copied().unwrap_or([0u8; 32]);
        let mut b = [0u8; 8];
        b.copy_from_slice(&fe[..8]);
        u64::from_le_bytes(b)
    }

    /// The node-self-cell carries the live status on its slots, decodable with the
    /// SAME little-endian shape deos-js reads — not a static/opaque stub.
    #[test]
    fn self_cell_slots_carry_live_status() {
        let status = fixture();
        let node_cell = NodeSelfCell::from_status(status.clone());
        let cell = node_cell.ledger().get(&node_cell.id()).unwrap();

        // VALUE substance: the operator cell's balance/nonce.
        assert_eq!(cell.state.balance(), 4242);
        assert_eq!(cell.state.nonce(), 9);

        // STATE substance: the host status, per the slot layout, deos-js-decodable.
        assert_eq!(slot_u64(cell, LEDGER_HEIGHT_SLOT), 100);
        assert_eq!(slot_u64(cell, DAG_HEIGHT_SLOT), 105);
        assert_eq!(slot_u64(cell, BLOCK_COUNT_SLOT), 101);
        assert_eq!(slot_u64(cell, PEER_COUNT_SLOT), 4);
        assert_eq!(slot_u64(cell, COMMITTEE_EPOCH_SLOT), 2);
        assert_eq!(slot_u64(cell, LEAN_PRODUCER_SLOT), 1);
        assert_eq!(slot_u64(cell, FULL_TURN_PROVING_SLOT), 0);
        assert_eq!(slot_u64(cell, CONSENSUS_LIVE_SLOT), 1);
        assert_eq!(slot_u64(cell, HEALTHY_SLOT), 1);
        assert_eq!(slot_u64(cell, SOLO_SLOT), 0);
    }

    /// The node-self-cell id == the operator agent cell id (`derive_raw`), so
    /// reflecting the node names the same sovereign id deos-js crawls.
    #[test]
    fn self_cell_id_is_operator_agent_cell() {
        let status = fixture();
        let node_cell = NodeSelfCell::from_status(status.clone());
        assert_eq!(node_cell.id(), status.operator_cell);
    }

    /// THE REFLEXIVE READ-PATH: `with_ledger` (the `WorldSink`-shaped read) hands
    /// back a ledger whose ONLY cell is the node-self-cell — exactly what deos-js's
    /// `world_cells_json` + `cell_json` would crawl.
    #[test]
    fn with_ledger_exposes_exactly_the_node_self_cell() {
        let node_cell = NodeSelfCell::from_status(fixture());
        let mut ids: Vec<CellId> = Vec::new();
        node_cell.with_ledger(&mut |l| {
            ids = l.iter().map(|(id, _)| *id).collect();
        });
        assert_eq!(ids, vec![node_cell.id()]);
    }

    /// THE REFLEXIVE IMAGE, END-TO-END: reflecting the node through the SAME
    /// `deos_reflect::reflect_cell` deos-js uses yields the live status as a cell
    /// view — balance, nonce, and the host-status slots all present in the JSON.
    #[test]
    fn reflect_json_renders_node_as_a_live_cell() {
        let node_cell = NodeSelfCell::from_status(fixture());
        let json = node_cell.reflect_json();

        // It is a Cell reflection (the uniform reflective object).
        assert!(json.contains("\"kind\":\"Cell\""));
        // VALUE substance present: the operator balance (4242) renders as a balance field.
        assert!(json.contains("\"key\":\"balance\""));
        assert!(json.contains("4242"));
        // The nonce (9) renders.
        assert!(json.contains("\"key\":\"nonce\""));
        // STATE substance present: the host-status slots render as fieldSlots
        // (the live status, surfaced on the cell). At least the height slot is non-zero.
        assert!(json.contains("\"key\":\"state[0]\""));
        assert!(json.contains("fieldSlot"));
    }

    /// IT UPDATES ON CHANGE (not static): a node that has advanced (more blocks,
    /// higher operator nonce, a moved ledger height) reflects a DIFFERENT cell view
    /// — the reflexive image tracks the running node.
    #[test]
    fn reflect_tracks_live_node_state() {
        let before = NodeSelfCell::from_status(fixture());

        let mut advanced = fixture();
        advanced.ledger_height = 200;
        advanced.dag_height = 207;
        advanced.block_count = 201;
        advanced.operator_nonce = 17;
        advanced.operator_balance = 5000;
        advanced.full_turn_proving = true;
        let after = NodeSelfCell::from_status(advanced);

        // The cell views differ — the height slot moved, the nonce moved.
        let before_cell = before.ledger().get(&before.id()).unwrap();
        let after_cell = after.ledger().get(&after.id()).unwrap();
        assert_ne!(
            slot_u64(before_cell, LEDGER_HEIGHT_SLOT),
            slot_u64(after_cell, LEDGER_HEIGHT_SLOT)
        );
        assert_eq!(slot_u64(after_cell, LEDGER_HEIGHT_SLOT), 200);
        assert_eq!(after_cell.state.nonce(), 17);
        assert_eq!(after_cell.state.balance(), 5000);
        // The full-turn-proving bit flipped on.
        assert_eq!(slot_u64(before_cell, FULL_TURN_PROVING_SLOT), 0);
        assert_eq!(slot_u64(after_cell, FULL_TURN_PROVING_SLOT), 1);

        // And the reflected JSON differs (the reflexive image moved with the node).
        assert_ne!(before.reflect_json(), after.reflect_json());
    }
}
