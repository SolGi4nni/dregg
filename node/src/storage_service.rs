//! Storage gateway service — the ORGANS §3 weld.
//!
//! Connects three pieces that all existed but were disconnected:
//!
//! 1. **The content-addressed store** (`dregg-storage`: [`ContentStore`] with
//!    ownership / refcounting / quota metering) — previously unreachable from
//!    the node.
//! 2. **The verified StorageGatewayMandate cell**
//!    (`starbridge-storage-gateway-mandate`, seeded at boot as the
//!    `sgm-gateway` genesis cell) — op allowlist, key-prefix scope, GET
//!    clearance, and a volume budget whose law (`Monotonic volume_spent` +
//!    `volume_spent ≤ volume_ceiling`, the Lean `sgm_volume_legal_forever`
//!    keystone) is installed as the cell's program and therefore enforced by
//!    the **executor** on every committed turn that touches the cell.
//! 3. **HTTP routes** (`/storage/put|get|stat|list|quota`) that the browser
//!    extension calls (previously the dead `/files/*` routes).
//!
//! # Admission model (fail-closed)
//!
//! Every storage operation must be admitted by the mandate cell before any
//! byte is stored or returned:
//!
//! - **capability**: the node operator's agent cell must hold a c-list
//!   capability over the gateway cell (granted by
//!   `starbridge_seed::grant_operator_reach` when the cell is seeded). No
//!   capability ⇒ refuse.
//! - **op allowlist**: the requested op (GET/PUT/LIST) must be in the
//!   gateway's allowed set. Disallowed op ⇒ refuse.
//! - **prefix scope** (PUT): the object key must lie under the mandated key
//!   prefix, whose hash is pinned in the cell (`KEY_PREFIX_HASH_SLOT`).
//!   Outside the prefix ⇒ refuse.
//! - **clearance** (GET): the request must present the read-compartment
//!   label (header `x-dregg-clearance`) whose hash is pinned in the cell
//!   (`READ_COMPARTMENT_SLOT`). Missing/wrong ⇒ refuse.
//! - **volume budget**: each op debits the Stingray-style volume counter.
//!   The debit is committed as a real `storage_op` turn against the gateway
//!   cell through the node's authoritative executor path — where the cell
//!   program (`Monotonic` + `FieldLteField spent ≤ ceiling`) is the
//!   enforcement tooth. Over budget ⇒ refuse (both at the predicate mirror
//!   here and, independently, by the executor's program gate).
//!
//! The admission predicate mirrors the Lean `sgmAdmitM` exactly (we call the
//! SGM crate's `sgm_admit` as the oracle and `debug_assert` agreement).
//!
//! Out of scope (adopted design for later, per ORGANS §3): Willow 3D-area
//! caveats, range-based set reconciliation, the per-collection persistence
//! axis. The blob store here is in-memory (matching `ContentStore`).

use std::collections::{BTreeMap, HashMap};

use axum::body::Bytes;
use axum::extract::{Path as AxumPath, Query, State};
use axum::http::{HeaderMap, StatusCode, header};
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::{Json, Router};
use serde::{Deserialize, Serialize};

use dregg_cell::CellId;
use dregg_storage::content::ContentStore;
use dregg_storage::quota::SpaceBank;
use dregg_storage::{ContentHash, QuotaId};
use dregg_turn::action::{Event, symbol};
use dregg_turn::{CallForest, Effect, Turn, TurnResult};

use starbridge_storage_gateway_mandate::{
    COMMITMENT_ANCHOR_SLOT, DEFAULT_COMMITMENT_ANCHOR, DEFAULT_KEY_PREFIX,
    DEFAULT_READ_COMPARTMENT, KEY_PREFIX_HASH_SLOT, LAST_OP_SLOT, OBJECT_KEY_SLOT,
    READ_COMPARTMENT_SLOT, StorageOp, VOLUME_CEILING_SLOT, VOLUME_SPENT_SLOT, field_from_bytes,
    key_prefix_field, object_key_field, sgm_admit, sgm_child_program_vk,
};

use crate::state::{NodeState, NodeStateInner};

// =============================================================================
// Configuration
// =============================================================================

/// Storage-gateway service configuration. The values here feed the gateway
/// cell's one-time `init_gateway` binding (WriteOnce slots); after the cell is
/// initialized, ADMISSION reads the pinned commitments FROM THE CELL and this
/// config is only trusted insofar as it matches them (binding-checked on every
/// request — a mismatch refuses, fail-closed).
#[derive(Clone, Debug)]
pub struct StorageGatewayConfig {
    /// Mandated key prefix (PUT scope). The cell pins `blake3(key_prefix)`.
    pub key_prefix: String,
    /// GET read-compartment label. The cell pins `blake3(read_compartment)`.
    pub read_compartment: String,
    /// Volume ceiling bound into the cell at init (WriteOnce).
    pub volume_ceiling: u64,
    /// Commitment anchor bound into the cell at init (WriteOnce).
    pub commitment_anchor: u64,
    /// Op allowlist (Lean `opAllowed`).
    pub allowed_ops: Vec<StorageOp>,
    /// Computrons granted to the per-gateway quota cell in the space bank.
    pub quota_computrons: u64,
    /// Optional hard byte cap for the per-gateway quota cell.
    pub quota_max_bytes: Option<u64>,
}

impl StorageGatewayConfig {
    /// Defaults, overridable via `DREGG_STORAGE_VOLUME_CEILING`,
    /// `DREGG_STORAGE_KEY_PREFIX`, `DREGG_STORAGE_READ_COMPARTMENT`.
    pub fn from_env() -> Self {
        let volume_ceiling = std::env::var("DREGG_STORAGE_VOLUME_CEILING")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(1_000_000);
        let key_prefix = std::env::var("DREGG_STORAGE_KEY_PREFIX")
            .unwrap_or_else(|_| DEFAULT_KEY_PREFIX.to_string());
        let read_compartment = std::env::var("DREGG_STORAGE_READ_COMPARTMENT")
            .unwrap_or_else(|_| DEFAULT_READ_COMPARTMENT.to_string());
        Self {
            key_prefix,
            read_compartment,
            volume_ceiling,
            commitment_anchor: DEFAULT_COMMITMENT_ANCHOR,
            allowed_ops: vec![StorageOp::Get, StorageOp::Put, StorageOp::List],
            quota_computrons: 1 << 40,
            quota_max_bytes: None,
        }
    }
}

// =============================================================================
// Service state
// =============================================================================

/// A stored object record in the gateway's key index.
#[derive(Clone, Debug)]
pub struct StoredObject {
    pub hash: ContentHash,
    pub gateway: CellId,
    pub size: u64,
}

/// The storage-gateway service: the content-addressed store plus the
/// key → hash index. Lives inside [`NodeStateInner`] so route handlers mutate
/// it under the same global write lock as the ledger (admission reads ledger
/// state; the debit turn mutates it).
pub struct StorageGatewayService {
    pub config: StorageGatewayConfig,
    /// The content-addressed blob store (ownership / refcounting / quota).
    pub store: ContentStore,
    /// Per-gateway-cell quota in the store's space bank (lazily allocated;
    /// the gateway cell is the OWNER/payer of every blob it admits).
    quotas: HashMap<CellId, QuotaId>,
    /// Object key index (key → blob). `ContentStore` is nameless by design;
    /// the gateway layer owns naming, scoped under the mandate prefix.
    objects: BTreeMap<String, StoredObject>,
}

impl StorageGatewayService {
    pub fn new(config: StorageGatewayConfig) -> Self {
        // cost_per_byte=1: the quota meter charges a computron per byte.
        let bank = SpaceBank::new(1, 1, 0.5);
        Self {
            config,
            store: ContentStore::new(bank),
            quotas: HashMap::new(),
            objects: BTreeMap::new(),
        }
    }

    pub fn from_env() -> Self {
        Self::new(StorageGatewayConfig::from_env())
    }

    /// The quota cell paying for blobs admitted by `gateway` (lazily created).
    fn quota_for(&mut self, gateway: CellId) -> QuotaId {
        if let Some(q) = self.quotas.get(&gateway) {
            return *q;
        }
        let q = self.store.bank.allocate_quota(
            gateway.0,
            self.config.quota_computrons,
            self.config.quota_max_bytes,
        );
        self.quotas.insert(gateway, q);
        q
    }

    /// Reverse-lookup an object key for a content hash (for GET audit slots).
    fn key_for_hash(&self, hash: &ContentHash) -> Option<String> {
        self.objects
            .iter()
            .find(|(_, o)| o.hash == *hash)
            .map(|(k, _)| k.clone())
    }
}

// =============================================================================
// Refusals (fail-closed admission outcomes)
// =============================================================================

/// Every way a storage request can be refused. Mapped to an HTTP status +
/// machine-readable `reason` tag.
#[derive(Debug)]
pub enum StorageRefusal {
    /// Node cipherclerk is locked — no operator authority to exercise.
    Locked,
    /// No storage-gateway mandate cell resolvable (or the named cell is not
    /// an SGM cell). Without the mandate there is no admission: refuse.
    NoGateway(String),
    /// The operator's agent cell does not hold a capability over the gateway
    /// cell — the request presents no exercisable capability.
    NoCapability(String),
    /// The cell's pinned prefix/compartment/ceiling commitments do not match
    /// the service configuration — we cannot interpret the mandate's scope,
    /// so every op refuses.
    BindingMismatch(String),
    /// The op is not in the mandate's allowlist.
    OpNotAllowed(&'static str),
    /// PUT key outside the mandated prefix.
    PrefixViolation { key: String, prefix: String },
    /// GET without (or with wrong) read-compartment clearance.
    ClearanceDenied,
    /// The volume debit would exceed the ceiling.
    VolumeBudgetExceeded { spent: u64, cost: u64, ceiling: u64 },
    /// The authoritative executor rejected the debit turn (the cell-program
    /// enforcement tooth: Monotonic + spent ≤ ceiling).
    TurnRejected(String),
    /// The content store refused (quota exhausted, not found, not owner…).
    Store(String),
    /// Malformed request (bad hex, bad key, …).
    BadRequest(String),
    /// Blob not present.
    NotFound,
}

impl StorageRefusal {
    fn status(&self) -> StatusCode {
        match self {
            StorageRefusal::Locked
            | StorageRefusal::NoCapability(_)
            | StorageRefusal::OpNotAllowed(_)
            | StorageRefusal::PrefixViolation { .. }
            | StorageRefusal::ClearanceDenied
            | StorageRefusal::TurnRejected(_) => StatusCode::FORBIDDEN,
            StorageRefusal::NoGateway(_) | StorageRefusal::BindingMismatch(_) => {
                StatusCode::SERVICE_UNAVAILABLE
            }
            StorageRefusal::VolumeBudgetExceeded { .. } => StatusCode::INSUFFICIENT_STORAGE,
            StorageRefusal::Store(_) => StatusCode::INSUFFICIENT_STORAGE,
            StorageRefusal::BadRequest(_) => StatusCode::BAD_REQUEST,
            StorageRefusal::NotFound => StatusCode::NOT_FOUND,
        }
    }

    fn reason(&self) -> &'static str {
        match self {
            StorageRefusal::Locked => "locked",
            StorageRefusal::NoGateway(_) => "no-gateway",
            StorageRefusal::NoCapability(_) => "no-capability",
            StorageRefusal::BindingMismatch(_) => "binding-mismatch",
            StorageRefusal::OpNotAllowed(_) => "op-not-allowed",
            StorageRefusal::PrefixViolation { .. } => "prefix-violation",
            StorageRefusal::ClearanceDenied => "clearance-denied",
            StorageRefusal::VolumeBudgetExceeded { .. } => "volume-budget-exceeded",
            StorageRefusal::TurnRejected(_) => "turn-rejected",
            StorageRefusal::Store(_) => "store-refused",
            StorageRefusal::BadRequest(_) => "bad-request",
            StorageRefusal::NotFound => "not-found",
        }
    }

    fn detail(&self) -> String {
        match self {
            StorageRefusal::Locked => "node cipherclerk is locked".into(),
            StorageRefusal::NoGateway(d)
            | StorageRefusal::NoCapability(d)
            | StorageRefusal::BindingMismatch(d)
            | StorageRefusal::TurnRejected(d)
            | StorageRefusal::Store(d)
            | StorageRefusal::BadRequest(d) => d.clone(),
            StorageRefusal::OpNotAllowed(op) => {
                format!("op {op} is not in the mandate allowlist")
            }
            StorageRefusal::PrefixViolation { key, prefix } => {
                format!("key {key:?} is outside the mandated prefix {prefix:?}")
            }
            StorageRefusal::ClearanceDenied => {
                "missing or wrong read-compartment clearance (x-dregg-clearance)".into()
            }
            StorageRefusal::VolumeBudgetExceeded {
                spent,
                cost,
                ceiling,
            } => format!("volume budget exceeded: spent {spent} + cost {cost} > ceiling {ceiling}"),
            StorageRefusal::NotFound => "content not found".into(),
        }
    }
}

impl IntoResponse for StorageRefusal {
    fn into_response(self) -> Response {
        let body = serde_json::json!({
            "error": self.detail(),
            "reason": self.reason(),
        });
        (self.status(), Json(body)).into_response()
    }
}

// =============================================================================
// Gateway resolution + slot reads
// =============================================================================

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode_32(hex: &str) -> Option<[u8; 32]> {
    if hex.len() != 64 {
        return None;
    }
    let mut bytes = [0u8; 32];
    for (i, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(bytes)
}

/// Read a state slot as a 32-byte field element.
fn slot(cell: &dregg_cell::Cell, index: u8) -> [u8; 32] {
    cell.state.fields[index as usize]
}

/// Read a state slot as a big-endian u64 (the cell-program decoding —
/// `dregg_cell::program::field_to_u64` semantics).
fn slot_u64(cell: &dregg_cell::Cell, index: u8) -> u64 {
    let f = slot(cell, index);
    u64::from_be_bytes(f[24..32].try_into().expect("8-byte tail"))
}

fn field_u64(value: u64) -> [u8; 32] {
    let mut f = [0u8; 32];
    f[24..32].copy_from_slice(&value.to_be_bytes());
    f
}

/// Whether `cell` is a storage-gateway mandate cell: its installed program VK
/// is the canonical SGM child VK (the factory `ChildVkStrategy::Fixed` value).
fn is_sgm_cell(cell: &dregg_cell::Cell) -> bool {
    cell.verification_key
        .as_ref()
        .is_some_and(|vk| vk.hash == sgm_child_program_vk())
}

/// Resolve the gateway mandate cell for a request.
///
/// With `override_hex` (header `x-dregg-storage-gateway`), the named cell must
/// exist AND be an SGM cell. Otherwise scan the ledger for SGM cells and pick
/// the (deterministically) smallest id — the boot-seeded `sgm-gateway` cell in
/// the common case. No SGM cell ⇒ refuse (there is no mandate to admit under).
pub fn resolve_gateway(
    s: &NodeStateInner,
    override_hex: Option<&str>,
) -> Result<CellId, StorageRefusal> {
    if let Some(hex) = override_hex {
        let bytes = hex_decode_32(hex).ok_or_else(|| {
            StorageRefusal::BadRequest(format!("malformed gateway cell id: {hex}"))
        })?;
        let id = CellId(bytes);
        let cell = s.ledger.get(&id).ok_or_else(|| {
            StorageRefusal::NoGateway(format!("gateway cell {hex} not in ledger"))
        })?;
        if !is_sgm_cell(cell) {
            return Err(StorageRefusal::NoGateway(format!(
                "cell {hex} is not a storage-gateway mandate cell"
            )));
        }
        return Ok(id);
    }

    let mut candidates: Vec<CellId> = s
        .ledger
        .iter()
        .filter(|(_, cell)| is_sgm_cell(cell))
        .map(|(id, _)| *id)
        .collect();
    candidates.sort_by(|a, b| a.0.cmp(&b.0));
    candidates.into_iter().next().ok_or_else(|| {
        StorageRefusal::NoGateway(
            "no storage-gateway mandate cell in ledger (was the starbridge seed run?)".into(),
        )
    })
}

/// The request-level authority gate: the node must be unlocked and the
/// operator's agent cell must hold a c-list capability over the gateway cell
/// (granted at seed time by `grant_operator_reach`).
///
/// Runs BEFORE `ensure_gateway_initialized` in every route: without authority
/// over the gateway the node must not even attempt the one-time init turn —
/// a request pinned to a gateway the operator holds no capability over
/// refuses `no-capability`, not whatever the doomed init turn would say.
/// (`admit` re-checks the same gate — defense in depth for direct callers.)
pub fn require_operator_authority(
    s: &NodeStateInner,
    gateway: CellId,
) -> Result<(), StorageRefusal> {
    if !s.unlocked {
        return Err(StorageRefusal::Locked);
    }
    let operator_cell = crate::executor_setup::local_agent_cell(s);
    let holds_cap = s
        .ledger
        .get(&operator_cell)
        .map(|c| c.capabilities.has_access(&gateway))
        .unwrap_or(false);
    if !holds_cap {
        return Err(StorageRefusal::NoCapability(format!(
            "operator agent cell {} holds no capability over gateway {}",
            hex_encode(&operator_cell.0),
            hex_encode(&gateway.0),
        )));
    }
    Ok(())
}

// =============================================================================
// Gateway initialization (one-time WriteOnce binding)
// =============================================================================

/// A factory-born gateway cell is empty: `init_gateway` binds the anchor,
/// ceiling, prefix hash, and read-compartment hash ONCE (WriteOnce slots,
/// frozen thereafter by the cell program). Idempotent: an already-initialized
/// cell is only binding-checked.
///
/// Fail-closed: if the cell's pinned commitments do not match this node's
/// configuration, every subsequent op refuses (`BindingMismatch`) — we will
/// not admit under a mandate whose scope we cannot interpret.
pub fn ensure_gateway_initialized(
    s: &mut NodeStateInner,
    gateway: CellId,
) -> Result<(), StorageRefusal> {
    let cfg = s.storage_gateway.config.clone();
    let cell = s
        .ledger
        .get(&gateway)
        .ok_or_else(|| StorageRefusal::NoGateway("gateway cell vanished".into()))?;

    if slot_u64(cell, VOLUME_CEILING_SLOT) == 0 {
        let effects = vec![
            Effect::SetField {
                cell: gateway,
                index: COMMITMENT_ANCHOR_SLOT as usize,
                value: field_u64(cfg.commitment_anchor),
            },
            Effect::SetField {
                cell: gateway,
                index: VOLUME_CEILING_SLOT as usize,
                value: field_u64(cfg.volume_ceiling),
            },
            Effect::SetField {
                cell: gateway,
                index: KEY_PREFIX_HASH_SLOT as usize,
                value: key_prefix_field(&cfg.key_prefix),
            },
            Effect::SetField {
                cell: gateway,
                index: READ_COMPARTMENT_SLOT as usize,
                value: field_from_bytes(cfg.read_compartment.as_bytes()),
            },
            Effect::EmitEvent {
                cell: gateway,
                event: Event::new(
                    symbol("storage-gateway-initialized"),
                    vec![
                        field_u64(cfg.commitment_anchor),
                        field_u64(cfg.volume_ceiling),
                        key_prefix_field(&cfg.key_prefix),
                        field_from_bytes(cfg.read_compartment.as_bytes()),
                    ],
                ),
            },
        ];
        commit_operator_turn(s, gateway, "init_gateway", effects)?;
    }

    let cell = s
        .ledger
        .get(&gateway)
        .ok_or_else(|| StorageRefusal::NoGateway("gateway cell vanished".into()))?;
    if slot(cell, KEY_PREFIX_HASH_SLOT) != key_prefix_field(&cfg.key_prefix) {
        return Err(StorageRefusal::BindingMismatch(
            "gateway cell pins a different key prefix than this node's configuration".into(),
        ));
    }
    if slot(cell, READ_COMPARTMENT_SLOT) != field_from_bytes(cfg.read_compartment.as_bytes()) {
        return Err(StorageRefusal::BindingMismatch(
            "gateway cell pins a different read compartment than this node's configuration".into(),
        ));
    }
    if slot_u64(cell, VOLUME_CEILING_SLOT) == 0 {
        return Err(StorageRefusal::BindingMismatch(
            "gateway cell volume ceiling is zero (uninitialized)".into(),
        ));
    }
    Ok(())
}

// =============================================================================
// Admission (the mandate gate)
// =============================================================================

/// A successfully admitted op: the post-debit volume counter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AdmittedOp {
    pub new_spent: u64,
    pub cost: u64,
}

/// Admit one storage op under the gateway mandate. Mirrors the Lean
/// `sgmAdmitM` admission exactly (the SGM crate's `sgm_admit` is asserted as
/// the oracle): op allowlist → (GET) clearance / (PUT) prefix scope → volume
/// debit. Plus the request-level capability check: the node operator's agent
/// cell must hold a c-list capability over the gateway cell.
pub fn admit(
    s: &NodeStateInner,
    gateway: CellId,
    op: StorageOp,
    key: &str,
    clearance: Option<&str>,
) -> Result<AdmittedOp, StorageRefusal> {
    // Capability: the operator presents its c-list capability over the
    // mandate cell (granted at seed time by `grant_operator_reach`).
    require_operator_authority(s, gateway)?;

    let cfg = &s.storage_gateway.config;
    let cell = s
        .ledger
        .get(&gateway)
        .ok_or_else(|| StorageRefusal::NoGateway("gateway cell vanished".into()))?;

    let spent = slot_u64(cell, VOLUME_SPENT_SLOT);
    let ceiling = slot_u64(cell, VOLUME_CEILING_SLOT);
    let cost = op.demo_cost();

    // Op allowlist (Lean `opAllowed`).
    if !cfg.allowed_ops.contains(&op) {
        return Err(StorageRefusal::OpNotAllowed(match op {
            StorageOp::Get => "GET",
            StorageOp::Put => "PUT",
            StorageOp::List => "LIST",
        }));
    }

    // Per-op scope checks (Lean `putPrefixOK` / `getClearanceOK`).
    let clearance_label = clearance.map(|c| field_from_bytes(c.as_bytes()));
    match op {
        StorageOp::Put => {
            if !key.starts_with(&cfg.key_prefix) {
                return Err(StorageRefusal::PrefixViolation {
                    key: key.to_string(),
                    prefix: cfg.key_prefix.clone(),
                });
            }
        }
        StorageOp::Get => {
            let pinned = slot(cell, READ_COMPARTMENT_SLOT);
            if clearance_label != Some(pinned) {
                return Err(StorageRefusal::ClearanceDenied);
            }
        }
        StorageOp::List => {}
    }

    // Volume debit (Lean `Slice.tryDebit`).
    if spent.saturating_add(cost) > ceiling {
        return Err(StorageRefusal::VolumeBudgetExceeded {
            spent,
            cost,
            ceiling,
        });
    }
    let new_spent = spent + cost;

    // The verified-mirror predicate is the oracle: assert agreement.
    debug_assert_eq!(
        sgm_admit(
            spent,
            ceiling,
            key,
            &cfg.key_prefix,
            op,
            &cfg.allowed_ops,
            clearance_label.as_slice(),
            slot(cell, READ_COMPARTMENT_SLOT),
        ),
        Some(new_spent),
        "route admission diverged from sgm_admit"
    );

    Ok(AdmittedOp { new_spent, cost })
}

// =============================================================================
// The debit turn (executor-enforced)
// =============================================================================

/// Commit the `storage_op` debit turn against the gateway cell through the
/// node's authoritative executor path. THIS is where the mandate's volume law
/// is enforced in-protocol: the gateway cell's program (`Monotonic
/// volume_spent` + `FieldLteField volume_spent ≤ volume_ceiling`, installed at
/// factory birth from the SGM descriptor) is evaluated by the executor's
/// per-cell predicate gate — a debit past the ceiling is REJECTED even if the
/// route-level admission were bypassed.
///
/// Effects mirror the SGM crate's `build_storage_op_action` (Lean
/// `sgmStorageChain`): object_key, last_op, volume_spent, `storage-op` event.
pub fn commit_storage_op(
    s: &mut NodeStateInner,
    gateway: CellId,
    op: StorageOp,
    key: &str,
    new_spent: u64,
    blob_hash: [u8; 32],
) -> Result<[u8; 32], StorageRefusal> {
    let op_field = field_u64(op.to_field_value());
    let key_field = object_key_field(key);
    let spent_field = field_u64(new_spent);
    let effects = vec![
        Effect::SetField {
            cell: gateway,
            index: OBJECT_KEY_SLOT as usize,
            value: key_field,
        },
        Effect::SetField {
            cell: gateway,
            index: LAST_OP_SLOT as usize,
            value: op_field,
        },
        Effect::SetField {
            cell: gateway,
            index: VOLUME_SPENT_SLOT as usize,
            value: spent_field,
        },
        Effect::EmitEvent {
            cell: gateway,
            event: Event::new(
                symbol("storage-op"),
                vec![op_field, key_field, blob_hash, spent_field],
            ),
        },
    ];
    commit_operator_turn(s, gateway, "storage_op", effects)
}

/// Build, sign, and execute one operator turn against `target` through the
/// same authoritative path as `/turn/submit` (`new_submit_executor` over the
/// live ledger, receipt appended to the operator's chain on commit).
fn commit_operator_turn(
    s: &mut NodeStateInner,
    target: CellId,
    method: &str,
    effects: Vec<Effect>,
) -> Result<[u8; 32], StorageRefusal> {
    let federation_id = crate::executor_setup::federation_id_for_executor(s);
    let agent_cell = crate::executor_setup::local_agent_cell(s);

    let action = s
        .cclerk
        .make_action(target, method, effects, &federation_id);
    let mut call_forest = CallForest::new();
    call_forest.add_root(action);

    let previous_receipt_hash = s.cclerk.receipt_chain().last().map(|r| r.receipt_hash());
    let nonce = s
        .ledger
        .get(&agent_cell)
        .map(|c| c.state.nonce())
        .unwrap_or(0);

    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);

    let mut turn = Turn {
        agent: agent_cell,
        nonce,
        fee: 0,
        memo: None,
        valid_until: Some(now + 3600),
        call_forest,
        depends_on: vec![],
        previous_receipt_hash,
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    let executor = crate::executor_setup::new_submit_executor(s);
    // The fee IS the computron budget (`computrons_used > turn.fee` rejects):
    // meter the turn at the executor's own cost schedule. The operator agent
    // cell pays it from its balance — an unfunded operator refuses fail-closed
    // (`InsufficientBalance` surfaces as `turn-rejected`; fund via the faucet).
    turn.fee = executor.estimate_cost(&turn);
    let turn_hash = turn.hash();

    if let Some(head) = previous_receipt_hash {
        executor.set_last_receipt_hash(agent_cell, head);
    }

    match executor.execute(&turn, &mut s.ledger) {
        TurnResult::Committed { receipt, .. } => {
            s.cclerk.append_receipt(receipt).map_err(|e| {
                StorageRefusal::TurnRejected(format!("receipt chain mismatch: {e}"))
            })?;
            Ok(turn_hash)
        }
        TurnResult::Rejected { reason, .. } => {
            Err(StorageRefusal::TurnRejected(reason.to_string()))
        }
        TurnResult::Expired => Err(StorageRefusal::TurnRejected("turn expired".into())),
        TurnResult::Pending => Err(StorageRefusal::TurnRejected("turn pending".into())),
    }
}

// =============================================================================
// Routes
// =============================================================================

/// The storage gateway route surface. Mounted inside the node's PROTECTED
/// router (bearer-token gate) in `api.rs`.
pub fn routes() -> Router<NodeState> {
    Router::new()
        .route("/storage/put", post(post_storage_put))
        .route("/storage/get/{hash}", get(get_storage_get))
        .route("/storage/stat/{hash}", get(get_storage_stat))
        .route("/storage/list", get(get_storage_list))
        .route("/storage/quota", get(get_storage_quota))
}

#[derive(Serialize)]
struct PutResponse {
    hash: String,
    size: u64,
    key: String,
    turn_hash: String,
    volume_spent: u64,
}

#[derive(Serialize)]
struct StatResponse {
    exists: bool,
    size: Option<u64>,
    volume_spent: u64,
}

#[derive(Serialize)]
struct ListEntry {
    key: String,
    hash: String,
    size: u64,
}

#[derive(Serialize)]
struct ListResponse {
    entries: Vec<ListEntry>,
    volume_spent: u64,
}

#[derive(Serialize)]
struct QuotaResponse {
    bytes_stored: u64,
    bytes_limit: u64,
    computrons_used: u64,
    computrons_remaining: u64,
    object_count: u64,
    volume_spent: u64,
    volume_ceiling: u64,
}

#[derive(Deserialize)]
struct ListQuery {
    #[serde(default)]
    prefix: Option<String>,
}

fn header_str<'h>(headers: &'h HeaderMap, name: &str) -> Option<&'h str> {
    headers.get(name).and_then(|v| v.to_str().ok())
}

/// `POST /storage/put` — store a blob under the mandate.
///
/// Body: raw bytes. Headers: `x-dregg-object-key` (optional; defaults to
/// `<prefix><blake3-hex>`), `x-dregg-storage-gateway` (optional cell-id pin).
async fn post_storage_put(
    State(state): State<NodeState>,
    headers: HeaderMap,
    body: Bytes,
) -> Result<Json<PutResponse>, StorageRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;

    let gateway = resolve_gateway(inner, header_str(&headers, "x-dregg-storage-gateway"))?;
    require_operator_authority(inner, gateway)?;
    ensure_gateway_initialized(inner, gateway)?;

    let content_hash = blake3::hash(&body);
    let key = match header_str(&headers, "x-dregg-object-key") {
        Some(k) => k.to_string(),
        None => format!(
            "{}{}",
            inner.storage_gateway.config.key_prefix,
            hex_encode(content_hash.as_bytes())
        ),
    };

    // ADMISSION: op allowlist + capability + prefix scope + volume debit.
    let admitted = admit(inner, gateway, StorageOp::Put, &key, None)?;

    // The debit turn THROUGH the executor (cell program = enforcement tooth).
    // The blob-hash audit word in the `storage-op` event is the same blake3
    // the content store derives, binding the on-cell record to the blob.
    let turn_hash = commit_storage_op(
        inner,
        gateway,
        StorageOp::Put,
        &key,
        admitted.new_spent,
        *content_hash.as_bytes(),
    )?;

    // Only an ADMITTED + COMMITTED op reaches the store.
    let quota = inner.storage_gateway.quota_for(gateway);
    let stored = inner
        .storage_gateway
        .store
        .write(&body, &quota)
        .map_err(|e| StorageRefusal::Store(format!("{e:?}")))?;
    let size = body.len() as u64;
    inner.storage_gateway.objects.insert(
        key.clone(),
        StoredObject {
            hash: stored,
            gateway,
            size,
        },
    );
    let volume_spent = admitted.new_spent;
    drop(s);

    state.emit(crate::state::NodeEvent::Receipt {
        hash: hex_encode(&turn_hash),
    });

    Ok(Json(PutResponse {
        hash: hex_encode(&stored.0),
        size,
        key,
        turn_hash: hex_encode(&turn_hash),
        volume_spent,
    }))
}

/// `GET /storage/get/{hash}` — fetch a blob under the mandate.
///
/// Headers: `x-dregg-clearance` (the read-compartment label — REQUIRED),
/// `x-dregg-storage-gateway` (optional cell-id pin).
async fn get_storage_get(
    State(state): State<NodeState>,
    AxumPath(hash_hex): AxumPath<String>,
    headers: HeaderMap,
) -> Result<Response, StorageRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;

    let gateway = resolve_gateway(inner, header_str(&headers, "x-dregg-storage-gateway"))?;
    require_operator_authority(inner, gateway)?;
    ensure_gateway_initialized(inner, gateway)?;

    let hash = ContentHash(
        hex_decode_32(&hash_hex)
            .ok_or_else(|| StorageRefusal::BadRequest(format!("malformed hash: {hash_hex}")))?,
    );
    let key = inner
        .storage_gateway
        .key_for_hash(&hash)
        .unwrap_or_else(|| format!("blob:{hash_hex}"));

    // ADMISSION (clearance is checked here): refuse BEFORE revealing whether
    // the blob exists.
    let admitted = admit(
        inner,
        gateway,
        StorageOp::Get,
        &key,
        header_str(&headers, "x-dregg-clearance"),
    )?;

    // Existence check after clearance, before the debit (no charge for a miss).
    if !inner.storage_gateway.store.contains(&hash) {
        return Err(StorageRefusal::NotFound);
    }

    let turn_hash = commit_storage_op(
        inner,
        gateway,
        StorageOp::Get,
        &key,
        admitted.new_spent,
        hash.0,
    )?;

    let data = inner
        .storage_gateway
        .store
        .read(&hash)
        .ok_or(StorageRefusal::NotFound)?
        .to_vec();
    drop(s);

    state.emit(crate::state::NodeEvent::Receipt {
        hash: hex_encode(&turn_hash),
    });

    Ok((
        StatusCode::OK,
        [(header::CONTENT_TYPE, "application/octet-stream")],
        data,
    )
        .into_response())
}

/// `GET /storage/stat/{hash}` — existence + size (a LIST-class op).
async fn get_storage_stat(
    State(state): State<NodeState>,
    AxumPath(hash_hex): AxumPath<String>,
    headers: HeaderMap,
) -> Result<Json<StatResponse>, StorageRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;

    let gateway = resolve_gateway(inner, header_str(&headers, "x-dregg-storage-gateway"))?;
    require_operator_authority(inner, gateway)?;
    ensure_gateway_initialized(inner, gateway)?;

    let hash = ContentHash(
        hex_decode_32(&hash_hex)
            .ok_or_else(|| StorageRefusal::BadRequest(format!("malformed hash: {hash_hex}")))?,
    );
    let key = format!("stat:{hash_hex}");
    let admitted = admit(inner, gateway, StorageOp::List, &key, None)?;
    commit_storage_op(
        inner,
        gateway,
        StorageOp::List,
        &key,
        admitted.new_spent,
        hash.0,
    )?;

    Ok(Json(StatResponse {
        exists: inner.storage_gateway.store.contains(&hash),
        size: inner.storage_gateway.store.blob_size(&hash),
        volume_spent: admitted.new_spent,
    }))
}

/// `GET /storage/list?prefix=` — list object keys (a LIST-class op).
async fn get_storage_list(
    State(state): State<NodeState>,
    Query(query): Query<ListQuery>,
    headers: HeaderMap,
) -> Result<Json<ListResponse>, StorageRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;

    let gateway = resolve_gateway(inner, header_str(&headers, "x-dregg-storage-gateway"))?;
    require_operator_authority(inner, gateway)?;
    ensure_gateway_initialized(inner, gateway)?;

    let list_prefix = query
        .prefix
        .unwrap_or_else(|| inner.storage_gateway.config.key_prefix.clone());
    let admitted = admit(inner, gateway, StorageOp::List, &list_prefix, None)?;
    commit_storage_op(
        inner,
        gateway,
        StorageOp::List,
        &list_prefix,
        admitted.new_spent,
        [0u8; 32],
    )?;

    let entries = inner
        .storage_gateway
        .objects
        .iter()
        .filter(|(k, o)| k.starts_with(&list_prefix) && o.gateway == gateway)
        .map(|(k, o)| ListEntry {
            key: k.clone(),
            hash: hex_encode(&o.hash.0),
            size: o.size,
        })
        .collect();

    Ok(Json(ListResponse {
        entries,
        volume_spent: admitted.new_spent,
    }))
}

/// `GET /storage/quota` — meter introspection (capability-gated, no debit).
async fn get_storage_quota(
    State(state): State<NodeState>,
    headers: HeaderMap,
) -> Result<Json<QuotaResponse>, StorageRefusal> {
    let mut s = state.write().await;
    let inner = &mut *s;

    let gateway = resolve_gateway(inner, header_str(&headers, "x-dregg-storage-gateway"))?;
    require_operator_authority(inner, gateway)?;
    ensure_gateway_initialized(inner, gateway)?;

    let cell = inner
        .ledger
        .get(&gateway)
        .ok_or_else(|| StorageRefusal::NoGateway("gateway cell vanished".into()))?;
    let volume_spent = slot_u64(cell, VOLUME_SPENT_SLOT);
    let volume_ceiling = slot_u64(cell, VOLUME_CEILING_SLOT);

    let quota = inner.storage_gateway.quota_for(gateway);
    let (used, remaining, limit) = inner
        .storage_gateway
        .store
        .bank
        .get(&quota)
        .map(|q| (q.total_consumed, q.available(), q.max_bytes.unwrap_or(0)))
        .unwrap_or((0, 0, 0));

    Ok(Json(QuotaResponse {
        bytes_stored: inner.storage_gateway.store.total_bytes(),
        bytes_limit: limit,
        computrons_used: used,
        computrons_remaining: remaining,
        object_count: inner.storage_gateway.store.blob_count() as u64,
        volume_spent,
        volume_ceiling,
    }))
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::Request;
    use http_body_util::BodyExt;
    use tower::ServiceExt;

    /// Build a NodeState with the REAL boot seed: devnet starbridge seeding
    /// creates the sgm-gateway cell via an actual factory-birth turn and
    /// grants the operator the capability over it (`grant_operator_reach`) —
    /// the same path the live node takes.
    async fn seeded_state() -> (NodeState, CellId, tempfile::TempDir) {
        let dir = tempfile::tempdir().expect("tempdir");
        let state = NodeState::new(dir.path(), vec![]).expect("node state");
        let gateway = {
            let mut s = state.write().await;
            s.unlocked = true;
            let federation_id = crate::executor_setup::federation_id_for_executor(&s);
            let operator = s.cclerk.public_key().0;
            let stats = crate::starbridge_seed::seed_default_starbridge_cells_devnet(
                dir.path(),
                &mut s.ledger,
                federation_id,
                Some(operator),
            );
            assert!(
                stats.created > 0,
                "devnet seed must create starbridge cells (stats: {stats:?})"
            );
            // Fund the operator agent cell: every gateway turn (init + each
            // storage_op debit) pays its metered computron fee from this
            // balance — exactly what the devnet faucet does for a live node
            // (see `NodeIdentityResponse::agent_cell`). An unfunded operator
            // refuses fail-closed; these tests exercise the gate, so fund it.
            let operator_cell = crate::executor_setup::local_agent_cell(&s);
            assert!(
                s.ledger
                    .get_mut(&operator_cell)
                    .expect("seed created the operator agent cell")
                    .state
                    .credit_balance(1_000_000),
                "operator agent cell accepts funding"
            );
            resolve_gateway(&s, None).expect("seeded sgm-gateway cell resolves")
        };
        (state, gateway, dir)
    }

    fn gateway_slot_u64(s: &NodeStateInner, gateway: CellId, index: u8) -> u64 {
        slot_u64(s.ledger.get(&gateway).expect("gateway cell"), index)
    }

    async fn do_put(
        state: &NodeState,
        key: Option<&str>,
        body: &[u8],
    ) -> (StatusCode, serde_json::Value) {
        let app = routes().with_state(state.clone());
        let mut req = Request::builder().uri("/storage/put").method("POST");
        if let Some(k) = key {
            req = req.header("x-dregg-object-key", k);
        }
        let resp = app
            .oneshot(req.body(Body::from(body.to_vec())).unwrap())
            .await
            .unwrap();
        let status = resp.status();
        let bytes = resp.into_body().collect().await.unwrap().to_bytes();
        let json = serde_json::from_slice(&bytes).unwrap_or(serde_json::json!({}));
        (status, json)
    }

    async fn do_get(
        state: &NodeState,
        hash_hex: &str,
        clearance: Option<&str>,
    ) -> (StatusCode, Vec<u8>) {
        let app = routes().with_state(state.clone());
        let mut req = Request::builder()
            .uri(format!("/storage/get/{hash_hex}"))
            .method("GET");
        if let Some(c) = clearance {
            req = req.header("x-dregg-clearance", c);
        }
        let resp = app.oneshot(req.body(Body::empty()).unwrap()).await.unwrap();
        let status = resp.status();
        let bytes = resp.into_body().collect().await.unwrap().to_bytes();
        (status, bytes.to_vec())
    }

    // ── the weld: put/get roundtrip THROUGH the gate ─────────────────────────

    #[tokio::test]
    async fn put_get_roundtrip_debits_mandate() {
        let (state, gateway, _dir) = seeded_state().await;

        let body = b"hello, mandate-gated storage";
        let (status, json) = do_put(&state, Some("uploads/hello.txt"), body).await;
        assert_eq!(status, StatusCode::OK, "admitted PUT must succeed: {json}");
        let hash_hex = json["hash"].as_str().expect("hash in response").to_string();
        assert_eq!(json["size"].as_u64(), Some(body.len() as u64));

        // The mandate cell debited PUT cost (5) — written by the committed turn.
        {
            let s = state.write().await;
            assert_eq!(
                gateway_slot_u64(&s, gateway, VOLUME_SPENT_SLOT),
                StorageOp::Put.demo_cost(),
                "volume_spent slot must reflect the executor-committed debit"
            );
            assert_eq!(
                gateway_slot_u64(&s, gateway, LAST_OP_SLOT),
                StorageOp::Put.to_field_value(),
            );
        }

        // GET with clearance roundtrips the bytes and debits GET cost (1).
        let (status, data) = do_get(&state, &hash_hex, Some(DEFAULT_READ_COMPARTMENT)).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(data, body.to_vec(), "roundtrip bytes must match");
        {
            let s = state.write().await;
            assert_eq!(
                gateway_slot_u64(&s, gateway, VOLUME_SPENT_SLOT),
                StorageOp::Put.demo_cost() + StorageOp::Get.demo_cost(),
            );
        }
    }

    // ── refusal 1: no capability ─────────────────────────────────────────────

    #[tokio::test]
    async fn refuses_without_capability() {
        let (state, gateway, _dir) = seeded_state().await;

        // Build a second SGM-shaped cell the operator holds NO capability
        // over, and pin the request to it: admission must refuse.
        let rogue = {
            let mut s = state.write().await;
            let template = s.ledger.get(&gateway).expect("gateway").clone();
            let mut cell = dregg_cell::Cell::with_balance(
                [7u8; 32],
                *blake3::hash(b"rogue-gateway").as_bytes(),
                0,
            );
            cell.verification_key = template.verification_key.clone();
            cell.program = template.program.clone();
            let id = cell.id();
            s.ledger.insert_cell(cell).expect("rogue cell inserts");
            id
        };

        let app = routes().with_state(state.clone());
        let resp = app
            .oneshot(
                Request::builder()
                    .uri("/storage/put")
                    .method("POST")
                    .header("x-dregg-object-key", "uploads/x.txt")
                    .header("x-dregg-storage-gateway", hex_encode(&rogue.0))
                    .body(Body::from("data"))
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::FORBIDDEN);
        let bytes = resp.into_body().collect().await.unwrap().to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(json["reason"], "no-capability");
    }

    // ── refusal 2: wrong prefix ──────────────────────────────────────────────

    #[tokio::test]
    async fn refuses_put_outside_prefix() {
        let (state, gateway, _dir) = seeded_state().await;

        let (status, json) = do_put(&state, Some("secret/doc.txt"), b"sneaky").await;
        assert_eq!(status, StatusCode::FORBIDDEN);
        assert_eq!(json["reason"], "prefix-violation");

        // Nothing stored, nothing debited beyond the init turn.
        let s = state.write().await;
        assert_eq!(s.storage_gateway.store.blob_count(), 0);
        assert_eq!(gateway_slot_u64(&s, gateway, VOLUME_SPENT_SLOT), 0);
    }

    // ── refusal 3: over volume budget (route gate + executor tooth) ──────────

    #[tokio::test]
    async fn refuses_over_volume_budget_and_executor_enforces() {
        let (state, gateway, _dir) = seeded_state().await;
        {
            // Bind a tiny ceiling: 12 admits two PUTs (5+5) and refuses a third.
            let mut s = state.write().await;
            s.storage_gateway.config.volume_ceiling = 12;
        }

        let (s1, _) = do_put(&state, Some("uploads/a"), b"a").await;
        let (s2, _) = do_put(&state, Some("uploads/b"), b"b").await;
        assert_eq!(s1, StatusCode::OK);
        assert_eq!(s2, StatusCode::OK);

        let (s3, json) = do_put(&state, Some("uploads/c"), b"c").await;
        assert_eq!(s3, StatusCode::INSUFFICIENT_STORAGE, "{json}");
        assert_eq!(json["reason"], "volume-budget-exceeded");

        // The EXECUTOR tooth, independent of route admission: a debit turn
        // past the ceiling violates the cell program (FieldLteField) and is
        // rejected by the authoritative executor.
        let mut s = state.write().await;
        let spent = gateway_slot_u64(&s, gateway, VOLUME_SPENT_SLOT);
        assert_eq!(spent, 10, "two committed PUT debits");
        let over = commit_storage_op(
            &mut s,
            gateway,
            StorageOp::Put,
            "uploads/bypass",
            13, // > ceiling 12
            [0u8; 32],
        );
        match over {
            Err(StorageRefusal::TurnRejected(_)) => {}
            other => panic!("executor must reject over-ceiling debit, got {other:?}"),
        }
        assert_eq!(
            gateway_slot_u64(&s, gateway, VOLUME_SPENT_SLOT),
            10,
            "rejected turn must not move the counter"
        );
    }

    // ── refusal 4: disallowed op ─────────────────────────────────────────────

    #[tokio::test]
    async fn refuses_disallowed_op() {
        let (state, _gateway, _dir) = seeded_state().await;
        {
            let mut s = state.write().await;
            s.storage_gateway.config.allowed_ops = vec![StorageOp::Put, StorageOp::Get];
        }

        let app = routes().with_state(state.clone());
        let resp = app
            .oneshot(
                Request::builder()
                    .uri("/storage/list")
                    .method("GET")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::FORBIDDEN);
        let bytes = resp.into_body().collect().await.unwrap().to_bytes();
        let json: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(json["reason"], "op-not-allowed");
    }

    // ── refusal 5 (bonus): GET without clearance ─────────────────────────────

    #[tokio::test]
    async fn refuses_get_without_clearance() {
        let (state, _gateway, _dir) = seeded_state().await;

        let body = b"cleared readers only";
        let (status, json) = do_put(&state, Some("uploads/sealed.txt"), body).await;
        assert_eq!(status, StatusCode::OK);
        let hash_hex = json["hash"].as_str().unwrap().to_string();

        let (status, _) = do_get(&state, &hash_hex, None).await;
        assert_eq!(status, StatusCode::FORBIDDEN, "no clearance header");
        let (status, _) = do_get(&state, &hash_hex, Some("wrong-compartment")).await;
        assert_eq!(status, StatusCode::FORBIDDEN, "wrong clearance label");
        let (status, data) = do_get(&state, &hash_hex, Some(DEFAULT_READ_COMPARTMENT)).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(data, body.to_vec());
    }

    // ── refcount / ownership behavior on put ─────────────────────────────────

    #[tokio::test]
    async fn duplicate_put_dedups_with_refcount_and_charges_quota() {
        let (state, gateway, _dir) = seeded_state().await;

        let body = b"identical bytes";
        let (s1, j1) = do_put(&state, Some("uploads/copy-1"), body).await;
        let (s2, j2) = do_put(&state, Some("uploads/copy-2"), body).await;
        assert_eq!(s1, StatusCode::OK);
        assert_eq!(s2, StatusCode::OK);
        assert_eq!(
            j1["hash"], j2["hash"],
            "identical content must dedup to one content hash"
        );

        let mut s = state.write().await;
        // One blob in the store (refcounted), two keys in the index.
        assert_eq!(s.storage_gateway.store.blob_count(), 1);
        assert_eq!(s.storage_gateway.objects.len(), 2);
        assert_eq!(
            s.storage_gateway.store.total_bytes(),
            body.len() as u64,
            "deduped blob stored once"
        );
        // Both writes charged the gateway's quota (the payer claims storage
        // under its quota even on dedup — ContentStore::write contract).
        let quota = s.storage_gateway.quota_for(gateway);
        let consumed = s
            .storage_gateway
            .store
            .bank
            .get(&quota)
            .expect("quota cell")
            .total_consumed;
        assert_eq!(
            consumed,
            2 * body.len() as u64,
            "both PUTs charge the owning quota (cost_per_byte=1)"
        );
        // And the mandate debited twice.
        assert_eq!(
            gateway_slot_u64(&s, gateway, VOLUME_SPENT_SLOT),
            2 * StorageOp::Put.demo_cost(),
        );
    }

    // ── stat + list + quota surface ──────────────────────────────────────────

    #[tokio::test]
    async fn stat_list_quota_report_through_the_gate() {
        let (state, gateway, _dir) = seeded_state().await;

        let body = b"observable";
        let (status, json) = do_put(&state, Some("uploads/obs.bin"), body).await;
        assert_eq!(status, StatusCode::OK);
        let hash_hex = json["hash"].as_str().unwrap().to_string();

        let app = routes().with_state(state.clone());
        let resp = app
            .clone()
            .oneshot(
                Request::builder()
                    .uri(format!("/storage/stat/{hash_hex}"))
                    .method("GET")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let bytes = resp.into_body().collect().await.unwrap().to_bytes();
        let stat: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(stat["exists"], true);
        assert_eq!(stat["size"].as_u64(), Some(body.len() as u64));

        let resp = app
            .clone()
            .oneshot(
                Request::builder()
                    .uri("/storage/list")
                    .method("GET")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let bytes = resp.into_body().collect().await.unwrap().to_bytes();
        let list: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(list["entries"].as_array().unwrap().len(), 1);
        assert_eq!(list["entries"][0]["key"], "uploads/obs.bin");

        let resp = app
            .oneshot(
                Request::builder()
                    .uri("/storage/quota")
                    .method("GET")
                    .body(Body::empty())
                    .unwrap(),
            )
            .await
            .unwrap();
        assert_eq!(resp.status(), StatusCode::OK);
        let bytes = resp.into_body().collect().await.unwrap().to_bytes();
        let quota: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(quota["bytes_stored"].as_u64(), Some(body.len() as u64));
        assert_eq!(quota["object_count"].as_u64(), Some(1));
        // stat (2) + list (2) + put (5) debits so far.
        let s = state.write().await;
        assert_eq!(gateway_slot_u64(&s, gateway, VOLUME_SPENT_SLOT), 9);
    }
}
