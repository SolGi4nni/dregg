//! Relay operator service.
//!
//! Exposes the storage-template relay operator service. Operators bond
//! computrons to host inboxes, accept store-and-forward messages from senders,
//! deliver them to recipients on drain, charge fees, and run periodic GC.
//!
//! # Endpoints
//!
//! ```text
//! GET  /relay/status            -- operator info (bond, inboxes, earnings)
//! POST /relay/subscribe         -- create a hosted inbox
//! DELETE /relay/unsubscribe     -- remove an inbox
//! POST /relay/send/:dest        -- enqueue a message
//! GET  /relay/drain             -- drain your inbox (authenticated)
//! GET  /relay/inbox/:id/status  -- check inbox status
//! GET  /relay/proof/:msg_id     -- get dequeue proof for a delivered message
//! ```

// RelayOperator is deprecated in favor of the relay_operator_factory_descriptor cell-program template (STORAGE-AS-CELL-PROGRAMS.md §3.5); this service is the legacy in-process path, migration tracked separately.
#![allow(deprecated)]

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

use axum::extract::{Path, State};
use axum::http::StatusCode;
use axum::routing::{delete, get, post};
use axum::{Json, Router};
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;
use tracing::info;

use dregg_storage::inbox::InboxMessage;
use dregg_storage::operator::RelayOperator;
use dregg_storage::queue::{DequeueProof, MerkleQueue, QueueEntry};
use dregg_storage_templates::relay_operator::{
    BYTES_RELAYED_THIS_EPOCH_SLOT, DEFAULT_EPOCH_DURATION, HOSTED_INBOX_ROOT_SLOT,
    QUOTA_BYTES_PER_EPOCH_SLOT, initial_state, relay_operator_child_program_vk,
    relay_operator_factory_descriptor, relay_operator_program_with,
};

// ─── Delivery-proof bounding (audit #10: slash-safe eviction) ───────────────────
//
// `delivery_proofs` is the sticky DELIVERED-set the dispute referee reads as the
// content-address-honest delivery witness (see `relay_dispute::handle_dispute`):
// membership of a box's `content_hash` acquits a dispute over it. Left unbounded it
// grows forever (GC skipped it). It could NOT be blindly ring/TTL-evicted because a
// dispute only had a LOWER admissibility bound (`at_height >= accept_by`, no upper
// bound), so dropping a still-disputable delivered box's proof would flip an acquit
// into a Dropped verdict and WRONGLY SLASH an honest relay.
//
// The fix pairs an UPPER dispute deadline with a height-keyed eviction whose
// thresholds COINCIDE:
//
//   * `handle_dispute` rejects, against the node's OWN finalized `current_height`
//     (unforgeable, unlike the disputer's `at_height`), any dispute with
//     `current_height > accept_by + dispute_window_blocks` — past that height the
//     delivery is FINAL.
//   * a cached proof is retained iff `current_height <= dispute_deadline`, where
//     `dispute_deadline = enqueued_at + CUSTODY_DEADLINE_BLOCKS + dispute_window`.
//
// Under the receipt construction `accept_by = enqueued_at + custody_deadline`
// (captp `Bus::enqueue`, data_plane.rs: `accept_by = now + default_deadline`), and
// `enqueued_at <= drain height`, we have `dispute_deadline >= accept_by +
// dispute_window`. So a proof is only ever evicted at or AFTER the height at which
// every dispute that could read it is already inadmissible — eviction can never turn
// an acquit into a slash. This is the invariant eviction safety rests on.

/// The custody deadline horizon (blocks past a box's enqueue height) by which the
/// relay must have delivered or refunded, else it has DROPPED the box. Mirrors the
/// captp data-plane bus deadline (`Bus::default_deadline` = 100, data_plane.rs),
/// where a minted `CustodyReceipt` sets `accept_by = enqueue + default_deadline`.
///
/// SAFETY INVARIANT: eviction assumes `accept_by <= enqueued_at +
/// CUSTODY_DEADLINE_BLOCKS` for every valid receipt (true by that construction). A
/// deployment that raises the bus `default_deadline` MUST raise this in lockstep, or
/// a proof could be evicted while a longer-deadline dispute is still open.
pub const CUSTODY_DEADLINE_BLOCKS: u64 = 100;

/// Default dispute (challenge) window: blocks PAST a box's `accept_by` during which
/// its delivery may still be disputed. After `accept_by + dispute_window` the
/// delivery is FINAL and its cached proof is evictable. Chosen conservatively as the
/// default message lifetime (`RelayConfig::message_ttl_blocks` / the bus
/// `default_ttl` = 1000): an honest wronged party has a full message-lifetime of
/// blocks after the deadline to raise a dispute — comfortably longer than the
/// consensus finality depth (`FINALITY_DEPTH_ROUNDS` = 6) and the custody deadline
/// horizon. Tunable via `RelayConfig::dispute_window_blocks`.
pub const DEFAULT_DISPUTE_WINDOW_BLOCKS: u64 = 1_000;

/// Default hard cap on cached delivery proofs — a memory backstop above the
/// structural bound (deliveries within one live dispute window, itself throttled by
/// the send-side per-epoch byte quota `RateLimitBySum` + inbox capacities; with the
/// default config ~1.1 epochs of a 100k-byte/epoch quota). Reaching it means TTL
/// eviction has not kept pace; a drain then caches only as many proofs as fit and
/// leaves the rest ENQUEUED (still in custody, no witness gap) — backpressure, never
/// dropping a within-window proof (which could wrongly slash). Tunable via
/// `RelayConfig::max_delivery_proofs`.
pub const DEFAULT_MAX_DELIVERY_PROOFS: usize = 262_144;

fn default_dispute_window_blocks() -> u64 {
    DEFAULT_DISPUTE_WINDOW_BLOCKS
}

fn default_max_delivery_proofs() -> usize {
    DEFAULT_MAX_DELIVERY_PROOFS
}

// ─── Configuration ────────────────────────────────────────────────────────────

/// Configuration for the relay operator service.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RelayConfig {
    /// Port to listen on.
    pub listen_port: u16,
    /// Operator identity key (32 bytes, hex-encoded when serialized to file).
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub operator_key: [u8; 32],
    /// Bond amount (computrons staked).
    pub bond_amount: u64,
    /// Fee policy (what assets accepted, at what rates).
    pub fee_policy: FeePolicy,
    /// Maximum total capacity to host (sum of all inbox capacities).
    pub max_total_capacity: usize,
    /// GC interval in seconds.
    pub gc_interval_secs: u64,
    /// TTL for messages in blocks (used during GC).
    pub message_ttl_blocks: u64,
    /// Dispute (challenge) window: blocks past a box's `accept_by` deadline during
    /// which its delivery may still be disputed. After `accept_by +
    /// dispute_window_blocks` the delivery is FINAL and its cached delivery proof is
    /// evictable (audit #10). See [`DEFAULT_DISPUTE_WINDOW_BLOCKS`].
    #[serde(default = "default_dispute_window_blocks")]
    pub dispute_window_blocks: u64,
    /// Hard cap on cached delivery proofs (memory backstop). See
    /// [`DEFAULT_MAX_DELIVERY_PROOFS`].
    #[serde(default = "default_max_delivery_proofs")]
    pub max_delivery_proofs: usize,
    /// SLA: max delivery latency in blocks.
    pub max_delivery_latency_blocks: u64,
    /// Path for persistent state file.
    pub state_file: PathBuf,
    /// Default inbox capacity for new subscriptions.
    pub default_inbox_capacity: usize,
    /// Default minimum deposit for new inboxes.
    pub default_min_deposit: u64,
}

impl Default for RelayConfig {
    fn default() -> Self {
        Self {
            listen_port: 3100,
            operator_key: [0u8; 32],
            bond_amount: 10_000,
            fee_policy: FeePolicy::default(),
            max_total_capacity: 100_000,
            gc_interval_secs: 300,
            message_ttl_blocks: 1000,
            dispute_window_blocks: DEFAULT_DISPUTE_WINDOW_BLOCKS,
            max_delivery_proofs: DEFAULT_MAX_DELIVERY_PROOFS,
            max_delivery_latency_blocks: 50,
            state_file: PathBuf::from("./relay-state.json"),
            default_inbox_capacity: 100,
            default_min_deposit: 100,
        }
    }
}

/// Fee policy: which assets are accepted and at what rates.
///
/// Computrons are an OPERATOR-LOCAL number: every operator sets its own
/// acceptance policy and there is deliberately no global peg (see
/// `docs/deos/COMPUTRON-POLICY.md`). The former single-asset knob
/// (`accept_external_assets` + `external_rate_micros`) is generalized into a
/// per-asset table; the fail-closed default (refuse everything) is preserved
/// as the empty table.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FeePolicy {
    /// Minimum deposit per message (in computrons).
    pub min_deposit_computrons: u64,
    /// Subscription fee (one-time, for creating an inbox).
    pub subscription_fee: u64,
    /// Per-asset acceptance table for computron refills, keyed by the
    /// hex-encoded 32-byte `Payable` asset id (an asset IS its issuer cell's
    /// `token_id` — see `dregg_payable::AssetId`; bridged tokens carry the
    /// bridge-minted issuer id). FAIL CLOSED: an asset absent from this table
    /// is refused, and the default table is empty.
    #[serde(default)]
    pub external_assets: BTreeMap<String, AssetRatePolicy>,
}

/// One row of the operator's external-asset acceptance table: the terms under
/// which THIS operator sells computron refills for one `Payable` asset. Purely
/// operator-local — another operator may quote any other rate or none.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct AssetRatePolicy {
    /// Exchange rate: external asset units per computron (fixed-point,
    /// [`COMPUTRON_RATE_SCALE`] = 1:1). A rate of 0 is invalid and always
    /// refuses (it would quote infinite computrons per unit).
    pub rate_micros: u64,
    /// Whether the operator currently accepts this asset. A disabled row
    /// refuses without being deleted, so an operator can pause an asset and
    /// keep its quoted rate on record.
    pub enabled: bool,
}

impl Default for FeePolicy {
    fn default() -> Self {
        Self {
            min_deposit_computrons: 100,
            subscription_fee: 1000,
            external_assets: BTreeMap::new(),
        }
    }
}

impl FeePolicy {
    /// Declare (or overwrite) an acceptance row for `asset` at `rate_micros`
    /// external units per computron, enabled.
    pub fn accept_asset(&mut self, asset: &[u8; 32], rate_micros: u64) {
        self.external_assets.insert(
            hex_encode(asset),
            AssetRatePolicy {
                rate_micros,
                enabled: true,
            },
        );
    }

    /// Look up the acceptance row for `asset`. `None` = not in the table =
    /// refused (fail closed).
    pub fn asset_policy(&self, asset: &[u8; 32]) -> Option<&AssetRatePolicy> {
        self.external_assets.get(&hex_encode(asset))
    }
}

// ─── Computron refill (operator-local purchase path, rung 1) ─────────────────

/// Fixed-point scale for [`AssetRatePolicy::rate_micros`]: `1_000_000` means
/// 1 external asset unit per computron.
pub const COMPUTRON_RATE_SCALE: u64 = 1_000_000;

/// An accepted external-asset payment presented for a computron refill: the
/// operator observed `external_amount` units of `asset` paid to it (bridge
/// deposit voucher, `Payable` receipt, …) and now credits `recipient`.
///
/// Rung 1 deliberately does NOT verify the external payment here — the voucher
/// is the operator's own accounting input (the operator is crediting out of
/// its OWN pre-funded cell, so a false voucher only hurts the operator).
/// Binding the voucher to a bridge attestation is a named residual in
/// `docs/deos/COMPUTRON-POLICY.md`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RefillVoucher {
    /// The `Payable` asset id the payment was denominated in.
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub asset: [u8; 32],
    /// External asset units paid.
    pub external_amount: u64,
    /// The cell to credit computrons to.
    pub recipient: dregg_cell::CellId,
}

/// Why a computron refill was refused. Every arm is fail-closed: no state
/// changes on refusal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RefillRefused {
    /// Asset absent from the operator's acceptance table (the default).
    AssetNotAccepted,
    /// Asset row present but disabled by the operator.
    AssetDisabled,
    /// Asset row quotes a zero rate (invalid: infinite computrons per unit).
    ZeroRate,
    /// The credit does not fit the ledger's signed 64-bit balance domain.
    CreditOverflow {
        external_amount: u64,
        rate_micros: u64,
    },
    /// The payment converts to zero computrons (dust below one computron);
    /// accepting it would take payment and credit nothing.
    ZeroCredit,
    /// The operator's pre-funded cell cannot cover the credit. A refill is a
    /// CONSERVING transfer, never a mint — an underfunded operator refuses.
    OperatorCellInsufficient { available: i64, required: u64 },
    /// The ledger refused the transfer for another reason (missing operator
    /// or recipient cell, overflow at the destination, …).
    LedgerRejected(String),
}

impl std::fmt::Display for RefillRefused {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AssetNotAccepted => write!(f, "asset not in the operator acceptance table"),
            Self::AssetDisabled => write!(f, "asset disabled by the operator"),
            Self::ZeroRate => write!(f, "asset row quotes a zero rate"),
            Self::CreditOverflow {
                external_amount,
                rate_micros,
            } => write!(
                f,
                "credit overflows the balance domain ({external_amount} units at rate {rate_micros})"
            ),
            Self::ZeroCredit => write!(f, "payment converts to zero computrons"),
            Self::OperatorCellInsufficient {
                available,
                required,
            } => write!(
                f,
                "operator cell holds {available}, refill requires {required}"
            ),
            Self::LedgerRejected(e) => write!(f, "ledger refused the refill transfer: {e}"),
        }
    }
}

/// Convert an external-asset amount to a computron credit under `policy`.
/// Pure and fail-closed: unknown asset, disabled row, zero rate, overflow,
/// and dust-to-zero all refuse.
pub fn computron_credit(
    policy: &FeePolicy,
    asset: &[u8; 32],
    external_amount: u64,
) -> Result<u64, RefillRefused> {
    let row = policy
        .asset_policy(asset)
        .ok_or(RefillRefused::AssetNotAccepted)?;
    if !row.enabled {
        return Err(RefillRefused::AssetDisabled);
    }
    if row.rate_micros == 0 {
        return Err(RefillRefused::ZeroRate);
    }
    // u128 headroom: u64 × 1e6 cannot overflow u128, so the conversion itself
    // is exact; only the RESULT can leave the balance domain.
    let credit =
        (external_amount as u128) * (COMPUTRON_RATE_SCALE as u128) / (row.rate_micros as u128);
    if credit == 0 {
        return Err(RefillRefused::ZeroCredit);
    }
    // The ledger's balance domain is signed 64-bit; a credit above i64::MAX
    // could never be applied (and must not wrap or saturate).
    if credit > i64::MAX as u128 {
        return Err(RefillRefused::CreditOverflow {
            external_amount,
            rate_micros: row.rate_micros,
        });
    }
    Ok(credit as u64)
}

/// Apply an accepted refill: credit `voucher.recipient` with the computron
/// value of the payment as a CONSERVING transfer out of `operator_cell`
/// (mirroring the faucet mechanics in `api.rs::post_faucet` — a transfer,
/// never a mint). Refused, with no state change, when the operator cell lacks
/// balance. Returns the computrons credited.
pub fn apply_computron_refill(
    ledger: &mut dregg_cell::Ledger,
    policy: &FeePolicy,
    operator_cell: dregg_cell::CellId,
    voucher: &RefillVoucher,
) -> Result<u64, RefillRefused> {
    let credit = computron_credit(policy, &voucher.asset, voucher.external_amount)?;
    // Precise refusal when the operator cell cannot cover the credit. The
    // transfer below would also refuse (`apply_delta` forbids a source going
    // below zero), but this surfaces the balances for the operator's log.
    // `credit ≤ i64::MAX` is guaranteed by `computron_credit`'s domain gate.
    if let Some(op) = ledger.get(&operator_cell)
        && op.state.balance() < credit as i64
    {
        return Err(RefillRefused::OperatorCellInsufficient {
            available: op.state.balance(),
            required: credit,
        });
    }
    // The CONSERVING transfer: `computron_transfers` debits the operator cell
    // and credits the recipient atomically — the same ordinary-move discipline
    // the faucet's finalized Transfer turn lands in (`api.rs::post_faucet`).
    // Nothing is created; a missing operator/recipient cell or a destination
    // overflow refuses with the ledger untouched.
    let full = dregg_cell::LedgerDelta {
        created: Vec::new(),
        updated: Vec::new(),
        computron_transfers: vec![(operator_cell, voucher.recipient, credit)],
        removed: Vec::new(),
    };
    ledger
        .apply_delta(&full)
        .map_err(|e| RefillRefused::LedgerRejected(format!("{e:?}")))?;
    Ok(credit)
}

// ─── Service State ────────────────────────────────────────────────────────────

/// Shared relay service state.
pub struct RelayState {
    /// Legacy in-memory queue engine. The storage-template mirror below is the
    /// public cell-program state; this engine remains the byte queue backend
    /// until hosted inbox queues are fully cell-backed.
    pub operator: RelayOperator,
    /// Storage-template cell-program mirror for the relay operator.
    pub template: RelayTemplateState,
    /// Configuration.
    pub config: RelayConfig,
    /// Current block height (updated by the node or a ticker). Used as the finalized
    /// frontier for delivery-proof eviction and the dispute-window gate.
    pub current_height: u64,
    /// Delivered-message proofs: `content_hash -> DeliveryProofRecord`. The sticky
    /// delivery witness the dispute referee reads (its keys are the DELIVERED set).
    /// Bounded by height-keyed eviction past each proof's dispute deadline + a hard
    /// cap (audit #10); see [`DeliveryProofRecord`] and
    /// [`RelayState::evict_expired_delivery_proofs`].
    pub delivery_proofs: std::collections::HashMap<[u8; 32], DeliveryProofRecord>,
    /// Total messages delivered since startup.
    pub messages_delivered: u64,
    /// Total messages received since startup.
    pub messages_received: u64,
}

pub type SharedRelayState = Arc<RwLock<RelayState>>;

/// A cached delivery proof plus the height past which its delivery is FINAL.
///
/// `dispute_deadline = enqueued_at + CUSTODY_DEADLINE_BLOCKS + dispute_window_blocks`
/// — the box's `accept_by` (enqueue + custody horizon) plus the dispute window. Once
/// the finalized frontier (`current_height`) passes it, no dispute over this box is
/// admissible (`relay_dispute::handle_dispute` rejects `current_height > accept_by +
/// window`), so the proof can be evicted without ever flipping an acquit into a
/// slash. See the module-level bounding note.
#[derive(Debug, Clone)]
pub struct DeliveryProofRecord {
    /// The dequeue proof retrieved by `GET /relay/proof/:msg_id`.
    pub proof: DequeueProof,
    /// Finalized height past which the delivery is FINAL and this proof is evictable.
    pub dispute_deadline: u64,
}

impl RelayState {
    /// Evict every cached delivery proof whose dispute deadline has passed below the
    /// finalized frontier `height` — i.e. `height > dispute_deadline` (at `height ==
    /// dispute_deadline` the window is still open, so RETAIN). Returns the count
    /// evicted.
    ///
    /// SLASH-SAFE by construction: `relay_dispute::handle_dispute` rejects any dispute
    /// with `current_height > accept_by + dispute_window`, and each retained proof's
    /// `dispute_deadline >= accept_by + dispute_window` (the receipt-construction
    /// invariant, see [`CUSTODY_DEADLINE_BLOCKS`]). So a proof is only ever dropped at
    /// or after the height at which every dispute that could read it is already
    /// inadmissible — eviction can never turn an acquit into a slash.
    pub fn evict_expired_delivery_proofs(&mut self, height: u64) -> usize {
        let before = self.delivery_proofs.len();
        self.delivery_proofs
            .retain(|_, rec| height <= rec.dispute_deadline);
        before - self.delivery_proofs.len()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RelayTemplateState {
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub factory_vk: [u8; 32],
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub factory_hash: [u8; 32],
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub child_program_vk: [u8; 32],
    pub epoch_duration_blocks: u64,
    pub slots: [[u8; 32]; 8],
    pub hosted_inboxes: BTreeMap<[u8; 32], RelayTemplateHostedInbox>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RelayTemplateHostedInbox {
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub owner: [u8; 32],
    pub committed_capacity: usize,
    pub min_deposit: u64,
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub queue_root: [u8; 32],
    pub pending_messages: usize,
    pub last_drain_height: u64,
    pub evicted: bool,
    pub queue_entries: Vec<RelayTemplateQueueEntry>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RelayTemplateQueueEntry {
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub content_hash: [u8; 32],
    #[serde(serialize_with = "hex_ser_32", deserialize_with = "hex_de_32")]
    pub sender: [u8; 32],
    pub deposit: u64,
    pub enqueued_at: u64,
    pub size: usize,
    /// The retained message body (base64 ciphertext), held until drain.
    /// The queue/proof layer commits only to `content_hash`; the body is
    /// the store-and-forward payload the recipient's crank decrypts. The
    /// hash binds it: a recipient recomputes the content hash from the
    /// delivered body and the dequeue proof's roots cover that hash.
    #[serde(default)]
    pub payload_b64: String,
}

impl From<&RelayTemplateQueueEntry> for QueueEntry {
    fn from(entry: &RelayTemplateQueueEntry) -> Self {
        Self {
            content_hash: entry.content_hash,
            sender: entry.sender,
            deposit: entry.deposit,
            enqueued_at: entry.enqueued_at,
            size: entry.size,
        }
    }
}

impl RelayTemplateState {
    pub fn new(config: &RelayConfig) -> Self {
        let descriptor = relay_operator_factory_descriptor();
        let operator_pk_hash = blake3_field(&config.operator_key);
        let route_table_root = default_route_table_root();
        let quota = config.max_total_capacity as u64;
        Self {
            factory_vk: descriptor.factory_vk,
            factory_hash: descriptor.hash(),
            child_program_vk: relay_operator_child_program_vk(),
            epoch_duration_blocks: DEFAULT_EPOCH_DURATION,
            slots: initial_state(
                config.bond_amount,
                config.bond_amount,
                quota,
                operator_pk_hash,
                route_table_root,
            ),
            hosted_inboxes: BTreeMap::new(),
        }
    }

    pub fn hosted_inbox_root(&self) -> [u8; 32] {
        self.slots[HOSTED_INBOX_ROOT_SLOT as usize]
    }

    pub fn bytes_relayed_this_epoch(&self) -> u64 {
        u64_from_field(self.slots[BYTES_RELAYED_THIS_EPOCH_SLOT as usize])
    }

    pub fn quota_bytes_per_epoch(&self) -> u64 {
        u64_from_field(self.slots[QUOTA_BYTES_PER_EPOCH_SLOT as usize])
    }

    pub fn active_inbox_count(&self) -> usize {
        self.hosted_inboxes
            .values()
            .filter(|inbox| !inbox.evicted)
            .count()
    }

    pub fn total_capacity(&self) -> usize {
        self.hosted_inboxes
            .values()
            .filter(|inbox| !inbox.evicted)
            .map(|inbox| inbox.committed_capacity)
            .sum()
    }

    pub fn total_pending(&self) -> usize {
        self.hosted_inboxes
            .values()
            .filter(|inbox| !inbox.evicted)
            .map(|inbox| inbox.pending_messages)
            .sum()
    }

    fn register_inbox(
        &mut self,
        owner: [u8; 32],
        capacity: usize,
        min_deposit: u64,
        queue_root: [u8; 32],
    ) -> Result<[u8; 32], String> {
        if self
            .hosted_inboxes
            .get(&owner)
            .is_some_and(|inbox| !inbox.evicted)
        {
            return Err("relay template register_inbox rejected already-hosted inbox".into());
        }
        self.hosted_inboxes.insert(
            owner,
            RelayTemplateHostedInbox {
                owner,
                committed_capacity: capacity,
                min_deposit,
                queue_root,
                pending_messages: 0,
                last_drain_height: 0,
                evicted: false,
                queue_entries: Vec::new(),
            },
        );
        self.commit_hosted_root()
    }

    fn mark_inbox_evicted(&mut self, owner: &[u8; 32]) -> Result<[u8; 32], String> {
        let inbox = self
            .hosted_inboxes
            .get_mut(owner)
            .ok_or_else(|| "relay template unsubscribe rejected missing inbox".to_string())?;
        if inbox.evicted {
            return Err("relay template unsubscribe rejected already-evicted inbox".into());
        }
        inbox.evicted = true;
        inbox.pending_messages = 0;
        inbox.queue_root = [0u8; 32];
        inbox.queue_entries.clear();
        self.commit_hosted_root()
    }

    fn record_enqueue(
        &mut self,
        owner: &[u8; 32],
        msg: InboxMessage,
        deposit: u64,
        height: u64,
    ) -> Result<(), String> {
        let before = self.clone();
        let bytes = msg.size() as u64;
        self.record_relay_bytes(bytes)?;
        let inbox = match self.hosted_inboxes.get_mut(owner) {
            Some(inbox) if !inbox.evicted => inbox,
            Some(_) => {
                *self = before;
                return Err("relay template enqueue rejected evicted inbox".into());
            }
            None => {
                *self = before;
                return Err("relay template enqueue rejected missing inbox".into());
            }
        };
        if inbox.pending_messages >= inbox.committed_capacity {
            *self = before;
            return Err("relay template enqueue rejected full inbox".into());
        }
        inbox.queue_entries.push(RelayTemplateQueueEntry {
            content_hash: inbox_message_content_hash(&msg),
            sender: msg.sender(),
            deposit,
            enqueued_at: height,
            size: msg.size(),
            payload_b64: inbox_message_payload_b64(&msg),
        });
        inbox.pending_messages = inbox.queue_entries.len();
        inbox.queue_root = queue_root_from_template_entries(
            inbox.committed_capacity,
            inbox.queue_entries.iter().map(QueueEntry::from),
        )?;
        if let Err(e) = self.commit_hosted_root() {
            *self = before;
            return Err(e);
        }
        Ok(())
    }

    fn drain_inbox(
        &mut self,
        owner: &[u8; 32],
        max: usize,
        height: u64,
    ) -> Result<Vec<(QueueEntry, DequeueProof, String)>, String> {
        let before = self.clone();
        let inbox = match self.hosted_inboxes.get_mut(owner) {
            Some(inbox) if !inbox.evicted => inbox,
            Some(_) => return Err("relay template drain rejected evicted inbox".into()),
            None => return Err("relay template drain rejected missing inbox".into()),
        };
        let drain_count = max.min(inbox.queue_entries.len());
        let mut queue = template_queue_from_entries(
            inbox.committed_capacity,
            inbox.queue_entries.iter().map(QueueEntry::from),
        )?;
        let mut drained = Vec::with_capacity(drain_count);
        for i in 0..drain_count {
            let (entry, proof) = queue
                .dequeue()
                .map_err(|e| format!("relay template drain queue rejected: {e:?}"))?;
            // Deliver the retained body alongside the proof; the entry's
            // content_hash (covered by the proof roots) binds it.
            let payload_b64 = inbox.queue_entries[i].payload_b64.clone();
            drained.push((entry, proof, payload_b64));
        }
        inbox.queue_entries.drain(0..drain_count);
        inbox.pending_messages = inbox.queue_entries.len();
        inbox.queue_root = queue.root();
        inbox.last_drain_height = height;
        if let Err(e) = self.commit_hosted_root() {
            *self = before;
            return Err(e);
        }
        Ok(drained)
    }

    fn validate_enqueue(&self, owner: &[u8; 32], bytes: u64, deposit: u64) -> Result<(), String> {
        let previous = self.bytes_relayed_this_epoch();
        let next = previous
            .checked_add(bytes)
            .ok_or_else(|| "relay template byte counter overflow".to_string())?;
        let quota = self.quota_bytes_per_epoch();
        if next > quota {
            return Err(format!(
                "relay template RateLimitBySum rejected {previous} + {bytes} > {quota}"
            ));
        }
        let inbox = match self.hosted_inboxes.get(owner) {
            Some(inbox) if !inbox.evicted => inbox,
            Some(_) => return Err("relay template enqueue rejected evicted inbox".into()),
            None => return Err("relay template enqueue rejected missing inbox".into()),
        };
        if inbox.pending_messages >= inbox.committed_capacity {
            return Err("relay template enqueue rejected full inbox".into());
        }
        if deposit < inbox.min_deposit {
            return Err(format!(
                "relay template enqueue rejected insufficient deposit {deposit} < {}",
                inbox.min_deposit
            ));
        }
        Ok(())
    }

    fn commit_hosted_root(&mut self) -> Result<[u8; 32], String> {
        let new_root = self.compute_hosted_root();
        if new_root == [0u8; 32] && self.active_inbox_count() > 0 {
            return Err("relay template register_inbox would set zero hosted_inbox_root".into());
        }
        self.slots[HOSTED_INBOX_ROOT_SLOT as usize] = new_root;
        Ok(new_root)
    }

    fn compute_hosted_root(&self) -> [u8; 32] {
        if self.active_inbox_count() == 0 {
            return [0u8; 32];
        }
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"dregg-relay-template-hosted-inbox-root-v1");
        for (owner, inbox) in &self.hosted_inboxes {
            if inbox.evicted {
                continue;
            }
            hasher.update(owner);
            hasher.update(&(inbox.committed_capacity as u64).to_be_bytes());
            hasher.update(&inbox.min_deposit.to_be_bytes());
            hasher.update(&inbox.queue_root);
            hasher.update(&(inbox.pending_messages as u64).to_be_bytes());
            hasher.update(&inbox.last_drain_height.to_be_bytes());
        }
        *hasher.finalize().as_bytes()
    }

    fn record_relay_bytes(&mut self, bytes: u64) -> Result<(), String> {
        let previous = self.bytes_relayed_this_epoch();
        let next = previous
            .checked_add(bytes)
            .ok_or_else(|| "relay template byte counter overflow".to_string())?;
        let quota = self.quota_bytes_per_epoch();
        if next > quota {
            return Err(format!(
                "relay template RateLimitBySum rejected {previous} + {bytes} > {quota}"
            ));
        }
        self.slots[BYTES_RELAYED_THIS_EPOCH_SLOT as usize] = u64_field(next);
        Ok(())
    }

    pub fn relay_case_has_dfa_and_rate_limit(&self) -> bool {
        let program =
            relay_operator_program_with(self.quota_bytes_per_epoch(), self.epoch_duration_blocks);
        let dregg_cell::program::CellProgram::Cases(cases) = program else {
            return false;
        };
        cases.iter().any(|case| {
            matches!(
                &case.guard,
                dregg_cell::program::TransitionGuard::MethodIs { method }
                    if *method == dregg_storage_templates::relay_operator::relay_method_symbol()
            ) && case.constraints.iter().any(|c| {
                matches!(
                    c,
                    dregg_cell::StateConstraint::RateLimitBySum { slot_index, .. }
                        if *slot_index == BYTES_RELAYED_THIS_EPOCH_SLOT
                )
            }) && case.constraints.iter().any(|c| {
                matches!(
                    c,
                    dregg_cell::StateConstraint::Witnessed { wp }
                        if matches!(wp.kind, dregg_cell::predicate::WitnessedPredicateKind::Dfa)
                )
            })
        })
    }
}

// ─── HTTP API Types ───────────────────────────────────────────────────────────

/// GET /relay/status response.
#[derive(Serialize)]
pub struct RelayStatusResponse {
    pub operator_id: String,
    pub relay_template_factory_vk: String,
    pub relay_template_factory_hash: String,
    pub relay_template_child_program_vk: String,
    pub relay_template_hosted_inbox_root: String,
    pub relay_template_bytes_relayed_this_epoch: u64,
    pub relay_template_quota_bytes_per_epoch: u64,
    pub relay_template_dfa_rate_limit_bound: bool,
    pub bond: u64,
    pub required_bond: u64,
    pub is_underbonded: bool,
    pub active_inboxes: usize,
    pub total_pending_messages: usize,
    pub earned_fees: u64,
    pub max_delivery_latency_blocks: u64,
    pub current_height: u64,
    pub messages_delivered: u64,
    pub messages_received: u64,
    pub gc_interval_secs: u64,
}

/// POST /relay/subscribe request.
#[derive(Deserialize)]
pub struct SubscribeRequest {
    /// Owner public key (hex-encoded, 64 chars).
    pub owner: String,
    /// Requested inbox capacity (optional, defaults to config).
    pub capacity: Option<usize>,
    /// Custom minimum deposit (optional, defaults to config).
    pub min_deposit: Option<u64>,
    /// Hex-encoded 8-byte nonce, included in the signed message to bind the
    /// request to a single use (F-P1-1).
    pub nonce: String,
    /// Hex-encoded 64-byte Ed25519 signature over
    /// `b"dregg-relay-subscribe-v1" || owner || nonce`.
    pub signature: String,
}

/// POST /relay/subscribe response.
#[derive(Serialize)]
pub struct SubscribeResponse {
    pub owner: String,
    pub capacity: usize,
    pub min_deposit: u64,
    pub subscription_fee_paid: u64,
    pub relay_template_hosted_inbox_root: String,
}

/// DELETE /relay/unsubscribe request.
#[derive(Deserialize)]
pub struct UnsubscribeRequest {
    /// Owner public key (hex-encoded).
    pub owner: String,
    /// Hex-encoded 8-byte nonce (F-P1-1).
    pub nonce: String,
    /// Hex-encoded 64-byte Ed25519 signature over
    /// `b"dregg-relay-unsubscribe-v1" || owner || nonce`.
    pub signature: String,
}

/// POST /relay/send/:dest request.
#[derive(Deserialize)]
pub struct SendRequest {
    /// Sender public key (hex-encoded).
    pub sender: String,
    /// Message payload (base64-encoded).
    pub payload: String,
    /// Deposit amount (computrons).
    pub deposit: u64,
}

/// POST /relay/send/:dest response.
#[derive(Debug, Serialize)]
pub struct SendResponse {
    pub queue_root: String,
    pub position: usize,
    pub relay_template_bytes_relayed_this_epoch: u64,
}

/// GET /relay/drain request (via query params or auth header).
#[derive(Deserialize)]
pub struct DrainQuery {
    /// Owner public key (hex-encoded).
    pub owner: String,
    /// Maximum messages to drain.
    pub max: Option<usize>,
    /// Hex-encoded 8-byte nonce (F-P1-1).
    pub nonce: String,
    /// Hex-encoded 64-byte Ed25519 signature over
    /// `b"dregg-relay-drain-v1" || owner || nonce || max_le_bytes`.
    pub signature: String,
}

/// GET /relay/drain response.
#[derive(Serialize)]
pub struct DrainResponse {
    pub messages: Vec<DrainedMessage>,
    pub new_root: String,
}

/// A single drained message with proof.
#[derive(Serialize)]
pub struct DrainedMessage {
    pub content_hash: String,
    pub sender: String,
    pub deposit: u64,
    pub enqueued_at: u64,
    /// Entry size in bytes — part of the proof-covered `QueueEntry` leaf.
    pub size: usize,
    pub proof_old_root: String,
    pub proof_new_root: String,
    /// Absolute head index (metadata; NOT root-bound — see `DequeueProof`).
    pub proof_position: usize,
    /// Leaf hashes of the entries remaining after this dequeue, FIFO (hex).
    /// Together with the roots + the entry fields this is the FULL
    /// `dregg_storage::queue::DequeueProof`, so the recipient's crank can
    /// run `verify_dequeue_proof{,_against}` itself.
    pub proof_remaining_leaves: Vec<String>,
    /// Base64 ciphertext body, retained from send. `content_hash` (covered
    /// by the dequeue proof's roots) binds it — recipients MUST recompute
    /// and compare.
    pub payload: String,
}

/// GET /relay/inbox/:id/status response.
#[derive(Serialize)]
pub struct InboxStatusResponse {
    pub owner: String,
    pub pending_messages: usize,
    pub committed_capacity: usize,
    pub queue_root: String,
    pub last_drain_height: u64,
    pub evicted: bool,
}

/// GET /relay/proof/:msg_id response.
#[derive(Serialize)]
pub struct ProofResponse {
    pub msg_id: String,
    pub old_root: String,
    pub new_root: String,
    pub found: bool,
}

/// Generic error response.
#[derive(Debug, Serialize)]
pub struct ErrorResponse {
    pub error: String,
}

// ─── Router ───────────────────────────────────────────────────────────────────

/// Build the relay service HTTP router.
pub fn relay_router(state: SharedRelayState) -> Router {
    Router::new()
        .route("/relay/status", get(handle_status))
        .route("/relay/subscribe", post(handle_subscribe))
        .route("/relay/unsubscribe", delete(handle_unsubscribe))
        .route("/relay/send/{dest}", post(handle_send))
        .route("/relay/drain", get(handle_drain))
        .route("/relay/inbox/{id}/status", get(handle_inbox_status))
        .route("/relay/proof/{msg_id}", get(handle_proof))
        .route("/relay/dispute", post(crate::relay_dispute::handle_dispute))
        .with_state(state)
}

// ─── Auth helpers (F-P1-1) ────────────────────────────────────────────────────

/// Verify an Ed25519 signature over a domain-separated message that the
/// `owner` is supposed to have signed. Used to gate subscribe/unsubscribe/drain
/// (F-P1-1).
fn verify_owner_signature(
    owner: &[u8; 32],
    signature_hex: &str,
    domain: &[u8],
    payload: &[u8],
) -> Result<(), &'static str> {
    use ed25519_dalek::{Signature, Verifier, VerifyingKey};

    let sig_bytes = hex_decode_var(signature_hex).map_err(|_| "invalid signature hex")?;
    if sig_bytes.len() != 64 {
        return Err("signature must be 64 bytes");
    }
    let mut sig_arr = [0u8; 64];
    sig_arr.copy_from_slice(&sig_bytes);
    let sig = Signature::from_bytes(&sig_arr);
    let vk = VerifyingKey::from_bytes(owner).map_err(|_| "invalid owner public key")?;

    let mut msg = Vec::with_capacity(domain.len() + payload.len());
    msg.extend_from_slice(domain);
    msg.extend_from_slice(payload);

    vk.verify(&msg, &sig)
        .map_err(|_| "signature does not verify")
}

fn hex_decode_var(s: &str) -> Result<Vec<u8>, ()> {
    if !s.is_ascii() || !s.len().is_multiple_of(2) {
        return Err(());
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    for i in 0..s.len() / 2 {
        out.push(u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).map_err(|_| ())?);
    }
    Ok(out)
}

// ─── Handlers ─────────────────────────────────────────────────────────────────

async fn handle_status(State(state): State<SharedRelayState>) -> Json<RelayStatusResponse> {
    let s = state.read().await;
    Json(RelayStatusResponse {
        operator_id: hex_encode(&s.operator.id),
        relay_template_factory_vk: hex_encode(&s.template.factory_vk),
        relay_template_factory_hash: hex_encode(&s.template.factory_hash),
        relay_template_child_program_vk: hex_encode(&s.template.child_program_vk),
        relay_template_hosted_inbox_root: hex_encode(&s.template.hosted_inbox_root()),
        relay_template_bytes_relayed_this_epoch: s.template.bytes_relayed_this_epoch(),
        relay_template_quota_bytes_per_epoch: s.template.quota_bytes_per_epoch(),
        relay_template_dfa_rate_limit_bound: s.template.relay_case_has_dfa_and_rate_limit(),
        bond: s.operator.bond,
        required_bond: s.operator.required_bond(),
        is_underbonded: s.operator.is_underbonded(),
        active_inboxes: s.template.active_inbox_count(),
        total_pending_messages: s.template.total_pending(),
        earned_fees: s.operator.earned_fees,
        max_delivery_latency_blocks: s.operator.max_delivery_latency,
        current_height: s.current_height,
        messages_delivered: s.messages_delivered,
        messages_received: s.messages_received,
        gc_interval_secs: s.config.gc_interval_secs,
    })
}

async fn handle_subscribe(
    State(state): State<SharedRelayState>,
    Json(req): Json<SubscribeRequest>,
) -> Result<Json<SubscribeResponse>, (StatusCode, Json<ErrorResponse>)> {
    let owner = hex_decode_32(&req.owner).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid owner key (expected 64 hex chars)".to_string(),
            }),
        )
    })?;

    // F-P1-1: require an Ed25519 signature from `owner` over a domain-separated
    // (owner, nonce) tuple. Without this, any network attacker could subscribe
    // an inbox in another user's name.
    let nonce_bytes = hex_decode_var(&req.nonce).map_err(|_| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid nonce hex".to_string(),
            }),
        )
    })?;
    let mut payload = Vec::with_capacity(32 + nonce_bytes.len());
    payload.extend_from_slice(&owner);
    payload.extend_from_slice(&nonce_bytes);
    if let Err(e) = verify_owner_signature(
        &owner,
        &req.signature,
        b"dregg-relay-subscribe-v1",
        &payload,
    ) {
        return Err((
            StatusCode::FORBIDDEN,
            Json(ErrorResponse {
                error: format!("subscribe signature rejected: {e}"),
            }),
        ));
    }

    let mut s = state.write().await;
    let capacity = req.capacity.unwrap_or(s.config.default_inbox_capacity);
    let min_deposit = req.min_deposit.unwrap_or(s.config.default_min_deposit);

    // Check total capacity limit.
    let current_total = s.template.total_capacity();
    if current_total + capacity > s.config.max_total_capacity {
        return Err((
            StatusCode::SERVICE_UNAVAILABLE,
            Json(ErrorResponse {
                error: format!(
                    "would exceed max total capacity ({} + {} > {})",
                    current_total, capacity, s.config.max_total_capacity
                ),
            }),
        ));
    }

    s.operator
        .host_inbox(owner, capacity, min_deposit)
        .map_err(|e| {
            let msg = format!("{e:?}");
            let status = match &e {
                dregg_storage::relay::RelayError::AlreadyHosted { .. } => StatusCode::CONFLICT,
                dregg_storage::relay::RelayError::Underbonded { .. } => {
                    StatusCode::SERVICE_UNAVAILABLE
                }
                _ => StatusCode::BAD_REQUEST,
            };
            (status, Json(ErrorResponse { error: msg }))
        })?;
    let queue_root = s.operator.inbox_root(&owner).unwrap_or([0u8; 32]);
    let hosted_root = s
        .template
        .register_inbox(owner, capacity, min_deposit, queue_root)
        .map_err(|e| {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(ErrorResponse { error: e }),
            )
        })?;

    let fee = s.config.fee_policy.subscription_fee;
    info!(
        owner = %req.owner,
        capacity = capacity,
        "new inbox subscription"
    );

    Ok(Json(SubscribeResponse {
        owner: req.owner,
        capacity,
        min_deposit,
        subscription_fee_paid: fee,
        relay_template_hosted_inbox_root: hex_encode(&hosted_root),
    }))
}

async fn handle_unsubscribe(
    State(state): State<SharedRelayState>,
    Json(req): Json<UnsubscribeRequest>,
) -> Result<Json<serde_json::Value>, (StatusCode, Json<ErrorResponse>)> {
    let owner = hex_decode_32(&req.owner).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid owner key".to_string(),
            }),
        )
    })?;

    // F-P1-1: require Ed25519 signature from owner.
    let nonce_bytes = hex_decode_var(&req.nonce).map_err(|_| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid nonce hex".to_string(),
            }),
        )
    })?;
    let mut payload = Vec::with_capacity(32 + nonce_bytes.len());
    payload.extend_from_slice(&owner);
    payload.extend_from_slice(&nonce_bytes);
    if let Err(e) = verify_owner_signature(
        &owner,
        &req.signature,
        b"dregg-relay-unsubscribe-v1",
        &payload,
    ) {
        return Err((
            StatusCode::FORBIDDEN,
            Json(ErrorResponse {
                error: format!("unsubscribe signature rejected: {e}"),
            }),
        ));
    }

    let mut s = state.write().await;
    let refunds = s.operator.evict_inbox(&owner);
    s.template.mark_inbox_evicted(&owner).map_err(|e| {
        (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(ErrorResponse { error: e }),
        )
    })?;

    info!(
        owner = %req.owner,
        refunds = refunds.len(),
        "inbox unsubscribed (evicted)"
    );

    Ok(Json(serde_json::json!({
        "owner": req.owner,
        "refunds_issued": refunds.len(),
        "total_refunded": refunds.iter().map(|r| r.amount).sum::<u64>(),
    })))
}

async fn handle_send(
    State(state): State<SharedRelayState>,
    Path(dest): Path<String>,
    Json(req): Json<SendRequest>,
) -> Result<Json<SendResponse>, (StatusCode, Json<ErrorResponse>)> {
    let destination = hex_decode_32(&dest).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid destination key (expected 64 hex chars)".to_string(),
            }),
        )
    })?;

    let sender = hex_decode_32(&req.sender).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid sender key".to_string(),
            }),
        )
    })?;

    let payload = base64_decode(&req.payload).map_err(|e| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: format!("invalid base64 payload: {e}"),
            }),
        )
    })?;

    let mut s = state.write().await;
    let current_height = s.current_height;

    let msg = InboxMessage::Encrypted {
        ciphertext: payload,
        sender,
    };
    let relayed_bytes = match &msg {
        InboxMessage::Encrypted { ciphertext, .. } => ciphertext.len() as u64,
        InboxMessage::Capability { cert_bytes, .. } => cert_bytes.len() as u64,
        InboxMessage::SturdyRef { uri, .. } => uri.len() as u64,
    };
    s.template
        .validate_enqueue(&destination, relayed_bytes, req.deposit)
        .map_err(|e| {
            let status = if e.contains("missing inbox") {
                StatusCode::NOT_FOUND
            } else if e.contains("insufficient deposit") {
                StatusCode::PAYMENT_REQUIRED
            } else {
                StatusCode::SERVICE_UNAVAILABLE
            };
            (status, Json(ErrorResponse { error: e }))
        })?;
    s.template
        .record_enqueue(&destination, msg, req.deposit, current_height)
        .map_err(|e| {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(ErrorResponse { error: e }),
            )
        })?;

    s.messages_received += 1;
    let pending = s.template.total_pending();
    let bytes_relayed = s.template.bytes_relayed_this_epoch();
    let root = s
        .template
        .hosted_inboxes
        .get(&destination)
        .map(|inbox| inbox.queue_root)
        .unwrap_or([0u8; 32]);

    Ok(Json(SendResponse {
        queue_root: hex_encode(&root),
        position: pending,
        relay_template_bytes_relayed_this_epoch: bytes_relayed,
    }))
}

async fn handle_drain(
    State(state): State<SharedRelayState>,
    axum::extract::Query(query): axum::extract::Query<DrainQuery>,
) -> Result<Json<DrainResponse>, (StatusCode, Json<ErrorResponse>)> {
    let owner = hex_decode_32(&query.owner).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid owner key".to_string(),
            }),
        )
    })?;

    let max = query.max.unwrap_or(100);

    // F-P1-1: require Ed25519 signature from `owner` over (owner, nonce, max).
    // Without this, anyone on the network could drain any inbox.
    let nonce_bytes = hex_decode_var(&query.nonce).map_err(|_| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid nonce hex".to_string(),
            }),
        )
    })?;
    let mut payload = Vec::with_capacity(32 + nonce_bytes.len() + 8);
    payload.extend_from_slice(&owner);
    payload.extend_from_slice(&nonce_bytes);
    payload.extend_from_slice(&(max as u64).to_le_bytes());
    if let Err(e) =
        verify_owner_signature(&owner, &query.signature, b"dregg-relay-drain-v1", &payload)
    {
        return Err((
            StatusCode::FORBIDDEN,
            Json(ErrorResponse {
                error: format!("drain signature rejected: {e}"),
            }),
        ));
    }

    let mut s = state.write().await;
    let current_height = s.current_height;
    let dispute_window = s.config.dispute_window_blocks;
    // Bound the delivery-proof cache (audit #10). First evict proofs past their
    // dispute deadline (below the finalized frontier); then cap how many NEW proofs
    // this drain may cache to the remaining room. We deliver only as many boxes as we
    // can WITNESS: a box we cannot cache stays enqueued (still in custody, no witness
    // gap) — backpressure under a flood, never dropping a within-window proof (which
    // could wrongly slash). In normal operation the cache is far below the cap, so
    // `effective_max == max`.
    s.evict_expired_delivery_proofs(current_height);
    let room = s
        .config
        .max_delivery_proofs
        .saturating_sub(s.delivery_proofs.len());
    let effective_max = max.min(room);
    let drained = s
        .template
        .drain_inbox(&owner, effective_max, current_height)
        .map_err(|e| {
            let status = if e.contains("missing inbox") {
                StatusCode::NOT_FOUND
            } else {
                StatusCode::BAD_REQUEST
            };
            (status, Json(ErrorResponse { error: e }))
        })?;
    // Store delivery proofs and build response.
    let messages: Vec<DrainedMessage> = drained
        .into_iter()
        .map(|(entry, proof, payload)| {
            // Cache the proof, stamped with the height past which its delivery is
            // FINAL: accept_by (= enqueued_at + custody horizon) + the dispute window.
            // `evict_expired_delivery_proofs` drops it only past this height, which is
            // exactly when every dispute over it is inadmissible (see handle_dispute).
            let dispute_deadline = entry
                .enqueued_at
                .saturating_add(CUSTODY_DEADLINE_BLOCKS)
                .saturating_add(dispute_window);
            s.delivery_proofs.insert(
                entry.content_hash,
                DeliveryProofRecord {
                    proof: proof.clone(),
                    dispute_deadline,
                },
            );
            s.messages_delivered += 1;

            DrainedMessage {
                content_hash: hex_encode(&entry.content_hash),
                sender: hex_encode(&entry.sender),
                deposit: entry.deposit,
                enqueued_at: entry.enqueued_at,
                size: entry.size,
                proof_old_root: hex_encode(&proof.old_root),
                proof_new_root: hex_encode(&proof.new_root),
                proof_position: proof.position,
                proof_remaining_leaves: proof
                    .remaining_leaves
                    .iter()
                    .map(|leaf| hex_encode(leaf))
                    .collect(),
                payload,
            }
        })
        .collect();

    let new_root = s
        .template
        .hosted_inboxes
        .get(&owner)
        .map(|inbox| inbox.queue_root)
        .unwrap_or([0u8; 32]);

    Ok(Json(DrainResponse {
        messages,
        new_root: hex_encode(&new_root),
    }))
}

async fn handle_inbox_status(
    State(state): State<SharedRelayState>,
    Path(id): Path<String>,
) -> Result<Json<InboxStatusResponse>, (StatusCode, Json<ErrorResponse>)> {
    let owner = hex_decode_32(&id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid inbox id (expected 64 hex chars)".to_string(),
            }),
        )
    })?;

    let s = state.read().await;
    let hosted = s.template.hosted_inboxes.get(&owner).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "inbox not found".to_string(),
            }),
        )
    })?;

    Ok(Json(InboxStatusResponse {
        owner: id,
        pending_messages: hosted.pending_messages,
        committed_capacity: hosted.committed_capacity,
        queue_root: hex_encode(&hosted.queue_root),
        last_drain_height: hosted.last_drain_height,
        evicted: hosted.evicted,
    }))
}

async fn handle_proof(
    State(state): State<SharedRelayState>,
    Path(msg_id): Path<String>,
) -> Result<Json<ProofResponse>, (StatusCode, Json<ErrorResponse>)> {
    let msg_hash = hex_decode_32(&msg_id).ok_or_else(|| {
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "invalid msg_id (expected 64 hex chars)".to_string(),
            }),
        )
    })?;

    let s = state.read().await;
    if let Some(rec) = s.delivery_proofs.get(&msg_hash) {
        Ok(Json(ProofResponse {
            msg_id,
            old_root: hex_encode(&rec.proof.old_root),
            new_root: hex_encode(&rec.proof.new_root),
            found: true,
        }))
    } else {
        Ok(Json(ProofResponse {
            msg_id,
            old_root: String::new(),
            new_root: String::new(),
            found: false,
        }))
    }
}

// ─── Service Lifecycle ────────────────────────────────────────────────────────

/// Start the relay service: initialize operator, spawn GC task, serve HTTP.
pub async fn run_relay_service(config: RelayConfig) {
    info!(
        port = config.listen_port,
        bond = config.bond_amount,
        max_capacity = config.max_total_capacity,
        gc_interval = config.gc_interval_secs,
        state_file = %config.state_file.display(),
        "starting relay operator service"
    );

    // Initialize the relay operator.
    let operator = RelayOperator::new(
        config.operator_key,
        config.bond_amount,
        config.max_delivery_latency_blocks,
    );
    let template = RelayTemplateState::new(&config);

    let relay_state = Arc::new(RwLock::new(RelayState {
        operator,
        template,
        config: config.clone(),
        current_height: 0,
        delivery_proofs: std::collections::HashMap::new(),
        messages_delivered: 0,
        messages_received: 0,
    }));

    // Spawn the GC background task.
    let gc_state = relay_state.clone();
    let gc_interval = config.gc_interval_secs;
    let message_ttl = config.message_ttl_blocks;
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(gc_interval));
        loop {
            interval.tick().await;
            let mut s = gc_state.write().await;
            let height = s.current_height;
            // Bound delivery_proofs (audit #10): evict every proof past its dispute
            // deadline (below the finalized frontier). Slash-safe — see
            // `RelayState::evict_expired_delivery_proofs`.
            let delivery_proofs_evicted = s.evict_expired_delivery_proofs(height);
            let result = s.operator.gc_expired(height, message_ttl);
            if result.messages_collected > 0 || delivery_proofs_evicted > 0 {
                info!(
                    collected = result.messages_collected,
                    operator_fees = result.operator_fees,
                    refunds = result.sender_refunds.len(),
                    delivery_proofs_evicted,
                    delivery_proofs_live = s.delivery_proofs.len(),
                    "relay GC pass completed"
                );
            }
        }
    });

    // Spawn a block height ticker (simulates block production for standalone mode).
    let height_state = relay_state.clone();
    tokio::spawn(async move {
        let mut interval = tokio::time::interval(Duration::from_secs(12));
        loop {
            interval.tick().await;
            let mut s = height_state.write().await;
            s.current_height += 1;
        }
    });

    // Build and serve the HTTP API.
    let app = relay_router(relay_state);

    let addr = std::net::SocketAddr::new(
        std::net::IpAddr::V4(std::net::Ipv4Addr::new(0, 0, 0, 0)),
        config.listen_port,
    );

    info!(%addr, "relay service HTTP API listening");

    let listener = tokio::net::TcpListener::bind(addr)
        .await
        .expect("failed to bind relay HTTP listener");

    axum::serve(listener, app)
        .with_graceful_shutdown(async {
            tokio::signal::ctrl_c()
                .await
                .expect("failed to listen for Ctrl-C");
            info!("relay service shutting down");
        })
        .await
        .expect("relay HTTP server error");
}

// ─── Utility Functions ────────────────────────────────────────────────────────

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn u64_field(value: u64) -> [u8; 32] {
    let mut field = [0u8; 32];
    field[24..].copy_from_slice(&value.to_be_bytes());
    field
}

fn u64_from_field(field: [u8; 32]) -> u64 {
    u64::from_be_bytes(field[24..].try_into().expect("field suffix is 8 bytes"))
}

fn blake3_field(bytes: &[u8]) -> [u8; 32] {
    *blake3::hash(bytes).as_bytes()
}

fn default_route_table_root() -> [u8; 32] {
    blake3_field(b"dregg-relay-route-table-v1:any-encrypted-message")
}

fn inbox_message_content_hash(msg: &InboxMessage) -> [u8; 32] {
    let mut buf = Vec::new();
    match msg {
        InboxMessage::Capability { cert_bytes, sender } => {
            buf.push(0x01);
            buf.extend_from_slice(sender);
            buf.extend_from_slice(cert_bytes);
        }
        InboxMessage::SturdyRef { uri, sender } => {
            buf.push(0x02);
            buf.extend_from_slice(sender);
            buf.extend_from_slice(uri.as_bytes());
        }
        InboxMessage::Encrypted { ciphertext, sender } => {
            buf.push(0x03);
            buf.extend_from_slice(sender);
            buf.extend_from_slice(ciphertext);
        }
    }
    *blake3::hash(&buf).as_bytes()
}

/// Base64 of the message body the relay retains for delivery (the same bytes
/// `inbox_message_content_hash` commits to, minus the tag/sender framing).
fn inbox_message_payload_b64(msg: &InboxMessage) -> String {
    use base64::Engine;
    let body: &[u8] = match msg {
        InboxMessage::Capability { cert_bytes, .. } => cert_bytes,
        InboxMessage::SturdyRef { uri, .. } => uri.as_bytes(),
        InboxMessage::Encrypted { ciphertext, .. } => ciphertext,
    };
    base64::engine::general_purpose::STANDARD.encode(body)
}

fn template_queue_from_entries(
    capacity: usize,
    entries: impl IntoIterator<Item = QueueEntry>,
) -> Result<MerkleQueue, String> {
    let mut queue = MerkleQueue::new(capacity);
    for entry in entries {
        queue
            .enqueue(entry)
            .map_err(|e| format!("relay template queue rebuild rejected: {e:?}"))?;
    }
    Ok(queue)
}

fn queue_root_from_template_entries(
    capacity: usize,
    entries: impl IntoIterator<Item = QueueEntry>,
) -> Result<[u8; 32], String> {
    Ok(template_queue_from_entries(capacity, entries)?.root())
}

fn hex_decode_32(s: &str) -> Option<[u8; 32]> {
    if !s.is_ascii() || s.len() != 64 {
        return None;
    }
    let mut bytes = [0u8; 32];
    for (i, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(bytes)
}

fn base64_decode(s: &str) -> Result<Vec<u8>, String> {
    use base64::Engine;
    base64::engine::general_purpose::STANDARD
        .decode(s)
        .map_err(|e| e.to_string())
}

fn hex_ser_32<S: serde::Serializer>(bytes: &[u8; 32], s: S) -> Result<S::Ok, S::Error> {
    s.serialize_str(&hex_encode(bytes))
}

fn hex_de_32<'de, D: serde::Deserializer<'de>>(d: D) -> Result<[u8; 32], D::Error> {
    let s = String::deserialize(d)?;
    hex_decode_32(&s).ok_or_else(|| serde::de::Error::custom("expected 64 hex chars"))
}

// ─── Adversarial tests for F-P1-1 (relay caller-authentication) ──────────────
//
// These tests exercise `verify_owner_signature` directly. The handlers
// themselves are thin wrappers around the verifier (see handle_subscribe,
// handle_unsubscribe, handle_drain) so verifying the verifier is sufficient
// to demonstrate the regression-coverage. A future router-level integration
// test (deferred while sdk/cell rebuild is in flight) would also exercise
// the wiring.

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::{Signer, SigningKey};

    fn make_key(seed_byte: u8) -> (SigningKey, [u8; 32]) {
        let mut seed = [0u8; 32];
        seed[0] = seed_byte;
        let sk = SigningKey::from_bytes(&seed);
        let pk = sk.verifying_key().to_bytes();
        (sk, pk)
    }

    #[test]
    fn hex_decoders_reject_non_ascii_input() {
        let variable = format!("a\u{e9}0");
        assert_eq!(variable.len(), 4);
        assert!(hex_decode_var(&variable).is_err());

        let fixed = format!("a\u{e9}{}", "0".repeat(61));
        assert_eq!(fixed.len(), 64);
        assert_eq!(hex_decode_32(&fixed), None);
    }

    fn test_config() -> RelayConfig {
        RelayConfig {
            operator_key: [0xAA; 32],
            bond_amount: 10_000,
            max_total_capacity: 64,
            default_inbox_capacity: 8,
            default_min_deposit: 1,
            ..RelayConfig::default()
        }
    }

    fn test_state(config: RelayConfig) -> RelayState {
        RelayState {
            operator: RelayOperator::new(
                config.operator_key,
                config.bond_amount,
                config.max_delivery_latency_blocks,
            ),
            template: RelayTemplateState::new(&config),
            config,
            current_height: 0,
            delivery_proofs: std::collections::HashMap::new(),
            messages_delivered: 0,
            messages_received: 0,
        }
    }

    fn sign_request(sk: &SigningKey, domain: &[u8], payload: &[u8]) -> String {
        let mut full = Vec::new();
        full.extend_from_slice(domain);
        full.extend_from_slice(payload);
        sk.sign(&full)
            .to_bytes()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect()
    }

    fn signed_subscribe(sk: &SigningKey, owner: [u8; 32]) -> SubscribeRequest {
        let nonce = b"sub1";
        let mut payload = Vec::new();
        payload.extend_from_slice(&owner);
        payload.extend_from_slice(nonce);
        SubscribeRequest {
            owner: hex_encode(&owner),
            capacity: Some(2),
            min_deposit: Some(1),
            nonce: hex_encode(nonce),
            signature: sign_request(sk, b"dregg-relay-subscribe-v1", &payload),
        }
    }

    /// F-P1-1: an unsigned drain request must be rejected. (The verifier is
    /// the choke-point: an empty/garbage signature must not be accepted.)
    #[test]
    fn audit_f_p1_1_unsigned_drain_rejected() {
        let (_sk, pk) = make_key(1);
        let payload = b"\x00\x01\x02";
        // Empty signature.
        assert!(verify_owner_signature(&pk, "", b"dregg-relay-drain-v1", payload).is_err());
        // Garbage signature.
        let bad = "ff".repeat(64);
        assert!(verify_owner_signature(&pk, &bad, b"dregg-relay-drain-v1", payload).is_err());
    }

    /// F-P1-1: a drain signature by another key (key A) but claiming to be
    /// from a different owner (key B) MUST be rejected.
    #[test]
    fn audit_f_p1_1_wrong_signer_rejected() {
        let (sk_a, _pk_a) = make_key(1);
        let (_sk_b, pk_b) = make_key(2);
        let mut payload = Vec::new();
        payload.extend_from_slice(&pk_b);
        payload.extend_from_slice(b"nonce123");
        // Sign with A's key but verify against B.
        let mut full = Vec::new();
        full.extend_from_slice(b"dregg-relay-drain-v1");
        full.extend_from_slice(&payload);
        let sig = sk_a.sign(&full);
        let sig_hex: String = sig.to_bytes().iter().map(|b| format!("{b:02x}")).collect();

        assert!(
            verify_owner_signature(&pk_b, &sig_hex, b"dregg-relay-drain-v1", &payload).is_err(),
            "must reject when signer != claimed owner"
        );
    }

    /// F-P1-1: a correctly-signed drain request passes.
    #[test]
    fn audit_f_p1_1_valid_drain_signature_accepted() {
        let (sk, pk) = make_key(7);
        let mut payload = Vec::new();
        payload.extend_from_slice(&pk);
        payload.extend_from_slice(b"nonce456");
        payload.extend_from_slice(&100u64.to_le_bytes());

        let mut full = Vec::new();
        full.extend_from_slice(b"dregg-relay-drain-v1");
        full.extend_from_slice(&payload);
        let sig = sk.sign(&full);
        let sig_hex: String = sig.to_bytes().iter().map(|b| format!("{b:02x}")).collect();

        assert!(
            verify_owner_signature(&pk, &sig_hex, b"dregg-relay-drain-v1", &payload).is_ok(),
            "valid signature should pass"
        );
    }

    /// F-P1-1: a drain signature signed for a DIFFERENT domain (e.g.,
    /// subscribe) must NOT be replayable as a drain signature.
    #[test]
    fn audit_f_p1_1_cross_domain_replay_rejected() {
        let (sk, pk) = make_key(11);
        let payload = b"some-payload";

        // Sign for subscribe.
        let mut full = Vec::new();
        full.extend_from_slice(b"dregg-relay-subscribe-v1");
        full.extend_from_slice(payload);
        let sig = sk.sign(&full);
        let sig_hex: String = sig.to_bytes().iter().map(|b| format!("{b:02x}")).collect();

        // Verifies under subscribe domain.
        assert!(
            verify_owner_signature(&pk, &sig_hex, b"dregg-relay-subscribe-v1", payload).is_ok()
        );
        // Replayed as drain: rejected.
        assert!(verify_owner_signature(&pk, &sig_hex, b"dregg-relay-drain-v1", payload).is_err());
        // Replayed as unsubscribe: rejected.
        assert!(
            verify_owner_signature(&pk, &sig_hex, b"dregg-relay-unsubscribe-v1", payload).is_err()
        );
    }

    /// F-P1-1: the request structs require nonce + signature fields. Verify
    /// the deserialization layer rejects requests that omit them.
    #[test]
    fn audit_f_p1_1_subscribe_schema_requires_signature() {
        let bad = serde_json::json!({
            "owner": "ab".repeat(32),
        });
        assert!(serde_json::from_value::<SubscribeRequest>(bad).is_err());

        let good = serde_json::json!({
            "owner": "ab".repeat(32),
            "nonce": "0011",
            "signature": "00".repeat(64),
        });
        assert!(serde_json::from_value::<SubscribeRequest>(good).is_ok());
    }

    /// F-P1-1: same for unsubscribe.
    #[test]
    fn audit_f_p1_1_unsubscribe_schema_requires_signature() {
        let bad = serde_json::json!({
            "owner": "ab".repeat(32),
        });
        assert!(serde_json::from_value::<UnsubscribeRequest>(bad).is_err());

        let good = serde_json::json!({
            "owner": "ab".repeat(32),
            "nonce": "0011",
            "signature": "00".repeat(64),
        });
        assert!(serde_json::from_value::<UnsubscribeRequest>(good).is_ok());
    }

    #[test]
    fn relay_template_mirror_binds_canonical_descriptor_and_dfa_rate_limit_case() {
        let config = test_config();
        let template = RelayTemplateState::new(&config);
        let descriptor = relay_operator_factory_descriptor();

        assert_eq!(template.factory_vk, descriptor.factory_vk);
        assert_eq!(template.factory_hash, descriptor.hash());
        assert_eq!(template.child_program_vk, relay_operator_child_program_vk());
        assert_eq!(
            template.quota_bytes_per_epoch(),
            config.max_total_capacity as u64
        );
        assert!(template.relay_case_has_dfa_and_rate_limit());
    }

    #[tokio::test]
    async fn relay_template_subscribe_updates_hosted_root() {
        let (sk, owner) = make_key(21);
        let state = Arc::new(RwLock::new(test_state(test_config())));
        let before = state.read().await.template.hosted_inbox_root();

        let response = handle_subscribe(State(state.clone()), Json(signed_subscribe(&sk, owner)))
            .await
            .expect("subscribe should succeed")
            .0;

        let after = state.read().await.template.hosted_inbox_root();
        assert_ne!(before, after);
        assert_ne!(after, [0u8; 32]);
        assert_eq!(
            response.relay_template_hosted_inbox_root,
            hex_encode(&after)
        );
    }

    #[tokio::test]
    async fn relay_template_inbox_status_uses_template_registry() {
        let (sk, owner) = make_key(23);
        let state = Arc::new(RwLock::new(test_state(test_config())));
        let _ = handle_subscribe(State(state.clone()), Json(signed_subscribe(&sk, owner)))
            .await
            .expect("subscribe should succeed");

        state.write().await.operator.hosted_inboxes.remove(&owner);

        let response = handle_inbox_status(State(state), Path(hex_encode(&owner)))
            .await
            .expect("template registry should be sufficient for status")
            .0;

        assert_eq!(response.owner, hex_encode(&owner));
        assert_eq!(response.committed_capacity, 2);
        assert_eq!(response.pending_messages, 0);
        assert!(!response.evicted);
    }

    #[tokio::test]
    async fn relay_template_unsubscribe_updates_hosted_root_and_status() {
        let (sk, owner) = make_key(24);
        let state = Arc::new(RwLock::new(test_state(test_config())));
        let _ = handle_subscribe(State(state.clone()), Json(signed_subscribe(&sk, owner)))
            .await
            .expect("subscribe should succeed");
        let before = state.read().await.template.hosted_inbox_root();

        let nonce = b"unsub1";
        let mut payload = Vec::new();
        payload.extend_from_slice(&owner);
        payload.extend_from_slice(nonce);
        let response = handle_unsubscribe(
            State(state.clone()),
            Json(UnsubscribeRequest {
                owner: hex_encode(&owner),
                nonce: hex_encode(nonce),
                signature: sign_request(&sk, b"dregg-relay-unsubscribe-v1", &payload),
            }),
        )
        .await
        .expect("unsubscribe should succeed")
        .0;

        assert_eq!(response["refunds_issued"], 0);
        let status = handle_inbox_status(State(state.clone()), Path(hex_encode(&owner)))
            .await
            .expect("evicted template inbox remains inspectable")
            .0;
        assert!(status.evicted);
        assert_eq!(status.queue_root, hex_encode(&[0u8; 32]));
        assert_ne!(state.read().await.template.hosted_inbox_root(), before);
    }

    #[tokio::test]
    async fn relay_template_send_is_rate_limited_by_counter() {
        let (sk, owner) = make_key(22);
        let state = Arc::new(RwLock::new(test_state(RelayConfig {
            max_total_capacity: 4,
            ..test_config()
        })));
        let _ = handle_subscribe(State(state.clone()), Json(signed_subscribe(&sk, owner)))
            .await
            .expect("subscribe should succeed");

        let err = handle_send(
            State(state.clone()),
            Path(hex_encode(&owner)),
            Json(SendRequest {
                sender: hex_encode(&[0xBC; 32]),
                payload: {
                    use base64::Engine;
                    base64::engine::general_purpose::STANDARD.encode([1u8; 5])
                },
                deposit: 1,
            }),
        )
        .await
        .expect_err("template RateLimitBySum mirror should reject oversized send");

        assert_eq!(err.0, StatusCode::SERVICE_UNAVAILABLE);
        assert_eq!(state.read().await.template.bytes_relayed_this_epoch(), 0);
    }

    #[tokio::test]
    async fn relay_template_rejects_missing_inbox_before_backend_send() {
        let state = Arc::new(RwLock::new(test_state(test_config())));
        let missing_owner = [0xCD; 32];

        let err = handle_send(
            State(state.clone()),
            Path(hex_encode(&missing_owner)),
            Json(SendRequest {
                sender: hex_encode(&[0xBC; 32]),
                payload: {
                    use base64::Engine;
                    base64::engine::general_purpose::STANDARD.encode([1u8; 3])
                },
                deposit: 1,
            }),
        )
        .await
        .expect_err("legacy queue should still reject missing inbox");

        assert_eq!(err.0, StatusCode::NOT_FOUND);
        assert_eq!(state.read().await.template.bytes_relayed_this_epoch(), 0);
    }

    #[tokio::test]
    async fn relay_template_send_and_drain_do_not_need_operator_queue_backend() {
        let (sk, owner) = make_key(25);
        let state = Arc::new(RwLock::new(test_state(test_config())));
        let _ = handle_subscribe(State(state.clone()), Json(signed_subscribe(&sk, owner)))
            .await
            .expect("subscribe should succeed");

        state.write().await.operator.hosted_inboxes.remove(&owner);

        let send = handle_send(
            State(state.clone()),
            Path(hex_encode(&owner)),
            Json(SendRequest {
                sender: hex_encode(&[0xBC; 32]),
                payload: {
                    use base64::Engine;
                    base64::engine::general_purpose::STANDARD.encode([1u8; 3])
                },
                deposit: 1,
            }),
        )
        .await
        .expect("template queue should accept send without operator inbox")
        .0;

        assert_eq!(send.position, 1);
        assert_eq!(state.read().await.template.total_pending(), 1);

        let nonce = b"drain-template";
        let max = 1usize;
        let mut payload = Vec::new();
        payload.extend_from_slice(&owner);
        payload.extend_from_slice(nonce);
        payload.extend_from_slice(&(max as u64).to_le_bytes());
        let drain = handle_drain(
            State(state.clone()),
            axum::extract::Query(DrainQuery {
                owner: hex_encode(&owner),
                max: Some(max),
                nonce: hex_encode(nonce),
                signature: sign_request(&sk, b"dregg-relay-drain-v1", &payload),
            }),
        )
        .await
        .expect("template queue should drain without operator inbox")
        .0;

        assert_eq!(drain.messages.len(), 1);
        assert_eq!(drain.messages[0].sender, hex_encode(&[0xBC; 32]));
        assert_eq!(state.read().await.template.total_pending(), 0);
        assert_eq!(state.read().await.messages_delivered, 1);
    }

    // ─── audit #10: delivery_proofs are bounded (TTL/height evict + hard cap) ──────
    //
    // Both-directions falsifiers for the memory bound. The slash-safety of the bound
    // (an evicted proof never wrongly slashes an honest relay) is proven against the
    // real dispute handler in `relay_dispute`'s test module; here we prove the map is
    // actually bounded (a) under a flood by TTL/height eviction, and (b) at the hard
    // cap by backpressure that never drops a within-window proof.

    fn signed_subscribe_cap(sk: &SigningKey, owner: [u8; 32], capacity: usize) -> SubscribeRequest {
        let nonce = b"sub-cap";
        let mut payload = Vec::new();
        payload.extend_from_slice(&owner);
        payload.extend_from_slice(nonce);
        SubscribeRequest {
            owner: hex_encode(&owner),
            capacity: Some(capacity),
            min_deposit: Some(1),
            nonce: hex_encode(nonce),
            signature: sign_request(sk, b"dregg-relay-subscribe-v1", &payload),
        }
    }

    async fn drain_signed(
        state: &Arc<RwLock<RelayState>>,
        sk: &SigningKey,
        owner: [u8; 32],
        max: usize,
    ) -> DrainResponse {
        let nonce = b"drain-audit10";
        let mut payload = Vec::new();
        payload.extend_from_slice(&owner);
        payload.extend_from_slice(nonce);
        payload.extend_from_slice(&(max as u64).to_le_bytes());
        handle_drain(
            State(state.clone()),
            axum::extract::Query(DrainQuery {
                owner: hex_encode(&owner),
                max: Some(max),
                nonce: hex_encode(nonce),
                signature: sign_request(sk, b"dregg-relay-drain-v1", &payload),
            }),
        )
        .await
        .expect("drain")
        .0
    }

    async fn send_one(state: &Arc<RwLock<RelayState>>, owner: [u8; 32], tag: [u8; 4]) {
        handle_send(
            State(state.clone()),
            Path(hex_encode(&owner)),
            Json(SendRequest {
                sender: hex_encode(&[0xBC; 32]),
                payload: {
                    use base64::Engine;
                    base64::engine::general_purpose::STANDARD.encode(tag)
                },
                deposit: 1,
            }),
        )
        .await
        .expect("send");
    }

    /// (b) A flood of deliveries stays bounded: proofs past their dispute deadline are
    /// height-evicted, so the live set never exceeds deliveries within ONE window.
    #[tokio::test]
    async fn audit10_delivery_proofs_bounded_under_flood_by_height_eviction() {
        let (sk, owner) = make_key(42);
        let window = 50u64;
        let state = Arc::new(RwLock::new(test_state(RelayConfig {
            dispute_window_blocks: window,
            default_inbox_capacity: 8,
            max_total_capacity: 100_000,
            ..test_config()
        })));
        let _ = handle_subscribe(
            State(state.clone()),
            Json(signed_subscribe_cap(&sk, owner, 8)),
        )
        .await
        .expect("subscribe");

        // Round 1 at height 0: deliver 4 boxes → 4 proofs, each with dispute_deadline
        // = enqueued_at(0) + CUSTODY_DEADLINE_BLOCKS(100) + window(50) = 150.
        for i in 0..4u8 {
            send_one(&state, owner, [i, i, i, i]).await;
        }
        let drain = drain_signed(&state, &sk, owner, 4).await;
        assert_eq!(drain.messages.len(), 4);
        assert_eq!(state.read().await.delivery_proofs.len(), 4);
        // enqueued_at(0) + CUSTODY_DEADLINE_BLOCKS + window.
        for rec in state.read().await.delivery_proofs.values() {
            assert_eq!(rec.dispute_deadline, CUSTODY_DEADLINE_BLOCKS + window);
        }

        // The finalized frontier advances past their deadline: they evict — no leak.
        {
            let mut s = state.write().await;
            s.current_height = 151;
            assert_eq!(s.evict_expired_delivery_proofs(151), 4);
        }
        assert!(
            state.read().await.delivery_proofs.is_empty(),
            "old deliveries evicted"
        );

        // Round 2 at the new height: fresh proofs, still bounded to one window's worth.
        for i in 4..8u8 {
            send_one(&state, owner, [i, i, i, i]).await;
        }
        let drain = drain_signed(&state, &sk, owner, 4).await;
        assert_eq!(drain.messages.len(), 4);
        assert_eq!(
            state.read().await.delivery_proofs.len(),
            4,
            "live set bounded to one window's deliveries — the leak is closed"
        );
    }

    /// (b/c) At the hard cap, a drain caches only as many proofs as fit and leaves the
    /// rest ENQUEUED (still in custody, no witness gap) — backpressure, NOT a dropped
    /// within-window proof (which could wrongly slash).
    #[tokio::test]
    async fn audit10_delivery_proof_cap_applies_backpressure_no_witness_gap() {
        let (sk, owner) = make_key(43);
        let state = Arc::new(RwLock::new(test_state(RelayConfig {
            max_delivery_proofs: 2,
            default_inbox_capacity: 8,
            max_total_capacity: 100_000,
            ..test_config()
        })));
        let _ = handle_subscribe(
            State(state.clone()),
            Json(signed_subscribe_cap(&sk, owner, 8)),
        )
        .await
        .expect("subscribe");

        for i in 0..5u8 {
            send_one(&state, owner, [i, i, i, i]).await;
        }
        assert_eq!(state.read().await.template.total_pending(), 5);

        // Drain up to 5, but the cache cap is 2: only 2 are delivered + cached; the
        // other 3 stay enqueued (their witness is never lost — they were not delivered).
        let drain = drain_signed(&state, &sk, owner, 5).await;
        assert_eq!(
            drain.messages.len(),
            2,
            "delivered only as many boxes as the cache can witness"
        );
        let s = state.read().await;
        assert_eq!(s.delivery_proofs.len(), 2, "cache bounded at the cap");
        assert_eq!(
            s.template.total_pending(),
            3,
            "the undelivered rest remain enqueued — backpressure, no witness gap"
        );
    }

    // ─── Computron purchase path, rung 1 (operator-local policy) ──────────
    //
    // Adversarial tests, both polarities: every refusal arm bites (disabled
    // asset, unknown asset, zero rate, overflow, dust, underfunded operator
    // cell) AND the accepted path conserves exactly (a transfer, never a
    // mint — total ledger supply invariant across the refill).

    const USDC_TEST_ASSET: [u8; 32] = [0x11; 32];
    const COMPUTRON_TOKEN: [u8; 32] = [0x0C; 32];

    /// A ledger with an operator pre-funded cell and an empty recipient cell,
    /// mirroring the faucet's genesis-funded source + provisioned destination.
    fn refill_test_ledger(
        operator_balance: i64,
    ) -> (dregg_cell::Ledger, dregg_cell::CellId, dregg_cell::CellId) {
        let mut ledger = dregg_cell::Ledger::new();
        let operator = ledger
            .insert_cell(dregg_cell::Cell::with_balance(
                [0xA1; 32],
                COMPUTRON_TOKEN,
                operator_balance,
            ))
            .expect("insert operator cell");
        let recipient = ledger
            .insert_cell(dregg_cell::Cell::with_balance(
                [0xB2; 32],
                COMPUTRON_TOKEN,
                0,
            ))
            .expect("insert recipient cell");
        (ledger, operator, recipient)
    }

    fn total_supply(ledger: &dregg_cell::Ledger) -> i64 {
        ledger.iter().map(|(_, cell)| cell.state.balance()).sum()
    }

    fn refill_policy(rate_micros: u64, enabled: bool) -> FeePolicy {
        let mut policy = FeePolicy::default();
        policy.external_assets.insert(
            hex_encode(&USDC_TEST_ASSET),
            AssetRatePolicy {
                rate_micros,
                enabled,
            },
        );
        policy
    }

    fn voucher(external_amount: u64, recipient: dregg_cell::CellId) -> RefillVoucher {
        RefillVoucher {
            asset: USDC_TEST_ASSET,
            external_amount,
            recipient,
        }
    }

    /// FAIL CLOSED: the default policy (empty table) refuses every asset, and
    /// an asset absent from a non-empty table is refused too.
    #[test]
    fn computron_refill_unknown_asset_refused_fail_closed() {
        let (mut ledger, operator, recipient) = refill_test_ledger(10_000);
        let supply_before = total_supply(&ledger);

        // Empty table (the default): refuse.
        let empty = FeePolicy::default();
        assert_eq!(
            apply_computron_refill(&mut ledger, &empty, operator, &voucher(100, recipient)),
            Err(RefillRefused::AssetNotAccepted),
        );

        // Non-empty table, but a DIFFERENT asset than the voucher's: refuse.
        let mut other_asset_only = FeePolicy::default();
        other_asset_only.accept_asset(&[0x22; 32], COMPUTRON_RATE_SCALE);
        assert_eq!(
            apply_computron_refill(
                &mut ledger,
                &other_asset_only,
                operator,
                &voucher(100, recipient)
            ),
            Err(RefillRefused::AssetNotAccepted),
        );

        assert_eq!(
            total_supply(&ledger),
            supply_before,
            "refusal changed state"
        );
        assert_eq!(ledger.get(&recipient).unwrap().state.balance(), 0);
    }

    /// A disabled table row refuses even though the rate is on record.
    #[test]
    fn computron_refill_disabled_asset_refused() {
        let (mut ledger, operator, recipient) = refill_test_ledger(10_000);
        let policy = refill_policy(COMPUTRON_RATE_SCALE, false);

        assert_eq!(
            apply_computron_refill(&mut ledger, &policy, operator, &voucher(100, recipient)),
            Err(RefillRefused::AssetDisabled),
        );
        assert_eq!(ledger.get(&recipient).unwrap().state.balance(), 0);
        assert_eq!(ledger.get(&operator).unwrap().state.balance(), 10_000);
    }

    /// A zero rate is invalid (it quotes infinite computrons per unit) and
    /// must refuse rather than divide by zero or credit anything.
    #[test]
    fn computron_refill_zero_rate_refused() {
        let (mut ledger, operator, recipient) = refill_test_ledger(10_000);
        let policy = refill_policy(0, true);

        assert_eq!(
            apply_computron_refill(&mut ledger, &policy, operator, &voucher(100, recipient)),
            Err(RefillRefused::ZeroRate),
        );
        assert_eq!(ledger.get(&recipient).unwrap().state.balance(), 0);
    }

    /// A credit exceeding the ledger's signed 64-bit balance domain refuses
    /// instead of wrapping or saturating.
    #[test]
    fn computron_refill_overflow_refused() {
        let (mut ledger, operator, recipient) = refill_test_ledger(10_000);

        // u64::MAX units at a 1:1 rate → credit u64::MAX > i64::MAX: refuse.
        let policy = refill_policy(COMPUTRON_RATE_SCALE, true);
        assert_eq!(
            apply_computron_refill(
                &mut ledger,
                &policy,
                operator,
                &voucher(u64::MAX, recipient)
            ),
            Err(RefillRefused::CreditOverflow {
                external_amount: u64::MAX,
                rate_micros: COMPUTRON_RATE_SCALE,
            }),
        );

        // A sub-scale rate multiplies the credit above u64 entirely: refuse.
        let cheap = refill_policy(1, true);
        assert_eq!(
            apply_computron_refill(&mut ledger, &cheap, operator, &voucher(u64::MAX, recipient)),
            Err(RefillRefused::CreditOverflow {
                external_amount: u64::MAX,
                rate_micros: 1,
            }),
        );
        assert_eq!(ledger.get(&recipient).unwrap().state.balance(), 0);
    }

    /// Dust below one computron refuses: accepting the payment while crediting
    /// zero would silently take the payer's asset for nothing.
    #[test]
    fn computron_refill_dust_zero_credit_refused() {
        let (mut ledger, operator, recipient) = refill_test_ledger(10_000);
        // 2 external units per computron; 1 unit converts to 0 computrons.
        let policy = refill_policy(2 * COMPUTRON_RATE_SCALE, true);

        assert_eq!(
            apply_computron_refill(&mut ledger, &policy, operator, &voucher(1, recipient)),
            Err(RefillRefused::ZeroCredit),
        );
        assert_eq!(ledger.get(&recipient).unwrap().state.balance(), 0);
    }

    /// A refill exceeding the operator pre-funded cell is refused with NO
    /// state change — a refill is a transfer, never a mint, so an underfunded
    /// operator cannot credit anyone.
    #[test]
    fn computron_refill_exceeding_operator_cell_refused() {
        let (mut ledger, operator, recipient) = refill_test_ledger(100);
        let policy = refill_policy(COMPUTRON_RATE_SCALE, true);

        // 500 units at 1:1 → 500 computrons > the operator's 100.
        let refused =
            apply_computron_refill(&mut ledger, &policy, operator, &voucher(500, recipient));
        assert_eq!(
            refused,
            Err(RefillRefused::OperatorCellInsufficient {
                available: 100,
                required: 500,
            }),
        );
        assert_eq!(
            ledger.get(&operator).unwrap().state.balance(),
            100,
            "refused refill debited the operator"
        );
        assert_eq!(
            ledger.get(&recipient).unwrap().state.balance(),
            0,
            "refused refill credited the recipient"
        );
    }

    /// The accepted path: exact rate conversion, exact conservation. The
    /// operator is debited precisely what the recipient is credited and the
    /// total ledger supply is invariant (Σ before = Σ after — a transfer,
    /// never a mint), with no cells created.
    #[test]
    fn computron_refill_accepted_conserves_exactly() {
        let (mut ledger, operator, recipient) = refill_test_ledger(10_000);
        // 0.5 external units per computron: 250 units → exactly 500 computrons.
        let policy = refill_policy(COMPUTRON_RATE_SCALE / 2, true);
        let supply_before = total_supply(&ledger);
        let cells_before = ledger.len();

        let credited =
            apply_computron_refill(&mut ledger, &policy, operator, &voucher(250, recipient))
                .expect("enabled asset within operator balance must be accepted");

        assert_eq!(credited, 500, "rate conversion must be exact");
        assert_eq!(ledger.get(&operator).unwrap().state.balance(), 10_000 - 500);
        assert_eq!(ledger.get(&recipient).unwrap().state.balance(), 500);
        assert_eq!(
            total_supply(&ledger),
            supply_before,
            "refill must conserve total supply exactly"
        );
        assert_eq!(ledger.len(), cells_before, "refill must not create cells");
    }
}
