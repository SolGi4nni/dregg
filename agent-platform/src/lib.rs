//! # agent-platform — rent, host, meter, and reap confined agent grains.
//!
//! The agent-side twin of the hosting substrate's webcell platform. A tenant is a
//! [`dregg_agent::session::Session`] — a hosted, cap+budget-bounded, receipted
//! agent, "the unit a hosting layer rents out per user" — opened under
//! [`Confinement::Hosted`] (lexically-confinable tools only; a raw `shell` is
//! refused) over a [`HostedLease`]. [`AgentPlatform::rent`] provisions the grain,
//! [`drive`](AgentPlatform::drive) runs one goal (metered, receipted) and advances
//! the lease's durable checkpoint with a **verified binding** of the session
//! (digest + chain tip + turn count + consumed — read back and re-checked on
//! every [`verify`](AgentPlatform::verify)),
//! [`bill_period`](AgentPlatform::bill_period) meters and settles the rent
//! (in-process or on-chain via the injected [`Settlement`]), and
//! [`reap_if_behind`](AgentPlatform::reap_if_behind) reclaims a delinquent grain.
//! This is the first stone of THE GRAIN (`docs/THE-GRAIN.md`): a hosted agent is
//! a rentable, verifiable grain.
//!
//! ## What a renter can check — the honest R-ladder (`docs/THE-GRAIN.md` face #1)
//!
//! - **R0 (landed, in `dregg-agent`):** the receipt-chain key is a fresh RANDOM
//!   secret, never derived from the public agent id — a third party holding a
//!   report cannot forge a self-consistent chain. The HOST still runs the signer,
//!   so R0 alone is tamper-evidence, not host-independence.
//! - **R1 (landed, here):** rent with a [`RenterAnchor`] and countersign
//!   checkpoints ([`checkpoint_offer`](AgentPlatform::checkpoint_offer) /
//!   [`submit_checkpoint`](AgentPlatform::submit_checkpoint)) — third-party-
//!   verifiable anti-rewrite + anti-truncation relative to a renter-acknowledged
//!   checkpoint, no circuits.
//! - **R2 (the weld is here; the turn is as real as the minter):**
//!   [`drive_minted`](AgentPlatform::drive_minted) welds every admitted action
//!   to a turn committed through the supplied [`GrainTurnMinter`], and
//!   [`verify_r2`](AgentPlatform::verify_r2) rejects any receipt that is not a
//!   view over a committed turn. With `grain-turn`'s real `ToolGatewayMinter`
//!   that is a GENUINE kernel turn and the meter becomes a host-side executor
//!   caveat; `dregg_agent`'s `SyntheticMinter` exercises only the seam (tests).
//! - **R3 (the named gap):** proving the committed turns genuinely RAN is the
//!   whole-history STARK leg — [`grain_verify::WHOLE_HISTORY_GAP`], VK-terminal.

/// The federation / local-submit leg: a minted grain turn lands on a REAL
/// (locally-runnable) node's ledger + finalized receipt log, cross-node-verifiable.
pub mod node;
/// Serve the platform over HTTP (rent/drive/verify a grain over the mesh).
pub mod serve;
/// Roles as an attenuable facet lattice — the per-grain share model.
pub mod share;
/// The SSE transcript wire — replay a grain's drive as meta/step/done frames.
pub mod transcript;

pub use node::{LocalNode, NodeError, NodeMinter};
pub use share::Role;

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use serde::{Deserialize, Serialize};

use dregg_agent::agent::{AgentBrain, AgentRunReport, AgentVerified, GrainTurnMinter};
use dregg_agent::receipt::ReceiptBody;
use dregg_agent::session::{Confinement, GoalReport, Session, parse_caps_confined};
use dregg_agent::toolkit::Toolkit;
use dregg_agent::tools::OperatorTools;
use dregg_cell::{Cell, CellId};
use hosted_durable::{LeaseCharge, SettleReceipt, Settlement};
use hosted_lease::{
    FieldElement, HostedLease, LeaseTerms, PrepaidLeaseTerms, WORKING_BASE, field_from_u64,
};
// THE FOLD: the vat's verified lifecycle machine. A tenant's grain lifecycle is a
// `VatState` sealed on the SAME lease cell (slots disjoint from the lease economics),
// advanced only through the legality-checked `apply_transition` — no ad-hoc state.
// THE FUSION: `open_vat_prepaid` opens the durable image + the FUSED prepaid
// meter+reserve + the lifecycle in one pass (the meter/pay-drift-free rent path).
use starbridge_vat::lifecycle::{WitnessStance, apply_transition, open_vat_prepaid, read_state};
pub use starbridge_vat::{VatState, VatTransition};

/// **The R1 renter finality anchor**, supplied whole at rent: the renter-chosen
/// `nonce` (the genesis pin, re-exposed bound to the session signer in every
/// attestation so the renter recognizes their own session) AND the renter's
/// ed25519 `pubkey` (the key the platform pins checkpoint countersignatures
/// against, so it can never forge an acknowledgement). One struct on purpose:
/// the R1 teeth ([`grain_verify::GrainAttestation::verify_for_renter`]) need
/// BOTH, so half an anchor is unrepresentable — a grain either has the full
/// anchor or is honestly bare tamper-evidence.
#[derive(Clone, Copy, Debug)]
pub struct RenterAnchor {
    /// The renter-chosen genesis nonce (the pin a renter recognizes).
    pub nonce: [u8; 32],
    /// The renter's ed25519 public key countersignatures are pinned against.
    pub pubkey: [u8; 32],
}

/// Prepaid rent funding: a fresh grain's lease cell is opened holding enough to
/// cover this many rent periods. An operator-facing sizing knob, overflow-checked
/// against attacker-facing `rent_per_period` at rent.
///
/// This same number seeds the grain's FUSED prepaid reserve
/// ([`HostedLease::open_prepaid`], `budget := rent_per_period * FUNDED_PERIODS`):
/// the reserve mirrors the real funded balance, and each bill draws one rent from
/// the reserve in the SAME atomic write that advances the meter cursor
/// ([`dregg_cell::prepaid_lease`], Lean rung `PrepaidLease.lean`). So meter/pay
/// drift is unrepresentable — not app discipline — and the reserve bounds the
/// bills: a draw past it is refused `InsufficientBudget` before any value moves
/// (see [`AgentPlatform::bill_period`]).
const FUNDED_PERIODS: i64 = 1024;

/// Durable-image working keys (all `>= WORKING_BASE`): where the grain's lease
/// checkpoint binds the session, so the committed `EXEC_COLL` heap carries — and
/// [`AgentPlatform::verify`] re-checks — the mind's advance.
/// The head receipt hash of the session's cumulative chain (zero = empty chain).
pub const WK_CHAIN_TIP: u32 = WORKING_BASE;
/// The number of committed receipts (turns) in the chain.
pub const WK_NUM_TURNS: u32 = WORKING_BASE + 1;
/// The session's cumulative consumed budget.
pub const WK_CONSUMED: u32 = WORKING_BASE + 2;

/// **THE RESUMABLE-SESSION CARRIER — Phase 2 (wake-from-lease).** Beyond the three
/// cursor slots above (which [`image_binds`] re-checks for divergence — a CURSOR, not
/// enough to reconstruct), a checkpoint also persists the FULL resumable session
/// carrier ([`SessionCarrier`]: the receipt secret + consumed + the whole
/// [`AgentRunReport`] + the R2 committed-turn manifest) so a grain is WAKEABLE from
/// its lease heap ALONE ([`AgentPlatform::wake_from_lease`]). The blob is chunked
/// across working slots beyond `WORKING_BASE + 3`, mirroring
/// `starbridge_v2::agent_memory::AgentMemoryCheckpoint`'s persist-and-reconstitute
/// discipline: a LENGTH slot, a ROOT-TOOTH slot (a hash of the full carrier bytes),
/// then N data slots (each packs 32 carrier bytes).
///
/// The carrier byte length (its data slots are `WK_CARRIER_DATA_BASE + i`, `i` in
/// `0..ceil(len/32)`).
pub const WK_CARRIER_LEN: u32 = WORKING_BASE + 3;
/// The anti-substitution ROOT TOOTH: `blake3(carrier_bytes)`. The cold wake
/// reassembles the data slots and REFUSES fail-closed if they do not re-hash to this
/// (a tampered or truncated carrier — the same byte-identical discipline
/// `AgentMemoryCheckpoint::resume_into` holds).
pub const WK_CARRIER_ROOT: u32 = WORKING_BASE + 4;
/// The first carrier DATA slot; slot `WK_CARRIER_DATA_BASE + i` packs carrier bytes
/// `[32*i .. 32*i+32)` (the final slot zero-padded), read back under [`WK_CARRIER_LEN`].
pub const WK_CARRIER_DATA_BASE: u32 = WORKING_BASE + 5;

/// **THE FULL RESUMABLE SESSION CARRIER** persisted into the lease's committed
/// `EXEC_COLL` heap every checkpoint — everything needed to reconstitute the grain's
/// [`Session`] from the heap ALONE ([`AgentPlatform::wake_from_lease`]), the umem
/// full-carrier discipline of `starbridge_v2::agent_memory::AgentMemoryCheckpoint`
/// lifted onto the hosting lease.
///
/// ## Secret handling (be explicit — this is the R0 signing key)
///
/// `receipt_secret` is the grain's ed25519 receipt-chain SIGNING seed. Persisting it
/// into the committed heap commits only its ROOT — a hash (`WK_CARRIER_ROOT`) that is
/// third-party-safe; the heap PREIMAGE (this struct's bytes) is host-held DATA
/// AVAILABILITY. The host runs the agent and ALREADY holds the secret, so committing
/// the root (or attesting the grain) does NOT leak it to a third party:
/// [`AgentRunReport::signer`] stays the PUBLIC key, and the secret appears in NO
/// attestation / report / verify surface. **Export caveat (a SEPARATE concern, not
/// solved here):** shipping the carrier PREIMAGE to another host to migrate the grain
/// WOULD ship the signing secret with it — carrier export across a trust boundary
/// needs a re-key / sealed-transfer step this in-process persist deliberately does not
/// attempt.
#[derive(Clone, Debug, Serialize, Deserialize)]
struct SessionCarrier {
    /// The grain's receipt-chain signing seed (see the type note — host-held; its
    /// committed root is a hash, never exposed in an attestation).
    receipt_secret: [u8; 32],
    /// The cumulative consumed budget the woken meter is pre-charged to.
    consumed: i64,
    /// The whole cumulative session report — the receipt chain + cells + counts +
    /// signer the woken [`Session`] is rebuilt from ([`Session::wake_from_report`]).
    report: AgentRunReport,
    /// **R2** — the committed-turn manifest ([`Tenant::committed_turns`]), restored so
    /// a cold-woken grain still re-witnesses at R2 without the retained in-RAM Tenant.
    committed_turns: Vec<[u8; 32]>,
    /// The goal transcript (per-goal prompt + steps) so a cold-woken grain restores
    /// its full `/transcript` history, not just the verifiable receipt state.
    history: Vec<GoalReport>,
}

/// One rented agent grain: the confined session, its hosting lease, the terms, and
/// the workdir its fs-grants resolve against (the platform roots every drive's
/// toolkit here — a caller cannot hand a grain tools rooted outside its rented
/// confinement).
struct Tenant {
    session: Session,
    lease: HostedLease,
    /// **THE FOLD — the grain's verified lifecycle state.** A vat lifecycle
    /// (`Created`/`Running`/`Sleeping`/`Lapsed`/`Reaped`) sealed on the lease cell
    /// (slots disjoint from the lease economics) at rent. This field is the cached
    /// read of [`starbridge_vat::lifecycle::read_state`] over `lease.cell()`; every
    /// mutation goes through [`Tenant::transition`], which advances it ONLY via the
    /// legality-checked [`apply_transition`] (the executor's `Monotonic(VAT_PHASE)`
    /// tooth), so an illegal move (e.g. waking a reaped grain) is refused up front.
    vat: VatState,
    terms: LeaseTerms,
    workdir: std::path::PathBuf,
    /// The cap bundle string the grain was rented under. Kept so a COLD wake
    /// ([`wake_from_lease`](AgentPlatform::wake_from_lease)) can rebuild the SAME
    /// [`dregg_agent::session::Session`]'s `AgentSpec` (identical caps + budget +
    /// workdir ⇒ identical asset + ceiling ⇒ the woken `handle.id`/budget/asset match
    /// the persisted report), reconstituting the session from the heap without the
    /// retained in-RAM one.
    caps: String,
    /// **The grain's receipt-chain SIGNING SECRET** (host-held). The session is opened
    /// under it ([`Session::open_with_secret`]) so a cold wake re-signs the resumed
    /// chain with the SAME key. It is persisted (as part of [`SessionCarrier`]) into
    /// the committed `EXEC_COLL` heap — only its ROOT is committed (a hash,
    /// third-party-safe); the heap preimage is host-held data availability. NEVER
    /// placed in any attestation / report / verify surface (`report.signer` stays the
    /// PUBLIC key). See [`SessionCarrier`] for the full secret-handling + export note.
    receipt_secret: [u8; 32],
    /// The grain's budget ceiling (as granted at [`rent`](AgentPlatform::rent)).
    /// The served-path minter ([`open_minter`](AgentPlatform::open_minter)) sets
    /// its `ToolGateway` rate ceiling to this, so the executor's own `calls_made`
    /// `FieldLte` caveat bounds the number of committed turns host-side — the
    /// meter as a kernel caveat, not merely session-local.
    budget: i64,
    /// The account that owns this grain — the only subject authorized to drive it.
    owner: String,
    /// **R1 — the renter finality anchor** ([`RenterAnchor`]), or `None` when the
    /// renter supplied none at rent (R1 is then unavailable — the grain falls back
    /// to bare tamper-evidence).
    anchor: Option<RenterAnchor>,
    /// The latest renter-countersigned checkpoint (`POST <host>/checkpoint`), stored
    /// so `attest` can hand it to a third-party verifier for the anti-rewrite/anti-
    /// truncation teeth. Monotone in `num_turns` (never regresses on store).
    checkpoint: Option<grain_verify::CountersignedCheckpoint>,
    /// **R2 — the committed-turn manifest**: every kernel-turn hash a
    /// [`GrainTurnMinter`] committed for this grain across every
    /// [`drive_minted`](AgentPlatform::drive_minted), in order. What
    /// [`verify_r2`](AgentPlatform::verify_r2) checks the receipts' links against.
    committed_turns: Vec<[u8; 32]>,
    /// **The grain's local node** — the ledger + finalized receipt log its minted
    /// turns land on ([`node::LocalNode`]). Lazily brought up on the first served
    /// drive together with [`node_minter`](Self::node_minter). A cheap `Arc`-sharing
    /// handle the platform reads/verifies the finalized chain through
    /// ([`verify_landed`](AgentPlatform::verify_landed)). `None` until the grain has
    /// been driven through the minting path (or after a cold wake, re-brought-up).
    node: Option<node::LocalNode>,
    /// **The grain's persistent node-backed minter** ([`node::NodeMinter`]). Opened
    /// once and reused across drives, so the worker cell is stable and the node's
    /// finalized chain is a single-agent, verifiable sequence that accumulates every
    /// turn the grain commits. Replaces `grain-turn`'s per-drive throwaway runtime on
    /// the served path.
    node_minter: Option<node::NodeMinter>,
    /// **The share ACL** — `(verified X-Dregg-Subject → [`Role`])` grants beyond the
    /// owner. The owner is NOT stored here (they are implicit [`Role::Admin`] via
    /// [`AgentPlatform::role_of`]); a subject absent from both the owner slot and
    /// this map is a non-member (fail-closed → the routes 404, no existence oracle).
    acl: HashMap<String, Role>,
}

impl Tenant {
    /// Advance the grain's lifecycle by ONE vat transition on the lease cell — the
    /// single seam every lifecycle move flows through. It calls the legality-checked
    /// [`apply_transition`] (so an illegal move — waking a reaped grain, sleeping a
    /// non-running one — is refused by the machine's own tooth, agreeing with the
    /// executor's `Monotonic(VAT_PHASE)` re-enforcement), then caches the new state.
    /// On `BringUp` it binds the box + endpoint to a stable per-host token (the box
    /// is re-placed on every wake); the other transitions clear them (no box while
    /// not Running).
    fn transition(&mut self, host: &str, t: VatTransition) -> Result<VatState, AgentPlatformError> {
        let (machine, endpoint) = match t {
            VatTransition::BringUp => (box_token(host), box_token(host) ^ 0x01),
            VatTransition::Sleep | VatTransition::Lapse | VatTransition::Reap => (0, 0),
        };
        let to = apply_transition(self.lease.cell_mut(), t, machine, endpoint)
            .map_err(|e| AgentPlatformError::Lifecycle(format!("{e:?}")))?;
        self.vat = to;
        Ok(to)
    }
}

/// A stable, nonzero box/endpoint token for a host — the vat's `MACHINE`/`ENDPOINT`
/// slots want a placement identity, and a hosted agent grain's "box" is the
/// in-process session, so we bind a deterministic per-host token (the first 8 bytes
/// of `blake3(host)`, forced nonzero) re-bound on each `BringUp`.
fn box_token(host: &str) -> u64 {
    let h = blake3::hash(host.as_bytes());
    let mut b = [0u8; 8];
    b.copy_from_slice(&h.as_bytes()[..8]);
    u64::from_le_bytes(b) | 1
}

/// The platform every rented agent grain is hosted on, keyed by host.
pub struct AgentPlatform {
    /// Keyed by host. The value is a **per-tenant** `Arc<Mutex<Tenant>>`: every
    /// method locks this outer map only *briefly* — to clone the grain's Arc (or
    /// insert/remove/scan) — then DROPS the map lock and locks the individual
    /// tenant for the operation. So a long-running drive (esp. `drive_live`'s
    /// blocking provider round-trip) holds only its OWN grain's lock and never
    /// stalls another tenant's rent/drive/verify/bill/attest (no head-of-line DoS).
    tenants: Mutex<HashMap<String, Arc<Mutex<Tenant>>>>,
    /// The current block height, advanced by the operator (from the node) via
    /// [`set_clock`](AgentPlatform::set_clock). `drive` audits each grain's rent
    /// schedule against it, so a delinquent grain lapses on use rather than being
    /// hosted free forever. Stays `0` (nothing lapses) until an operator ticks it.
    clock: std::sync::atomic::AtomicI64,
    /// **The federation node the platform submits minted turns to.** `None` (the
    /// default) means the built-in, in-process [`node::LocalNode`] — "a locally-hosted
    /// node you can actually use": every grain mints onto a real node ledger + a
    /// finalized, light-client-verifiable receipt log, no external daemon required.
    /// `Some(url)` names an EXTERNAL federation node (e.g. a homelab node); the
    /// platform still mints onto the local node here, and forwarding the finalized
    /// turn to `url`'s ingress over HTTP is the operational DEPLOY step (not performed
    /// in-process — the external node runs full multi-node blocklace consensus). See
    /// [`node_url`](AgentPlatform::node_url).
    node_url: Option<String>,
    /// **ROUTE (ii) — the HOST executor signing seed.** When `Some`, every grain
    /// this platform drives through the served / minted path
    /// ([`drive_serving`](AgentPlatform::drive_serving)) mints turns onto a
    /// [`node::NodeMinter`] opened under this seed, so every committed grain-turn
    /// receipt is Ed25519-signed over `canonical_executor_signed_message` — FORGE-
    /// ADMISSIBLE against [`executor_pubkey`](AgentPlatform::executor_pubkey) (the
    /// key an auditor pins in `trusted_executor_keys`). `None` (the default) leaves
    /// grain receipts UNSIGNED (`executor_signature == None`), byte-unchanged.
    executor_signing_seed: Option<[u8; 32]>,
}

/// Why an agent-platform operation was refused.
#[derive(Debug)]
pub enum AgentPlatformError {
    /// The cap bundle string was ill-formed or requested a hosted-forbidden tool.
    Caps(String),
    /// Opening the confined session failed.
    Session(String),
    /// No grain is hosted at that host.
    NoSuchGrain(String),
    /// A grain is already hosted at that host (rent does not evict an incumbent).
    GrainOccupied(String),
    /// **R1** — a checkpoint could not be offered / accepted (see the message):
    /// the session has committed nothing yet, no renter key was pinned at rent, the
    /// countersignature is wrong, or the checkpoint does not match the chain.
    Checkpoint(String),
    /// The caller is not authorized for this grain (not its owner).
    Unauthorized(String),
    /// The rental terms are ill-formed (e.g. a rent that overflows the funding).
    BadTerms(String),
    /// The grain's hosting lease has lapsed (non-payment): the slot is reclaimed.
    Lapsed,
    /// A vat lifecycle transition was refused by the machine (an illegal move —
    /// e.g. waking a reaped grain, or a malformed lifecycle slot).
    Lifecycle(String),
    /// Advancing the lease's durable checkpoint was refused.
    Lease(String),
    /// Settling a rent period was refused.
    Settle(String),
    /// Re-witnessing the session failed (a tampered receipt in some goal).
    Verify(String),
    /// The lease's durable image does not bind the session (the committed digest /
    /// chain tip / turn count / consumed disagree with the live session — a stale,
    /// tampered, or diverged image).
    ImageDiverged(String),
    /// **Phase 2 (wake-from-lease)** — the resumable session carrier read back from
    /// the `EXEC_COLL` heap could not be reconstituted fail-closed: no carrier was
    /// persisted, a data slot was truncated (missing), the reassembled bytes did not
    /// re-hash to the committed ROOT TOOTH (tampered), or they did not deserialize.
    /// A cold wake ([`AgentPlatform::wake_from_lease`]) REFUSES rather than stand up a
    /// partial or substituted session.
    CarrierRefused(String),
}

impl std::fmt::Display for AgentPlatformError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AgentPlatformError::Caps(e) => write!(f, "cap bundle refused: {e}"),
            AgentPlatformError::Session(e) => write!(f, "session open refused: {e}"),
            AgentPlatformError::NoSuchGrain(h) => write!(f, "no agent grain hosted at `{h}`"),
            AgentPlatformError::GrainOccupied(h) => write!(f, "a grain is already hosted at `{h}`"),
            AgentPlatformError::Checkpoint(e) => write!(f, "renter checkpoint refused: {e}"),
            AgentPlatformError::Unauthorized(s) => write!(f, "not authorized for this grain: {s}"),
            AgentPlatformError::BadTerms(e) => write!(f, "ill-formed rental terms: {e}"),
            AgentPlatformError::Lapsed => {
                write!(f, "the hosting lease has lapsed: grain reclaimed")
            }
            AgentPlatformError::Lifecycle(e) => write!(f, "vat lifecycle transition refused: {e}"),
            AgentPlatformError::Lease(e) => write!(f, "durable checkpoint refused: {e}"),
            AgentPlatformError::Settle(e) => write!(f, "rent settlement refused: {e}"),
            AgentPlatformError::Verify(e) => write!(f, "session re-witness failed: {e}"),
            AgentPlatformError::ImageDiverged(e) => {
                write!(f, "the durable image does not bind the session: {e}")
            }
            AgentPlatformError::CarrierRefused(e) => {
                write!(f, "resumable session carrier refused: {e}")
            }
        }
    }
}

impl std::error::Error for AgentPlatformError {}

impl Default for AgentPlatform {
    fn default() -> Self {
        Self::new()
    }
}

/// The result of [`AgentPlatform::verify_landed`]: the grain's minted turns are on
/// a real node's finalized, light-client-verifiable ledger log.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Landed {
    /// How many turns are finalized on the node's receipt log.
    pub finalized_len: usize,
    /// How many turns the grain's committed-turn manifest names (all of which were
    /// confirmed present on the finalized log).
    pub manifest_len: usize,
}

impl AgentPlatform {
    /// An empty platform submitting minted turns to the built-in local node (the
    /// default — no external node URL configured).
    pub fn new() -> AgentPlatform {
        AgentPlatform {
            tenants: Mutex::new(HashMap::new()),
            clock: std::sync::atomic::AtomicI64::new(0),
            node_url: None,
            executor_signing_seed: None,
        }
    }

    /// **ROUTE (ii) — install the HOST executor signing seed on this platform**
    /// (builder form). Every grain subsequently driven through the served / minted
    /// path signs its committed grain-turn receipts under this seed, so a grain turn
    /// is forge-admissible (a `RequiredCheck::CommittedReceipt` / auditor verifying
    /// against [`executor_pubkey`](Self::executor_pubkey) passes). Additive: without
    /// it, grain receipts stay UNSIGNED, byte-unchanged.
    pub fn with_executor_signing_key(mut self, seed: [u8; 32]) -> AgentPlatform {
        self.executor_signing_seed = Some(seed);
        self
    }

    /// The Ed25519 executor PUBLIC key this platform's grains sign their turn
    /// receipts under (derived from the installed seed), or `None` when no seed is
    /// installed (grain receipts unsigned). A forge / auditor pins this in
    /// `trusted_executor_keys` to admit the platform's grains' signed receipts.
    pub fn executor_pubkey(&self) -> Option<[u8; 32]> {
        self.executor_signing_seed
            .as_ref()
            .map(dregg_sdk::executor_pubkey_from_seed)
    }

    /// An empty platform configured to target the federation node at `url` (a local
    /// daemon or a homelab node). The minted turns are still committed onto the
    /// built-in local node here; forwarding the finalized turn to `url` over HTTP is
    /// the operational deploy step (see [`node_url`](Self::node_url)). Pass an empty
    /// string / `None`-equivalent to fall back to the default local node.
    pub fn with_node_url(url: impl Into<String>) -> AgentPlatform {
        let url = url.into();
        AgentPlatform {
            tenants: Mutex::new(HashMap::new()),
            clock: std::sync::atomic::AtomicI64::new(0),
            node_url: (!url.is_empty()).then_some(url),
            executor_signing_seed: None,
        }
    }

    /// The external federation node URL this platform is configured to submit to, or
    /// `None` when it uses the built-in local node (the default). When `Some`,
    /// forwarding the finalized turn to that node's `/turns/submit` ingress is the
    /// operational deploy step — the in-process local node is what mints + verifies
    /// here.
    pub fn node_url(&self) -> Option<&str> {
        self.node_url.as_deref()
    }

    /// Advance the platform's notion of the current block height (from the node). A
    /// production operator ticks this each block; `drive` audits every grain's rent
    /// schedule against it, so a grain behind on rent lapses on next use. (The
    /// separate biller loop calls [`bill_period`](AgentPlatform::bill_period) to
    /// actually collect + settle the rent.)
    ///
    /// **Monotone**: block height never rewinds, so a regression is ignored (a
    /// rewound clock would silently re-extend credit to a delinquent-but-not-yet-
    /// lapsed grain). Returns the effective clock after the tick.
    pub fn set_clock(&self, block: i64) -> i64 {
        self.clock
            .fetch_max(block, std::sync::atomic::Ordering::Relaxed)
            .max(block)
    }

    /// The current block height the platform audits against.
    pub fn clock(&self) -> i64 {
        self.clock.load(std::sync::atomic::Ordering::Relaxed)
    }

    /// Clone the per-tenant handle for `host` under a BRIEF map lock (dropped on
    /// return), so the caller can then lock just that one grain for a long
    /// operation without holding the platform-wide map lock across it.
    fn tenant_arc(&self, host: &str) -> Result<Arc<Mutex<Tenant>>, AgentPlatformError> {
        self.tenants
            .lock()
            .expect("platform poisoned")
            .get(host)
            .cloned()
            .ok_or_else(|| AgentPlatformError::NoSuchGrain(host.to_string()))
    }

    /// Provision an agent grain for `account` at `host`: parse `caps` under
    /// [`Confinement::Hosted`] (a raw `shell` is refused), open a confined session
    /// with `budget`, and open the rental lease (funded to cover
    /// [`FUNDED_PERIODS`]). The grain's tools resolve fs grants against `workdir`
    /// (every drive's toolkit is rooted there by the platform).
    ///
    /// `anchor` is the optional **R1 renter finality anchor** ([`RenterAnchor`] —
    /// the genesis nonce + the renter's countersign pubkey, whole or absent).
    /// With it, the grain supports the anti-rewrite/anti-truncation
    /// `GET`/`POST <host>/checkpoint` protocol; without it, the grain is honestly
    /// bare tamper-evidence.
    #[allow(clippy::too_many_arguments)] // one rent verb > two half-anchored ones
    pub fn rent(
        &self,
        host: impl Into<String>,
        account: &str,
        caps: &str,
        budget: i64,
        workdir: &str,
        terms: LeaseTerms,
        anchor: Option<RenterAnchor>,
    ) -> Result<String, AgentPlatformError> {
        let host = host.into();
        // Never evict an incumbent: renting an occupied host is refused, not a
        // silent overwrite (which would destroy a live tenant's session + lease).
        {
            let tenants = self.tenants.lock().expect("platform poisoned");
            if tenants.contains_key(&host) {
                return Err(AgentPlatformError::GrainOccupied(host));
            }
        }
        // Prepaid rent funding, overflow-checked (rent_per_period is attacker-facing
        // over the wire): a huge rent must fail closed, not wrap to garbage or panic.
        let funding = (terms.rent_per_period as i64)
            .checked_mul(FUNDED_PERIODS)
            .ok_or_else(|| {
                AgentPlatformError::BadTerms("rent_per_period funding overflows".into())
            })?;

        let bundle = parse_caps_confined(caps, account, budget, workdir, Confinement::Hosted)
            .map_err(AgentPlatformError::Caps)?;
        // Open under a fresh RANDOM receipt-chain secret we RETAIN (host-held), rather
        // than `Session::open`'s internal random draw: the grain must be able to cold
        // wake and re-sign the resumed chain with the SAME key, so the secret is
        // persisted (as part of the carrier) into the committed heap — see
        // [`SessionCarrier`] for the secret-handling + export note.
        let receipt_secret = fresh_receipt_secret();
        let session = Session::open_with_secret(account, bundle.spec, receipt_secret)
            .map_err(|e| AgentPlatformError::Session(e.to_string()))?;

        // THE FOLD + THE FUSION: rent = open_vat_prepaid (opens the durable image AND
        // the FUSED prepaid meter+reserve AND seals the vat lifecycle at `Created` on
        // the same cell) + a `BringUp` transition to `Running` (the launch). The
        // prepaid reserve is seeded to `rent_per_period * FUNDED_PERIODS` (== the
        // `funding` the lease cell balance holds), so the reserve MIRRORS the real
        // balance: each bill draws one rent from the reserve in the SAME atomic write
        // that advances the meter cursor (meter/pay drift unrepresentable). The lease
        // is then wrapped read/meter-side by a `HostedLease` over the SAME cell
        // (`from_cell_prepaid`, never a second open). A hosted agent grain rents
        // Symbolic (verify-later) — proofs re-derived on collapse, not as-you-go.
        let prepaid_terms = PrepaidLeaseTerms::new(
            terms.lease,    // lessee — the obligor/payer (the lease cell)
            terms.provider, // lessor — the beneficiary (the provider)
            terms.asset,
            terms.rent_per_period as i64,
            terms.period,
            terms.start,
            terms.max_periods,
            funding, // the prepaid reserve mirrors the funded balance
        );
        let mut lease_cell =
            Cell::with_balance(bytes32(terms.lease), bytes32(terms.asset), funding);
        open_vat_prepaid(
            &mut lease_cell,
            &prepaid_terms,
            field_from_u64(0),
            WitnessStance::Symbolic,
        )
        .map_err(|e| AgentPlatformError::Lease(format!("{e:?}")))?;
        // Launch: Created → Running, binding the box + endpoint for this host.
        apply_transition(
            &mut lease_cell,
            VatTransition::BringUp,
            box_token(&host),
            box_token(&host) ^ 0x01,
        )
        .map_err(|e| AgentPlatformError::Lifecycle(format!("{e:?}")))?;
        let vat =
            read_state(&lease_cell).map_err(|e| AgentPlatformError::Lifecycle(format!("{e:?}")))?;
        let lease = HostedLease::from_cell_prepaid(lease_cell, prepaid_terms);

        let mut tenants = self.tenants.lock().expect("platform poisoned");
        // Re-check under the write lock (TOCTOU with the read check above).
        if tenants.contains_key(&host) {
            return Err(AgentPlatformError::GrainOccupied(host));
        }
        tenants.insert(
            host.clone(),
            Arc::new(Mutex::new(Tenant {
                session,
                lease,
                vat,
                terms,
                workdir: std::path::PathBuf::from(workdir),
                caps: caps.to_string(),
                receipt_secret,
                budget,
                owner: account.to_string(),
                anchor,
                checkpoint: None,
                committed_turns: Vec::new(),
                node: None,
                node_minter: None,
                acl: HashMap::new(),
            })),
        );
        Ok(host)
    }

    /// The account that owns the grain at `host` (the only subject authorized to
    /// drive it), if hosted. The serve layer checks the caller's verified subject
    /// against this before driving.
    pub fn owner_of(&self, host: &str) -> Option<String> {
        // Brief map lock to clone the Arc, then read the owner off the tenant.
        let arc = self
            .tenants
            .lock()
            .expect("platform poisoned")
            .get(host)
            .cloned()?;
        let owner = arc.lock().expect("tenant poisoned").owner.clone();
        Some(owner)
    }

    /// **The caller's role on the grain at `host`, if any.** The owner is implicit
    /// [`Role::Admin`]; a shared subject gets its ACL-granted role; a non-member — or
    /// no grain here at all — is `None`. The serve layer turns `None` into a `404`
    /// on every route, so a non-member gets no existence oracle (a grain that isn't
    /// theirs is indistinguishable from a grain that isn't there).
    pub fn role_of(&self, host: &str, subject: &str) -> Option<Role> {
        let arc = self
            .tenants
            .lock()
            .expect("platform poisoned")
            .get(host)
            .cloned()?;
        let t = arc.lock().expect("tenant poisoned");
        if t.owner == subject {
            return Some(Role::Admin);
        }
        t.acl.get(subject).copied()
    }

    /// **Share the grain at `host` with `subject` at `role`** (owner/Admin only).
    /// The `caller` must resolve to an Admin role on the grain; a member below Admin
    /// is [`Unauthorized`](AgentPlatformError::Unauthorized) (403) and a non-member
    /// is [`NoSuchGrain`](AgentPlatformError::NoSuchGrain) (404 — no existence
    /// oracle). Granting a role to the owner is a no-op (they stay implicit Admin).
    pub fn share(
        &self,
        host: &str,
        caller: &str,
        subject: &str,
        role: Role,
    ) -> Result<(), AgentPlatformError> {
        match self.role_of(host, caller) {
            Some(Role::Admin) => {}
            Some(_) => {
                return Err(AgentPlatformError::Unauthorized(caller.to_string()));
            }
            None => return Err(AgentPlatformError::NoSuchGrain(host.to_string())),
        }
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        if guard.owner == subject {
            // The owner is already implicit Admin; do not shadow them in the ACL.
            return Ok(());
        }
        guard.acl.insert(subject.to_string(), role);
        Ok(())
    }

    /// **Revoke `subject`'s share on the grain at `host`** (owner/Admin only). Same
    /// authorization shape as [`share`](AgentPlatform::share). Un-sharing a subject
    /// that holds no grant succeeds (idempotent); the owner cannot be un-shared
    /// (they are never in the ACL, and stay implicit Admin).
    pub fn unshare(
        &self,
        host: &str,
        caller: &str,
        subject: &str,
    ) -> Result<(), AgentPlatformError> {
        match self.role_of(host, caller) {
            Some(Role::Admin) => {}
            Some(_) => {
                return Err(AgentPlatformError::Unauthorized(caller.to_string()));
            }
            None => return Err(AgentPlatformError::NoSuchGrain(host.to_string())),
        }
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        guard.acl.remove(subject);
        Ok(())
    }

    /// **The grain's drive transcript as an SSE `text/event-stream` body** —
    /// meta/step/done frames replaying every committed reason→act→observe step (see
    /// [`transcript`](crate::transcript) for the honest replay-not-live scope).
    /// Any member (Viewer+) may read it; the serve layer gates that.
    pub fn transcript(&self, host: &str) -> Result<String, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let guard = arc.lock().expect("tenant poisoned");
        Ok(transcript::transcript_stream(host, &guard.session))
    }

    /// The hosts currently served.
    pub fn hosts(&self) -> Vec<String> {
        let mut hosts: Vec<String> = self
            .tenants
            .lock()
            .expect("platform poisoned")
            .keys()
            .cloned()
            .collect();
        hosts.sort();
        hosts
    }

    /// Drive one typed `goal` through the grain at `host`: run the confined session's
    /// reason→act→observe loop against `brain` (metered, receipted, gated by the
    /// fixed cap bundle; the toolkit is the platform's operator tools ROOTED AT THE
    /// GRAIN'S RENTED WORKDIR — a caller cannot substitute tools rooted outside the
    /// confinement), then advance the lease's durable checkpoint with the verified
    /// session binding. Refuses on a lapsed lease. Returns the goal's delta report.
    ///
    /// The receipts this path seals carry NO kernel-turn link (the honest default:
    /// no executor is attached). For receipts that are views over genuine committed
    /// kernel turns — the R2 rung — use [`drive_minted`](Self::drive_minted).
    pub fn drive(
        &self,
        host: &str,
        goal: impl Into<String>,
        brain: &mut dyn AgentBrain,
    ) -> Result<GoalReport, AgentPlatformError> {
        self.drive_in(host, goal, brain, Mint::None, None)
    }

    /// **R2 — [`drive`](Self::drive) welded to genuine kernel turns.** Every
    /// admitted action is first minted as a REAL committed executor turn through
    /// `minter` (refusal admits nothing — the executor's own caveat is the
    /// host-side meter), and the committed turn hash is sealed into the action's
    /// receipt as its `turn_receipt_hash`. The platform records each committed
    /// hash into the grain's manifest, which [`verify_r2`](Self::verify_r2) checks
    /// every receipt against.
    ///
    /// The real kernel minter is `grain-turn`'s `ToolGatewayMinter` (the verified
    /// executor + proven `ToolGateway`); `dregg_agent`'s `SyntheticMinter` only
    /// exercises the seam and never stands in for it silently — the caller always
    /// chooses, explicitly.
    pub fn drive_minted(
        &self,
        host: &str,
        goal: impl Into<String>,
        brain: &mut dyn AgentBrain,
        minter: &mut dyn GrainTurnMinter,
    ) -> Result<GoalReport, AgentPlatformError> {
        self.drive_in(host, goal, brain, Mint::External(minter), None)
    }

    /// **The DEFAULT served drive — R2, minter-wired.** Constructs the platform's
    /// REAL kernel minter (`grain-turn`'s [`ToolGatewayMinter`], its `ToolGateway`
    /// rate ceiling set to the grain's budget) and routes the drive through it, so
    /// EVERY admitted action a hosted agent takes becomes a genuine committed
    /// executor turn and its receipt is a VIEW over that turn ([`verify_r2`] passes).
    /// This is the path the served HTTP route ([`drive_live`](Self::drive_live)) and
    /// any hosted embedding drive through by default — R0→R2 for the shipped product.
    ///
    /// The unminted [`drive`](Self::drive) is retained as the explicit
    /// standalone/adoption escape hatch (no executor attached, receipts below R2);
    /// the SERVED default is this, which mints.
    ///
    /// **The federation / local-submit leg (this is the keystone the wave closed):**
    /// the minted turns commit onto the grain's [`node::LocalNode`] — a real,
    /// locally-runnable node's ledger + finalized, light-client-verifiable receipt
    /// log — through a persistent [`node::NodeMinter`], NOT a per-drive throwaway
    /// `AgentRuntime`. So a renter no longer just trusts THIS process's private
    /// runtime: the committed turn lands on a node's ledger, is recorded on its
    /// finalized chain, and [`verify_landed`](Self::verify_landed) (a light-client
    /// verify + membership check) confirms it. Point the platform at an EXTERNAL
    /// federation node with [`with_node_url`](Self::with_node_url) — forwarding the
    /// finalized turn to a homelab node's ingress is the operational deploy step
    /// (still local here). Proving the turns RAN under a whole-chain STARK is the
    /// remaining R3 leg ([`grain_verify::WHOLE_HISTORY_GAP`]).
    pub fn drive_serving(
        &self,
        host: &str,
        goal: impl Into<String>,
        brain: &mut dyn AgentBrain,
    ) -> Result<GoalReport, AgentPlatformError> {
        self.drive_in(host, goal, brain, Mint::Node, None)
    }

    /// **THE FUSION — a served drive whose minted turns commit to a zkOracle
    /// attestation.** Exactly [`drive_serving`](Self::drive_serving), but every turn
    /// minted onto the grain's [`node::LocalNode`] ALSO witnesses `attestation_commitment`
    /// (the canonical hash of the confined brain's `ZkOracleAttestation` —
    /// `deos_hermes::attestation_commitment`) at the grain-turn cell's attestation slot.
    /// So the on-ledger, finalized receipt now binds "this action was driven by a
    /// **jailed** (`deos-hermes` host) **attested** (authentic ∧ well-formed ∧
    /// injection-free) brain," and [`verify_landed_attested`](Self::verify_landed_attested)
    /// confirms the landed turn carries the commitment. A light client holding the
    /// attestation recomputes its commitment and checks it equals the witnessed slot —
    /// an unattested or forged binding is distinguishable.
    pub fn drive_serving_attested(
        &self,
        host: &str,
        goal: impl Into<String>,
        brain: &mut dyn AgentBrain,
        attestation_commitment: [u8; 32],
    ) -> Result<GoalReport, AgentPlatformError> {
        self.drive_in(host, goal, brain, Mint::Node, Some(attestation_commitment))
    }

    /// The one drive path both public drives share: audit the rent schedule, run
    /// the goal (optionally minted), record any committed turn hashes, checkpoint.
    /// `attestation` (Node mint only) binds a zkOracle attestation commitment onto the
    /// minted turns.
    fn drive_in(
        &self,
        host: &str,
        goal: impl Into<String>,
        brain: &mut dyn AgentBrain,
        mint: Mint<'_>,
        attestation: Option<[u8; 32]>,
    ) -> Result<GoalReport, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        let tenant = &mut *guard;
        // Audit the rent schedule at the operator's clock — a grain behind on rent
        // lapses ON USE rather than trusting a stale flag (the "free hosting" fix).
        let _ = tenant
            .lease
            .lapse_if_behind(self.clock.load(std::sync::atomic::Ordering::Relaxed));
        if tenant.lease.is_lapsed() {
            return Err(AgentPlatformError::Lapsed);
        }
        // The served path mints onto the grain's LOCAL NODE. Bring the node + its
        // persistent node-backed minter up lazily (once), so the worker cell stays
        // stable and the node's finalized chain accumulates a single-agent, verifiable
        // sequence across drives.
        if matches!(mint, Mint::Node) && tenant.node_minter.is_none() {
            let localnode = node::LocalNode::new(host);
            // ROUTE (ii): open the minter under the platform's HOST executor signing
            // seed (when set), so every grain turn this node mints is host-signed and
            // forge-admissible. `None` keeps grain receipts unsigned (byte-unchanged).
            // Upgrade-safety: an anchored (owner-provided RenterAnchor) grain is
            // enveloped — its authority-widening slots gate to the owner key, so the
            // host cannot escalate over the grain through the executor.
            // WAVE A / WELD — OWNER LIVENESS: pass the renter/owner PUBLIC key down
            // (not just its `owner_envelope_vk`) so the grain's node executor can
            // REGISTER the owner-envelope verifier and the owner can actually
            // authorize the Custom-gated widening turns. The vk_hash for the cell's
            // permission slots is re-derived inside `admit_enveloped_owned`.
            let owner_pubkey = tenant.anchor.as_ref().map(|a| a.pubkey);
            let node_minter = node::NodeMinter::open_signed(
                localnode.clone(),
                tenant.budget,
                self.executor_signing_seed,
                owner_pubkey,
            )
            .map_err(|e| AgentPlatformError::Session(format!("open node minter: {e}")))?;
            tenant.node = Some(localnode);
            tenant.node_minter = Some(node_minter);
        }
        let toolkit = OperatorTools::new(Toolkit::new(), &tenant.workdir);
        let report = match mint {
            Mint::None => tenant.session.run_goal(goal, brain, &toolkit),
            Mint::External(inner) => {
                // Record every hash the minter commits into the grain's manifest —
                // the host-side committed-turn set verify_r2 audits receipts against.
                let mut recording = RecordingMinter {
                    inner,
                    minted: Vec::new(),
                };
                let report =
                    tenant
                        .session
                        .run_goal_minted(goal, brain, &toolkit, Some(&mut recording));
                tenant.committed_turns.extend(recording.minted);
                report
            }
            Mint::Node => {
                // Drive through the grain's PERSISTENT node-backed minter: every
                // admitted action is minted as a genuine executor turn onto the local
                // node's ledger AND landed on its finalized receipt log. Record the
                // committed hashes into the manifest, same as the external path.
                let node_minter = tenant
                    .node_minter
                    .as_mut()
                    .expect("node minter brought up above");
                // THE FUSION: bind the zkOracle attestation commitment onto the minter,
                // so every turn this drive commits also witnesses the confined brain's
                // attestation (a `None` leaves the turns unattested).
                if let Some(commitment) = attestation {
                    node_minter.bind_attestation(commitment);
                }
                let mut recording = RecordingMinter {
                    inner: node_minter,
                    minted: Vec::new(),
                };
                let report =
                    tenant
                        .session
                        .run_goal_minted(goal, brain, &toolkit, Some(&mut recording));
                tenant.committed_turns.extend(recording.minted);
                report
            }
        };
        checkpoint_tenant(tenant)?;
        Ok(report)
    }

    /// Drive one `goal` through the grain at `host` with a LIVE model brain: wire
    /// dregg-agent's OpenAI-compatible HTTP transport (a BYO key resolved from env)
    /// as the session's brain over the grain's granted `tools`, run it, and
    /// checkpoint. Each tool-call the model reaches for still crosses the fixed cap
    /// bundle before it becomes a receipt. Refuses on a lapsed lease or a missing
    /// key. `model`/base URL come from `DREGG_LLM_MODEL`/`DREGG_LLM_BASE` (defaults
    /// otherwise).
    ///
    /// **R2 — this served path MINTS.** The drive routes through
    /// [`drive_serving`](Self::drive_serving), which constructs the platform's real
    /// `grain-turn` kernel minter and welds every admitted action to a genuine
    /// committed executor turn — so the shipped served route produces R2 receipts
    /// (views over kernel turns), not unminted shadow receipts. The per-tenant lock
    /// is held only across `drive_serving`'s own drive (the platform-wide map lock is
    /// already dropped, so a slow provider round-trip never stalls another tenant —
    /// the head-of-line property is preserved). See `drive_serving` for the honest
    /// residual (in-process ledger; the federation-submit leg is next).
    #[cfg(feature = "live-brain")]
    pub fn drive_live(
        &self,
        host: &str,
        goal: impl Into<String>,
        tools: &[String],
    ) -> Result<GoalReport, AgentPlatformError> {
        use dregg_agent::agent::op;
        use dregg_agent::brain::{DEFAULT_OPENAI_BASE, LiveOpenAICompatCaller, OpenAICompatBrain};

        let goal = goal.into();
        // The live brain needs only env + goal + tools (no tenant state), so build
        // it before locking — a missing key fails fast without touching the grain.
        let key = live_key()
            .ok_or_else(|| AgentPlatformError::Session("no LLM key in env (DREGG_LLM_API_KEY / ANTHROPIC_API_KEY / OPENAI_API_KEY / NVIDIA_API_KEY)".into()))?;
        // `chat_completions_url` appends `/chat/completions` to the BASE, so the base
        // must already carry the provider's version segment (`…/v1`). The bare
        // `https://api.openai.com` default built `…/chat/completions` (no `/v1`) — a 404.
        let base =
            std::env::var("DREGG_LLM_BASE").unwrap_or_else(|_| DEFAULT_OPENAI_BASE.to_string());
        let model = std::env::var("DREGG_LLM_MODEL").unwrap_or_else(|_| "gpt-4o-mini".to_string());
        // A grain's granted tools split across TWO advertisement rails, and mis-slotting
        // them silently breaks the drive: operator-rail tools (`fs_write`, `shell`, …)
        // carry real `path`/`content` schemas and MUST ride `with_op_tools`, while flat
        // toolkit services (`run_tests`, `verify_deploy`, …) ride the parameterless
        // `invoke(service=…)` enum. Advertising an operator tool as a service hands the
        // model a call it cannot express, so its correct `fs_write` reads as an unknown
        // tool, the retry loop exhausts, and the drive admits nothing.
        let (op_tools, services): (Vec<String>, Vec<String>) = tools
            .iter()
            .cloned()
            .partition(|t| op::ALL.contains(&t.as_str()));
        let mut brain = OpenAICompatBrain::with_base(
            &goal,
            services,
            vec![],
            key,
            &base,
            &model,
            LiveOpenAICompatCaller::new(),
        )
        .with_op_tools(op_tools);
        // The served default MINTS: route through the real kernel minter (R2), not
        // the unminted `run_goal`. `drive_serving` handles the per-tenant lock, the
        // lapse-on-use audit, the minted drive, and the checkpoint.
        self.drive_serving(host, &goal, &mut brain)
    }

    /// Bill one rent `period` for `host` at `clock`: read-only GATE the bill on the
    /// FUSED prepaid meter ([`HostedLease::check_bill`] — refusing off-schedule /
    /// replay / over-draw / exhausted-reserve BEFORE any value moves), settle the
    /// drawn rent through `settlement` (the conserving cross-cell `Transfer` — the
    /// in-process double in tests, the on-chain node rail in production), then
    /// [`discharge`](HostedLease::discharge) it (the ONE atomic write that draws the
    /// rent from the reserve AND advances the meter cursor).
    ///
    /// Settlement COMPLEMENTS the meter, it does not replace it: `discharge` is the
    /// in-cell meter-plus-reserve-draw counter (moves NO value cross-cell), `settle`
    /// is the one cross-cell payment. Each bill draws exactly `rent` and settles that
    /// same `rent`, so `sum(settled) == drawn_total <= budget`. No double-pay (settle
    /// is exactly-once by `(lease_id, period)`, discharge is one-shot by the cursor);
    /// no unpaid draw (`check_bill`'s `InsufficientBudget` backstop refuses drawing
    /// past the reserve BEFORE settle runs). The tenant guard is held across all
    /// three, so the gate → settle → discharge sequence is atomic per grain.
    pub fn bill_period<S: Settlement>(
        &self,
        host: &str,
        period: i64,
        clock: i64,
        settlement: &S,
    ) -> Result<SettleReceipt, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        let tenant = &mut *guard;
        // GATE (read-only): refuse off-schedule / replay / over-draw / over-reserve
        // BEFORE any value moves. `rent` is the amount this period WILL draw.
        let rent = tenant
            .lease
            .check_bill(period, clock)
            .map_err(|e| AgentPlatformError::Lease(e.to_string()))?;
        // SETTLE the drawn rent — the one conserving cross-cell payment.
        let terms = &tenant.terms;
        let charge = LeaseCharge::new(
            hex32(terms.lease),
            hex32(terms.provider),
            hex32(terms.asset),
            host,
            period,
            rent,
        );
        let receipt = settlement
            .settle(&charge)
            .map_err(|e| AgentPlatformError::Settle(e.to_string()))?;
        // DISCHARGE: the ONE atomic write — draw exactly `rent` from the reserve AND
        // advance the meter cursor. The gate already proved this accepts, so the draw
        // and the settled payment are the same `rent` (sum(settled) == drawn_total).
        tenant
            .lease
            .discharge(period, clock)
            .map_err(|e| AgentPlatformError::Lease(e.to_string()))?;
        Ok(receipt)
    }

    /// Re-witness the session at `host`: the cumulative receipt chain is
    /// signature-consistent, unbroken, monotone, and the consumed budget stays
    /// at/under the ceiling — AND the lease's durable image binds this session
    /// (the committed digest / chain tip / turn count / consumed read back from
    /// the `EXEC_COLL` heap agree with the live session; a stale or tampered
    /// image is [`ImageDiverged`](AgentPlatformError::ImageDiverged)).
    ///
    /// Honest strength (the R-ladder, crate docs): the chain key is a fresh
    /// RANDOM secret (R0 — a third party holding the report cannot forge), but
    /// the HOST runs the signer, so this alone is tamper-evidence, not
    /// host-independence. R1 ([`RenterAnchor`] + the checkpoint countersign) adds
    /// third-party-verifiable anti-rewrite/anti-truncation; R2
    /// ([`verify_r2`](Self::verify_r2)) binds each receipt to a committed kernel
    /// turn; proving those turns RAN is R3's whole-history STARK leg
    /// ([`grain_verify::WHOLE_HISTORY_GAP`]).
    pub fn verify(&self, host: &str) -> Result<AgentVerified, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let guard = arc.lock().expect("tenant poisoned");
        let verified = guard
            .session
            .verify()
            .map_err(|e| AgentPlatformError::Verify(format!("{e:?}")))?;
        image_binds(&guard)?;
        Ok(verified)
    }

    /// **R2 — re-witness the grain at `host` against its committed-turn manifest**:
    /// [`verify`](Self::verify) (chain + budget + durable-image bind) PLUS every
    /// admitted receipt must be a view over a kernel turn the platform's minter
    /// actually committed ([`drive_minted`](Self::drive_minted)'s recorded
    /// manifest). A receipt with no turn link — e.g. from a plain unminted
    /// [`drive`](Self::drive) — or with a link naming no committed turn is
    /// REFUSED, both teeth per `grain_verify::GrainAttestation::verify_r2`.
    ///
    /// Honest scope (R2, not R3): this proves the receipts are bound to turns the
    /// executor host committed and that the meter was executor-enforced; it does
    /// not re-execute the turns (that is the whole-history STARK leg).
    pub fn verify_r2(&self, host: &str) -> Result<grain_verify::R2Verified, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let guard = arc.lock().expect("tenant poisoned");
        image_binds(&guard)?;
        self.attestation_of(&guard)
            .verify_r2(&guard.committed_turns)
            .map_err(|e| AgentPlatformError::Verify(format!("{e:?}")))
    }

    /// **The federation / local-submit leg — confirm the grain's minted turns
    /// LANDED on a real node, cross-node-verifiably.** Runs the local node's
    /// light-client verify ([`node::LocalNode::verify`] — the finalized receipt chain
    /// is a non-empty, unbroken, single-agent, state-continuous chain) AND checks that
    /// EVERY turn hash in the grain's committed-turn manifest is present on the node's
    /// finalized log ([`node::LocalNode::contains`]). Returns the [`Landed`] summary
    /// (the finalized chain length + how many manifest turns landed).
    ///
    /// This is what a renter checks to know the receipts are views over turns a real
    /// node committed — not just this process's private in-process runtime. It is
    /// stronger than [`verify_r2`](Self::verify_r2)'s host-side manifest: the manifest
    /// says "the host claims it minted these"; this says "these turns are on a node's
    /// finalized, independently re-verifiable ledger log."
    ///
    /// `NotLanded` if the grain has never been driven through the served minting path
    /// (no node brought up), or if a manifest turn is missing from the finalized log,
    /// or the chain fails structural verification.
    pub fn verify_landed(&self, host: &str) -> Result<Landed, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let guard = arc.lock().expect("tenant poisoned");
        let node = guard.node.as_ref().ok_or_else(|| {
            AgentPlatformError::Verify("grain has no local node (never driven-minted)".into())
        })?;
        // Light-client verify: the node's finalized receipt chain is structurally sound.
        node.verify()
            .map_err(|e| AgentPlatformError::Verify(format!("node chain unverifiable: {e}")))?;
        // Every manifest turn must be on the node's finalized log (it landed, not just
        // "the host says it minted it").
        for turn_hash in &guard.committed_turns {
            if !node.contains(turn_hash) {
                return Err(AgentPlatformError::Verify(format!(
                    "manifest turn {turn_hash:?} is not on the node's finalized log"
                )));
            }
        }
        Ok(Landed {
            finalized_len: node.finalized_len(),
            manifest_len: guard.committed_turns.len(),
        })
    }

    /// **THE FUSION verify — the landed turns are bound to a zkOracle attestation.**
    /// Runs [`verify_landed`](Self::verify_landed) (the light-client chain verify +
    /// manifest-membership check), THEN confirms the grain's committed grain-turn cell
    /// witnesses `expected_commitment` at its attestation slot — i.e. the finalized,
    /// on-ledger turns commit to the confined brain's `ZkOracleAttestation`.
    ///
    /// A light client passes the commitment it recomputed from the attestation it holds
    /// (`deos_hermes::attestation_commitment(&att)`); this returns `Ok` iff the landed
    /// turns carry exactly that commitment. An UNATTESTED grain (slot at the zero
    /// default) or a FORGED binding (a different hash on the ledger than the real
    /// attestation's) is [`AgentPlatformError::Verify`] — distinguishable, not accepted.
    pub fn verify_landed_attested(
        &self,
        host: &str,
        expected_commitment: [u8; 32],
    ) -> Result<Landed, AgentPlatformError> {
        let landed = self.verify_landed(host)?;
        let arc = self.tenant_arc(host)?;
        let guard = arc.lock().expect("tenant poisoned");
        let minter = guard.node_minter.as_ref().ok_or_else(|| {
            AgentPlatformError::Verify("grain has no node minter (never driven-minted)".into())
        })?;
        match minter.attestation_slot() {
            Some(c) if c == expected_commitment => Ok(landed),
            Some(c) => Err(AgentPlatformError::Verify(format!(
                "landed turn's attestation commitment {c:?} does not match the expected \
                 attestation {expected_commitment:?} (forged or wrong-brain binding)"
            ))),
            None => Err(AgentPlatformError::Verify(
                "the grain's committed turn cell has no attestation slot".into(),
            )),
        }
    }

    /// **THE RAIL JOIN — the landed attestation slot is proven by REAL TEE vendor
    /// crypto.** [`verify_landed_attested`](Self::verify_landed_attested) (unchanged,
    /// Rail A) is a plain byte-compare: it confirms the landed turns witness *some*
    /// expected 32 bytes, trusting the caller to know what those bytes mean. This is
    /// the join to Rail B (the `WitnessedPredicate` crypto): it runs the SAME
    /// light-client chain checks ([`verify_landed`](Self::verify_landed)), reads the
    /// commitment the finalized ledger witnesses at [`grain_turn::ATTESTATION_SLOT`],
    /// then requires a genuine TEE quote to bind it — the
    /// [`dregg_cell::tee_attest::tee_attestation_predicate`] for `pinned_measurement`
    /// at the attestation slot, verified through the caller's `registry` against
    /// `tee_proof`. The registered verifier (install the real vendor crypto with
    /// `deos_hermes::tee_fact::install_tee_fact_verifier`; an empty registry refuses)
    /// enforces the full contract: the quote is vendor-signed to the hardware root,
    /// its measurement equals `pinned_measurement` (pinned out of band), and its
    /// `report_data` equals the LANDED slot value — so "an enclave-attested session"
    /// becomes a light-client-checkable fact: *the measured binary, inside a genuine
    /// TEE, bound exactly this finalized session commitment.*
    ///
    /// `tee_proof` is the kind-prefixed quote blob
    /// ([`dregg_cell::tee_attest::encode_tee_proof`]`(kind, document)`) — e.g. an AWS
    /// Nitro attestation document as `dregg-tee-produce` transports it. Fail-closed
    /// everywhere: no node, no slot, an unregistered predicate kind, or any vendor-
    /// crypto refusal (forged/tampered quote, wrong measurement, unbound
    /// `report_data`, down-level TCB) is [`AgentPlatformError::Verify`].
    ///
    /// Honest strength: this adds **single-hardware-root execution-integrity** on top
    /// of the landed R2 rail — you trust the CPU vendor's attestation root, and the
    /// quote says nothing about the output's *correctness* (that remains R3's
    /// whole-history STARK leg).
    pub fn verify_landed_tee_attested(
        &self,
        host: &str,
        registry: &dregg_cell::predicate::WitnessedPredicateRegistry,
        pinned_measurement: [u8; 32],
        tee_proof: &[u8],
    ) -> Result<Landed, AgentPlatformError> {
        // Rail A: the light-client chain verify + manifest-membership check.
        let landed = self.verify_landed(host)?;
        // The landed ground truth: the commitment witnessed at ATTESTATION_SLOT on
        // the node's committed grain-turn cell (read off the finalized ledger, not
        // off any host claim).
        let arc = self.tenant_arc(host)?;
        let guard = arc.lock().expect("tenant poisoned");
        let minter = guard.node_minter.as_ref().ok_or_else(|| {
            AgentPlatformError::Verify("grain has no node minter (never driven-minted)".into())
        })?;
        let slot = minter.attestation_slot().ok_or_else(|| {
            AgentPlatformError::Verify(
                "the grain's committed turn cell has no attestation slot".into(),
            )
        })?;
        // Rail B: the quote must be genuine (vendor-signed to the hardware root),
        // for the pinned binary, and bound to EXACTLY the landed slot commitment.
        let predicate = dregg_cell::tee_attest::tee_attestation_predicate(
            pinned_measurement,
            grain_turn::ATTESTATION_SLOT as u8,
        );
        registry
            .verify(
                &predicate,
                &dregg_cell::predicate::PredicateInput::Slot(&slot),
                tee_proof,
            )
            .map_err(|e| {
                AgentPlatformError::Verify(format!(
                    "TEE attestation predicate refused the landed slot binding: {e:?}"
                ))
            })?;
        Ok(landed)
    }

    /// Lapse the lease at `host` if it is behind schedule at `clock` (non-payment):
    /// the grain is reclaimed and driving it is refused. Returns whether it lapsed.
    pub fn reap_if_behind(&self, host: &str, clock: i64) -> Result<bool, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        let lapsed = guard
            .lease
            .lapse_if_behind(clock)
            .map_err(|e| AgentPlatformError::Lease(e.to_string()))?;
        // THE FOLD: mirror the lease's LAPSED tooth in the vat lifecycle — any live
        // grain moves to `Lapsed` (routed through the legality-checked transition, so
        // an already-lapsed/terminal grain is a no-op, never a double-lapse).
        if lapsed && guard.vat != VatState::Lapsed && !guard.vat.is_terminal() {
            guard.transition(host, VatTransition::Lapse)?;
        }
        Ok(lapsed)
    }

    /// **Sleep the grain at `host`** — checkpoint-and-tear-down. Routes the vat
    /// `Running → Sleeping` transition: the box goes dark and metering stops; the
    /// durable image is what follows. Refused if the grain is not Running (the
    /// machine's own tooth). The session + committed history are retained for the wake.
    pub fn sleep(&self, host: &str) -> Result<VatState, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        guard.transition(host, VatTransition::Sleep)
    }

    /// **Wake the grain at `host` from its lease** — the named *wake-from-lease* move,
    /// delivered for free by the fold: the vat's `BringUp` from `Sleeping → Running`
    /// re-places the box, restores from the durable image, and resumes metering.
    /// Refused if the grain is not Sleeping (the machine's own tooth).
    pub fn wake(&self, host: &str) -> Result<VatState, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        guard.transition(host, VatTransition::BringUp)
    }

    /// **COLD WAKE — rebuild the grain's session from its lease heap ALONE.** The
    /// distinct cold path beside the vat-lifecycle [`wake`](Self::wake) (which resumes
    /// metering but NEEDS the in-RAM `Tenant.session`): this RECONSTITUTES the session
    /// itself from the full resumable carrier persisted in `EXEC_COLL`, the wake a
    /// grain needs after its process-local RAM is gone.
    ///
    /// It reads the carrier back (length + data slots), verifies the ROOT TOOTH
    /// FAIL-CLOSED (a tampered or truncated carrier is [`CarrierRefused`], never a
    /// partial reconstruction — the byte-identical discipline of
    /// `AgentMemoryCheckpoint::resume_into`), rebuilds the [`Session`] via
    /// [`Session::wake_from_report`] (the heap-persisted secret + consumed + receipt
    /// chain — NOT the retained in-memory session and NOT the filesystem
    /// [`ConsumedStore`](dregg_agent::session_store::ConsumedStore)), installs it plus
    /// the restored R2 committed-turn manifest, and RE-WITNESSES the reconstruction
    /// (chain + durable-image bind) before returning it.
    ///
    /// After this, [`verify`](Self::verify) / [`verify_r2`](Self::verify_r2) hold and
    /// [`attest`](Self::attest) reproduces the grain's chain — the session is as real
    /// as the one that was lost. Refuses if no grain is hosted at `host` or the
    /// carrier does not reconstitute.
    pub fn wake_from_lease(&self, host: &str) -> Result<AgentVerified, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        let tenant = &mut *guard;
        // Read + reassemble + root-tooth-verify the carrier off the committed heap.
        let carrier = read_carrier(tenant)?;
        // Rebuild the AgentSpec exactly as `rent` did (same caps/budget/workdir ⇒ same
        // asset + ceiling), so the woken handle.id/budget/asset match the persisted
        // report — reading only RETAINED rental terms, never the lost session.
        let workdir = tenant.workdir.to_string_lossy();
        let bundle = parse_caps_confined(
            &tenant.caps,
            &tenant.owner,
            tenant.budget,
            &workdir,
            Confinement::Hosted,
        )
        .map_err(AgentPlatformError::Caps)?;
        let session = Session::wake_from_report(
            &tenant.owner,
            bundle.spec,
            carrier.receipt_secret,
            &carrier.report,
            carrier.history,
        )
        .map_err(|e| AgentPlatformError::Session(e.to_string()))?;
        drop(workdir);
        // Install the reconstituted session + the restored R2 manifest (both from the
        // heap), replacing whatever was — or was not — in RAM.
        tenant.committed_turns = carrier.committed_turns;
        tenant.session = session;
        // Fail-closed self-check: the reconstruction re-witnesses (chain signature +
        // budget) AND still binds the unchanged durable image, or the wake refuses.
        let verified = tenant
            .session
            .verify()
            .map_err(|e| AgentPlatformError::Verify(format!("{e:?}")))?;
        image_binds(tenant)?;
        Ok(verified)
    }

    /// The grain's current verified lifecycle state at `host` — the vat [`VatState`]
    /// read off the lease cell (created / running / sleeping / lapsed / reaped), or
    /// [`NoSuchGrain`](AgentPlatformError::NoSuchGrain).
    pub fn grain_state(&self, host: &str) -> Result<VatState, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let guard = arc.lock().expect("tenant poisoned");
        read_state(guard.lease.cell()).map_err(|e| AgentPlatformError::Lifecycle(format!("{e:?}")))
    }

    /// The renter's artifact for the grain at `host`: a
    /// [`grain_verify::GrainAttestation`] over the session's cumulative receipt
    /// chain, carrying whatever R1 anchor material the grain holds (the genesis
    /// pin bound to THIS chain's signer + the latest renter-countersigned
    /// checkpoint), so a third party can run the anti-rewrite/anti-truncation
    /// teeth via `verify_for_renter`.
    ///
    /// Honest strength: with no anchor this is a **tamper-evident receipt log**
    /// under a random secret signer (R0) — the HOST runs the signer, so a
    /// malicious host could still present a self-consistent alternate history;
    /// that is exactly what the R1 anchor pins and the R3 whole-history STARK leg
    /// ([`grain_verify::WHOLE_HISTORY_GAP`]) will remove. Nothing below R3 forces
    /// completeness ("did nothing else").
    pub fn attest(&self, host: &str) -> Result<grain_verify::GrainAttestation, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let guard = arc.lock().expect("tenant poisoned");
        Ok(self.attestation_of(&guard))
    }

    /// Assemble the grain's attestation with its R1 anchor material attached
    /// (shared by [`attest`](Self::attest) and [`verify_r2`](Self::verify_r2)).
    fn attestation_of(&self, tenant: &Tenant) -> grain_verify::GrainAttestation {
        let mut att = grain_verify::GrainAttestation::attest(&tenant.session);
        if let Some(anchor) = &tenant.anchor {
            att = att.with_genesis(grain_verify::GenesisPin {
                renter_nonce: anchor.nonce,
                signer: tenant.session.report().signer,
            });
        }
        if let Some(cs) = &tenant.checkpoint {
            att = att.with_checkpoint(cs.clone());
        }
        att
    }

    /// **R1** — the checkpoint a renter should countersign for the grain's CURRENT
    /// chain tip: `(head_root, num_turns)`. This is what `GET <host>/checkpoint`
    /// returns; the renter countersigns it with
    /// [`grain_verify::countersign_checkpoint`] and POSTs it back. Refused if the
    /// session has committed nothing yet (no tip to acknowledge).
    pub fn checkpoint_offer(
        &self,
        host: &str,
    ) -> Result<grain_verify::RenterCheckpoint, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let guard = arc.lock().expect("tenant poisoned");
        grain_verify::GrainAttestation::attest(&guard.session)
            .checkpoint_to_countersign()
            .ok_or_else(|| {
                AgentPlatformError::Checkpoint(
                    "the grain has committed no turns to checkpoint yet".into(),
                )
            })
    }

    /// **R1** — accept a renter's countersigned checkpoint (`POST <host>/checkpoint`)
    /// and store it as the grain's latest acknowledgement. Fail-closed: a renter
    /// pubkey must have been pinned at rent, the countersignature must be BY that
    /// pinned key and verify, the checkpoint must match a real committed prefix of
    /// the current chain (so the platform never stores a bogus root), and it must
    /// not regress below the stored acknowledgement (`num_turns` monotone).
    pub fn submit_checkpoint(
        &self,
        host: &str,
        cs: grain_verify::CountersignedCheckpoint,
    ) -> Result<(), AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let mut guard = arc.lock().expect("tenant poisoned");
        let tenant = &mut *guard;
        let pinned = tenant.anchor.map(|a| a.pubkey).ok_or_else(|| {
            AgentPlatformError::Checkpoint(
                "no renter anchor pinned at rent; R1 unavailable for this grain".into(),
            )
        })?;
        if cs.renter_pubkey != pinned {
            return Err(AgentPlatformError::Checkpoint(
                "countersignature is not by the pinned renter key".into(),
            ));
        }
        if !cs.sig_verifies() {
            return Err(AgentPlatformError::Checkpoint(
                "renter countersignature does not verify".into(),
            ));
        }
        // The acknowledged checkpoint must match a genuine committed prefix — the
        // platform never stores a root the chain does not actually have.
        let report = tenant.session.report();
        let n = cs.checkpoint.num_turns;
        if n == 0 || n as usize > report.receipts.len() {
            return Err(AgentPlatformError::Checkpoint(format!(
                "checkpoint num_turns {n} is not a committed prefix (chain has {} turns)",
                report.receipts.len()
            )));
        }
        let at = report.receipts[(n - 1) as usize].receipt_hash();
        if at != Some(cs.checkpoint.head_root) {
            return Err(AgentPlatformError::Checkpoint(
                "checkpoint head_root does not match the chain at that position".into(),
            ));
        }
        // Monotone: never regress the acknowledged tip (an old checkpoint replayed
        // to enable a later truncation is refused on store).
        if let Some(prev) = &tenant.checkpoint
            && n < prev.checkpoint.num_turns
        {
            return Err(AgentPlatformError::Checkpoint(format!(
                "checkpoint regresses: num_turns {n} < stored {}",
                prev.checkpoint.num_turns
            )));
        }
        tenant.checkpoint = Some(cs);
        Ok(())
    }

    /// The consumed budget of the grain at `host` (its running meter).
    pub fn consumed(&self, host: &str) -> Result<i64, AgentPlatformError> {
        let arc = self.tenant_arc(host)?;
        let consumed = arc.lock().expect("tenant poisoned").session.consumed();
        Ok(consumed)
    }
}

/// Advance the grain's lease checkpoint (the `Monotonic` cursor moves, so a light
/// client sees the mind advance and it cannot rewind) and write the **session
/// binding** into the durable image: the `blake3(report)` digest (the cursor's
/// bound state) plus the chain tip / turn count / consumed working keys
/// ([`WK_CHAIN_TIP`]/[`WK_NUM_TURNS`]/[`WK_CONSUMED`]). [`image_binds`] reads all
/// four back on every platform `verify`, so a stale/tampered image is a refusal,
/// not a decoration.
///
/// **Phase 2 (wake-from-lease):** the checkpoint now ALSO persists the FULL resumable
/// session carrier ([`SessionCarrier`]) into the committed heap — the cursor slots
/// above stay (that is what [`image_binds`] re-checks for divergence), and beyond them
/// the carrier's length + root-tooth + data slots make the grain WAKEABLE from the
/// heap ALONE ([`AgentPlatform::wake_from_lease`]). The carrier is written in the SAME
/// atomic `checkpoint` write as the cursor, so a light client sees ONE advance binding
/// BOTH the cursor and the reconstructable image.
fn checkpoint_tenant(tenant: &mut Tenant) -> Result<(), AgentPlatformError> {
    let report = tenant.session.report();
    let digest = session_digest(&report);
    // The three cursor slots ([`image_binds`] re-checks these) FOLLOWED BY the carrier
    // slots (the full reconstructable image) — one working vector, one atomic write.
    let mut working = session_binding(&report).to_vec();
    working.extend(carrier_slots(tenant, &report)?);
    tenant
        .lease
        .checkpoint(digest, &working)
        .map_err(|e| AgentPlatformError::Lease(e.to_string()))?;
    Ok(())
}

/// Build the carrier heap slots for a checkpoint: serialize the [`SessionCarrier`]
/// (postcard, mirroring `AgentMemoryCheckpoint::to_bytes`), then lay it out as a
/// LENGTH slot + a ROOT-TOOTH slot (`blake3` of the full bytes) + N data slots (each
/// packs 32 carrier bytes, the last zero-padded). The root tooth is what the cold wake
/// re-derives and refuses on mismatch (a tampered/truncated carrier).
fn carrier_slots(
    tenant: &Tenant,
    report: &AgentRunReport,
) -> Result<Vec<(u32, FieldElement)>, AgentPlatformError> {
    let carrier = SessionCarrier {
        receipt_secret: tenant.receipt_secret,
        consumed: report.consumed,
        report: report.clone(),
        committed_turns: tenant.committed_turns.clone(),
        history: tenant.session.history().to_vec(),
    };
    let bytes = postcard::to_allocvec(&carrier)
        .map_err(|e| AgentPlatformError::CarrierRefused(format!("serialize carrier: {e}")))?;
    let mut slots = Vec::with_capacity(2 + bytes.len().div_ceil(32));
    slots.push((WK_CARRIER_LEN, field_from_u64(bytes.len() as u64)));
    slots.push((WK_CARRIER_ROOT, *blake3::hash(&bytes).as_bytes()));
    for (i, chunk) in bytes.chunks(32).enumerate() {
        let mut fe = [0u8; 32];
        fe[..chunk.len()].copy_from_slice(chunk);
        slots.push((WK_CARRIER_DATA_BASE + i as u32, fe));
    }
    Ok(slots)
}

/// **Read + reassemble the resumable carrier off the lease's `EXEC_COLL` heap and
/// verify its ROOT TOOTH — FAIL-CLOSED.** The read-back half of [`carrier_slots`],
/// holding the byte-identical anti-substitution discipline of
/// `AgentMemoryCheckpoint::resume_into`: an absent length slot (nothing persisted), a
/// missing data slot (truncation), a byte-flip that re-hashes to a different root
/// (tamper), or a deserialize failure is [`CarrierRefused`] — never a partial or
/// substituted reconstruction.
fn read_carrier(tenant: &Tenant) -> Result<SessionCarrier, AgentPlatformError> {
    let len = tenant
        .lease
        .read_working(WK_CARRIER_LEN)
        .map(|fe| u64_from_field(&fe) as usize)
        .ok_or_else(|| {
            AgentPlatformError::CarrierRefused(
                "no resumable carrier persisted in the lease heap (never checkpointed)".into(),
            )
        })?;
    let root = tenant.lease.read_working(WK_CARRIER_ROOT).ok_or_else(|| {
        AgentPlatformError::CarrierRefused("carrier root-tooth slot is absent".into())
    })?;
    let n_slots = len.div_ceil(32);
    let mut bytes = Vec::with_capacity(n_slots * 32);
    for i in 0..n_slots {
        let fe = tenant
            .lease
            .read_working(WK_CARRIER_DATA_BASE + i as u32)
            .ok_or_else(|| {
                AgentPlatformError::CarrierRefused(format!(
                    "carrier truncated: data slot {i} of {n_slots} is missing"
                ))
            })?;
        bytes.extend_from_slice(&fe);
    }
    bytes.truncate(len);
    // ROOT TOOTH, fail-closed: the reassembled bytes MUST re-hash to the committed
    // root. A flipped byte in any data slot (or a wrong length) re-derives a different
    // root and the wake refuses — the anti-substitution tooth over the whole carrier.
    if *blake3::hash(&bytes).as_bytes() != root {
        return Err(AgentPlatformError::CarrierRefused(
            "root-tooth mismatch: the reassembled carrier does not match the committed root \
             (tampered or truncated)"
                .into(),
        ));
    }
    postcard::from_bytes(&bytes)
        .map_err(|e| AgentPlatformError::CarrierRefused(format!("deserialize carrier: {e}")))
}

/// Decode a `u64` from the last 8 big-endian bytes of a field element — the inverse of
/// [`hosted_lease::field_from_u64`] (kept local so this crate needs no direct
/// `starbridge_execution_lease` dep for the one read).
fn u64_from_field(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// A fresh, unpredictable 32-byte receipt-chain secret from OS randomness — the
/// host-held signing seed a grain is opened under (and persists, root-committed, into
/// its carrier) so a cold wake re-signs the resumed chain with the SAME key.
fn fresh_receipt_secret() -> [u8; 32] {
    let mut secret = [0u8; 32];
    getrandom::fill(&mut secret).expect("operating-system randomness is available");
    secret
}

/// The working-memory binding of a session report: chain tip (zero for an empty
/// chain), committed turn count, cumulative consumed.
fn session_binding(report: &AgentRunReport) -> [(u32, FieldElement); 3] {
    let tip = report
        .receipts
        .last()
        .and_then(|r| r.receipt_hash())
        .unwrap_or([0u8; 32]);
    [
        (WK_CHAIN_TIP, tip),
        (WK_NUM_TURNS, field_from_u64(report.receipts.len() as u64)),
        (WK_CONSUMED, field_from_u64(report.consumed.max(0) as u64)),
    ]
}

/// **Read the durable image back and check it binds the live session** — the
/// other half that makes the checkpoint a verified binding instead of a stamp
/// nothing reads. Compares the committed digest ([`hosted_lease::KEY_DIGEST`])
/// and every [`session_binding`] working key against values re-derived from the
/// session right now. Skipped only before the first checkpoint (`step == 0`, the
/// genesis image — there is nothing bound yet). Any disagreement — a divergence
/// between the witnessed durable image and the mind it claims to bind — is
/// [`AgentPlatformError::ImageDiverged`].
fn image_binds(tenant: &Tenant) -> Result<(), AgentPlatformError> {
    if tenant.lease.step() == 0 {
        return Ok(());
    }
    let report = tenant.session.report();
    let want_digest = session_digest(&report);
    let got_digest = tenant.lease.read_working(hosted_lease::KEY_DIGEST);
    if got_digest != Some(want_digest) {
        return Err(AgentPlatformError::ImageDiverged(
            "committed state digest disagrees with the live session".into(),
        ));
    }
    for (key, want) in session_binding(&report) {
        if tenant.lease.read_working(key) != Some(want) {
            let name = match key {
                WK_CHAIN_TIP => "chain tip",
                WK_NUM_TURNS => "turn count",
                _ => "consumed",
            };
            return Err(AgentPlatformError::ImageDiverged(format!(
                "committed {name} disagrees with the live session"
            )));
        }
    }
    Ok(())
}

/// A field-element digest of the session's cumulative report — the state the
/// lease checkpoint cursor binds (see [`checkpoint_tenant`] / [`image_binds`]).
fn session_digest(report: &AgentRunReport) -> FieldElement {
    let bytes = serde_json::to_vec(report).unwrap_or_default();
    *blake3::hash(&bytes).as_bytes()
}

/// How a drive mints its admitted actions.
enum Mint<'a> {
    /// No minter — receipts carry no kernel-turn link (the standalone/adoption
    /// escape hatch, below R2).
    None,
    /// A caller-supplied minter (e.g. `drive_minted`'s explicit `grain-turn` minter
    /// or a test `SyntheticMinter`).
    External(&'a mut dyn GrainTurnMinter),
    /// The served default: the grain's persistent node-backed minter, minting onto
    /// the local node's ledger + finalized log (brought up lazily in `drive_in`).
    Node,
}

/// Forwards to a caller-supplied [`GrainTurnMinter`] and RECORDS every committed
/// turn hash, so [`AgentPlatform::drive_minted`] can append exactly what was
/// minted to the grain's manifest (the minter trait itself exposes no history).
struct RecordingMinter<'a> {
    inner: &'a mut dyn GrainTurnMinter,
    minted: Vec<[u8; 32]>,
}

impl GrainTurnMinter for RecordingMinter<'_> {
    fn mint_turn(
        &mut self,
        label: &str,
        cost: i64,
        consumed_after: i64,
        cell_root: [u8; 32],
    ) -> Result<[u8; 32], String> {
        let hash = self
            .inner
            .mint_turn(label, cost, consumed_after, cell_root)?;
        self.minted.push(hash);
        Ok(hash)
    }
}

/// Resolve a BYO LLM provider key from the env chain (redacted-Debug preserved by
/// `ProviderKey`). Same order the live brain honors.
#[cfg(feature = "live-brain")]
fn live_key() -> Option<dregg_agent::brain::ProviderKey> {
    use dregg_agent::brain::ProviderKey;
    ProviderKey::from_env("dregg", "DREGG_LLM_API_KEY")
        .or_else(|| ProviderKey::from_env("anthropic", "ANTHROPIC_API_KEY"))
        .or_else(|| ProviderKey::from_env("openai", "OPENAI_API_KEY"))
        .or_else(|| ProviderKey::from_env("nvidia", "NVIDIA_API_KEY"))
}

fn bytes32(cell: CellId) -> [u8; 32] {
    let mut a = [0u8; 32];
    a.copy_from_slice(cell.as_bytes());
    a
}

fn hex32(cell: CellId) -> String {
    cell.as_bytes().iter().map(|b| format!("{b:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_agent::agent::{AgentAction, PlannedBrain, SyntheticMinter, ToolCall};
    use hosted_durable::TestConservingLedger;

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }

    fn terms() -> LeaseTerms {
        // provider=2, lease cell=7, asset=9; rent 100 every 50 blocks from 1000.
        LeaseTerms::new(cid(2), cid(7), cid(9), 100, 50, 1000, 0)
    }

    fn workdir() -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!("dregg-grain-{}", std::process::id()));
        std::fs::create_dir_all(&p).unwrap();
        p
    }

    /// A recorded brain: a fixed plan of fs writes (hosted-safe — no shell).
    fn fs_plan(files: &[(&str, &str)]) -> PlannedBrain {
        let plan = files
            .iter()
            .map(|(path, content)| {
                AgentAction::Op(ToolCall::new(
                    "fs_write",
                    [
                        ("path".to_string(), path.to_string()),
                        ("content".to_string(), content.to_string()),
                    ],
                ))
            })
            .collect();
        PlannedBrain::new(plan)
    }

    #[test]
    fn an_agent_grain_is_rented_driven_metered_witnessed_and_reaped() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        let host = platform
            .rent(
                "alice.agents.dregg",
                "dga1_alice",
                "fs", // hosted-safe cap bundle (a raw `shell` would be refused)
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision the agent grain");

        // Drive a goal — the confined agent writes two files, metered + receipted.
        let mut brain = fs_plan(&[("notes.txt", "hello"), ("plan.txt", "world")]);
        let report = platform
            .drive(&host, "write my notes", &mut brain)
            .expect("drive the grain");
        assert!(report.admitted > 0, "the grain did admitted work");
        assert!(platform.consumed(&host).unwrap() > 0, "the meter drew down");

        // Re-witness the session (chain + budget + the durable-image bind).
        platform.verify(&host).expect("the session re-witnesses");

        // Bill period 0 (rent due at 1000): meter + settle a real conserving transfer.
        let ledger = TestConservingLedger::new();
        ledger.fund(&hex32(cid(9)), &hex32(cid(7)), 100_000);
        let settled = platform
            .bill_period(&host, 0, 1000, &ledger)
            .expect("meter + settle rent");
        assert_eq!(settled.amount, 100);
        assert_eq!(
            ledger.balance(&hex32(cid(9)), &hex32(cid(2))),
            100,
            "the provider was paid the rent"
        );

        // Miss period 1's rent → the grain is reaped → driving refuses.
        assert!(platform.reap_if_behind(&host, 1100).expect("audit"));
        let mut brain2 = fs_plan(&[("late.txt", "x")]);
        assert!(matches!(
            platform.drive(&host, "too late", &mut brain2),
            Err(AgentPlatformError::Lapsed)
        ));
    }

    /// **THE FUSION, end to end over the platform.** Billing meters AND settles as
    /// one gated sequence on the FUSED prepaid meter: each `bill_period` gates
    /// (`check_bill`), settles the drawn rent, then discharges it in ONE atomic
    /// write. After N bills the committed reserve is `budget − N·rent`, the drawn
    /// total is `N·rent == discharged_count·rent`, and `sum(settled) == drawn_total`
    /// (settle and draw are the same rent). A replay is `WrongPeriod` and an
    /// off-schedule bill is `NotYetDue` — BOTH refused by the gate BEFORE settle, so
    /// no value moves and `settled_total` does not budge (no double-pay, no drift).
    #[test]
    fn bill_period_fuses_meter_and_settlement_on_the_prepaid_reserve() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        let host = platform
            .rent(
                "fused.agents.dregg",
                "dga1_fused",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(), // rent 100 / 50 blocks / start 1000
                None,
            )
            .expect("provision");
        let ledger = TestConservingLedger::new();
        // Fund the payer (the lease cell, cid(7)) — mirrors the reserve.
        ledger.fund(&hex32(cid(9)), &hex32(cid(7)), 1_000_000);

        // Three on-schedule bills: each draws + settles exactly the rent.
        for k in 0..3i64 {
            let receipt = platform
                .bill_period(&host, k, 1000 + k * 50, &ledger)
                .expect("gate → settle → discharge");
            assert_eq!(receipt.amount, 100, "each bill settles exactly the rent");
            // The committed reserve + drawn total after n bills (meter == draw).
            let n = k + 1;
            let (remaining, drawn, count) = read_prepaid(&platform, &host);
            assert_eq!(
                remaining,
                100 * FUNDED_PERIODS - n * 100,
                "reserve == budget − n·rent"
            );
            assert_eq!(drawn, n * 100, "drawn == n·rent");
            assert_eq!(drawn, count * 100, "drawn == discharged_count·rent");
            // sum(settled) tracks the drawn total exactly.
            assert_eq!(
                ledger.settled_total(&host),
                drawn,
                "sum(settled) == drawn_total"
            );
        }
        let settled_after_three = ledger.settled_total(&host);
        assert_eq!(settled_after_three, 300);

        // Replay period 0: the gate refuses WrongPeriod BEFORE settle — no double-pay,
        // and the reserve/drawn are untouched.
        assert!(matches!(
            platform.bill_period(&host, 0, 1000, &ledger),
            Err(AgentPlatformError::Lease(_))
        ));
        assert_eq!(
            ledger.settled_total(&host),
            settled_after_three,
            "a replayed period does not settle again"
        );
        let (remaining, drawn, _) = read_prepaid(&platform, &host);
        assert_eq!(
            drawn, 300,
            "the meter did not advance on the refused replay"
        );
        assert_eq!(remaining, 100 * FUNDED_PERIODS - 300);

        // Off-schedule (period 3 due at 1150) billed early at clock 1149: NotYetDue,
        // refused by the gate BEFORE settle — no value moved.
        assert!(matches!(
            platform.bill_period(&host, 3, 1149, &ledger),
            Err(AgentPlatformError::Lease(_))
        ));
        assert_eq!(
            ledger.settled_total(&host),
            settled_after_three,
            "an off-schedule bill moves no value"
        );
    }

    /// Read the grain's committed prepaid `(remaining_budget, drawn_total,
    /// discharged_count)` off its lease cell (test helper).
    fn read_prepaid(platform: &AgentPlatform, host: &str) -> (i64, i64, i64) {
        let arc = platform.tenants.lock().unwrap().get(host).cloned().unwrap();
        let t = arc.lock().unwrap();
        let st = hosted_lease::PrepaidLeaseState::read(t.lease.cell())
            .expect("the grain rides the prepaid meter");
        (st.remaining_budget, st.drawn_total, st.discharged_count)
    }

    /// **THE FOLD, end to end.** A rented grain's lifecycle IS a vat: it launches to
    /// `Running`, sleeps to `Sleeping`, wakes back to `Running` (the wake-from-lease),
    /// refuses every illegal move by the machine's own tooth, and a delinquent grain
    /// moves to `Lapsed` — from which it can never wake again.
    #[test]
    fn the_grain_lifecycle_is_a_vat_machine() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        let host = platform
            .rent(
                "vat.agents.dregg",
                "dga1_vic",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision the grain");

        // rent = open_vat + BringUp → the grain launches Running.
        assert_eq!(platform.grain_state(&host).unwrap(), VatState::Running);

        // sleep = Running → Sleeping (checkpoint-and-tear-down).
        assert_eq!(platform.sleep(&host).unwrap(), VatState::Sleeping);
        assert_eq!(platform.grain_state(&host).unwrap(), VatState::Sleeping);

        // Illegal by the machine's tooth: you cannot sleep an already-sleeping grain.
        assert!(matches!(
            platform.sleep(&host),
            Err(AgentPlatformError::Lifecycle(_))
        ));

        // wake = Sleeping → Running (the named wake-from-lease, delivered by the fold).
        assert_eq!(platform.wake(&host).unwrap(), VatState::Running);
        assert_eq!(platform.grain_state(&host).unwrap(), VatState::Running);

        // Illegal: you cannot wake a grain that is already up.
        assert!(matches!(
            platform.wake(&host),
            Err(AgentPlatformError::Lifecycle(_))
        ));

        // Miss the rent → the lease lapses AND the vat lifecycle mirrors it to Lapsed.
        assert!(platform.reap_if_behind(&host, 1100).expect("audit"));
        assert_eq!(platform.grain_state(&host).unwrap(), VatState::Lapsed);

        // A lapsed grain can never wake again (BringUp is illegal from Lapsed).
        assert!(matches!(
            platform.wake(&host),
            Err(AgentPlatformError::Lifecycle(_))
        ));
    }

    #[test]
    fn drive_audits_the_schedule_and_lapses_a_delinquent_grain() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        let host = platform
            .rent(
                "del.agents.dregg",
                "dga1_del",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision");
        // The operator advances the clock past period 1's due block (1050) with no
        // rent ever paid — drive must AUDIT the schedule and lapse, not host free.
        platform.set_clock(1100);
        let mut brain = fs_plan(&[("x.txt", "y")]);
        assert!(matches!(
            platform.drive(&host, "go", &mut brain),
            Err(AgentPlatformError::Lapsed)
        ));
    }

    /// The platform clock is MONOTONE: a regression is ignored (block height never
    /// rewinds — a rewound clock would re-extend credit to a delinquent grain).
    #[test]
    fn the_platform_clock_never_rewinds() {
        let platform = AgentPlatform::new();
        assert_eq!(platform.set_clock(100), 100);
        assert_eq!(platform.set_clock(50), 100, "a clock regression is ignored");
        assert_eq!(platform.clock(), 100);
        assert_eq!(platform.set_clock(150), 150, "a genuine advance lands");
    }

    /// The platform-wide map lock is NOT held across a drive. A slow/stalled drive
    /// on grain A (here simulated by holding A's *tenant* lock, exactly what
    /// `drive_live` holds across its blocking provider round-trip) must not block a
    /// concurrent rent/drive/verify/bill on grain B — no head-of-line DoS.
    #[test]
    fn two_grains_can_be_driven_without_head_of_line_blocking() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        platform
            .rent(
                "a.agents.dregg",
                "dga1_a",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("rent A");
        platform
            .rent(
                "b.agents.dregg",
                "dga1_b",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("rent B");

        // Clone A's per-tenant handle under a brief map lock, then HOLD A's tenant
        // lock — simulating a live drive mid HTTP round-trip inside grain A.
        let a_arc = platform
            .tenants
            .lock()
            .expect("map lock")
            .get("a.agents.dregg")
            .cloned()
            .expect("A is hosted");
        let a_guard = a_arc.lock().expect("hold A's tenant lock");

        // With A's tenant lock held for the whole scope, grain B stays fully
        // operable. If any of these held the map lock across A's drive, this thread
        // would deadlock on the map lock and never join.
        std::thread::scope(|s| {
            let handle = s.spawn(|| {
                assert_eq!(
                    platform.owner_of("b.agents.dregg").as_deref(),
                    Some("dga1_b"),
                    "owner_of(B) resolves while A is held"
                );
                assert_eq!(platform.consumed("b.agents.dregg").unwrap(), 0);
                let mut brain = fs_plan(&[("b.txt", "hi")]);
                let report = platform
                    .drive("b.agents.dregg", "go", &mut brain)
                    .expect("drive B while A is held");
                assert!(report.admitted > 0, "B did admitted work");
                platform.verify("b.agents.dregg").expect("B re-witnesses");
            });
            handle
                .join()
                .expect("B operates without blocking on A's held tenant lock");
        });

        // A's tenant lock was reachable throughout via its own Arc; release it and
        // confirm A itself is still hosted + operable.
        drop(a_guard);
        assert_eq!(
            platform.owner_of("a.agents.dregg").as_deref(),
            Some("dga1_a")
        );
    }

    /// **R1 — the renter finality anchor, end-to-end over the platform.** A pinned
    /// grain: the renter supplies a nonce + pubkey at rent; drives commit turns; the
    /// renter fetches + countersigns a checkpoint and POSTs it back; the chain then
    /// extends; and a third party re-witnesses the attestation with the renter's
    /// pins — anti-rewrite + anti-truncation, trusting no host. Plus the store teeth:
    /// a wrong-key countersignature and a fabricated head_root are refused.
    #[test]
    fn r1_the_checkpoint_protocol_anchors_a_grain_end_to_end() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        let renter_seed = [0x5au8; 32];
        let renter_pub = dregg_agent::receipt::ReceiptSigner::from_seed(renter_seed).public();
        let nonce = [0x11u8; 32];
        let host = platform
            .rent(
                "anchored.agents.dregg",
                "dga1_anchor",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                Some(RenterAnchor {
                    nonce,
                    pubkey: renter_pub,
                }),
            )
            .expect("provision a pinned grain");

        // Before any drive there is nothing to checkpoint.
        assert!(matches!(
            platform.checkpoint_offer(&host),
            Err(AgentPlatformError::Checkpoint(_))
        ));

        // Drive a goal → the grain commits turns.
        let mut brain = fs_plan(&[("a.txt", "1"), ("b.txt", "2")]);
        platform
            .drive(&host, "write", &mut brain)
            .expect("drive the grain");

        // The renter fetches, countersigns, and submits the checkpoint.
        let cp = platform
            .checkpoint_offer(&host)
            .expect("offer a checkpoint");
        assert!(cp.num_turns >= 1);
        let cs = grain_verify::countersign_checkpoint(renter_seed, cp);
        platform
            .submit_checkpoint(&host, cs)
            .expect("store the renter countersignature");

        // A WRONG-KEY countersignature (not the pinned renter key) is refused.
        let cp_again = platform.checkpoint_offer(&host).unwrap();
        let evil = grain_verify::countersign_checkpoint([0x99u8; 32], cp_again);
        assert!(matches!(
            platform.submit_checkpoint(&host, evil),
            Err(AgentPlatformError::Checkpoint(_))
        ));

        // A FABRICATED head_root under the RIGHT key is refused (does not match chain).
        let bogus = grain_verify::RenterCheckpoint {
            head_root: [0xEEu8; 32],
            num_turns: 1,
        };
        let cs_bogus = grain_verify::countersign_checkpoint(renter_seed, bogus);
        assert!(matches!(
            platform.submit_checkpoint(&host, cs_bogus),
            Err(AgentPlatformError::Checkpoint(_))
        ));

        // Drive more → the chain extends past the acknowledged checkpoint.
        let mut brain2 = fs_plan(&[("c.txt", "3")]);
        platform
            .drive(&host, "more", &mut brain2)
            .expect("drive more");

        // The attestation carries the genesis pin + the countersigned checkpoint; a
        // third party holding (attestation + renter pubkey + nonce) re-witnesses it.
        let att = platform.attest(&host).expect("attest");
        assert!(att.genesis.is_some(), "the genesis pin is exposed");
        assert!(
            att.checkpoint.is_some(),
            "the countersigned checkpoint is carried"
        );
        att.verify_for_renter(&renter_pub, &nonce)
            .expect("the renter/third-party anti-rewrite/anti-truncation check passes");

        // A grain with NO renter anchor pinned cannot accept a checkpoint (R1 off).
        let host2 = platform
            .rent(
                "bare.agents.dregg",
                "dga1_bare",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision a bare grain");
        let mut b3 = fs_plan(&[("d.txt", "4")]);
        platform.drive(&host2, "x", &mut b3).expect("drive");
        let cp3 = platform.checkpoint_offer(&host2).unwrap();
        let cs3 = grain_verify::countersign_checkpoint(renter_seed, cp3);
        assert!(matches!(
            platform.submit_checkpoint(&host2, cs3),
            Err(AgentPlatformError::Checkpoint(_))
        ));
    }

    /// **The durable image BINDS the session — both polarities.** After a drive,
    /// the lease's committed heap carries the chain tip / turn count / consumed /
    /// digest and `verify` re-checks them (positive). Tampering any of them in the
    /// durable image — or stamping a digest of a different mind — is caught as
    /// `ImageDiverged` (negative): the checkpoint is a verified binding, not a
    /// stamp nothing reads.
    #[test]
    fn the_durable_image_binds_the_session_and_a_tamper_is_caught() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        let host = platform
            .rent(
                "bound.agents.dregg",
                "dga1_bound",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision");

        // Before any drive the image is genesis (step 0) — verify passes vacuously
        // on the image leg (nothing bound yet), receipts empty.
        platform.verify(&host).expect("a fresh grain verifies");

        let mut brain = fs_plan(&[("a.txt", "1"), ("b.txt", "2")]);
        platform.drive(&host, "write", &mut brain).expect("drive");

        // Positive: the image carries the real binding and verify re-checks it.
        {
            let arc = platform
                .tenants
                .lock()
                .unwrap()
                .get(&host)
                .cloned()
                .unwrap();
            let t = arc.lock().unwrap();
            let report = t.session.report();
            assert!(t.lease.step() > 0, "the cursor advanced");
            assert_eq!(
                t.lease.read_working(WK_NUM_TURNS),
                Some(field_from_u64(report.receipts.len() as u64)),
                "the committed turn count is the session's"
            );
            assert_eq!(
                t.lease.read_working(WK_CHAIN_TIP),
                Some(report.receipts.last().unwrap().receipt_hash().unwrap()),
                "the committed chain tip is the session's"
            );
        }
        platform.verify(&host).expect("the bound image verifies");

        // Negative 1: overwrite the committed chain tip (digest kept honest) —
        // the read-back bites.
        {
            let arc = platform
                .tenants
                .lock()
                .unwrap()
                .get(&host)
                .cloned()
                .unwrap();
            let mut t = arc.lock().unwrap();
            let digest = session_digest(&t.session.report());
            t.lease
                .checkpoint(digest, &[(WK_CHAIN_TIP, [0xEEu8; 32])])
                .expect("tamper the image");
        }
        assert!(
            matches!(
                platform.verify(&host),
                Err(AgentPlatformError::ImageDiverged(_))
            ),
            "a tampered chain tip in the durable image is refused"
        );

        // Heal it, then Negative 2: stamp a digest of a DIFFERENT mind.
        {
            let arc = platform
                .tenants
                .lock()
                .unwrap()
                .get(&host)
                .cloned()
                .unwrap();
            let mut t = arc.lock().unwrap();
            let tenant = &mut *t;
            let report = tenant.session.report();
            let digest = session_digest(&report);
            tenant
                .lease
                .checkpoint(digest, &session_binding(&report))
                .expect("heal the image");
        }
        platform
            .verify(&host)
            .expect("the healed image binds again");
        {
            let arc = platform
                .tenants
                .lock()
                .unwrap()
                .get(&host)
                .cloned()
                .unwrap();
            let mut t = arc.lock().unwrap();
            let tenant = &mut *t;
            let report = tenant.session.report();
            tenant
                .lease
                .checkpoint([0xABu8; 32], &session_binding(&report))
                .expect("stamp a foreign digest");
        }
        assert!(
            matches!(
                platform.verify(&host),
                Err(AgentPlatformError::ImageDiverged(_))
            ),
            "a digest of a different mind is refused"
        );
    }

    /// **R2 — receipts become views over committed kernel turns, both polarities.**
    /// A minted drive links every admitted receipt to a turn the minter committed,
    /// and `verify_r2` passes against the platform-recorded manifest. An UNMINTED
    /// drive fails `verify_r2` (unlinked receipts — the honest default is below
    /// R2). And an executor-style refusal (the minter's host-side caveat biting)
    /// admits NOTHING: no receipt, no budget draw.
    #[test]
    fn r2_minted_drives_verify_and_unminted_or_refused_do_not_inflate() {
        let wd = workdir();
        let platform = AgentPlatform::new();

        // ── minted: every admitted action rides a committed kernel turn ────────
        let minted_host = platform
            .rent(
                "r2.agents.dregg",
                "dga1_r2",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision");
        let mut minter = SyntheticMinter::new();
        let mut brain = fs_plan(&[("m1.txt", "a"), ("m2.txt", "b")]);
        let report = platform
            .drive_minted(&minted_host, "write minted", &mut brain, &mut minter)
            .expect("minted drive");
        assert!(report.admitted > 0, "the minted grain did admitted work");
        let r2 = platform.verify_r2(&minted_host).expect("R2 verifies");
        assert_eq!(
            r2.linked as u64, report.admitted,
            "every admitted receipt is a view over a committed turn"
        );
        // A second minted drive extends the same manifest (it accumulates).
        let mut brain2 = fs_plan(&[("m3.txt", "c")]);
        platform
            .drive_minted(&minted_host, "more", &mut brain2, &mut minter)
            .expect("minted drive 2");
        let r2b = platform.verify_r2(&minted_host).expect("R2 still verifies");
        assert!(r2b.linked > r2.linked, "the manifest accumulated");

        // ── unminted: verify_r2 refuses (below R2 is not laundered as R2) ──────
        let bare_host = platform
            .rent(
                "r2bare.agents.dregg",
                "dga1_r2b",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision");
        let mut brain3 = fs_plan(&[("u1.txt", "x")]);
        platform
            .drive(&bare_host, "write unminted", &mut brain3)
            .expect("drive");
        platform
            .verify(&bare_host)
            .expect("R0 tamper-evidence still holds");
        assert!(
            matches!(
                platform.verify_r2(&bare_host),
                Err(AgentPlatformError::Verify(_))
            ),
            "an unminted grain does not pass R2"
        );

        // ── refusal: the executor-style caveat biting admits NOTHING ───────────
        let refused_host = platform
            .rent(
                "r2ref.agents.dregg",
                "dga1_r2r",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision");
        let mut refusing = SyntheticMinter::refusing_after(1);
        let mut brain4 = fs_plan(&[("r1.txt", "x"), ("r2.txt", "y"), ("r3.txt", "z")]);
        let refused_report = platform
            .drive_minted(&refused_host, "mostly refused", &mut brain4, &mut refusing)
            .expect("the drive itself completes");
        assert_eq!(
            refused_report.admitted, 1,
            "only the pre-refusal action admitted"
        );
        let r2r = platform
            .verify_r2(&refused_host)
            .expect("the admitted turn verifies");
        assert_eq!(r2r.linked, 1, "exactly the committed turn is linked");
    }

    /// **THE SERVED PATH MINTS — R2 through the REAL `grain-turn` minter.** This is
    /// the wiring proof: `drive_serving` (what the served HTTP route `drive_live`
    /// routes through) constructs the platform's genuine `grain-turn`
    /// `ToolGatewayMinter` internally — the caller passes NO minter — and yet every
    /// admitted receipt comes back a VIEW over a committed kernel turn: `verify_r2`
    /// passes and `linked == admitted`. The turns are minted by the executor itself
    /// (not the synthetic seam), so the meter is executor-enforced host-side.
    ///
    /// And the anti-forgery tooth BITES: a receipt whose turn link names a turn that
    /// was never committed (a fabricated manifest) is REFUSED (`R2FabricatedLink`) —
    /// so a forged R2 claim cannot pass, and the honest unminted `drive` is not
    /// laundered as R2 either.
    #[test]
    fn served_default_path_mints_r2_through_real_grain_turn_minter() {
        let wd = workdir();
        let platform = AgentPlatform::new();

        // The served/default path: NO minter is passed — `drive_serving` opens the
        // real grain-turn kernel minter itself (exactly what drive_live does).
        let host = platform
            .rent(
                "served.agents.dregg",
                "dga1_served",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision");
        let mut brain = fs_plan(&[("s1.txt", "hello"), ("s2.txt", "grain")]);
        let report = platform
            .drive_serving(&host, "write served", &mut brain)
            .expect("the served default drive mints");
        assert!(report.admitted > 0, "the served grain did admitted work");

        // Every admitted receipt is a view over a turn the REAL executor committed.
        let r2 = platform
            .verify_r2(&host)
            .expect("the served path verifies at R2");
        assert_eq!(
            r2.linked as u64, report.admitted,
            "every admitted receipt on the served path is a view over a committed kernel turn"
        );

        // FORGED variant: a receipt link naming a turn never committed is refused.
        // The attestation over the real session, checked against a bogus manifest
        // (no such committed turns), must trip the anti-forgery tooth.
        let att = platform.attest(&host).expect("attest the served grain");
        assert!(
            att.verify_r2(&[[0u8; 32]]).is_err(),
            "a forged manifest (turns never committed) fails R2 — a fabricated link is refused"
        );

        // And the unminted standalone `drive` is honestly below R2 (not laundered).
        let bare = platform
            .rent(
                "servedbare.agents.dregg",
                "dga1_servedb",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision");
        let mut brain2 = fs_plan(&[("b1.txt", "x")]);
        platform
            .drive(&bare, "write unminted", &mut brain2)
            .expect("unminted drive");
        assert!(
            matches!(
                platform.verify_r2(&bare),
                Err(AgentPlatformError::Verify(_))
            ),
            "the unminted standalone path does not pass R2"
        );
    }

    /// **THE FEDERATION / LOCAL-SUBMIT LEG — a minted turn LANDS on a real node's
    /// finalized ledger, cross-node-verifiably, and a forged turn is rejected.**
    ///
    /// The served path mints every admitted action onto the grain's
    /// [`node::LocalNode`]: a real node's ledger + finalized receipt log, not
    /// grain-turn's throwaway in-process runtime. This test drives the served path,
    /// then proves:
    ///   1. `verify_landed` confirms every manifest turn is on the node's finalized
    ///      log AND the log light-client-verifies (finalized_len == manifest_len ==
    ///      admitted).
    ///   2. A THIRD PARTY holding only the node's exported receipt chain re-verifies
    ///      it offline (`verify_receipt_chain`) — no trust in this host — and each
    ///      minted turn hash is present.
    ///   3. A second drive ACCUMULATES on the SAME persistent node (the chain grows,
    ///      single-agent, still verifiable).
    ///   4. The node's finalization gate REJECTS a forged/non-linking turn (a replayed
    ///      genesis receipt and a tampered receipt both fail to land).
    #[test]
    fn served_path_lands_minted_turns_on_a_real_node_and_forged_is_rejected() {
        use dregg_turn::verify_receipt_chain;

        let wd = workdir();
        let platform = AgentPlatform::new();
        assert_eq!(
            platform.node_url(),
            None,
            "the default platform submits to the built-in local node"
        );

        let host = platform
            .rent(
                "landed.agents.dregg",
                "dga1_landed",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision");

        let mut brain = fs_plan(&[("n1.txt", "alpha"), ("n2.txt", "beta"), ("n3.txt", "gamma")]);
        let report = platform
            .drive_serving(&host, "write onto the node", &mut brain)
            .expect("the served default drive mints onto the node");
        assert!(report.admitted > 0, "the served grain did admitted work");

        // R2 still holds (receipts are views over committed kernel turns).
        let r2 = platform.verify_r2(&host).expect("R2 verifies");
        assert_eq!(r2.linked as u64, report.admitted);

        // (1) The federation leg: every minted turn LANDED on the node's finalized
        // ledger log, and that log light-client-verifies.
        let landed = platform
            .verify_landed(&host)
            .expect("the minted turns landed on a real node + the chain verifies");
        assert_eq!(
            landed.manifest_len as u64, report.admitted,
            "every admitted turn is on the manifest"
        );
        assert_eq!(
            landed.finalized_len, landed.manifest_len,
            "and every manifest turn is finalized on the node's log"
        );
        assert!(landed.finalized_len > 0, "the node finalized real turns");

        // (2) THIRD-PARTY re-verification: export the node's receipt chain and verify
        // it offline, exactly as a light client would — no trust in this host.
        let (chain, manifest) = {
            let arc = platform
                .tenants
                .lock()
                .unwrap()
                .get(&host)
                .cloned()
                .unwrap();
            let t = arc.lock().unwrap();
            let node = t.node.as_ref().expect("the grain has a live local node");
            (node.chain(), t.committed_turns.clone())
        };
        verify_receipt_chain(&chain).expect("a third party re-verifies the node's finalized chain");
        assert_eq!(
            chain.len(),
            manifest.len(),
            "the node holds exactly the minted turns"
        );
        for turn_hash in &manifest {
            assert!(
                chain.iter().any(|r| &r.turn_hash == turn_hash),
                "each minted turn hash is on the node's finalized chain"
            );
        }

        // (3) A second drive accumulates on the SAME persistent node (a real,
        // growing node ledger for the grain — not a per-drive throwaway).
        let mut brain2 = fs_plan(&[("n4.txt", "delta")]);
        platform
            .drive_serving(&host, "one more", &mut brain2)
            .expect("second minted drive");
        let landed2 = platform
            .verify_landed(&host)
            .expect("still landed + verifies");
        assert!(
            landed2.finalized_len > landed.finalized_len,
            "the node's finalized log grew across drives"
        );

        // (4) The node's finalization gate REJECTS forged/non-linking turns.
        let arc = platform
            .tenants
            .lock()
            .unwrap()
            .get(&host)
            .cloned()
            .unwrap();
        let t = arc.lock().unwrap();
        let node = t.node.as_ref().expect("live node");
        let chain = node.chain();
        assert!(chain.len() >= 2);

        // 4a: replay the genesis receipt on top of the current head — no predecessor,
        // does not extend the head → rejected.
        let replay_genesis = chain[0].clone();
        assert!(
            matches!(node.land(replay_genesis), Err(NodeError::Rejected(_))),
            "a replayed genesis receipt is rejected by the node"
        );

        // 4b: a TAMPERED receipt (mutated turn_hash) copied from the head does not
        // link the head → rejected. The forged turn cannot be laundered onto the node.
        let mut tampered = chain.last().unwrap().clone();
        tampered.turn_hash = [0x99u8; 32];
        assert!(
            matches!(node.land(tampered.clone()), Err(NodeError::Rejected(_))),
            "a tampered receipt is rejected by the node's finalization gate"
        );
        // And the tampered turn is NOT on the finalized log (nothing forged landed).
        assert!(
            !node.contains(&[0x99u8; 32]),
            "the forged turn never landed"
        );

        // The honest chain is still intact + verifiable after the rejected attempts.
        verify_receipt_chain(&node.chain())
            .expect("the node chain is untouched by forgery attempts");
    }

    /// **THE FUSION — the attestation commitment is BOUND INTO the landed R2 turns.**
    /// The served-attested drive mints every action onto the grain's real node AND
    /// witnesses a zkOracle attestation commitment on the same finalized turns. This
    /// proves the wire end-to-end at the platform level:
    ///   1. an attested drive lands its turns AND `verify_landed_attested` confirms the
    ///      landed turns carry the exact commitment (jailed → attested → committed →
    ///      landed → verifiable);
    ///   2. the SAME grain driven with a DIFFERENT expected commitment is REFUSED (a
    ///      forged/wrong-brain binding is distinguishable);
    ///   3. an UNATTESTED grain (plain `drive_serving`) is refused by
    ///      `verify_landed_attested` (its turns carry no commitment) — so the binding is
    ///      load-bearing, not a constant-accept.
    ///
    /// (The commitment here is an opaque 32-byte hash — the platform is crypto-agnostic;
    /// that this hash IS the canonical `ZkOracleAttestation` fingerprint, re-verifiable
    /// against the real attestation, is proven in `deos-hermes`'s crown ledger test.)
    #[test]
    fn served_attested_drive_binds_the_attestation_into_the_landed_turns() {
        let wd = workdir();
        let platform = AgentPlatform::new();

        // A stand-in for `deos_hermes::attestation_commitment(&att)` (a confined,
        // attested brain's zkOracle attestation fingerprint).
        let attestation = [0x5Au8; 32];
        let wrong = [0x5Bu8; 32];

        let host = platform
            .rent(
                "attested.agents.dregg",
                "dga1_attested",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision");

        let mut brain = fs_plan(&[("a.txt", "one"), ("b.txt", "two")]);
        let report = platform
            .drive_serving_attested(&host, "write attested", &mut brain, attestation)
            .expect("the attested served drive mints + lands");
        assert!(report.admitted > 0, "the attested grain did admitted work");

        // (1) The turns landed AND commit to exactly this attestation.
        let landed = platform
            .verify_landed_attested(&host, attestation)
            .expect("the landed turns carry the attestation commitment");
        assert_eq!(landed.finalized_len, landed.manifest_len);
        assert!(landed.finalized_len > 0, "real turns finalized + attested");
        // Plain verify_landed still passes (the R2 + federation legs are untouched).
        platform.verify_landed(&host).expect("still landed");

        // (2) A DIFFERENT (forged) attestation is distinguishable — REFUSED.
        assert!(
            matches!(
                platform.verify_landed_attested(&host, wrong),
                Err(AgentPlatformError::Verify(_))
            ),
            "a forged/wrong-brain binding does not verify against the landed commitment"
        );

        // (3) An UNATTESTED grain's landed turns carry no commitment → refused. The
        // binding is load-bearing: a plain served drive is distinguishable from attested.
        let bare_host = platform
            .rent(
                "bare.agents.dregg",
                "dga1_bare",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision bare");
        let mut bare_brain = fs_plan(&[("c.txt", "three")]);
        platform
            .drive_serving(&bare_host, "write bare", &mut bare_brain)
            .expect("the unattested served drive mints + lands");
        platform
            .verify_landed(&bare_host)
            .expect("the bare grain's turns landed");
        assert!(
            matches!(
                platform.verify_landed_attested(&bare_host, attestation),
                Err(AgentPlatformError::Verify(_))
            ),
            "an unattested grain has no attestation binding → refused (distinguishable)"
        );
    }

    /// **THE RAIL JOIN, END TO END — an enclave-attested session becomes a
    /// light-client-checkable fact, driven by the REAL captured Nitro document.**
    /// The live capture enclave (us-east-1 c5.xlarge, debug) bound
    /// `user_data = [0xAB; 32]`; we bind that SAME commitment as the drive's
    /// attestation commitment, so the finalized ledger's ATTESTATION_SLOT carries
    /// exactly what the quote's `report_data` binds — the honest join, no mock:
    ///   1. drive_serving_attested lands turns witnessing [0xAB; 32], and
    ///      `verify_landed_tee_attested` (light-client chain checks + the REAL
    ///      Nitro COSE/X.509 verify through the registered rail) ACCEPTS with the
    ///      fixture document + its true measurement;
    ///   2. a WRONG pinned measurement is refused (quote for a different binary);
    ///   3. a TAMPERED document byte is refused (vendor signature breaks);
    ///   4. a grain whose LANDED commitment differs from the quote's report_data
    ///      is refused (the slot↔quote binding is load-bearing);
    ///   5. an EMPTY registry refuses even the genuine quote (fail-closed: no
    ///      vendor verifier installed means no TEE fact, ever).
    #[test]
    fn landed_tee_attested_joins_the_real_nitro_quote_to_the_landed_slot() {
        use dregg_cell::predicate::WitnessedPredicateRegistry;
        use dregg_cell::tee_attest::{
            TeeQuoteKind, TeeWitnessedPredicateVerifier, encode_tee_proof, tee_predicate_vk,
        };
        use dregg_tee_verify::{NitroVerifier, verify_nitro_core};

        /// The REAL captured live-enclave attestation document (tee-verify's fixture).
        const REAL_DOC: &[u8] = include_bytes!("../../tee-verify/tests/data/nitro_att.bin");
        // The commitment the capture enclave really bound into the quote.
        let commitment = [0xABu8; 32];
        let (claims, _) = verify_nitro_core(REAL_DOC).expect("the fixture doc verifies");
        let measurement = claims.measurement; // the enclave's true code identity

        // The host-side install (the same wiring deos_hermes::tee_fact performs):
        // the REAL Nitro verifier into dregg-cell's fail-closed seam, registered
        // under tee_predicate_vk. `without_freshness` because the doc is captured —
        // the crypto teeth (COSE sig + chain to the pinned AWS root) are unchanged.
        let mut registry = WitnessedPredicateRegistry::empty();
        registry.register_custom(
            tee_predicate_vk(),
            Arc::new(TeeWitnessedPredicateVerifier::with_verifier(Arc::new(
                NitroVerifier::without_freshness(),
            ))),
        );

        let wd = workdir();
        let platform = AgentPlatform::new();
        let host = platform
            .rent(
                "enclave.agents.dregg",
                "dga1_enclave",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision");
        let mut brain = fs_plan(&[("tee.txt", "attested")]);
        platform
            .drive_serving_attested(&host, "write tee-attested", &mut brain, commitment)
            .expect("the attested served drive mints + lands");

        let proof = encode_tee_proof(TeeQuoteKind::AwsNitro, REAL_DOC);

        // (1) ACCEPT: chain checks + the real vendor crypto bind quote → landed slot.
        let landed = platform
            .verify_landed_tee_attested(&host, &registry, measurement, &proof)
            .expect("the genuine quote proves the landed attestation slot");
        assert!(landed.finalized_len > 0, "real turns finalized");
        // The byte-compare rail (Rail A) still stands unchanged beside the join.
        platform
            .verify_landed_attested(&host, commitment)
            .expect("the plain byte-compare rail is untouched");

        // (2) A quote for a DIFFERENT measured binary is refused.
        assert!(
            matches!(
                platform.verify_landed_tee_attested(&host, &registry, [0u8; 32], &proof),
                Err(AgentPlatformError::Verify(_))
            ),
            "a wrong pinned measurement must be refused"
        );

        // (3) A TAMPERED signed byte breaks the vendor signature → refused.
        let mut tampered = REAL_DOC.to_vec();
        let mid = tampered.len() / 2;
        tampered[mid] ^= 0xFF;
        let tampered_proof = encode_tee_proof(TeeQuoteKind::AwsNitro, &tampered);
        assert!(
            matches!(
                platform.verify_landed_tee_attested(&host, &registry, measurement, &tampered_proof),
                Err(AgentPlatformError::Verify(_))
            ),
            "a tampered quote must be refused"
        );

        // (4) A grain whose LANDED commitment is not the quote's report_data is
        // refused — the quote is bound to one session, not transplantable.
        let other = platform
            .rent(
                "otherbind.agents.dregg",
                "dga1_otherbind",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision other");
        let mut other_brain = fs_plan(&[("o.txt", "other")]);
        platform
            .drive_serving_attested(&other, "write other-bound", &mut other_brain, [0x11u8; 32])
            .expect("the other attested drive mints + lands");
        assert!(
            matches!(
                platform.verify_landed_tee_attested(&other, &registry, measurement, &proof),
                Err(AgentPlatformError::Verify(_))
            ),
            "a landed commitment the quote did not bind must be refused"
        );

        // (5) FAIL-CLOSED: with no verifier registered, even the genuine quote is
        // refused (KindNotRegistered — the rail cannot be talked into accepting).
        let empty = WitnessedPredicateRegistry::empty();
        assert!(
            matches!(
                platform.verify_landed_tee_attested(&host, &empty, measurement, &proof),
                Err(AgentPlatformError::Verify(_))
            ),
            "an empty registry must refuse (fail-closed)"
        );
    }

    /// **PHASE 2 — A GRAIN COLD-WAKES FROM ITS LEASE HEAP ALONE, both polarities.**
    /// A minted drive persists the FULL resumable carrier into `EXEC_COLL` (secret +
    /// consumed + the whole report + the R2 manifest). We DROP the in-RAM session
    /// (overwrite it with a fresh empty one — a different signer, zero receipts, zero
    /// consumed) AND clear the committed-turn manifest, then `wake_from_lease` rebuilds
    /// BOTH from the heap: the reconstructed session re-witnesses at R0 AND R2 and
    /// reproduces the original signer / consumed / tip / receipt count — with no
    /// reliance on the lost session or any filesystem store. A TRUNCATED carrier
    /// (length past the data) and a TAMPERED data slot are each REFUSED fail-closed by
    /// the root tooth.
    #[test]
    fn a_grain_cold_wakes_from_its_lease_heap_and_tamper_is_refused() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        let host = platform
            .rent(
                "cold.agents.dregg",
                "dga1_cold",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision");

        // Drive a MINTED grain so the receipts carry turn links (R2 is exercised).
        let mut minter = SyntheticMinter::new();
        let mut brain = fs_plan(&[("a.txt", "1"), ("b.txt", "2")]);
        platform
            .drive_minted(&host, "write", &mut brain, &mut minter)
            .expect("minted drive");

        // Snapshot the ORIGINAL truths before we lose the session.
        let arc = || {
            platform
                .tenants
                .lock()
                .unwrap()
                .get(&host)
                .cloned()
                .unwrap()
        };
        let (orig_signer, orig_consumed, orig_tip, orig_len, orig_turns, orig_goals) = {
            let t = arc();
            let t = t.lock().unwrap();
            let r = t.session.report();
            (
                r.signer,
                r.consumed,
                r.tip(),
                r.receipts.len(),
                t.committed_turns.clone(),
                t.session.goal_count(),
            )
        };
        assert!(
            orig_len >= 2 && orig_consumed > 0,
            "the grain did real work"
        );
        assert!(!orig_turns.is_empty(), "the minted drive recorded turns");
        assert!(
            orig_goals >= 1,
            "the drive recorded a goal transcript to restore"
        );

        // DROP the in-RAM session: overwrite with a FRESH empty one (a DIFFERENT
        // signer, no receipts, zero consumed) and clear the manifest — the wake must
        // rebuild BOTH from the heap, not read them off the retained session.
        {
            let t = arc();
            let mut t = t.lock().unwrap();
            let bundle = parse_caps_confined(
                "fs",
                "dga1_cold",
                10_000,
                wd.to_str().unwrap(),
                Confinement::Hosted,
            )
            .unwrap();
            t.session = Session::open("dga1_cold", bundle.spec).unwrap();
            t.committed_turns.clear();
            assert_ne!(
                t.session.report().signer,
                orig_signer,
                "the replacement session has a different signer (the original is gone)"
            );
            assert_eq!(t.session.consumed(), 0, "the replacement has a fresh meter");
        }

        // COLD WAKE from the heap ALONE.
        platform
            .wake_from_lease(&host)
            .expect("cold wake rebuilds the session from EXEC_COLL");

        // The reconstruction re-witnesses at R0 AND R2 and matches the original.
        platform
            .verify(&host)
            .expect("the reconstructed session re-witnesses (chain + image bind)");
        platform
            .verify_r2(&host)
            .expect("the reconstructed session re-witnesses at R2");
        {
            let t = arc();
            let t = t.lock().unwrap();
            let r = t.session.report();
            assert_eq!(
                r.signer, orig_signer,
                "the resumed chain keeps the SAME signer"
            );
            assert_eq!(r.consumed, orig_consumed, "consumed restored from the heap");
            assert_eq!(r.tip(), orig_tip, "the chain tip is the original");
            assert_eq!(r.receipts.len(), orig_len, "every receipt was restored");
            assert_eq!(
                t.committed_turns, orig_turns,
                "the R2 committed-turn manifest was restored from the heap"
            );
            assert_eq!(
                t.session.goal_count(),
                orig_goals,
                "the goal transcript (history) was restored from the heap"
            );
        }

        // NEGATIVE (truncation): a length past the written data slots is refused; then
        // heal the length and confirm the wake works again.
        let honest_len = {
            let t = arc();
            let t = t.lock().unwrap();
            t.lease.read_working(WK_CARRIER_LEN).unwrap()
        };
        {
            let t = arc();
            let mut t = t.lock().unwrap();
            let digest = session_digest(&t.session.report());
            t.lease
                .checkpoint(digest, &[(WK_CARRIER_LEN, field_from_u64(999_999))])
                .expect("bump the carrier length past its data");
        }
        assert!(
            matches!(
                platform.wake_from_lease(&host),
                Err(AgentPlatformError::CarrierRefused(_))
            ),
            "a truncated carrier (length past the data) is refused"
        );
        {
            let t = arc();
            let mut t = t.lock().unwrap();
            let digest = session_digest(&t.session.report());
            t.lease
                .checkpoint(digest, &[(WK_CARRIER_LEN, honest_len)])
                .expect("heal the carrier length");
        }
        platform
            .wake_from_lease(&host)
            .expect("the healed carrier wakes again");

        // NEGATIVE (tamper): flipping one byte in a data slot re-hashes to a different
        // root and the wake refuses by the root tooth.
        {
            let t = arc();
            let mut t = t.lock().unwrap();
            let mut slot = t.lease.read_working(WK_CARRIER_DATA_BASE).unwrap();
            slot[0] ^= 0xFF;
            let digest = session_digest(&t.session.report());
            t.lease
                .checkpoint(digest, &[(WK_CARRIER_DATA_BASE, slot)])
                .expect("tamper a carrier data slot");
        }
        assert!(
            matches!(
                platform.wake_from_lease(&host),
                Err(AgentPlatformError::CarrierRefused(_))
            ),
            "a tampered carrier data slot is refused by the root tooth"
        );
    }

    /// A rented grain thinks LIVE: with `--features live-brain` and a provider key
    /// in env, drive_live has a real model reason→act→observe over the grain's
    /// granted tools, each tool-call crossing the cap gate. Ignored (needs a key +
    /// network); run on demand:
    /// `DREGG_LLM_API_KEY=… cargo test -p agent-platform --features live-brain -- --ignored`
    #[cfg(feature = "live-brain")]
    #[test]
    #[ignore]
    fn a_rented_grain_thinks_live() {
        let wd = workdir();
        let platform = AgentPlatform::new();
        let host = platform
            .rent(
                "bob.agents.dregg",
                "dga1_bob",
                "fs",
                100_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision the grain");
        let report = platform
            .drive_live(
                &host,
                "Write a file called hello.txt containing the word dregg, then finish.",
                &["fs_write".to_string()],
            )
            .expect("the live model drives the grain");
        assert!(
            report.admitted > 0,
            "the live model took an admitted action"
        );
        platform
            .verify(&host)
            .expect("the live session re-witnesses");
    }

    /// **ROUTE (ii) — the grain HOST installs its executor signing key, so every
    /// grain turn is signed + FORGE-ADMISSIBLE.** A platform opened WITH a host
    /// executor signing seed drives one served (node-minted) grain turn; the
    /// committed receipt on the node's finalized log is (a) `Finality::Final`, (b)
    /// carries an `executor_signature`, and (c) VERIFIES against the host's executor
    /// pubkey via `verify_receipt_signature_with_keys` — EXACTLY the check the forge
    /// gate (`RequiredCheck::CommittedReceipt`) and any auditor run.
    ///
    /// TWO POLES: with the correct host pubkey the turn verifies; with a DIFFERENT
    /// key it is REFUSED, and the DEFAULT no-seed platform mints UNSIGNED receipts
    /// (`executor_signature == None`, byte-unchanged) that the same check refuses.
    #[test]
    fn a_hosted_grain_turn_is_executor_signed_and_forge_admissible() {
        use dregg_turn::{Finality, verify_receipt_signature_with_keys};

        let host_seed = [0x5cu8; 32];
        let host_pubkey = dregg_sdk::executor_pubkey_from_seed(&host_seed);

        // --- SIGNED pole: platform WITH the host executor signing seed. ---
        let wd = workdir();
        let platform = AgentPlatform::new().with_executor_signing_key(host_seed);
        assert_eq!(
            platform.executor_pubkey(),
            Some(host_pubkey),
            "the platform exposes the host executor pubkey an auditor pins"
        );

        let host = platform
            .rent(
                "signed.agents.dregg",
                "dga1_signer",
                "fs",
                10_000,
                wd.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision the grain");

        // Served drive → mints genuine kernel turns onto the grain's local node.
        let mut brain = fs_plan(&[("notes.txt", "hello"), ("plan.txt", "world")]);
        let report = platform
            .drive_serving(&host, "write my notes", &mut brain)
            .expect("drive the served grain");
        assert!(report.admitted > 0, "the grain minted admitted work");

        // The minted turns landed on the node's finalized, light-client chain.
        let landed = platform
            .verify_landed(&host)
            .expect("the grain turns landed on the node");
        assert!(landed.finalized_len > 0, "at least one grain turn landed");

        // Export the finalized receipts off the grain's node and inspect them.
        let chain = {
            let arc = platform
                .tenants
                .lock()
                .unwrap()
                .get(&host)
                .cloned()
                .unwrap();
            let guard = arc.lock().unwrap();
            guard
                .node
                .as_ref()
                .expect("node brought up on the served drive")
                .chain()
        };
        assert!(
            !chain.is_empty(),
            "the finalized log holds committed grain turns"
        );
        for receipt in &chain {
            // (a) Final, (b) SIGNED, (c) forge-admissible against the host pubkey.
            assert_eq!(receipt.finality, Finality::Final, "grain turn is Final");
            assert!(
                receipt.executor_signature.is_some(),
                "route (ii): the host-signed grain turn carries an executor signature"
            );
            verify_receipt_signature_with_keys(receipt, &[host_pubkey]).expect(
                "the grain turn verifies against the host executor pubkey (forge-admissible)",
            );
            // POLE 1 — a DIFFERENT executor key is REFUSED.
            assert!(
                verify_receipt_signature_with_keys(receipt, &[[0x99u8; 32]]).is_err(),
                "a wrong executor key does not admit the grain turn"
            );
        }

        // --- UNSIGNED pole: the DEFAULT no-seed platform mints UNSIGNED receipts. ---
        let wd2 = workdir();
        let bare = AgentPlatform::new();
        assert_eq!(
            bare.executor_pubkey(),
            None,
            "no seed installed → no executor pubkey"
        );
        let bare_host = bare
            .rent(
                "unsigned.agents.dregg",
                "dga1_bare",
                "fs",
                10_000,
                wd2.to_str().unwrap(),
                terms(),
                None,
            )
            .expect("provision the bare grain");
        let mut brain2 = fs_plan(&[("notes.txt", "hi")]);
        bare.drive_serving(&bare_host, "write", &mut brain2)
            .expect("drive the bare grain");
        let bare_chain = {
            let arc = bare
                .tenants
                .lock()
                .unwrap()
                .get(&bare_host)
                .cloned()
                .unwrap();
            let guard = arc.lock().unwrap();
            guard.node.as_ref().expect("bare node up").chain()
        };
        assert!(
            !bare_chain.is_empty(),
            "the bare grain also committed turns"
        );
        for receipt in &bare_chain {
            // POLE 2 — the default path is byte-unchanged: UNSIGNED, forge check REFUSES.
            assert!(
                receipt.executor_signature.is_none(),
                "default (no-seed) grain turns stay UNSIGNED — byte-unchanged"
            );
            assert!(
                verify_receipt_signature_with_keys(receipt, &[host_pubkey]).is_err(),
                "an unsigned grain turn is refused by the forge check (not forge-admissible)"
            );
        }
    }
}
