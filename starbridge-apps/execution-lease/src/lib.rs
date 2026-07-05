//! # starbridge-execution-lease — durable execution as a PAYABLE RESOURCE.
//!
//! The "first primary resource" of the agent service economy is **durable
//! container execution for agents** — a fly.io-lite / cloudflare-lite provider
//! that LEASES durable execution slots to agents, metered and paid through the
//! dregg value layer. This crate models that provider on dregg-native
//! primitives, with NO new kernel effect:
//!
//!   * **The provider** offers durable execution slots from a factory
//!     ([`lease_factory_descriptor`]). Each slot, leased, becomes a **lease cell**.
//!   * **The lease** is a cap-bounded cell whose committed HEAP holds the agent's
//!     **durable execution image** ([`EXEC_COLL`]: a checkpoint step + a state
//!     digest + arbitrary working-memory keys). Because the heap is folded into
//!     the cell's state commitment ([`dregg_cell::state::compute_heap_root`]), the
//!     durable state SURVIVES, is PASSABLE (a cell + its heap is a portable image),
//!     and is WITNESSED (a light client sees the checkpoint cursor move). This is
//!     what "durable execution" concretely IS here: a committed umem cell-heap
//!     checkpoint, not a real container runtime — see the honest-gaps note below.
//!   * **The meter** is a [`dregg_cell::obligation_standing`] StandingObligation:
//!     the lease OWES `rent_per_period` to the provider every `period` blocks. Each
//!     period is discharged ONCE, on-schedule, for the exact rent — the recurring
//!     forge-detectors (no early/double/over/under discharge, no silent skip) bite.
//!   * **The payment** is a [`dregg_app_framework::Payable`] `pay` desugaring to ONE
//!     conserving kernel [`Effect::Transfer`] (lease cell → provider): per-asset
//!     Σδ=0 holds across the lease, so renting durable execution moves real value.
//!   * **The delivery** is a checkpoint advance: the lease's durable cursor
//!     ([`STEP_SLOT`] + [`STATE_DIGEST_SLOT`], mirrored into the heap) moves
//!     forward — the executor re-enforces [`StateConstraint::Monotonic`] on the
//!     step, so a rewind / forge of the durable cursor is a REAL refusal.
//!   * **The lapse** is non-payment: when the schedule audit
//!     ([`dregg_cell::obligation_standing::ObligationState::audit`]) finds a period
//!     went undischarged, the lease LAPSES ([`LAPSED_SLOT`]) and further delivery is
//!     refused (the provider reclaims the slot — the live-state precondition on
//!     [`fire_advance`] goes dark).
//!
//! ## The four axes (the unified starbridge-app template)
//!
//!   * the verified core — the [`FactoryDescriptor`] + the [`lease_cell_program`]
//!     (this file): the durable-cursor + rent invariants the executor re-enforces;
//!   * the SERVICE-CELL `invoke()` front door ([`service`]): a typed
//!     [`InterfaceDescriptor`] (`open` / `pay` / `advance` / `status`);
//!   * the deos-view CARD ([`card`]): the lease dashboard as a `deos.ui.*` tree;
//!   * the deos surface — the composed [`DeosApp`] ([`lease_app`] / [`register_deos`]).
//!
//! ## Honest gaps (what this is, and is not)
//!
//! This is a faithful MODEL of a durable-execution provider on the dregg value
//! layer — NOT a real container runtime. "Durable execution" here is the committed
//! umem cell-heap checkpoint image (a step cursor + a state digest + working
//! memory), advanced by the provider; it does not run agent code. The PAYMENT (a
//! conserving `Transfer`) and the durable-cursor forward-only tooth
//! (`Monotonic(STEP_SLOT)`) are REAL verified turns the executor enforces. The
//! METER advance (the obligation discharge) and the heap-checkpoint mirror are
//! executor-side ledger steps — the same named in-circuit seam StandingObligation
//! describes (a `DischargeObligation` effect binding "due ∧ not-discharged ⟹
//! discharged ∧ cursor advanced" into the EffectVM so a light client, not just a
//! re-executing validator, witnesses the meter). Welding a real WASM/OCI execution
//! engine to the checkpoint image is the fly.io-lite production lane this models.

#![forbid(unsafe_code)]

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellAffordance, CellId, CellMode,
    CellProgram, ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect, EmbeddedExecutor,
    Event, FactoryDescriptor, FireExecuteError, GatedAffordance, InspectorDescriptor,
    InvokeAuthority, InvokeRefused, Payable, StarbridgeAppContext, StateConstraint, TransitionCase,
    TransitionGuard, Turn, TurnReceipt, canonical_program_vk, hex_encode_32, symbol,
};
pub use dregg_app_framework::{FieldElement, field_from_bytes, field_from_u64};

use dregg_cell::Cell;
use dregg_cell::obligation_standing::{
    Discharge, ObligationError, ObligationState, ObligationTerms, decode_i64, discharge,
    encode_i64, open_obligation,
};

/// The deos-view CARD: the lease dashboard as a renderer-independent view-tree.
pub mod card;
/// The CELLS-AS-SERVICE-OBJECTS face: a typed `InterfaceDescriptor` + `invoke()`
/// dispatch over `open` / `pay` / `advance` / `status`.
pub mod service;

// =============================================================================
// Slot layout (the lease cell) — the program-enforced scalars
// =============================================================================

/// Slot 0 — `step`. The durable checkpoint cursor: how many checkpoints the
/// agent's execution has advanced. `Monotonic` (a checkpoint can never rewind —
/// durable execution only moves forward). Mirrored into [`EXEC_COLL`]/[`KEY_STEP`].
pub const STEP_SLOT: u8 = 0;
/// Slot 1 — `state_digest`. A 32-byte digest of the agent's current execution
/// image (the checkpointed state the provider holds). Re-bound each advance.
pub const STATE_DIGEST_SLOT: u8 = 1;
/// Slot 2 — `lapsed`. `0` = live, `1` = lapsed (non-payment). `Monotonic` (once
/// lapsed, stays lapsed — the provider has reclaimed the slot).
pub const LAPSED_SLOT: u8 = 2;
/// Slot 3 — `periods_paid`. Count of rent periods metered+paid. `Monotonic`.
pub const PERIODS_PAID_SLOT: u8 = 3;
/// Slot 4 — `rent_per_period`. The metered price of one period. `WriteOnce`
/// (sealed at lease open — the provider cannot silently re-price a live lease).
pub const RENT_SLOT: u8 = 4;
/// Slot 5 — `period`. The lease period length in blocks. `WriteOnce`.
pub const PERIOD_SLOT: u8 = 5;
/// Slot 6 — `provider_tag`. The provider/beneficiary cell tag. `WriteOnce`.
pub const PROVIDER_SLOT: u8 = 6;

// =============================================================================
// Durable execution image — the committed umem cell-heap checkpoint
// =============================================================================

/// Reserved heap collection id for the lease's **durable execution image** — the
/// umem cell-heap the agent's execution checkpoints into. Lives inside the cell's
/// committed heap (folded into the canonical state commitment via
/// [`dregg_cell::state::compute_heap_root`]), so the durable state survives, is
/// passable, and is witnessed. Chosen high to avoid colliding with application
/// heap collections (the same spirit as
/// [`dregg_cell::obligation_standing::OBLIGATION_COLL`]).
pub const EXEC_COLL: u32 = 0x0000_E3EC_u32; // "EXEC"

/// Heap key (in [`EXEC_COLL`]) — the durable checkpoint step (mirror of
/// [`STEP_SLOT`], canonical little-endian `i64`).
pub const KEY_STEP: u32 = 0;
/// Heap key (in [`EXEC_COLL`]) — the durable state digest (mirror of
/// [`STATE_DIGEST_SLOT`]).
pub const KEY_DIGEST: u32 = 1;
/// The first heap key (in [`EXEC_COLL`]) available for the agent's working
/// memory. Keys `>= WORKING_BASE` are the passable, witnessed scratch the running
/// execution writes into its durable image.
pub const WORKING_BASE: u32 = 16;

// =============================================================================
// Factory configuration
// =============================================================================

/// The factory VK the provider publishes for execution-lease cells.
pub const LEASE_FACTORY_VK: [u8; 32] = *b"starbridge-execution-lease-fact!";

/// Default per-epoch slot-creation budget (how many leases the provider issues).
pub const DEFAULT_CREATION_BUDGET: u64 = 256;

/// Default demo rent per period (in the lease's asset).
pub const DEFAULT_RENT_PER_PERIOD: u64 = 100;
/// Default demo period length (blocks between rent charges).
pub const DEFAULT_PERIOD: i64 = 50;
/// Default demo first-due block (period 0 falls due here).
pub const DEFAULT_START: i64 = 1000;

// =============================================================================
// Lease terms
// =============================================================================

/// The sealed terms of a durable-execution lease: WHO provides, WHO leases (and
/// pays), in WHAT asset, the rent per period, the period length, the first due
/// block, and an optional bounded number of periods (`0` = open-ended). The lease
/// cell is BOTH the rent obligor and the payer (it holds the prepaid balance the
/// rent is drawn from) and the holder of the durable execution image.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeaseTerms {
    /// The provider cell — the beneficiary of the rent (and the slot owner).
    pub provider: CellId,
    /// The lease cell — the agent's durable-execution slot: rent obligor, payer,
    /// and holder of the committed execution image.
    pub lease: CellId,
    /// The asset rent is denominated in (the lease cell's `token_id`).
    pub asset: CellId,
    /// Rent owed per period. Must be `> 0`.
    pub rent_per_period: u64,
    /// Period length in blocks. Must be `> 0`.
    pub period: i64,
    /// The block at which period `0` (the first rent) falls due.
    pub start: i64,
    /// Bounded number of periods, or `0` for an open-ended lease.
    pub max_periods: i64,
}

impl LeaseTerms {
    /// A lease: `lease` rents a durable-execution slot from `provider`, owing
    /// `rent_per_period` of `asset` every `period` blocks from `start`, for
    /// `max_periods` periods (`0` = open-ended).
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        provider: CellId,
        lease: CellId,
        asset: CellId,
        rent_per_period: u64,
        period: i64,
        start: i64,
        max_periods: i64,
    ) -> Self {
        LeaseTerms {
            provider,
            lease,
            asset,
            rent_per_period,
            period,
            start,
            max_periods,
        }
    }

    /// The rent schedule as a [`StandingObligation`](dregg_cell::obligation_standing)
    /// `ObligationTerms`: the lease (obligor) owes the provider (beneficiary) the
    /// rent each period. THIS is the meter — its committed cursor + forge-detectors
    /// bind the per-period charge.
    pub fn obligation(&self) -> ObligationTerms {
        ObligationTerms::new(
            self.lease,
            self.provider,
            self.asset,
            self.rent_per_period as i64,
            self.period,
            self.start,
            self.max_periods,
        )
    }

    /// Whether the terms are well-formed (positive rent/period, sound schedule).
    pub fn is_well_formed(&self) -> bool {
        self.rent_per_period > 0 && self.obligation().is_well_formed()
    }
}

/// Why a lease operation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeaseError {
    /// The terms are not well-formed (non-positive rent/period, etc).
    IllFormedTerms,
    /// The lease has LAPSED (non-payment): the provider has reclaimed the slot, so
    /// durable execution cannot advance.
    Lapsed,
    /// A metering (rent-discharge) step was refused — the underlying recurring
    /// obligation forge-detector (early / double / over / under / skip).
    Meter(ObligationError),
}

impl std::fmt::Display for LeaseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LeaseError::IllFormedTerms => write!(f, "lease terms are not well-formed"),
            LeaseError::Lapsed => write!(f, "lease has lapsed (non-payment): slot reclaimed"),
            LeaseError::Meter(e) => write!(f, "metering refused: {e}"),
        }
    }
}

impl std::error::Error for LeaseError {}

impl From<ObligationError> for LeaseError {
    fn from(e: ObligationError) -> Self {
        LeaseError::Meter(e)
    }
}

// =============================================================================
// Field helpers
// =============================================================================

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse
/// of [`field_from_u64`]).
pub fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// A field tag for a cell id (its raw 32 bytes) — used to pin the provider into
/// [`PROVIDER_SLOT`].
pub fn cell_tag(cell: CellId) -> FieldElement {
    let mut f = [0u8; 32];
    f.copy_from_slice(cell.as_bytes());
    f
}

// =============================================================================
// The verified core — CellProgram + FactoryDescriptor
// =============================================================================

/// The **life-of-lease invariants** the executor re-enforces on every touching
/// turn:
///
///   * `WriteOnce` on `RENT` / `PERIOD` / `PROVIDER` — the lease economics are
///     sealed at open; a live lease cannot be silently re-priced or re-pointed;
///   * `Monotonic` on `STEP` — the durable checkpoint cursor only moves FORWARD
///     (a rewind / forge of the durable execution image is refused);
///   * `Monotonic` on `LAPSED` — once lapsed (non-payment), stays lapsed;
///   * `Monotonic` on `PERIODS_PAID` — the metered-period count never rewinds.
pub fn lease_invariants() -> Vec<StateConstraint> {
    vec![
        StateConstraint::WriteOnce { index: RENT_SLOT },
        StateConstraint::WriteOnce { index: PERIOD_SLOT },
        StateConstraint::WriteOnce {
            index: PROVIDER_SLOT,
        },
        StateConstraint::Monotonic { index: STEP_SLOT },
        StateConstraint::Monotonic { index: LAPSED_SLOT },
        StateConstraint::Monotonic {
            index: PERIODS_PAID_SLOT,
        },
    ]
}

/// The lease cell program: an `Always` case carrying [`lease_invariants`] (the
/// economics + cursor invariants re-enforced on EVERY touching turn — including the
/// durable-cursor forward-only `Monotonic(STEP)` tooth on `advance`, and the
/// no-op-admitting monotonicity on the conserving rent `pay` Transfer). A pure
/// invariants program (no method-dispatch case), so every operation the lease
/// supports — `open` / `pay` / `advance` / `lapse` — is admitted as long as the
/// invariants hold.
pub fn lease_cell_program() -> CellProgram {
    CellProgram::Cases(vec![TransitionCase {
        guard: TransitionGuard::Always,
        constraints: lease_invariants(),
    }])
}

/// The life-of-lease invariants as a flat `Predicate` program — installed on a
/// seeded lease cell so the deos fires re-enforce them.
pub fn lease_invariants_program() -> CellProgram {
    CellProgram::Predicate(lease_invariants())
}

/// Canonical child program VK for lease cells.
pub fn lease_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&lease_cell_program())
}

/// The provider's factory descriptor for minting durable-execution lease cells.
pub fn lease_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: LEASE_FACTORY_VK,
        child_program_vk: Some(lease_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(lease_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![],
        state_constraints: lease_invariants(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![lease_factory_descriptor()]
}

// =============================================================================
// Lease core — pure operations over a Cell (unit-testable, executor-seedable)
// =============================================================================

/// **Open a durable-execution lease** on a cell: seal the rent obligation (the
/// meter), pin the `WriteOnce` economics, and initialize the durable execution
/// image (step 0 + a genesis state digest, in both the scalar slots and the
/// committed [`EXEC_COLL`] heap). After this the cell's commitment binds the
/// schedule AND the genesis checkpoint; nothing is paid and no execution has
/// advanced yet. Rejects ill-formed terms.
pub fn open_lease(
    cell: &mut Cell,
    terms: &LeaseTerms,
    genesis_digest: FieldElement,
) -> Result<(), LeaseError> {
    if !terms.is_well_formed() {
        return Err(LeaseError::IllFormedTerms);
    }
    // The meter: seal the rent StandingObligation into the cell's heap.
    open_obligation(cell, &terms.obligation()).map_err(LeaseError::Meter)?;

    let st = &mut cell.state;
    // The program-enforced economics + cursors.
    st.set_field(STEP_SLOT as usize, field_from_u64(0));
    st.set_field(STATE_DIGEST_SLOT as usize, genesis_digest);
    st.set_field(LAPSED_SLOT as usize, field_from_u64(0));
    st.set_field(PERIODS_PAID_SLOT as usize, field_from_u64(0));
    st.set_field(RENT_SLOT as usize, field_from_u64(terms.rent_per_period));
    st.set_field(PERIOD_SLOT as usize, field_from_u64(terms.period as u64));
    st.set_field(PROVIDER_SLOT as usize, cell_tag(terms.provider));
    // The durable execution image (umem heap): genesis checkpoint.
    st.set_heap(EXEC_COLL, KEY_STEP, encode_i64(0));
    st.set_heap(EXEC_COLL, KEY_DIGEST, genesis_digest);
    Ok(())
}

/// **Open ONLY the durable execution image** on a cell — the [`EXEC_COLL`] genesis
/// checkpoint (the [`STEP_SLOT`]/[`STATE_DIGEST_SLOT`] scalars + their committed
/// heap mirror) and the live [`LAPSED_SLOT`] latch — WITHOUT the rent
/// [`open_obligation`] meter and WITHOUT the economic slots
/// ([`RENT_SLOT`]/[`PERIOD_SLOT`]/[`PROVIDER_SLOT`]/[`PERIODS_PAID_SLOT`]).
///
/// This is the durable-image half of [`open_lease`] with the obligation meter
/// SUBTRACTED, for a lease whose meter is the FUSED
/// [`dregg_cell::prepaid_lease`] capacity (which carries its OWN sealed schedule +
/// reserve in the disjoint `PREPAID_LEASE_COLL`, so there is no separate
/// obligation cursor and no separately-sealed economics to keep in sync). After
/// this the cell binds the genesis checkpoint and reads live (not lapsed);
/// [`advance_checkpoint`] / [`mark_lapsed`] then drive it exactly as for an
/// obligation lease. Infallible — there is no schedule to well-form-check here.
pub fn open_durable_image(cell: &mut Cell, genesis_digest: FieldElement) {
    let st = &mut cell.state;
    st.set_field(STEP_SLOT as usize, field_from_u64(0));
    st.set_field(STATE_DIGEST_SLOT as usize, genesis_digest);
    st.set_field(LAPSED_SLOT as usize, field_from_u64(0));
    st.set_heap(EXEC_COLL, KEY_STEP, encode_i64(0));
    st.set_heap(EXEC_COLL, KEY_DIGEST, genesis_digest);
}

/// **Latch the lease LAPSED** (the provider reclaims the slot): set
/// [`LAPSED_SLOT`]. Idempotent — once lapsed, stays lapsed (the
/// `Monotonic(LAPSED_SLOT)` tooth). For a meter that audits its OWN schedule (the
/// fused prepaid meter) and needs to mirror the lapse into the durable-image
/// latch so [`is_lapsed`] / [`advance_checkpoint`] refuse further delivery, the
/// same way [`lapse_if_behind`] does for an obligation lease.
pub fn mark_lapsed(cell: &mut Cell) {
    cell.state
        .set_field(LAPSED_SLOT as usize, field_from_u64(1));
}

/// **Meter one rent period** on the lease cell: discharge the current period of
/// the rent obligation (the recurring forge-detectors bite — one-shot per period,
/// the rent obligation (the recurring forge-detectors bite — one-shot per period,
/// on-schedule, exactly the sealed rent), and bump [`PERIODS_PAID_SLOT`]. Returns
/// the rent amount that the PAYMENT (a separate conserving `Transfer`, see
/// [`pay_rent`]) must move from the lease to the provider.
///
/// This is the executor-side meter advance (the committed cursor moves — a light
/// client sees the period discharged). It does NOT itself move value; pairing it
/// with [`pay_rent`] is the metered-and-paid period.
pub fn meter_period(
    cell: &mut Cell,
    terms: &LeaseTerms,
    period_index: i64,
    clock: i64,
) -> Result<u64, LeaseError> {
    if is_lapsed(cell) {
        return Err(LeaseError::Lapsed);
    }
    let step = Discharge {
        period_index,
        amount: terms.rent_per_period as i64,
        clock,
    };
    let moved = discharge(cell, &terms.obligation(), &step).map_err(LeaseError::Meter)?;
    let paid = field_to_u64(cell.state.get_field(PERIODS_PAID_SLOT as usize).unwrap());
    cell.state
        .set_field(PERIODS_PAID_SLOT as usize, field_from_u64(paid + 1));
    Ok(moved as u64)
}

/// **Advance the durable execution image** (the provider delivers): move the
/// checkpoint cursor forward by one and re-bind the state digest, in BOTH the
/// scalar slots and the committed [`EXEC_COLL`] heap, and write any `working`
/// memory keys the running execution produced into the durable image. Refuses on a
/// lapsed lease (the slot has been reclaimed). Returns the new step.
///
/// This is the pure (unit-test / seed) form; the real executor-enforced delivery
/// is [`fire_advance`] (a verified turn the `Monotonic(STEP)` tooth bites a rewind
/// on), which then mirrors the heap via [`mirror_checkpoint`].
pub fn advance_checkpoint(
    cell: &mut Cell,
    new_digest: FieldElement,
    working: &[(u32, FieldElement)],
) -> Result<u64, LeaseError> {
    if is_lapsed(cell) {
        return Err(LeaseError::Lapsed);
    }
    let step = checkpoint_step(cell) + 1;
    let st = &mut cell.state;
    st.set_field(STEP_SLOT as usize, field_from_u64(step));
    st.set_field(STATE_DIGEST_SLOT as usize, new_digest);
    st.set_heap(EXEC_COLL, KEY_STEP, encode_i64(step as i64));
    st.set_heap(EXEC_COLL, KEY_DIGEST, new_digest);
    for (key, value) in working {
        debug_assert!(
            *key >= WORKING_BASE,
            "working memory uses keys >= WORKING_BASE"
        );
        st.set_heap(EXEC_COLL, *key, *value);
    }
    Ok(step)
}

/// **Mirror the durable execution image into the committed heap** after a verified
/// [`fire_advance`] turn moved the scalar [`STEP_SLOT`]/[`STATE_DIGEST_SLOT`].
/// Keeps the umem checkpoint heap (the passable, witnessed durable store) in step
/// with the executor-enforced cursor, and writes the running execution's `working`
/// memory.
pub fn mirror_checkpoint(cell: &mut Cell, working: &[(u32, FieldElement)]) {
    let step = checkpoint_step(cell);
    let digest = *cell.state.get_field(STATE_DIGEST_SLOT as usize).unwrap();
    let st = &mut cell.state;
    st.set_heap(EXEC_COLL, KEY_STEP, encode_i64(step as i64));
    st.set_heap(EXEC_COLL, KEY_DIGEST, digest);
    for (key, value) in working {
        st.set_heap(EXEC_COLL, *key, *value);
    }
}

/// **Lapse the lease if behind schedule** (non-payment). Audit the rent schedule
/// at `clock`: if the committed discharged-count lags what the schedule requires
/// (a period went unpaid), set [`LAPSED_SLOT`] and return `true` (the provider
/// reclaims the slot). If the lease is paid up, leave it live and return `false`.
pub fn lapse_if_behind(
    cell: &mut Cell,
    terms: &LeaseTerms,
    clock: i64,
) -> Result<bool, LeaseError> {
    if is_lapsed(cell) {
        return Ok(true);
    }
    let view = ObligationState::read(cell).map_err(LeaseError::Meter)?;
    match view.audit(&terms.obligation(), clock) {
        Ok(_) => Ok(false),
        Err(ObligationError::BehindSchedule { .. }) => {
            cell.state
                .set_field(LAPSED_SLOT as usize, field_from_u64(1));
            Ok(true)
        }
        Err(e) => Err(LeaseError::Meter(e)),
    }
}

// =============================================================================
// Lease state readers
// =============================================================================

/// Whether the lease has lapsed (non-payment).
pub fn is_lapsed(cell: &Cell) -> bool {
    cell.state
        .get_field(LAPSED_SLOT as usize)
        .map(|f| field_to_u64(f) != 0)
        .unwrap_or(false)
}

/// The durable checkpoint step (the scalar cursor).
pub fn checkpoint_step(cell: &Cell) -> u64 {
    cell.state
        .get_field(STEP_SLOT as usize)
        .map(field_to_u64)
        .unwrap_or(0)
}

/// The durable checkpoint step as recorded in the committed [`EXEC_COLL`] heap
/// (the umem durable image). Equals [`checkpoint_step`] for a consistent lease.
pub fn heap_checkpoint_step(cell: &Cell) -> i64 {
    cell.state
        .get_heap(EXEC_COLL, KEY_STEP)
        .map(|f| decode_i64(&f))
        .unwrap_or(0)
}

/// The number of rent periods metered+paid.
pub fn periods_paid(cell: &Cell) -> u64 {
    cell.state
        .get_field(PERIODS_PAID_SLOT as usize)
        .map(field_to_u64)
        .unwrap_or(0)
}

/// Read a working-memory key from the durable execution image.
pub fn working_memory(cell: &Cell, key: u32) -> Option<FieldElement> {
    cell.state.get_heap(EXEC_COLL, key)
}

// =============================================================================
// Payment — the conserving Transfer through the Payable DSI
// =============================================================================

/// A [`Payable`] handle on a lease cell — the lease pays its rent THROUGH the
/// shared `Payable` interface (a conserving kernel `Transfer`), so a durable-
/// execution rent payment interoperates with every other `Payable` app by default.
#[derive(Clone, Copy, Debug)]
pub struct LeaseWallet {
    /// The lease cell that holds + pays the prepaid balance.
    pub lease: CellId,
    /// The asset rent is denominated in (the lease cell's `token_id`).
    pub asset: CellId,
}

impl LeaseWallet {
    /// A wallet handle on `lease` denominating in `asset`.
    pub fn new(lease: CellId, asset: CellId) -> Self {
        LeaseWallet { lease, asset }
    }
}

impl Payable for LeaseWallet {
    fn payable_cell(&self) -> CellId {
        self.lease
    }
    fn payable_asset(&self) -> [u8; 32] {
        let mut a = [0u8; 32];
        a.copy_from_slice(self.asset.as_bytes());
        a
    }
}

/// **Build the rent payment** — a [`Payable`] `pay` of one period's rent from the
/// lease cell to the provider, desugaring to ONE conserving kernel
/// [`Effect::Transfer`]. Submit the returned [`Turn`] through the executor to move
/// the value (per-asset Σδ=0 holds). The `authority` is the lease holder's
/// authority for the `Signature`-gated `pay`.
pub fn pay_rent(
    cipherclerk: &AppCipherclerk,
    terms: &LeaseTerms,
    authority: InvokeAuthority,
) -> Result<Turn, InvokeRefused> {
    LeaseWallet::new(terms.lease, terms.asset).pay(
        cipherclerk,
        terms.rent_per_period,
        terms.provider,
        authority,
    )
}

// =============================================================================
// The deos-native surface — the lease as a composed DeosApp
// =============================================================================

/// The lease rights tiers, on the real attenuation lattice:
///   * the AGENT (lease holder) holds [`AuthRequired::Signature`] — it can `pay`
///     rent and request `advance` (drive its durable execution);
///   * the PROVIDER holds [`AuthRequired::None`]/root — it owns the slot (it can
///     `lapse` a delinquent lease + everything the agent can do).
pub const AGENT_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The provider rights tier (root). See [`AGENT_RIGHTS`].
pub const PROVIDER_RIGHTS: AuthRequired = AuthRequired::None;

/// The `advance` **live-state precondition** — the lease must be LIVE (not
/// lapsed): `LAPSED_SLOT == 0`. So an `advance` button is DARK on a lapsed lease
/// (the slot reclaimed) and LIT while the lease is current. This gates "may the
/// provider deliver execution now"; the durable-cursor INVARIANT
/// (`Monotonic(STEP_SLOT)`) is the installed [`lease_invariants_program`] the
/// executor re-enforces on the produced transition.
pub fn not_lapsed_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: LAPSED_SLOT,
        value: field_from_u64(0),
    }])
}

/// **The durable-execution lease as a composed [`DeosApp`]** — the whole
/// interaction surface on the deos bones. The lease cell is the agent's own cell
/// (`cipherclerk.cell_id()`).
///
///   * `advance` — a [`GatedAffordance`] (the provider delivers a checkpoint): a
///     live-state PRECONDITION (lease not lapsed); the real fire ([`fire_advance`])
///     submits the cursor-advancing turn, re-enforced by `Monotonic(STEP_SLOT)`;
///   * `pay` — a cap-only affordance (the agent pays rent), `Signature`;
///   * `lapse` — a cap-only affordance (the provider reclaims a delinquent slot),
///     root.
pub fn lease_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let lease = cipherclerk.cell_id();

    let advance = GatedAffordance::new(
        CellAffordance::new(
            "advance",
            AGENT_RIGHTS,
            Effect::SetField {
                cell: lease,
                index: STEP_SLOT as usize,
                value: field_from_u64(1),
            },
        ),
        not_lapsed_precondition(),
    );
    let pay = CellAffordance::new(
        "pay",
        AGENT_RIGHTS,
        Effect::EmitEvent {
            cell: lease,
            event: Event::new(symbol("lease-rent-paid"), vec![]),
        },
    );
    let lapse = CellAffordance::new(
        "lapse",
        PROVIDER_RIGHTS,
        Effect::SetField {
            cell: lease,
            index: LAPSED_SLOT as usize,
            value: field_from_u64(1),
        },
    );

    DeosApp::builder("execution-lease", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["compute".into(), "durable-execution".into()])
        .cell(
            DeosCell::new(lease, "lease")
                .gated(advance)
                .affordance(pay)
                .affordance(lapse)
                .publish(AGENT_RIGHTS),
        )
        .build()
}

/// **Seed the lease cell** so the gated fires have live state + the invariants
/// bite: install [`lease_cell_program`] (so the executor re-enforces the
/// durable-cursor + economics invariants on every touching turn), then open the
/// lease genesis state directly into the embedded ledger.
pub fn seed_lease(executor: &EmbeddedExecutor, terms: &LeaseTerms, genesis_digest: FieldElement) {
    let lease = executor.cell_id();
    executor.install_program(lease, lease_cell_program());
    executor.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&lease) {
            // open_lease seals the obligation + economics + genesis checkpoint.
            let _ = open_lease(cell, terms, genesis_digest);
        }
    });
}

/// **The `advance` cursor-advancing effects** — move the durable checkpoint cursor
/// forward to `new_step` and re-bind the state digest. The executor re-enforces
/// `Monotonic(STEP_SLOT)`, so a rewound cursor is a REAL refusal.
pub fn advance_effects(lease: CellId, new_step: u64, new_digest: FieldElement) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell: lease,
            index: STEP_SLOT as usize,
            value: field_from_u64(new_step),
        },
        Effect::SetField {
            cell: lease,
            index: STATE_DIGEST_SLOT as usize,
            value: new_digest,
        },
        Effect::EmitEvent {
            cell: lease,
            event: Event::new(
                symbol("lease-advanced"),
                vec![field_from_u64(new_step), new_digest],
            ),
        },
    ]
}

/// **Fire `advance`** — the deos cap∧state PRECONDITION gate (not lapsed,
/// anti-ghost in-band), then the verified cursor-advancing turn (reading the LIVE
/// step and adding one), re-enforced by the executor's `Monotonic(STEP_SLOT)`.
/// After the turn commits, [`mirror_checkpoint`] keeps the committed umem heap in
/// step and writes the running execution's `working` memory into the durable image.
/// A lapsed lease's `advance` never submits (the slot was reclaimed); a rewind is a
/// real executor refusal.
pub fn fire_advance(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
    new_digest: FieldElement,
    working: Vec<(u32, FieldElement)>,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let lease = cell.cell();
    let receipt = cell.fire_gated_through_executor_with(
        "advance",
        held,
        cipherclerk,
        executor,
        move |live| {
            let live_step = field_to_u64(&live.fields[STEP_SLOT as usize]);
            advance_effects(lease, live_step + 1, new_digest)
        },
    )?;
    // Mirror the executor-enforced scalar cursor into the committed umem heap (the
    // durable, passable, witnessed execution image) + write working memory.
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&lease) {
            mirror_checkpoint(c, &working);
        }
    });
    Ok(receipt)
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// Mount the deos-native surface ([`lease_app`]) on a shared context: build the
/// composed [`DeosApp`], seed the lease cell's program + genesis state, and fold
/// the app into the context's affordance registry.
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = lease_app(ctx.cipherclerk(), ctx.executor());
    let lease = ctx.executor().cell_id();
    let provider = CellId::from_bytes([0xAB; 32]);
    let asset = ctx.executor().cell_id();
    let terms = LeaseTerms::new(
        provider,
        lease,
        asset,
        DEFAULT_RENT_PER_PERIOD,
        DEFAULT_PERIOD,
        DEFAULT_START,
        0,
    );
    seed_lease(ctx.executor(), &terms, field_from_u64(1));
    app.register(ctx);
    app
}

/// The canonical web-constants module — the slot layout + event topics + factory
/// VK the JS surface is rendered from.
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("execution-lease")
        .slot("STEP_SLOT", STEP_SLOT as u64)
        .slot("STATE_DIGEST_SLOT", STATE_DIGEST_SLOT as u64)
        .slot("LAPSED_SLOT", LAPSED_SLOT as u64)
        .slot("PERIODS_PAID_SLOT", PERIODS_PAID_SLOT as u64)
        .slot("RENT_SLOT", RENT_SLOT as u64)
        .slot("PERIOD_SLOT", PERIOD_SLOT as u64)
        .slot("PROVIDER_SLOT", PROVIDER_SLOT as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&LEASE_FACTORY_VK))
        .topic("ADVANCED", "lease-advanced")
        .topic("RENT_PAID", "lease-rent-paid")
}

/// Register the execution-lease starbridge-app on a shared context.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(lease_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "execution-lease".into(),
        descriptor: serde_json::json!({
            "component": "dregg-execution-lease",
            "module": "/starbridge-apps/execution-lease/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["step", "state_digest", "lapsed", "periods_paid"],
            "slot_layout": {
                "step": STEP_SLOT,
                "state_digest": STATE_DIGEST_SLOT,
                "lapsed": LAPSED_SLOT,
                "periods_paid": PERIODS_PAID_SLOT,
                "rent_per_period": RENT_SLOT,
                "period": PERIOD_SLOT,
                "provider": PROVIDER_SLOT,
            },
            "exec_collection": EXEC_COLL,
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&lease_child_program_vk()),
            "operations": ["open", "pay", "advance", "lapse"],
        }),
    });

    register_deos(ctx);
    factory_vk
}

/// Build the on-ledger [`Action`] opening a lease (a record of the seal — the
/// genesis checkpoint + sealed economics). The state-binding `open_lease` runs
/// executor-side; this is the signed turn that records the open.
pub fn build_open_lease_action(
    cipherclerk: &AppCipherclerk,
    lease: CellId,
    terms: &LeaseTerms,
    genesis_digest: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: lease,
            index: RENT_SLOT as usize,
            value: field_from_u64(terms.rent_per_period),
        },
        Effect::SetField {
            cell: lease,
            index: PERIOD_SLOT as usize,
            value: field_from_u64(terms.period as u64),
        },
        Effect::SetField {
            cell: lease,
            index: PROVIDER_SLOT as usize,
            value: cell_tag(terms.provider),
        },
        Effect::SetField {
            cell: lease,
            index: STATE_DIGEST_SLOT as usize,
            value: genesis_digest,
        },
        Effect::EmitEvent {
            cell: lease,
            event: Event::new(
                symbol("lease-opened"),
                vec![
                    field_from_u64(terms.rent_per_period),
                    field_from_u64(terms.period as u64),
                    cell_tag(terms.provider),
                    genesis_digest,
                ],
            ),
        },
    ];
    cipherclerk.make_action(lease, "open_lease", effects)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, EmbeddedExecutor};

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }

    fn lease_cell() -> Cell {
        Cell::with_balance([7u8; 32], [9u8; 32], 0)
    }

    /// provider=2, lease=7 (the cell), asset=9; rent 100 every 50 blocks from 1000.
    fn sample_terms() -> LeaseTerms {
        LeaseTerms::new(cid(2), cid(7), cid(9), 100, 50, 1000, 0)
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32]);
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    #[test]
    fn factory_descriptor_is_stable() {
        assert_eq!(
            lease_factory_descriptor().hash(),
            lease_factory_descriptor().hash()
        );
    }

    #[test]
    fn open_seals_economics_and_genesis_checkpoint() {
        let terms = sample_terms();
        let mut cell = lease_cell();
        open_lease(&mut cell, &terms, field_from_u64(0xABCD)).unwrap();

        assert_eq!(checkpoint_step(&cell), 0);
        assert_eq!(heap_checkpoint_step(&cell), 0);
        assert!(!is_lapsed(&cell));
        assert_eq!(periods_paid(&cell), 0);
        assert_eq!(
            field_to_u64(cell.state.get_field(RENT_SLOT as usize).unwrap()),
            100
        );
        // The obligation (the meter) is sealed into the heap.
        assert!(ObligationState::read(&cell).is_ok());
    }

    #[test]
    fn ill_formed_terms_are_rejected() {
        let mut cell = lease_cell();
        let bad = LeaseTerms::new(cid(2), cid(7), cid(9), 0, 50, 1000, 0);
        assert_eq!(
            open_lease(&mut cell, &bad, field_from_u64(0)),
            Err(LeaseError::IllFormedTerms)
        );
    }

    #[test]
    fn metered_period_discharges_exactly_the_rent_one_shot() {
        let terms = sample_terms();
        let mut cell = lease_cell();
        open_lease(&mut cell, &terms, field_from_u64(0)).unwrap();

        // Period 0 due at 1000: an on-schedule meter accepts, moves exactly the rent.
        assert_eq!(meter_period(&mut cell, &terms, 0, 1000), Ok(100));
        assert_eq!(periods_paid(&cell), 1);
        // A replay of period 0 is refused (one-shot — the cursor advanced).
        assert!(matches!(
            meter_period(&mut cell, &terms, 0, 1000),
            Err(LeaseError::Meter(ObligationError::WrongPeriod { .. }))
        ));
        // An early discharge of period 1 (due 1050) at clock 1000 is refused.
        assert!(matches!(
            meter_period(&mut cell, &terms, 1, 1000),
            Err(LeaseError::Meter(ObligationError::NotYetDue { .. }))
        ));
    }

    #[test]
    fn checkpoint_advances_forward_and_survives_in_the_committed_heap() {
        let terms = sample_terms();
        let mut cell = lease_cell();
        open_lease(&mut cell, &terms, field_from_u64(1)).unwrap();
        let before = cell.state_commitment();

        // Advance the durable image, writing working memory.
        let s1 = advance_checkpoint(
            &mut cell,
            field_from_u64(2),
            &[(WORKING_BASE, field_from_u64(0xF00D))],
        )
        .unwrap();
        assert_eq!(s1, 1);
        assert_eq!(checkpoint_step(&cell), 1);
        assert_eq!(
            heap_checkpoint_step(&cell),
            1,
            "the umem heap mirrors the cursor"
        );
        // The durable working memory survives in the committed image.
        assert_eq!(
            working_memory(&cell, WORKING_BASE),
            Some(field_from_u64(0xF00D))
        );
        // Advancing moves the state commitment — a light client sees it.
        assert_ne!(
            before,
            cell.state_commitment(),
            "the checkpoint is witnessed"
        );

        let s2 = advance_checkpoint(&mut cell, field_from_u64(3), &[]).unwrap();
        assert_eq!(s2, 2);
    }

    #[test]
    fn lapse_on_non_payment_then_advance_is_refused() {
        let terms = sample_terms();
        let mut cell = lease_cell();
        open_lease(&mut cell, &terms, field_from_u64(1)).unwrap();

        // Pay period 0 only, then let the clock run well past period 1's due block.
        meter_period(&mut cell, &terms, 0, 1000).unwrap();
        // By clock 1100, periods 0,1,2 are due (start 1000, period 50): behind.
        let lapsed = lapse_if_behind(&mut cell, &terms, 1100).unwrap();
        assert!(lapsed, "a lease that skipped a period lapses");
        assert!(is_lapsed(&cell));

        // A lapsed lease cannot advance its durable execution (slot reclaimed).
        assert_eq!(
            advance_checkpoint(&mut cell, field_from_u64(9), &[]),
            Err(LeaseError::Lapsed)
        );
    }

    #[test]
    fn paid_up_lease_does_not_lapse() {
        let terms = sample_terms();
        let mut cell = lease_cell();
        open_lease(&mut cell, &terms, field_from_u64(1)).unwrap();
        // Discharge periods 0,1,2 on schedule (due 1000, 1050, 1100).
        for (k, clk) in [(0, 1000), (1, 1050), (2, 1100)] {
            meter_period(&mut cell, &terms, k, clk).unwrap();
        }
        // By clock 1100 the schedule demands 3 periods; this lease paid all 3.
        assert_eq!(lapse_if_behind(&mut cell, &terms, 1100), Ok(false));
        assert!(!is_lapsed(&cell));
    }

    #[test]
    fn pay_rent_desugars_to_one_conserving_transfer() {
        let cipherclerk = AppCipherclerk::new(AgentCipherclerk::new(), [5u8; 32]);
        let lease = cipherclerk.cell_id();
        let terms = LeaseTerms::new(cid(2), lease, cid(9), 100, 50, 1000, 0);
        let turn = pay_rent(&cipherclerk, &terms, InvokeAuthority::Signature).unwrap();
        let action = &turn.call_forest.roots[0].action;
        assert_eq!(action.method, symbol("pay"));
        assert_eq!(action.effects.len(), 1);
        assert!(matches!(
            action.effects[0],
            Effect::Transfer { from, to, amount }
                if from == lease && to == cid(2) && amount == 100
        ));
    }

    #[test]
    fn open_durable_image_seeds_the_image_without_meter_or_economics() {
        // The durable-image half alone: genesis checkpoint + live latch, and NO
        // obligation meter and NO economic slots (that half is the fused prepaid
        // capacity's job on this cell).
        let mut cell = lease_cell();
        open_durable_image(&mut cell, field_from_u64(0xABCD));
        assert_eq!(checkpoint_step(&cell), 0);
        assert_eq!(heap_checkpoint_step(&cell), 0);
        assert!(!is_lapsed(&cell));
        // No obligation meter was sealed (unlike open_lease).
        assert!(ObligationState::read(&cell).is_err());
        // No economics were sealed — the RENT slot was never written to the rent
        // (it stays at its zero default; open_lease would seal it to the rent).
        assert_eq!(
            cell.state
                .get_field(RENT_SLOT as usize)
                .map(field_to_u64)
                .unwrap_or(0),
            0
        );
        // The image advances + latches exactly as an obligation lease's does.
        assert_eq!(advance_checkpoint(&mut cell, field_from_u64(2), &[]), Ok(1));
        mark_lapsed(&mut cell);
        assert!(is_lapsed(&cell));
        assert_eq!(
            advance_checkpoint(&mut cell, field_from_u64(3), &[]),
            Err(LeaseError::Lapsed),
            "a lapsed durable image refuses further delivery"
        );
    }

    #[test]
    fn register_installs_factory_and_inspector() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, LEASE_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(ctx.inspector_registry().get("execution-lease").is_some());
    }
}
