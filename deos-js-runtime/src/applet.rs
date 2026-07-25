//! The **substance** the native runtime drives — a minimal cell-applet over the
//! embedded verified executor.
//!
//! This is the engine-independent half: it knows nothing about JS. It mints a cell on
//! a fresh [`DreggEngine`], registers a small declarative affordance surface, and
//! [`CellApplet::fire`]s a named affordance as a REAL cap-gated verified turn — the
//! SAME path `deos-js::applet::Applet::fire` runs (cap tooth → executor → receipt). The
//! `boa` runtime in [`crate::runtime`] is a thin bridge onto this surface, so a cell's
//! attached JS commits verified turns exactly as a static `{turn,arg}` button does.

use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, Cell, Permissions};
use dregg_sdk::embed::{DreggEngine, EngineConfig};
use dregg_turn::builder::{ActionBuilder, TurnBuilder};
use dregg_turn::TurnReceipt;
use dregg_types::CellId;

/// A model slot index (a cell-state field).
pub type Slot = usize;

/// Pack a `u64` into a [`FieldElement`] (little-endian low 8 bytes) — the model's
/// scalar shape, matching `deos-js::applet::pack_u64`.
pub fn pack_u64(v: u64) -> FieldElement {
    let mut fe = [0u8; 32];
    fe[..8].copy_from_slice(&v.to_le_bytes());
    fe
}

/// Read a `u64` back out of a [`FieldElement`].
pub fn unpack_u64(fe: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[..8]);
    u64::from_le_bytes(b)
}

/// A declarative apply rule — the portable shape of an affordance's effect, mirroring
/// `deos-js::portable::ApplyOp`. Reconstituting an affordance from this is what makes a
/// fire deterministic (the same writes for the same model + args).
///
/// Every variant lowers to the SAME ordinary `Effect::SetField` the executor already
/// enforces and a light client already witnesses — the op is purely a runtime-layer
/// *write-shape*, NOT a kernel/effect-vocabulary or circuit change. The literal-write
/// variants ([`ApplyOp::SetSlotFromArg`], [`ApplyOp::SetRegisterFromArgs`]) are the named
/// power-up that lets a JS affordance write the JS-supplied VALUE to a register, instead
/// of riding `AddToSlot` over a zeroed slot (which only lands `v` on a *fresh* `0`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ApplyOp {
    /// `slot := slot + max(args[0], 0)` (the counter `inc`).
    AddToSlot { slot: Slot },
    /// `slot := slot - max(args[0], 0)` saturating at 0 (the counter `dec`).
    SubFromSlot { slot: Slot },
    /// `slot := value` — set a slot to a fixed `u64` (e.g. `reset` to 0).
    SetSlot { slot: Slot, value: u64 },
    /// `slot := max(args[0], 0)` — a **literal write**: write the JS-supplied value
    /// DIRECTLY to a fixed register, overwriting whatever was there (a `put(v)` lands `v`
    /// exactly, even over a non-zero slot — the gap `AddToSlot` left). The named power-up.
    SetSlotFromArg { slot: Slot },
    /// `args[0] := max(args[1], 0)` — a **register-addressed literal write**: write the
    /// JS-supplied VALUE (`args[1]`) to the JS-supplied REGISTER (`args[0]`). This lets a
    /// JS affordance reach an ARBITRARY register chosen at call time — exactly the kvstore
    /// `put(reg, value)` shape, expressed in pure JS.
    SetRegisterFromArgs,
}

impl ApplyOp {
    /// The (slot, new-value) write this op produces against the current slot value and the
    /// JS-supplied `args` (`args[0]` is the legacy single arg; later positions feed the
    /// register-addressed write).
    pub fn write(&self, current: u64, args: &[i64]) -> (Slot, FieldElement) {
        let a0 = args.first().copied().unwrap_or(0);
        match *self {
            ApplyOp::AddToSlot { slot } => {
                let next = current.saturating_add(a0.max(0) as u64);
                (slot, pack_u64(next))
            }
            ApplyOp::SubFromSlot { slot } => {
                let next = current.saturating_sub(a0.max(0) as u64);
                (slot, pack_u64(next))
            }
            ApplyOp::SetSlot { slot, value } => (slot, pack_u64(value)),
            ApplyOp::SetSlotFromArg { slot } => (slot, pack_u64(a0.max(0) as u64)),
            ApplyOp::SetRegisterFromArgs => {
                let reg = a0.max(0) as usize;
                let value = args.get(1).copied().unwrap_or(0).max(0) as u64;
                (reg, pack_u64(value))
            }
        }
    }

    /// The model slot this op reads for its `current` value before writing. For the
    /// register-addressed write the target is dynamic (it comes from `args[0]`), and the
    /// op ignores `current`, so slot `0` is reported as an innocuous read site.
    pub fn slot(&self) -> Slot {
        match *self {
            ApplyOp::AddToSlot { slot }
            | ApplyOp::SubFromSlot { slot }
            | ApplyOp::SetSlot { slot, .. }
            | ApplyOp::SetSlotFromArg { slot } => slot,
            ApplyOp::SetRegisterFromArgs => 0,
        }
    }
}

/// One named affordance — a direction of the cell's polynomial-functor interface. A
/// fire is gated on `required` (the cap tooth) and commits `op`'s write as a verified
/// turn.
#[derive(Clone, Debug)]
pub struct Affordance {
    pub name: String,
    pub required: AuthRequired,
    pub op: ApplyOp,
}

/// Why a fire produced no turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FireError {
    /// No affordance with that name on this cell's surface.
    UnknownAffordance(String),
    /// The held authority does not satisfy the affordance's `required` (the cap tooth
    /// refused — nothing committed, nothing reached the executor).
    Unauthorized(String),
    /// The JS app named a cell it holds NO capability to. In the ocap stance a script
    /// can only reference the cell handles the host installed; a name absent from the
    /// cap table is unreachable — the over-reach commits NOTHING and the cell the name
    /// would have pointed at is never touched. (The keystone confinement refusal for the
    /// cross-cell host fns.)
    NoCapability(String),
    /// The JS named a method that does NOT route through the target cell's published
    /// [`dregg_cell::interface::InterfaceDescriptor`] (the verified DFA
    /// `route_method` path `invoke()` speaks). The method is not a member of the
    /// committed interface — fail-closed, nothing committed.
    MethodNotRouted(String),
    /// The JS named a [`dregg_cell::interface::Semantics::Serviced`] method through
    /// `tCell` — a serviced read is answered by the OFE cross-cell read, NOT a replay
    /// turn, so the bridge refuses to fire it (mirroring `invoke()`'s `ServicedSeam`
    /// refusal). The seam is named honestly rather than faked into a write.
    ServicedSeam(String),
    /// A commit-reveal **binding** refusal — the keystone tooth of the sealed-auction
    /// power-up. A revealed `(bidder, value, nonce)` did NOT re-hash to the sealed
    /// commitment frozen at commit time (or no commitment was ever sealed at that slot).
    /// The runtime OWNS the seal function, so a reveal binds to EXACTLY its commitment:
    /// no peeking-then-switching (a changed value no longer matches its frozen seal), and
    /// a non-committed party cannot open (an absent/zero seal never matches). Refused
    /// IN-BAND before any turn — nothing commits, the reveal never reaches the executor.
    CommitmentMismatch(String),
    /// The executor rejected the (authorized) turn.
    Executor(String),
}

impl std::fmt::Display for FireError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FireError::UnknownAffordance(n) => write!(f, "unknown affordance: {n}"),
            FireError::Unauthorized(n) => write!(f, "unauthorized affordance: {n}"),
            FireError::NoCapability(n) => write!(f, "no capability to cell: {n}"),
            FireError::MethodNotRouted(n) => {
                write!(
                    f,
                    "method does not route through the published interface: {n}"
                )
            }
            FireError::ServicedSeam(n) => {
                write!(f, "serviced method is a read, not a turn (no desugar): {n}")
            }
            FireError::CommitmentMismatch(n) => {
                write!(
                    f,
                    "revealed bid does not bind to its sealed commitment: {n}"
                )
            }
            FireError::Executor(e) => write!(f, "executor rejected the turn: {e}"),
        }
    }
}
impl std::error::Error for FireError {}

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

/// A cell-applet on a private embedded executor: the substance a native-JS handler
/// drives. ONE cell, a named affordance surface, and the `held` authority the runtime
/// is mounted under (the cap tooth's left side).
pub struct CellApplet {
    engine: DreggEngine,
    cell: CellId,
    held: AuthRequired,
    affordances: Vec<Affordance>,
    receipts: Vec<[u8; 32]>,
    prev_receipt: Option<[u8; 32]>,
}

impl CellApplet {
    /// Mint a cell-applet: seed `seed_fields` as the model, register `affordances`,
    /// mount under `held`. The drive path runs in `Symbolic` witness mode (the cheap
    /// local end — the state transition + every gate run identically; only the
    /// publishable Merkle commitment is deferred), exactly as `deos-js::applet`.
    pub fn mint(
        public_key: [u8; 32],
        token_id: [u8; 32],
        seed_fields: &[(Slot, u64)],
        affordances: Vec<Affordance>,
        held: AuthRequired,
    ) -> Self {
        let mut engine = DreggEngine::new(EngineConfig::for_testing());
        engine
            .executor()
            .set_witness_mode(dregg_turn::collapse::WitnessMode::Symbolic);

        let mut cell = Cell::with_balance(public_key, token_id, 1_000_000);
        cell.permissions = open_permissions();
        for (slot, value) in seed_fields {
            cell.state.set_field(*slot, pack_u64(*value));
        }
        let cell_id = cell.id();
        engine
            .ledger_mut()
            .insert_cell(cell)
            .expect("seed the applet cell onto the embedded ledger");

        CellApplet {
            engine,
            cell: cell_id,
            held,
            affordances,
            receipts: Vec::new(),
            prev_receipt: None,
        }
    }

    /// The applet's cell id (its sovereignty boundary).
    pub fn cell(&self) -> CellId {
        self.cell
    }

    /// The held authority the runtime is mounted under (the cap tooth's left side).
    pub fn held(&self) -> &AuthRequired {
        &self.held
    }

    /// Witnessed read of one model slot as a `u64`, direct off the live ledger.
    pub fn get_u64(&self, slot: Slot) -> u64 {
        self.engine
            .ledger()
            .get(&self.cell)
            .and_then(|c| c.state.get_field(slot).copied())
            .map(|fe| unpack_u64(&fe))
            .unwrap_or(0)
    }

    /// The current cell nonce (chains the next turn).
    fn nonce(&self) -> u64 {
        self.engine
            .ledger()
            .get(&self.cell)
            .map(|c| c.state.nonce())
            .unwrap_or(0)
    }

    /// The committed receipt tape (what the JS left on the ledger), in order.
    pub fn receipts(&self) -> &[[u8; 32]] {
        &self.receipts
    }

    /// The registered affordance names + the authority each requires.
    pub fn affordance_specs(&self) -> Vec<(String, AuthRequired)> {
        self.affordances
            .iter()
            .map(|a| (a.name.clone(), a.required.clone()))
            .collect()
    }

    /// **Fire an affordance** — commit ONE cap-gated verified turn on the embedded
    /// executor. The cap-bounded host fn `t(turn, arg)` calls exactly this.
    ///
    /// 1. resolve the affordance (unknown ⇒ no turn);
    /// 2. CAP TOOTH, in-band: `held` must satisfy the affordance's `required`
    ///    (`dregg_cell::is_attenuation`) — an over-reach commits NOTHING and never
    ///    reaches the executor;
    /// 3. compute the write as a pure function of the live model;
    /// 4. build + `execute_turn` the verified turn (affordance name as the action
    ///    method, the chain head threaded, the fee stamped).
    ///
    /// On success a real [`TurnReceipt`] returns; its hash joins the audit tape.
    pub fn fire(&mut self, affordance: &str, arg: i64) -> Result<TurnReceipt, FireError> {
        let aff = self
            .affordances
            .iter()
            .find(|a| a.name == affordance)
            .cloned()
            .ok_or_else(|| FireError::UnknownAffordance(affordance.to_string()))?;

        // (2) the REAL cap tooth, in-band.
        if !dregg_cell::is_attenuation(&self.held, &aff.required) {
            return Err(FireError::Unauthorized(affordance.to_string()));
        }

        // (3) write = pure function of the live model.
        let current = self.get_u64(aff.op.slot());
        let (slot, value) = aff.op.write(current, &[arg]);

        // (4) build + execute the verified turn (the cap tooth already ran in-band, so
        //     the action carries `Unchecked` authorization — single-custody embedded
        //     world; the agent is the applet cell).
        let nonce = self.nonce();
        let action = ActionBuilder::new_unchecked_for_tests(self.cell, affordance, self.cell)
            .effect_set_field(self.cell, slot as u64, value)
            .effect_increment_nonce(self.cell)
            .build();

        let mut tb = TurnBuilder::new(self.cell, nonce);
        tb.set_fee(10_000);
        if let Some(prev) = self.prev_receipt {
            tb.set_previous_receipt_hash(prev);
        }
        tb.add_action(action);
        let turn = tb.build();

        let receipt = self
            .engine
            .execute_turn(&turn)
            .map_err(|e| FireError::Executor(e.to_string()))?;
        let rh = receipt.receipt_hash();
        self.prev_receipt = Some(rh);
        self.receipts.push(rh);
        Ok(receipt)
    }
}
