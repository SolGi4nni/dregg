//! **deos-js-core** — the shared *substance* the two deos-js engines both bind.
//!
//! deos supports two JS engines that drive the SAME cell-applet surface:
//!
//!   - `deos-js` — real SpiderMonkey (`mozjs`), the web/servo engine;
//!   - `deos-js-runtime` — pure-Rust `boa`, the cockpit (gpui-native) + wasm engine.
//!
//! They are meant to be twins: the same authored applet, fired through either engine,
//! must leave byte-identical committed state. Historically they were HAND-SYNCED twins,
//! and they DRIFTED — the SM side's `ApplyOp` lacked the boa side's 5th
//! [`ApplyOp::SetRegisterFromArgs`] variant, and each carried its own copy of the
//! `pack_u64` codec and the per-variant arithmetic. Two copies that each compile green
//! are a standing drift source (backlog 2026-07-24 T2 / #5): a fix to one silently
//! diverges from the other.
//!
//! This crate is the ONE source of truth. Both engines import [`ApplyOp`] / [`CellModel`]
//! / [`pack_u64`] from here and delete their local copies; a cross-engine differential
//! test (`deos-js/tests/cross_engine_applyop_differential.rs`) asserts the two engines'
//! fire drivers produce byte-identical [`CellModel`] results across every variant,
//! including the previously-diverging 5th. It is PURE substance — no `mozjs`, no `boa`.
//!
//! ## The canonical FIRE CONTRACT
//!
//! The two engines also drifted on how a fire's *outcome* reaches JS. The canonical
//! contract, documented here as the single decision, is:
//!
//!   - **Value width — `i64`.** A committed fire returns the new value of the written
//!     slot as a signed 64-bit integer (a witnessed read off the live ledger). Model
//!     slots hold `u64`; a 32-bit return (`i32`) truncates a large committed value, so
//!     the wider `i64` is canonical.
//!   - **Refusal — SURFACE, do not swallow.** A refusal (unknown affordance, a cap-tooth
//!     `Unauthorized`, a routing/serviced-seam refusal, a commitment mismatch, or an
//!     executor rejection) is raised to the script as a thrown JS error AND recorded for
//!     the host (a `last_fire_error`-style side channel). It is NOT collapsed to an
//!     in-band `-1` sentinel value: `-1` is indistinguishable from a legitimately
//!     computed slot value and hides *which* gate refused, so a swallowed refusal is a
//!     silent-failure trap. Surfacing keeps the refusal observable to both the script's
//!     own `try/catch` and the embedding host.
//!
//! `deos-js-runtime` (boa) already conforms to this contract (`i64` + throw + record).
//! `deos-js` (SM) currently returns `i32` with a `-1` refusal sentinel; migrating its
//! host-fn glue to the canonical contract is a JS-observable behavior change (its
//! red-team surface tests assert the `-1`/swallow semantics) and is tracked as the
//! scoped remainder of this drift-closure, separate from the vocabulary unification this
//! crate lands.

use std::collections::BTreeMap;

use dregg_cell::state::FieldElement;
use dregg_types::CellId;
use serde::{Deserialize, Serialize};

/// A model slot index (a cell-state field). Both engines index the applet model by this.
pub type Slot = usize;

/// Pack a `u64` into a [`FieldElement`] — the model's scalar shape. This is THE codec both
/// engines pack/unpack the counter/register scalars with; the previously-duplicated per-engine
/// copies are gone.
///
/// ⚠ THE LANE: this delegates to `dregg_cell::field_from_u64` (big-endian into bytes `24..32`),
/// the u64 lane the verified kernel defines a `fields[]` slot to BE. It used to write
/// little-endian into bytes `0..8`, which is the OPPOSITE end of the value.
///
/// ⚑ WHY THAT USED TO BE FATAL, AND WHAT IT IS NOW. The deployed `setFieldVmDescriptor2-{slot}R24`
/// used to FREEZE the written slot's 7 completion lanes BEFORE↔AFTER, so only bytes `28..32` of a
/// field value could change on a setField turn — a `0..8` write lit a frozen lane and `pack_u64(1)`
/// did not truncate, it failed to PROVE at all. The VALUE8 epoch retired that freeze (the lanes are
/// freed and PUBLISHED as PIs 46..=52), so the whole 32-byte value is writable and a wrong-lane
/// encoder no longer fails loudly. It is still a **codec bug** — `unpack_u64` reads BE from `24..32`,
/// so an LE-into-`0..8` write reads back as a different number — and the detector is now static, not
/// proof-enforced: `circuit/tests/setfield_encoder_window_gate.rs`, whose type-directed walk
/// (`every_setfield_encoder_writes_inside_the_u64_lane`) is the load-bearing gate. The Lean
/// producer's `field_fits_wire_carrier` (`exec-lean/src/lean_shadow.rs:2499`, "bytes `0..24` must be
/// zero") is a SEPARATE, still-live eligibility bound.
pub fn pack_u64(v: u64) -> FieldElement {
    dregg_cell::field_from_u64(v)
}

/// Read a `u64` back out of a [`FieldElement`] (the inverse of [`pack_u64`]).
///
/// Moved to the u64 lane together with [`pack_u64`] — the pair must stay on the same lane or every
/// stored value reads back as garbage.
pub fn unpack_u64(fe: &FieldElement) -> u64 {
    dregg_cell::field_to_u64(fe)
}

/// A read-only view of an applet's MODEL (the cell's live state) — the positions of the
/// polynomial-functor interface. Built from the engine ledger on demand. Shared so BOTH
/// engines read the model identically before computing an [`ApplyOp`] write.
pub struct CellModel {
    fields: BTreeMap<Slot, FieldElement>,
    nonce: u64,
}

impl CellModel {
    /// Project a cell's live state off a ledger into a model (the positions of the
    /// polynomial functor). Only non-zero fields are captured; [`CellModel::field_u64`]
    /// reads an absent slot back as `0`.
    pub fn from_ledger(ledger: &dregg_cell::Ledger, cell_id: &CellId) -> Self {
        let mut fields = BTreeMap::new();
        let mut nonce = 0;
        if let Some(cell) = ledger.get(cell_id) {
            for slot in 0..dregg_cell::state::STATE_SLOTS {
                if let Some(fe) = cell.state.get_field(slot) {
                    if *fe != [0u8; 32] {
                        fields.insert(slot, *fe);
                    }
                }
            }
            nonce = cell.state.nonce();
        }
        CellModel { fields, nonce }
    }

    /// Read ONE model field as a `u64` directly off the ledger — WITHOUT projecting the
    /// whole cell into a [`CellModel`] (which builds an entire `BTreeMap` over all
    /// `STATE_SLOTS`). The hot read path (`get_u64`, a `bind` re-read, a counter-bump's
    /// current value) calls this per slot; building a map to pull one scalar is pure
    /// waste. Absent cell / empty slot reads back `0` (the same default `field_u64` gives).
    pub fn field_u64_direct(ledger: &dregg_cell::Ledger, cell_id: &CellId, slot: Slot) -> u64 {
        ledger
            .get(cell_id)
            .and_then(|cell| cell.state.get_field(slot).copied())
            .map(|fe| unpack_u64(&fe))
            .unwrap_or(0)
    }

    /// An empty model (no fields, nonce 0) — the default a closure-passing ledger read
    /// fills in (an attach path projects through a `with_ledger` callback).
    pub fn from_ledger_empty() -> Self {
        CellModel {
            fields: BTreeMap::new(),
            nonce: 0,
        }
    }

    /// Read a model field as a raw element.
    pub fn field(&self, slot: Slot) -> FieldElement {
        self.fields.get(&slot).copied().unwrap_or([0u8; 32])
    }

    /// Read a model field as a `u64` (the scalar shape).
    pub fn field_u64(&self, slot: Slot) -> u64 {
        unpack_u64(&self.field(slot))
    }

    /// The cell's nonce — bumps once per committed turn (the "how many affordances have
    /// fired" witness).
    pub fn nonce(&self) -> u64 {
        self.nonce
    }

    /// Iterate the model's non-zero `(slot, value)` fields in slot order (the
    /// `BTreeMap` iteration order) — the content-address a transclusion surface pins.
    pub fn iter_fields(&self) -> impl Iterator<Item = (&Slot, &FieldElement)> {
        self.fields.iter()
    }
}

/// The pure apply closure an affordance carries in the SM (`deos-js`) engine: live model
/// + JS-supplied arg → field-writes. Reconstituted from an [`ApplyOp`] by
/// [`ApplyOp::into_closure`]. Shared here so the closure and the boa side's
/// [`ApplyOp::write`] cannot drift — both route through the same [`ApplyOp::apply`].
pub type ApplyFn = Box<dyn Fn(&CellModel, i64) -> Vec<(Slot, FieldElement)>>;

/// A declarative apply rule — the portable shape of an affordance's effect, the UNION of
/// both engines' vocabularies. This is the part of the program that, in a live applet, is
/// a Rust closure; reconstituting it from a manifest is what makes a loaded affordance the
/// SAME affordance (same writes for the same model + args).
///
/// Every variant lowers to the SAME ordinary `Effect::SetField` the executor already
/// enforces and a light client already witnesses — the op is purely a runtime-layer
/// *write-shape*, NOT a kernel/effect-vocabulary or circuit change. Both engines share
/// this ONE enum and the ONE arithmetic in [`ApplyOp::write`]; the SM engine now carries
/// [`ApplyOp::SetRegisterFromArgs`] too (it was previously missing on that side).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ApplyOp {
    /// `slot := slot + max(args[0], 0)` saturating (the counter `inc`).
    AddToSlot { slot: Slot },
    /// `slot := slot - max(args[0], 0)` saturating at 0 (the counter `dec`).
    SubFromSlot { slot: Slot },
    /// `slot := value` — set a slot to a fixed `u64` (e.g. `reset` to 0).
    SetSlot { slot: Slot, value: u64 },
    /// `slot := max(args[0], 0)` — a **literal write**: write the JS-supplied value
    /// DIRECTLY to a fixed register, overwriting whatever was there (a `put(v)` lands `v`
    /// exactly, even over a non-zero slot — the gap `AddToSlot` left, which only lands
    /// `v` on a *fresh* `0`). Also the Pulse→Signals "track an externally-observed value"
    /// write verb (mirror a live World reading into a status card's model as a receipted
    /// verified turn).
    SetSlotFromArg { slot: Slot },
    /// `args[0] := max(args[1], 0)` — a **register-addressed literal write**: write the
    /// JS-supplied VALUE (`args[1]`) to the JS-supplied REGISTER (`args[0]`). This lets a
    /// JS affordance reach an ARBITRARY register chosen at call time — exactly the kvstore
    /// `put(reg, value)` shape, expressed in pure JS. (The variant the SM engine
    /// previously LACKED; the drift this crate closes.)
    SetRegisterFromArgs,
}

impl ApplyOp {
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

    /// **The one canonical arithmetic.** The `(slot, new-value)` write this op produces
    /// against the current slot value and the JS-supplied `args` (`args[0]` is the legacy
    /// single arg; `args[1]` feeds the register-addressed write). Every add/sub is
    /// SATURATING (a plain `cur + arg` panicked in debug / wrapped in release, so the two
    /// twin engines produced DIFFERENT receipted state — or a crash — for the same applet
    /// on overflow). Both engines call exactly this; there is no second copy to drift.
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

    /// Compute the write against a live [`CellModel`] and the JS-supplied `args` — the
    /// model-reading form both engines share (the SM engine's closure and the boa engine's
    /// driver both reach the arithmetic through here). Reads `current` at [`ApplyOp::slot`]
    /// off the model, then defers to the single [`ApplyOp::write`] arithmetic. Returns a
    /// `Vec` because the SM engine's [`ApplyFn`] is `Vec`-shaped; an [`ApplyOp`] always
    /// produces exactly one write.
    pub fn apply(&self, model: &CellModel, args: &[i64]) -> Vec<(Slot, FieldElement)> {
        let current = model.field_u64(self.slot());
        let (slot, value) = self.write(current, args);
        vec![(slot, value)]
    }

    /// Reconstitute the live SM apply closure (an [`ApplyFn`]). The closure is a pure
    /// function of the live model + the single JS-supplied arg, threaded as a 1-element
    /// arg slice into [`ApplyOp::apply`] — so the SM closure path and the boa driver path
    /// compute IDENTICAL writes. (The register-addressed [`ApplyOp::SetRegisterFromArgs`]
    /// needs a second arg the SM engine's single-arg `fire` does not yet supply; through
    /// this closure it sees `args = [arg]` and writes value 0 — the variant is now
    /// REPRESENTABLE on the SM side, and exposing a multi-arg SM fire is the scoped
    /// remainder.)
    pub fn into_closure(self) -> ApplyFn {
        Box::new(move |model, arg| self.apply(model, &[arg]))
    }
}
