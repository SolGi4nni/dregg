//! lean_apply.rs — THE SWAP state-producer: reconstitute a `cell::Ledger` from the verified
//! Lean executor's produced `WireState`.
//!
//! # The authority inversion this closes
//!
//! Today the node runs the verified Lean executor (`dregg_exec_full_forest_auth` /
//! `execFullForestG`, proven sorry-free) only as a passive veto-only SHADOW: the FFI produces a
//! full post-state, but `decode_shadow_verdict` keeps only `{committed, loglen, status}` and the
//! node commits the post-state the LEGACY Rust `TurnExecutor` produced. The verified executor is
//! never the state PRODUCER.
//!
//! The missing mechanism — which `dregg-lean-ffi/src/marshal.rs` names as "the biggest gap" — is a
//! `WireState → cell::Ledger` extractor. This module is that extractor. `dregg_lean_ffi`'s
//! `decode_shadow_state` now keeps the post-state `WireState`; here we map it back onto real
//! `CellId`s and reconstitute the authoritative ledger, so the verified executor's output can BE
//! the committed state.
//!
//! # The id seam
//!
//! The wire carries cells by a `u64` Nat (`marshal::cell_id_to_nat`'s codomain). The pre-state
//! snapshot assigned each referenced `CellId` a Nat via the SAME deterministic sorted scheme the
//! shadow marshaller uses (`lean_shadow::collect_id_map`). We invert that map (Nat → `CellId`) to
//! put the produced balances/nonces/fields back on the right cells. A produced cell whose Nat is
//! not in the inverse map is a marshaller gap (a created cell with a fresh, above-range Nat) and is
//! reported, never silently dropped.
//!
//! # Root computation (deliberately Rust-side)
//!
//! Lean produces the STATE; the EXISTING Rust hashing (`Ledger::root` / `hash_cell` =
//! `compute_canonical_state_commitment`) computes the commitment. We do NOT ask Lean to compute the
//! root — root-scheme unification is a separate later task. Here: Lean produces the cells, Rust
//! hashes them.
//!
//! # What the cell commitment binds — and the wire-model swap-gaps it reveals
//!
//! `compute_canonical_state_commitment` hashes, per cell:
//! `(balance, nonce, fields[0..8], permissions, verification_key, cap_root, lifecycle, program)`.
//! So for the Lean-produced ledger's `.root()` to equal the Rust-produced one, the reconstitution
//! must install the post-state of EVERY one of those that an effect can touch. The verified
//! `WireState` carries enough to reconstitute:
//!   * `balance` (via the per-asset `bal` side-table) — Transfer / Burn;
//!   * `nonce`, `fields[0..8]` (the cell record) — SetField / IncrementNonce;
//!   * `cap_root` (via the `caps` side-table → [`rebuild_capabilities`]) — best-effort, lossy.
//!
//! The `WireState` does NOT carry, and the reconstitution therefore CANNOT reproduce against a
//! mutated Rust post-state (these are genuine SWAP-GAPS, surfaced by the differential, NOT hidden):
//!   * **`lifecycle`** — the wire cell record has no lifecycle field. CellSeal / CellUnseal /
//!     CellDestroy mutate `lifecycle` in Rust → `.root()` diverges. The reconstitution carries the
//!     template lifecycle FORWARD (unchanged), so the divergence is exact and detectable.
//!   * **`permissions`** — the wire `setperms` arm carries a collapsed scalar; the produced
//!     `WireState` does not echo the full `Permissions` struct, so SetPermissions diverges.
//!   * **`verification_key`** — likewise, `setvk` carries a collapsed scalar.
//!   * **cap fidelity** — the wire `caps` model is `(target[, rights])` per edge; the Rust
//!     `cap_root` hashes `(target, slot, permissions, breadstuff, expires_at, allowed_effects)`, so
//!     a real GrantCapability's `cap_root` diverges (see [`rebuild_capabilities`]).
//!
//! Off-cell-commitment side-tables — escrows, queues, swiss, nullifiers, commitments — do NOT feed
//! `cell::Ledger::root()` at all (the Rust `TurnExecutor` keeps them OUTSIDE the `Ledger`), so an
//! escrow/queue/note effect's cell-ledger reconstitution agrees on `.root()` as long as it leaves
//! the touched CELLS' commitment fields unchanged — which they do (those effects are bal/structural,
//! not cell-scalar). The differential exercises a representative turn per family to pin exactly
//! which families round-trip and which are gaps.

use std::collections::HashMap;

use dregg_cell::permissions::AuthRequired;
use dregg_cell::{Cell, CellId, Ledger};
use dregg_lean_ffi::marshal::{Cap, WireState, WireValue};

use crate::executor::TurnExecutor;
use crate::lean_shadow::{self, ShadowHostCtx};
use crate::turn::Turn;
use crate::TurnResult;

/// Why a `WireState` could not be fully reconstituted into a `Ledger`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExtractError {
    /// A produced cell's wire Nat has no inverse in the pre-state id map (e.g. a freshly created
    /// cell whose Nat was assigned above the snapshot range). The verified executor edited a cell
    /// the marshaller cannot name back — a real marshaller gap, surfaced loudly.
    UnknownCellNat(u64),
    /// A produced cell's wire Nat maps to a `CellId` absent from the pre-state ledger (no template
    /// cell to carry the pk/token_id/permissions forward).
    NoTemplateCell { nat: u64, cell: CellId },
    /// A cell record carried a non-Int `balance`/`nonce` (the wire grammar should never emit this;
    /// fail-closed rather than coerce).
    NonIntScalar { nat: u64, field: &'static str },
    /// Driving the FFI / decoding the produced state failed.
    Ffi(String),
    /// The turn's forest was not fully marshallable (some effect has no wire arm), so there is no
    /// verified post-state to install.
    Ineligible,
}

impl std::fmt::Display for ExtractError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExtractError::UnknownCellNat(n) => {
                write!(f, "produced cell Nat {n} has no inverse in the pre-state id map (marshaller gap: a created/unmapped cell)")
            }
            ExtractError::NoTemplateCell { nat, cell } => {
                write!(f, "produced cell Nat {nat} -> {cell:?} has no pre-state template cell")
            }
            ExtractError::NonIntScalar { nat, field } => {
                write!(f, "produced cell Nat {nat} carried a non-Int `{field}`")
            }
            ExtractError::Ffi(e) => write!(f, "lean FFI / decode failed: {e}"),
            ExtractError::Ineligible => {
                write!(f, "turn forest not fully marshallable — no verified post-state to install")
            }
        }
    }
}

impl std::error::Error for ExtractError {}

/// Read a named `Int` field out of a cell record (returns `None` if absent or not an Int).
fn record_int(v: &WireValue, name: &str) -> Option<i128> {
    match v {
        WireValue::Record(fs) => fs.iter().find(|(k, _)| k == name).and_then(|(_, x)| match x {
            WireValue::Int(i) => Some(*i),
            _ => None,
        }),
        _ => None,
    }
}

/// Inverse of `lean_shadow::field_index_to_name` — map a wire field NAME back to its `fields[]`
/// slot index, or `None` for the scalar `balance`/`nonce` (handled separately) and any name that
/// is not a state slot.
fn field_name_to_index(name: &str) -> Option<usize> {
    match name {
        "balance" | "nonce" => None,
        "name" => Some(2),
        "owner" => Some(3),
        "expiry" => Some(4),
        "revoked" => Some(5),
        "target" => Some(6),
        other => other
            .strip_prefix("field_")
            .and_then(|n| n.parse::<usize>().ok()),
    }
}

/// Inverse of `lean_shadow::field_to_i128`: write the low 64 bits of an `i128` into the canonical
/// big-endian slot (`bytes[24..32]`).
fn i128_to_field(v: i128) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&(v as u64).to_be_bytes());
    out
}

/// Build the inverse id map (wire Nat → `CellId`) from the pre-state snapshot's id map.
fn invert_id_map(id_map: &HashMap<CellId, u64>) -> HashMap<u64, CellId> {
    id_map.iter().map(|(cid, nat)| (*nat, *cid)).collect()
}

/// Rebuild a cell's `CapabilitySet` from the verified executor's produced `caps` side-table edges.
///
/// The wire `caps` carries, per holder, a list of `Cap` (`Null` / `Node(target)` /
/// `Endpoint(target, rights)`). The verified kernel's delegate/revoke effects mutate THIS table
/// (an edge is the holder's authority over `target`); to install the produced cap post-state we
/// rebuild the cell's c-list from the produced edges, resolving each `target` wire Nat back to a
/// real `CellId` via the inverse id map.
///
/// # The cap-fidelity swap-gap (surfaced, never papered)
///
/// The Rust `cap_root` (which feeds `Ledger::root()`) hashes the FULL `CapabilityRef`
/// — `(target, slot, permissions, breadstuff, expires_at, allowed_effects)`. The wire `caps`
/// model carries ONLY `(target[, rights])` per edge; it drops the per-cap `slot` numbering,
/// `breadstuff`, `expires_at`, and `allowed_effects`. So a rebuilt cap set canonically hashes to
/// the SAME `cap_root` as the Rust one ONLY when the Rust caps are all bare `node`-shaped edges
/// with `AuthRequired::None`, no breadstuff/expiry/facet, AND the slot numbering coincides
/// (slot = insertion order). For a real `GrantCapability` (which grants `cap.permissions` at a
/// FRESH slot, possibly with a breadstuff) the rebuilt `cap_root` DIVERGES — a genuine swap-gap
/// (the wire cap model is lossier than the cell commitment), surfaced by the differential, never
/// hidden. `node`/`endpoint` rights both map to `AuthRequired::None` (full authority); the wire
/// `Auth` rights list does not map onto the `AuthRequired` lattice (another characterised gap).
///
/// An edge whose `target` wire Nat has no inverse (an above-snapshot fresh id) is reported.
fn rebuild_capabilities(
    edges: &[Cap],
    inv_id_map: &HashMap<u64, CellId>,
) -> Result<dregg_cell::capability::CapabilitySet, ExtractError> {
    let mut set = dregg_cell::capability::CapabilitySet::new();
    for cap in edges {
        let target_nat = match cap {
            Cap::Null => continue,
            Cap::Node(t) => *t,
            Cap::Endpoint(t, _rights) => *t,
        };
        let target = *inv_id_map
            .get(&target_nat)
            .ok_or(ExtractError::UnknownCellNat(target_nat))?;
        // Bare full-authority edge: the most the wire `caps` model carries.
        set.grant(target, AuthRequired::None);
    }
    Ok(set)
}

/// THE EXTRACTOR. Reconstitute a `cell::Ledger` from a verified-executor-produced `WireState`.
///
/// `inv_id_map` inverts the pre-state Nat labelling; `template` is the pre-state ledger whose cells
/// carry the identity/permission/capability fields the wire does not (pk, token_id, permissions,
/// c-list, program). For each produced cell we clone its template and overwrite the
/// balance/nonce/state-fields the verified executor produced.
///
/// Cells present in the template but ABSENT from the produced state (the verified executor left
/// them out of its output cell list) are carried forward UNCHANGED — the kernel's `cellsOfState`
/// only re-emits the cells it was given, so an unlisted template cell is unedited, not deleted.
pub fn wire_state_to_ledger(
    ws: &WireState,
    inv_id_map: &HashMap<u64, CellId>,
    template: &Ledger,
) -> Result<Ledger, ExtractError> {
    let mut produced_ids = std::collections::HashSet::new();
    let mut out_cells: HashMap<CellId, Cell> = HashMap::new();

    // The CANONICAL asset-0 balance lives in the per-asset `bal` side-table, NOT the cell record's
    // `balance` field — the verified Transfer (`bal` action) mutates `recKExecAsset`'s `bal` map and
    // leaves the record scalar at its seed value (a real wire-model fact, see the module-level note).
    // `cell::CellState::balance` is the asset-0 holding, so we read it from `bal` (asset 0), and only
    // fall back to the record `balance` when a cell has no `bal` entry.
    let asset0_bal: HashMap<u64, i128> = ws
        .bal
        .iter()
        .filter(|(_, asset, _)| *asset == 0)
        .map(|(cell, _, amt)| (*cell, *amt))
        .collect();

    // The produced CAPS side-table, keyed by holder Nat. The verified delegate/revoke effects
    // mutate this table; we install the rebuilt c-list onto every holder cell so the produced cap
    // post-state (→ each cell's `cap_root` → the merkle root) is reconstituted, not dropped. (See
    // `rebuild_capabilities` for the cap-fidelity swap-gap this surfaces.)
    let mut caps_by_holder: HashMap<u64, &Vec<Cap>> = HashMap::new();
    for (holder, edges) in &ws.caps {
        caps_by_holder.insert(*holder, edges);
    }

    for (nat, value) in &ws.cells {
        let cell_id = *inv_id_map
            .get(nat)
            .ok_or(ExtractError::UnknownCellNat(*nat))?;
        produced_ids.insert(cell_id);

        // Start from the pre-state template so identity/permissions/c-list/program survive.
        let mut cell = template
            .get(&cell_id)
            .cloned()
            .ok_or(ExtractError::NoTemplateCell { nat: *nat, cell: cell_id })?;

        // nonce is carried as a named scalar Int field in the cell record.
        let nonce = record_int(value, "nonce")
            .ok_or(ExtractError::NonIntScalar { nat: *nat, field: "nonce" })?;
        // balance: prefer the authoritative asset-0 `bal` entry; fall back to the record scalar.
        let bal = asset0_bal.get(nat).copied().or_else(|| record_int(value, "balance")).ok_or(
            ExtractError::NonIntScalar { nat: *nat, field: "balance" },
        )?;
        cell.state.set_balance(bal.max(0) as u64);
        cell.state.set_nonce(nonce.max(0) as u64);

        // Any other named Int field maps to a `fields[]` slot.
        if let WireValue::Record(fs) = value {
            for (k, x) in fs {
                if let (Some(idx), WireValue::Int(i)) = (field_name_to_index(k), x) {
                    if idx < dregg_cell::state::STATE_SLOTS {
                        let _ = cell.state.set_field(idx, i128_to_field(*i));
                    }
                }
            }
        }

        // Install the produced c-list (cap_root → merkle root). A produced cell with NO `caps`
        // entry is taken to hold the EMPTY c-list (the kernel's `capsOfState` only carries a
        // holder when it has edges), so we rebuild from the (possibly empty) wire edge list.
        let empty: Vec<Cap> = Vec::new();
        let edges = caps_by_holder.get(nat).copied().unwrap_or(&empty);
        cell.capabilities = rebuild_capabilities(edges, inv_id_map)?;

        out_cells.insert(cell_id, cell);
    }

    // A holder that appears ONLY in the `caps` table (its scalar cell state was unchanged, so the
    // kernel did not re-emit it under `cells`) still had its c-list edited — install it onto the
    // template cell so the produced cap post-state is not silently dropped.
    for (holder_nat, edges) in &ws.caps {
        if produced_ids
            .iter()
            .any(|cid| inv_id_map.get(holder_nat) == Some(cid))
        {
            continue; // already handled in the cells loop
        }
        let Some(&cell_id) = inv_id_map.get(holder_nat) else {
            return Err(ExtractError::UnknownCellNat(*holder_nat));
        };
        let mut cell = template
            .get(&cell_id)
            .cloned()
            .ok_or(ExtractError::NoTemplateCell { nat: *holder_nat, cell: cell_id })?;
        cell.capabilities = rebuild_capabilities(edges, inv_id_map)?;
        produced_ids.insert(cell_id);
        out_cells.insert(cell_id, cell);
    }

    // Reconstitute the ledger: produced cells (edited) + template cells the executor did not list
    // (carried unchanged, since the kernel only re-emits the cells it was handed).
    let mut ledger = Ledger::new();
    for (id, cell) in template.iter() {
        if let Some(produced) = out_cells.get(id) {
            let _ = ledger.insert_cell(produced.clone());
        } else {
            let _ = ledger.insert_cell(cell.clone());
        }
    }
    // Any produced cell NOT in the template (should be impossible given UnknownCellNat guards the
    // Nat, but defend against a fresh template-absent id) is inserted directly.
    for (id, cell) in &out_cells {
        if template.get(id).is_none() {
            let _ = ledger.insert_cell(cell.clone());
        }
    }

    Ok(ledger)
}

/// Drive a turn through the VERIFIED Lean executor and reconstitute the authoritative `Ledger` from
/// the post-state it produces — the full state-producer path (install the verified executor's
/// output). Returns the reconstituted ledger AND the commit bit.
///
/// `pre_ledger` is the pre-state; `host` the node-fed admission context (clock/freeze/head/budget).
/// On a rollback the verified executor echoes the (unchanged) pre-state, so the reconstituted
/// ledger equals the pre-state — which is exactly the legacy executor's rollback behaviour.
pub fn execute_via_lean(
    turn: &Turn,
    pre_ledger: &Ledger,
    host: &ShadowHostCtx,
) -> Result<(Ledger, bool), ExtractError> {
    if !lean_shadow::forest_is_marshallable(turn) {
        return Err(ExtractError::Ineligible);
    }
    let pre = lean_shadow::build_pre_ledger(turn, pre_ledger);
    let shadow_state =
        lean_shadow::run_shadow_state(turn, &pre, host).map_err(ExtractError::Ffi)?;
    let inv = invert_id_map(&pre.id_map);
    let ledger = wire_state_to_ledger(&shadow_state.state, &inv, pre_ledger)?;
    Ok((ledger, shadow_state.verdict.committed))
}

/// Which executor produced the committed state, plus the verified-vs-Rust differential, for one
/// producer-mode commit.
#[derive(Debug, Clone)]
pub enum ProducerOutcome {
    /// The VERIFIED Lean executor PRODUCED the committed state (it was installed into `ledger`).
    /// `committed` is the Lean commit bit; `lean_root` / `rust_root` are the two producers'
    /// post-state roots and `agree` is whether the commit bits AND roots matched. A `false` `agree`
    /// is a REAL runtime differential finding — surfaced by the caller, never papered over.
    LeanProduced {
        committed: bool,
        agree: bool,
        lean_root: [u8; 32],
        rust_root: [u8; 32],
        rust_committed: bool,
    },
    /// The turn was NOT eligible for the verified producer (its forest has an effect with no wire
    /// arm). Producer mode fell back to the Rust producer for THIS turn; `ledger` already carries
    /// the Rust post-state. `reason` says why the verified producer was skipped.
    Fallback { reason: ExtractError },
}

impl ProducerOutcome {
    /// `true` iff the verified producer ran AND its post-state diverged from the Rust differential.
    pub fn diverged(&self) -> bool {
        matches!(self, ProducerOutcome::LeanProduced { agree: false, .. })
    }
}

/// PRODUCER MODE (THE SWAP authority inversion). Make the VERIFIED Lean executor the authoritative
/// state PRODUCER for one finalized turn while keeping the receipt/proving machinery on the Rust
/// path, and run the Rust `TurnExecutor` as a demoted DIFFERENTIAL cross-check.
///
/// Mechanics — both producers run, on a SHARED admission decision:
///   1. Build the host admission ctx from `executor` (clock / freeze-set / chain-head / budget) —
///      the SAME ctx the Rust executor would build, so neither producer sees a different admission.
///   2. VERIFIED PRODUCER: drive the turn through the Lean FFI, reconstitute the post-state ledger.
///   3. RUST PRODUCER/RECEIPT: run `executor.execute(turn, ledger)` — this both mutates `ledger`
///      (producing the Rust post-state) AND yields the `TurnResult` (receipt / events) the caller
///      still needs. We snapshot the Rust post-state root for the differential.
///   4. INSTALL the verified post-state: overwrite `ledger` with the Lean-produced ledger, so the
///      COMMITTED state (and its merkle root) is the verified executor's output, not Rust's.
///   5. Return the Rust `TurnResult` (so receipt-chain append / proving / root attestation are
///      unchanged) AND a [`ProducerOutcome`] carrying the differential.
///
/// On INELIGIBILITY (an effect with no wire arm) the verified producer is skipped, `ledger` carries
/// the Rust post-state untouched, and [`ProducerOutcome::Fallback`] is returned — the safe behaviour
/// for a turn the wire model cannot yet represent.
///
/// IMPORTANT: a divergence ([`ProducerOutcome::diverged`]) is a real finding. This helper does NOT
/// reconcile it — it installs the VERIFIED post-state regardless (the verified executor is the
/// authority in producer mode) and reports the divergence for the caller to surface loudly.
pub fn produce_via_lean(
    executor: &TurnExecutor,
    turn: &Turn,
    ledger: &mut Ledger,
) -> (TurnResult, ProducerOutcome) {
    // Eligibility gate: if the verified producer cannot represent this turn, fall back to the Rust
    // producer entirely (it mutates `ledger` and yields the receipt as today).
    if !lean_shadow::forest_is_marshallable(turn) {
        let result = executor.execute(turn, ledger);
        return (result, ProducerOutcome::Fallback { reason: ExtractError::Ineligible });
    }

    let host = executor.build_shadow_host_ctx(turn, ledger);

    // VERIFIED PRODUCER: drive the turn through the Lean FFI and reconstitute the post-state from
    // the CURRENT pre-state (before the Rust executor mutates `ledger`).
    let lean = match execute_via_lean(turn, ledger, &host) {
        Ok(pair) => Some(pair),
        // A reconstitution error (e.g. a marshaller gap the eligibility gate did not catch) is a
        // real finding, but we must still commit SOME state — fall back to the Rust producer.
        Err(e) => {
            let result = executor.execute(turn, ledger);
            return (result, ProducerOutcome::Fallback { reason: e });
        }
    };
    let (mut lean_ledger, lean_committed) = lean.unwrap();
    let lean_root = lean_ledger.root();

    // RUST PRODUCER + RECEIPT: run the Rust executor in place — it mutates `ledger` to the Rust
    // post-state and yields the `TurnResult` (receipt/events) the commit path still consumes.
    let rust_result = executor.execute(turn, ledger);
    let rust_committed = matches!(rust_result, TurnResult::Committed { .. });
    let rust_root = ledger.root();

    let agree = lean_committed == rust_committed && lean_root == rust_root;

    // INSTALL THE VERIFIED POST-STATE: the COMMITTED ledger is now the verified executor's output.
    // On a Lean rejection the reconstituted ledger equals the pre-state, so this matches a verified
    // no-commit.
    *ledger = lean_ledger;

    (
        rust_result,
        ProducerOutcome::LeanProduced {
            committed: lean_committed,
            agree,
            lean_root,
            rust_root,
            rust_committed,
        },
    )
}
