//! lean_apply.rs — THE SWAP state-producer: reconstitute a `cell::Ledger` from the verified
//! Lean executor's produced `WireState`.
//!
//! # The authority inversion (Stage 0 / CRITICAL-1)
//!
//! On the COVERED set the verified Lean executor (`dregg_exec_full_forest_auth` / `execFullForestG`,
//! proven sorry-free) is the AUTHORITATIVE state producer AND verdict: `produce_via_lean` installs
//! its post-state and commit decision UNCONDITIONALLY, and demotes the legacy Rust `TurnExecutor` to
//! a checked REFERENCE that is verified AGAINST. A Lean↔Rust disagreement on a covered turn is a
//! surfaced RUST BUG (Rust is the artifact dregg2 replaces *because it is buggy*), NEVER a fallback
//! that lets the Rust path win. This is a refinement, not a differential: the verified producer's
//! output is what gets committed, not gated behind agreement with the thing it replaces.
//!
//! The enabling mechanism — which `dregg-lean-ffi/src/marshal.rs` named as "the biggest gap" — is a
//! `WireState → cell::Ledger` extractor. This module is that extractor: `dregg_lean_ffi`'s
//! `decode_shadow_state` keeps the post-state `WireState`, and here we map it back onto real
//! `CellId`s and reconstitute the authoritative ledger, so the verified executor's output IS the
//! committed state. The receipt the commit path chains is re-stamped to attest the installed (Lean)
//! root, so the receipt and the ledger agree on the authoritative post-state.
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
//! `(balance, nonce, fields[0..STATE_SLOTS], permissions, verification_key, cap_root, lifecycle, program)`.
//! So for the Lean-produced ledger's `.root()` to equal the Rust-produced one, the reconstitution
//! must install the post-state of EVERY one of those that an effect can touch. The verified
//! `WireState` carries enough to reconstitute:
//!   * `balance` (via the per-asset `bal` side-table) — Transfer / Burn;
//!   * `nonce`, `fields[0..STATE_SLOTS]` (the cell record) — SetField / IncrementNonce;
//!   * `cap_root` (via the `caps` side-table → [`rebuild_capabilities`]) — best-effort, lossy.
//!
//! The `WireState` does NOT carry several commitment-bound payloads — but for the SURVIVOR effects
//! whose payload comes from the TURN or the HOST (not from kernel state), the reconstitution
//! replays the exact deterministic mutation onto the template pre-state, GATED by the verified
//! kernel's commit decision (the same lever for all of them, see [`CapOp`] and [`StateOp`]):
//!   * **`lifecycle`** — the wire `lifecycle` table carries the DISCRIMINANT only; the Rust
//!     commitment binds the Sealed/Destroyed PAYLOAD (`reason_hash`/`sealed_at`,
//!     `death_certificate_hash`/`destroyed_at`). Those payloads are turn (`CellSeal { reason }`,
//!     the `CellDestroy` certificate) + host (`block_height`) data, so [`apply_state_ops`] replays
//!     `Cell::seal`/`Cell::unseal`/`Cell::destroy` byte-for-byte → CLOSED.
//!   * **`permissions`** / **`verification_key`** — the wire `setperms`/`setvk` arms carry a
//!     collapsed scalar; the full struct is turn-supplied, so the replay installs it exactly
//!     (`apply_set_permissions` / `apply_set_verification_key` mirrors) → CLOSED.
//!   * **MakeSovereign** — the verified `sovereignRebind` re-emits the cell as a commitment-only
//!     record (no readable scalars); Rust REMOVES the cell from `Ledger::cells`. The replay calls
//!     `Ledger::make_sovereign` on the reconstituted ledger (the same structural removal +
//!     `sovereign_commitments` insert) → CLOSED.
//!   * **RevokeDelegation** — a committing revoke bumps the PARENT's `delegation_epoch` and clears
//!     the CHILD's `delegation` snapshot (both commitment-bound); neither crosses the wire, but the
//!     mutation is fully deterministic from the turn (`bump_delegation_epoch` + `delegation = None`)
//!     → CLOSED.
//!   * **cap fidelity** — the wire `caps` model is `(target[, rights])` per edge; the Rust
//!     `cap_root` hashes `(target, slot, permissions, breadstuff, expires_at, allowed_effects)`. A
//!     GrantCapability/Introduce/AttenuateCapability leaf is reconstructed exactly by
//!     [`apply_cap_ops`] (see [`rebuild_capabilities`] for the lossy edge-only fallback).
//!
//! Off-cell-commitment side-tables — escrows, queues, swiss, nullifiers, commitments — do NOT feed
//! `cell::Ledger::root()` at all (the Rust `TurnExecutor` keeps them OUTSIDE the `Ledger`), so an
//! escrow/queue/note effect's cell-ledger reconstitution agrees on `.root()` as long as it leaves
//! the touched CELLS' commitment fields unchanged — which they do (those effects are bal/structural,
//! not cell-scalar). The differential exercises a representative turn per family to pin exactly
//! which families round-trip and which are gaps.

use std::collections::HashMap;

use dregg_cell::capability::CapabilityRef;
use dregg_cell::lifecycle::DeathCertificate;
use dregg_cell::permissions::AuthRequired;
use dregg_cell::{Cell, CellId, Ledger, Permissions, VerificationKey};
use dregg_lean_ffi::marshal::{Cap, WireState, WireValue};

use crate::TurnResult;
use crate::action::Effect;
use crate::executor::TurnExecutor;
use crate::forest::CallTree;
use crate::lean_shadow::{self, ShadowHostCtx};
use crate::turn::Turn;

/// A deterministic capability-set mutation a committed turn applies to ONE holder cell's c-list.
///
/// # The cap-fidelity lever (root-gap close)
///
/// The verified Lean kernel models a cell's c-list as an EDGE SET (`caps : holder → List Cap`,
/// each `Cap::Node(target)` an authority edge). Its verified gates DECIDE the commit bit — the
/// delegator must HOLD the edge (`recKDelegate`), the attenuation must be a monotone narrowing,
/// the introducer must hold the recipient + target edges. But the EDGE model does not carry the
/// full 7-field leaf the cell's `cap_root` (= `compute_canonical_capability_root`) binds:
/// `(slot, target, permissions, breadstuff, expires_at, allowed_effects)`.
///
/// The leaf-field VALUES of a grant/attenuate/introduce are not kernel state — they are fully
/// determined by the TURN (the `GrantCapability { cap }` parameters, the `AttenuateCapability`
/// narrowing, the `Introduce` permissions + host expiry) and the grantee's deterministic next
/// slot. So we reconstruct the EXACT post-state c-list by replaying the turn's cap mutation onto
/// the pre-state c-list — GATED by the kernel's verified commit decision. The kernel proves the
/// mutation was AUTHORIZED (non-amplification / production-authority); we apply the authorized,
/// deterministic leaf write that mirrors `executor::apply` byte-for-byte. The reconstituted
/// `cap_root` therefore EQUALS the Rust producer's, closing the cap-fidelity root-gap.
///
/// Only applied when the kernel COMMITTED — a rejected cap turn leaves the c-list untouched (the
/// non-vacuous tooth: a cross-cell grant the delegator cannot back, or a non-monotone attenuation,
/// is rejected by BOTH executors and the c-list does not move).
#[derive(Debug, Clone)]
pub enum CapOp {
    /// `GrantCapability { from, to, cap }` — install `cap` into `to`'s c-list at its next slot
    /// (mirrors `apply_grant_capability`'s `to_cell.capabilities.grant_ref(cap)`).
    Grant { to: CellId, cap: CapabilityRef },
    /// `Introduce { recipient, target, permissions }` — install a cap over `target` into
    /// `recipient`'s c-list at its next slot with the host-derived `expires_at` (mirrors
    /// `apply_introduce`'s `grant_with_expiry(target, permissions, block_height + lifetime)`).
    Introduce {
        recipient: CellId,
        target: CellId,
        permissions: AuthRequired,
        expires_at: u64,
    },
    /// `AttenuateCapability { cell, slot, … }` — narrow `cell`'s `slot` in place (mirrors
    /// `apply_attenuate_capability`'s `attenuate_in_place`).
    Attenuate {
        cell: CellId,
        slot: u32,
        narrower_permissions: AuthRequired,
        narrower_effects: Option<dregg_cell::EffectMask>,
        narrower_expiry: Option<u64>,
    },
}

impl CapOp {
    /// The holder cell whose c-list this op edits — the cell whose `cap_root` moves.
    fn holder(&self) -> CellId {
        match self {
            CapOp::Grant { to, .. } => *to,
            CapOp::Introduce { recipient, .. } => *recipient,
            CapOp::Attenuate { cell, .. } => *cell,
        }
    }
}

/// Collect the deterministic c-list mutations every cap effect in `turn` performs, resolving the
/// host-derived `expires_at` for `Introduce` from `intro_expiry` (= `block_height +
/// max_introduction_lifetime`, the value `apply_introduce` stamps). Walked in forest order so the
/// replay matches the executor's left-to-right effect order (slot assignment is order-sensitive).
fn collect_cap_ops(turn: &Turn, intro_expiry: u64) -> Vec<CapOp> {
    fn walk(tree: &CallTree, intro_expiry: u64, out: &mut Vec<CapOp>) {
        for eff in &tree.action.effects {
            match eff {
                Effect::GrantCapability { to, cap, .. } => {
                    out.push(CapOp::Grant {
                        to: *to,
                        cap: cap.clone(),
                    });
                }
                Effect::Introduce {
                    recipient,
                    target,
                    permissions,
                    ..
                } => {
                    out.push(CapOp::Introduce {
                        recipient: *recipient,
                        target: *target,
                        permissions: permissions.clone(),
                        expires_at: intro_expiry,
                    });
                }
                Effect::AttenuateCapability {
                    cell,
                    slot,
                    narrower_permissions,
                    narrower_effects,
                    narrower_expiry,
                } => {
                    out.push(CapOp::Attenuate {
                        cell: *cell,
                        slot: *slot,
                        narrower_permissions: narrower_permissions.clone(),
                        narrower_effects: *narrower_effects,
                        narrower_expiry: *narrower_expiry,
                    });
                }
                _ => {}
            }
        }
        for c in &tree.children {
            walk(c, intro_expiry, out);
        }
    }
    let mut out = Vec::new();
    for r in &turn.call_forest.roots {
        walk(r, intro_expiry, &mut out);
    }
    out
}

/// A deterministic non-cap commitment-field mutation a committed turn applies to a cell — the
/// SURVIVOR-effect root-gap close (the same lever as [`CapOp`], extended to four more families).
///
/// # The lever
///
/// For each of these effects the value the wire model DROPS is not kernel state — it comes from
/// the TURN (`CellSeal { reason }`, the `CellDestroy` certificate, the full `Permissions` /
/// `VerificationKey` structs) or the HOST (`block_height` stamps `sealed_at`), or it is a fully
/// deterministic structural move (`MakeSovereign`'s removal, `RevokeDelegation`'s epoch bump).
/// The verified kernel DECIDES the commit bit; when it committed, we replay the exact mutation the
/// Rust arm performs onto the template (pre-state) cell, byte-for-byte with `executor::apply`:
///
///   * `Seal`    → `Cell::seal(reason_hash, sealed_at)`        (apply.rs `apply_cell_seal`)
///   * `Unseal`  → `Cell::unseal()`                            (apply.rs `apply_cell_unseal`;
///     collected so a seal→unseal SEQUENCE within one turn replays in forest order)
///   * `Destroy` → `Cell::destroy(&certificate)`               (apply.rs `apply_cell_destroy`;
///     the FULL turn-supplied certificate — the wire `death_cert` table carries only the low 64
///     bits of the hash, which the replay deliberately does NOT use)
///   * `SetPermissions`     → `cell.permissions = new_permissions` (apply.rs `apply_set_permissions`)
///   * `SetVerificationKey` → `cell.verification_key = new_vk`     (apply.rs
///     `apply_set_verification_key`, including its blake3 integrity refusal)
///   * `MakeSovereign`      → `Ledger::make_sovereign(cell)`       (apply.rs `apply_make_sovereign`;
///     replayed at ledger-build time — the removal is structural, not per-cell)
///   * `RevokeDelegation`   → parent `bump_delegation_epoch()` + child `delegation = None`
///     (apply.rs `apply_revoke_delegation`)
///
/// Only applied when the kernel COMMITTED — a rejected turn leaves every field at its pre-state
/// (matching the Rust rollback), which is the non-vacuous tooth: an unauthorized seal/destroy/
/// setperm is rejected by BOTH executors and the field does not move.
#[derive(Debug, Clone)]
pub enum StateOp {
    /// `CellSeal { target, reason }` — Live/Archived → `Sealed { reason_hash, sealed_at }`.
    /// `reason_hash` is the turn's `reason`; `sealed_at` is the HOST block height (the value
    /// `apply_cell_seal` stamps via `self.block_height`).
    Seal {
        target: CellId,
        reason_hash: [u8; 32],
        sealed_at: u64,
    },
    /// `CellUnseal { target }` — Sealed → Live (payload-free; collected so lifecycle sequences
    /// replay in the executor's forest order).
    Unseal { target: CellId },
    /// `CellDestroy { target, certificate }` — any non-terminal → `Destroyed { hash, at }`, both
    /// derived from the FULL turn-supplied certificate (`certificate_hash()` /
    /// `destroyed_at_height`), never the lossy low-64 wire value.
    Destroy {
        target: CellId,
        certificate: DeathCertificate,
    },
    /// `SetPermissions { cell, new_permissions }` — install the full turn-supplied 8-field struct.
    SetPermissions {
        cell: CellId,
        new_permissions: Permissions,
    },
    /// `SetVerificationKey { cell, new_vk }` — install the turn-supplied VK (or clear it).
    SetVerificationKey {
        cell: CellId,
        new_vk: Option<VerificationKey>,
    },
    /// `MakeSovereign { cell }` — remove the cell from `Ledger::cells` and park its state
    /// commitment in `sovereign_commitments` (the structural ledger move).
    MakeSovereign { cell: CellId },
    /// `RevokeDelegation { child }` — bump the PARENT (= the action target) `delegation_epoch`
    /// and clear the child's `delegation` snapshot.
    RevokeDelegation { parent: CellId, child: CellId },
    /// `RefreshDelegation { child, snapshot }` — a SELF-refresh (`child == action target`):
    /// re-arm the child's `delegation` snapshot from its PARENT's CURRENT c-list. The mutation is
    /// fully deterministic from the pre-state (parent = `child.delegate`, the snapshot = the parent's
    /// live capabilities), gated on the verified commit. Mirrors `apply_refresh_delegation`.
    RefreshDelegation {
        child: CellId,
        /// The snapshot commitment the effect DECLARES (bound into `effects_hash`). The replay
        /// derives the genuine commitment from the parent's live c-list and only installs the
        /// snapshot when they match — the same forge antibody `apply_refresh_delegation` enforces.
        declared_snapshot: [u8; 32],
        /// The host wall-clock the snapshot's `refreshed_at` is stamped with (`self.current_timestamp`).
        now: u64,
    },
}

impl StateOp {
    /// The cells whose commitment fields this op edits (both parent and child for a revoke).
    fn touched(&self) -> Vec<CellId> {
        match self {
            StateOp::Seal { target, .. }
            | StateOp::Unseal { target }
            | StateOp::Destroy { target, .. } => vec![*target],
            StateOp::SetPermissions { cell, .. }
            | StateOp::SetVerificationKey { cell, .. }
            | StateOp::MakeSovereign { cell } => vec![*cell],
            StateOp::RevokeDelegation { parent, child } => vec![*parent, *child],
            // Only the CHILD's `delegation` snapshot moves; the parent's c-list is READ, not written.
            StateOp::RefreshDelegation { child, .. } => vec![*child],
        }
    }
}

/// Collect the deterministic non-cap commitment-field mutations every SURVIVOR effect in `turn`
/// performs (see [`StateOp`]). `seal_height` is the host block height (`ShadowHostCtx.block_height`
/// = the executor's `self.block_height`), the value `apply_cell_seal` stamps as `sealed_at`.
///
/// Walked in forest order so the replay matches the executor's left-to-right effect order (a
/// seal→unseal sequence is order-sensitive). The lifecycle/sovereign arms in `executor::apply`
/// carry a STRUCTURAL guard (`target == action_target` — a cross-cell lifecycle/sovereign mutation
/// is rejected before any state moves), so an effect violating it is NOT collected: Rust rolls the
/// turn back, and if the verified kernel nevertheless commits, the commit-bit mismatch surfaces as
/// a `CoveredDivergence` (conservative, keeps Rust) rather than a fabricated replay.
fn collect_state_ops(turn: &Turn, seal_height: u64, refresh_now: u64) -> Vec<StateOp> {
    fn walk(tree: &CallTree, seal_height: u64, refresh_now: u64, out: &mut Vec<StateOp>) {
        let action_target = tree.action.target;
        for eff in &tree.action.effects {
            match eff {
                Effect::CellSeal { target, reason } if *target == action_target => {
                    out.push(StateOp::Seal {
                        target: *target,
                        reason_hash: *reason,
                        sealed_at: seal_height,
                    });
                }
                Effect::CellUnseal { target } if *target == action_target => {
                    out.push(StateOp::Unseal { target: *target });
                }
                Effect::CellDestroy {
                    target,
                    certificate,
                } if *target == action_target => {
                    out.push(StateOp::Destroy {
                        target: *target,
                        certificate: certificate.clone(),
                    });
                }
                Effect::SetPermissions {
                    cell,
                    new_permissions,
                } => {
                    out.push(StateOp::SetPermissions {
                        cell: *cell,
                        new_permissions: new_permissions.clone(),
                    });
                }
                Effect::SetVerificationKey { cell, new_vk } => {
                    out.push(StateOp::SetVerificationKey {
                        cell: *cell,
                        new_vk: new_vk.clone(),
                    });
                }
                Effect::MakeSovereign { cell } if *cell == action_target => {
                    out.push(StateOp::MakeSovereign { cell: *cell });
                }
                Effect::RevokeDelegation { child } => {
                    out.push(StateOp::RevokeDelegation {
                        parent: action_target,
                        child: *child,
                    });
                }
                // Self-refresh only (`child == action target`); a cross-cell refresh is rejected by
                // both executors, so it is not collected (Rust rolls back; a verified commit would
                // surface as a commit-bit divergence, never a fabricated snapshot).
                Effect::RefreshDelegation { child, snapshot } if *child == action_target => {
                    out.push(StateOp::RefreshDelegation {
                        child: *child,
                        declared_snapshot: *snapshot,
                        now: refresh_now,
                    });
                }
                _ => {}
            }
        }
        for c in &tree.children {
            walk(c, seal_height, refresh_now, out);
        }
    }
    let mut out = Vec::new();
    for r in &turn.call_forest.roots {
        walk(r, seal_height, refresh_now, &mut out);
    }
    out
}

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
    /// The turn IS marshallable (the producer could run) but touches a characterized root-GAP
    /// effect whose Lean-reconstituted root provably DIVERGES from Rust (the wire model is lossier
    /// than the cell commitment). Outside the default-on COVERED set; falls back to Rust. `kind` is
    /// the first offending effect kind, so the fallback names exactly which gap blocked it.
    RootGap { kind: &'static str },
}

impl std::fmt::Display for ExtractError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExtractError::UnknownCellNat(n) => {
                write!(
                    f,
                    "produced cell Nat {n} has no inverse in the pre-state id map (marshaller gap: a created/unmapped cell)"
                )
            }
            ExtractError::NoTemplateCell { nat, cell } => {
                write!(
                    f,
                    "produced cell Nat {nat} -> {cell:?} has no pre-state template cell"
                )
            }
            ExtractError::NonIntScalar { nat, field } => {
                write!(f, "produced cell Nat {nat} carried a non-Int `{field}`")
            }
            ExtractError::Ffi(e) => write!(f, "lean FFI / decode failed: {e}"),
            ExtractError::Ineligible => {
                write!(
                    f,
                    "turn forest not fully marshallable — no verified post-state to install"
                )
            }
            ExtractError::RootGap { kind } => {
                write!(
                    f,
                    "turn touches the characterized root-gap effect `{kind}` (Lean-reconstituted \
                     root provably diverges from Rust) — outside the swap-safe covered set, fell \
                     back to the Rust producer"
                )
            }
        }
    }
}

impl std::error::Error for ExtractError {}

/// Read a named `Int` field out of a cell record (returns `None` if absent or not an Int).
fn record_int(v: &WireValue, name: &str) -> Option<i128> {
    match v {
        WireValue::Record(fs) => fs
            .iter()
            .find(|(k, _)| k == name)
            .and_then(|(_, x)| match x {
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
/// (slot = insertion order). For the cap effects whose post-state leaf the wire EDGE model cannot
/// carry — `GrantCapability` / `Introduce` / `AttenuateCapability` — the exact leaf is reconstructed
/// instead by [`apply_cap_ops`] (the cap-fidelity lever, see [`CapOp`]): the wire-edge rebuild is
/// the FALLBACK for holders no committed cap-op touched (e.g. a `RevokeDelegation`'s edge set).
/// `node`/`endpoint` rights both map to `AuthRequired::None` (full authority); the wire `Auth`
/// rights list does not map onto the `AuthRequired` lattice (a residual for the edge-only path).
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

/// Replay the committed turn's capability mutations onto the reconstituted ledger so each touched
/// holder cell's c-list — and therefore its `cap_root` — is EXACT (the cap-fidelity root-gap close).
///
/// For every holder a `CapOp` touches we recompute its c-list from the TEMPLATE (pre-state) c-list
/// plus the deterministic, turn-specified mutation, mirroring `executor::apply` byte-for-byte:
///   * `Grant`     → `grant_ref(cap)`            (apply_grant_capability's faithful install)
///   * `Introduce` → `grant_with_expiry(target, permissions, expires_at)`
///   * `Attenuate` → `attenuate_in_place(slot, …)`
///
/// Ops replay in forest order (slot assignment is order-sensitive) and against the WORKING c-list
/// (so two grants onto the same holder land at consecutive slots, as the executor assigns them).
///
/// Applied ONLY when `committed` — a rejected cap turn leaves c-lists at their pre-state (matching
/// the Rust producer's rollback). The verified kernel decides `committed`; we apply the authorized,
/// deterministic leaf write. The result OVERRIDES the lossy wire-edge rebuild for these holders.
fn apply_cap_ops(
    out_cells: &mut HashMap<CellId, Cell>,
    template: &Ledger,
    cap_ops: &[CapOp],
    committed: bool,
) -> Result<(), ExtractError> {
    if !committed || cap_ops.is_empty() {
        return Ok(());
    }
    // Seed each touched holder's working c-list from the TEMPLATE (the exact pre-state c-list with
    // its real slots/permissions/breadstuff/expiry/mask) — not from the lossy wire edges.
    let mut touched: std::collections::HashSet<CellId> = std::collections::HashSet::new();
    for op in cap_ops {
        let holder = op.holder();
        if touched.insert(holder) {
            // Establish the holder's working cell: prefer an already-produced cell (so balance/
            // nonce/fields the verified executor produced survive), else the template cell.
            if let std::collections::hash_map::Entry::Vacant(e) = out_cells.entry(holder) {
                let cell = template
                    .get(&holder)
                    .cloned()
                    .ok_or(ExtractError::NoTemplateCell {
                        nat: u64::MAX,
                        cell: holder,
                    })?;
                e.insert(cell);
            }
            // Reset the working c-list to the EXACT pre-state (the template carries the real
            // pre-state caps; the wire-edge rebuild above may have lossily overwritten it).
            let template_caps = template
                .get(&holder)
                .map(|c| c.capabilities.clone())
                .unwrap_or_default();
            if let Some(cell) = out_cells.get_mut(&holder) {
                cell.capabilities = template_caps;
            }
        }
    }
    // Replay the mutations in forest order against the working c-lists.
    for op in cap_ops {
        let holder = op.holder();
        let cell = out_cells
            .get_mut(&holder)
            .ok_or(ExtractError::NoTemplateCell {
                nat: u64::MAX,
                cell: holder,
            })?;
        match op {
            CapOp::Grant { cap, .. } => {
                cell.capabilities.grant_ref(cap);
            }
            CapOp::Introduce {
                target,
                permissions,
                expires_at,
                ..
            } => {
                cell.capabilities
                    .grant_with_expiry(*target, permissions.clone(), *expires_at);
            }
            CapOp::Attenuate {
                slot,
                narrower_permissions,
                narrower_effects,
                narrower_expiry,
                ..
            } => {
                cell.capabilities.attenuate_in_place(
                    *slot,
                    narrower_permissions.clone(),
                    *narrower_effects,
                    *narrower_expiry,
                );
            }
        }
    }
    Ok(())
}

/// Replay the committed turn's non-cap commitment-field mutations onto the reconstituted ledger
/// (the SURVIVOR-effect root-gap close, see [`StateOp`]). The per-cell half of the lever:
/// lifecycle (seal/unseal/destroy), permissions, verification key, and the revoke epoch bump are
/// replayed here; the structural `MakeSovereign` removal is replayed at ledger-build time by
/// [`wire_state_to_ledger`] (it edits the cell SET, not a cell).
///
/// Like [`apply_cap_ops`], each touched cell's working state is seeded from the already-produced
/// cell (so balances/nonces/fields the verified executor produced survive) or the template, and its
/// c-list is RESET to the exact template (pre-state) c-list: none of these Rust arms edits the
/// c-list, but the verified kernel may (`revokeDelegationA` is the cap-graph `removeEdge`) and the
/// wire-edge rebuild is lossy — the template carries the true bytes. Runs BEFORE [`apply_cap_ops`]
/// so a same-turn cap mutation still lands on top.
///
/// Applied ONLY when `committed`; mutations whose Rust arm would REFUSE (seal on a terminal cell,
/// a mis-bound VK, a revoke of a non-delegated child, an epoch overflow) are skipped rather than
/// fabricated — Rust rolled the turn back, so the commit bits differ and the divergence surfaces
/// as a `CoveredDivergence` (conservative, keeps Rust), never a silently-installed forgery.
fn apply_state_ops(
    out_cells: &mut HashMap<CellId, Cell>,
    template: &Ledger,
    state_ops: &[StateOp],
    committed: bool,
) -> Result<(), ExtractError> {
    if !committed || state_ops.is_empty() {
        return Ok(());
    }
    // Seed each touched cell's working state; reset its c-list to the EXACT pre-state (see above).
    let mut touched: std::collections::HashSet<CellId> = std::collections::HashSet::new();
    for op in state_ops {
        for cell_id in op.touched() {
            if touched.insert(cell_id) {
                if let std::collections::hash_map::Entry::Vacant(e) = out_cells.entry(cell_id) {
                    let cell =
                        template
                            .get(&cell_id)
                            .cloned()
                            .ok_or(ExtractError::NoTemplateCell {
                                nat: u64::MAX,
                                cell: cell_id,
                            })?;
                    e.insert(cell);
                }
                let template_caps = template
                    .get(&cell_id)
                    .map(|c| c.capabilities.clone())
                    .unwrap_or_default();
                if let Some(cell) = out_cells.get_mut(&cell_id) {
                    cell.capabilities = template_caps;
                }
            }
        }
    }
    // Replay the mutations in forest order, mirroring the `executor::apply` arms byte-for-byte.
    for op in state_ops {
        match op {
            StateOp::Seal {
                target,
                reason_hash,
                sealed_at,
            } => {
                if let Some(cell) = out_cells.get_mut(target) {
                    // `apply_cell_seal` → `c.seal(reason, self.block_height)`; a refused
                    // transition (already sealed / terminal) made Rust roll back — skip.
                    let _ = cell.seal(*reason_hash, *sealed_at);
                }
            }
            StateOp::Unseal { target } => {
                if let Some(cell) = out_cells.get_mut(target) {
                    // `apply_cell_unseal` → `c.unseal()`; refused (not sealed) ⇒ Rust rolled back.
                    let _ = cell.unseal();
                }
            }
            StateOp::Destroy {
                target,
                certificate,
            } => {
                if let Some(cell) = out_cells.get_mut(target) {
                    // `apply_cell_destroy` → `c.destroy(certificate)`. `Cell::destroy` itself
                    // checks `certificate.cell_id == self.id` and binds the FULL
                    // `certificate_hash()` + `destroyed_at_height` — the same code path Rust runs.
                    let _ = cell.destroy(certificate);
                }
            }
            StateOp::SetPermissions {
                cell,
                new_permissions,
            } => {
                if let Some(c) = out_cells.get_mut(cell) {
                    // `apply_set_permissions` → `c.permissions = new_permissions.clone()`. The
                    // cross-cell authority legs (`check_cross_cell_permission`) are commit-bit
                    // legs: the verified `stateAuthB` gate decides; a Rust-only refusal surfaces
                    // as a commit-bit divergence, never a replayed write.
                    c.permissions = new_permissions.clone();
                }
            }
            StateOp::SetVerificationKey { cell, new_vk } => {
                // `apply_set_verification_key` REJECTS a VK whose declared `hash` is not
                // `blake3(data)` (audit P0 #69) — mirror the refusal: never install a mis-bound
                // VK into the reconstituted ledger (Rust rolled back; commit bits diverge).
                if let Some(vk) = new_vk {
                    if *blake3::hash(&vk.data).as_bytes() != vk.hash {
                        continue;
                    }
                }
                if let Some(c) = out_cells.get_mut(cell) {
                    c.verification_key = new_vk.clone();
                }
            }
            // Structural — replayed at ledger-build time (`wire_state_to_ledger`).
            StateOp::MakeSovereign { .. } => {}
            StateOp::RevokeDelegation { parent, child } => {
                // `apply_revoke_delegation`: gate on the PRE-STATE delegation edge
                // (`child.delegate == Some(parent)`), then bump the parent's `delegation_epoch`
                // (refusing on overflow — Rust returns NonceOverflow and rolls back) and clear
                // the child's `delegation` snapshot. The parent's `delegate` pointer and the
                // child's `delegate` pointer are NOT touched (Rust leaves both).
                let edge_held = template
                    .get(child)
                    .map(|c| c.delegate == Some(*parent))
                    .unwrap_or(false);
                if !edge_held {
                    continue; // Rust rejects (DelegationDenied) — no field moves.
                }
                let bumped = out_cells
                    .get_mut(parent)
                    .map(|p| p.state.bump_delegation_epoch())
                    .unwrap_or(false);
                if !bumped {
                    continue; // epoch overflow — Rust rejects (NonceOverflow), rolls back.
                }
                if let Some(c) = out_cells.get_mut(child) {
                    c.delegation = None;
                }
            }
            StateOp::RefreshDelegation {
                child,
                declared_snapshot,
                now,
            } => {
                // `apply_refresh_delegation`: a SELF-refresh re-arms the child's `delegation`
                // snapshot from the PARENT's CURRENT c-list. Resolve the parent from the pre-state
                // `child.delegate`; a child with no parent is rejected by Rust (the verified commit
                // would then surface a commit-bit divergence), so skip.
                let Some(parent_id) = template.get(child).and_then(|c| c.delegate) else {
                    continue;
                };
                let Some(parent_cell) = template.get(&parent_id) else {
                    continue; // parent absent from the pre-state — Rust rolls back (CellNotFound).
                };
                let new_snapshot: Vec<dregg_cell::CapabilityRef> =
                    parent_cell.capabilities.iter().cloned().collect();
                let new_epoch = parent_cell.state.delegation_epoch();
                // THE FORGE ANTIBODY (mirrors apply_refresh_delegation): the declared snapshot MUST
                // equal the genuine commitment over the parent's live c-list, else Rust refuses — so
                // the replay refuses too (no fabricated snapshot).
                let clist_bytes = postcard::to_allocvec(&new_snapshot).unwrap_or_default();
                let clist_commitment =
                    dregg_cell::DelegatedRef::compute_clist_commitment(&clist_bytes);
                if &clist_commitment != declared_snapshot {
                    continue;
                }
                // `max_staleness` is carried forward from the child's existing snapshot (or 0).
                let max_staleness = template
                    .get(child)
                    .and_then(|c| c.delegation.as_ref().map(|d| d.max_staleness))
                    .unwrap_or(0);
                if let Some(c) = out_cells.get_mut(child) {
                    c.delegation = Some(dregg_cell::DelegatedRef::new(
                        parent_id,
                        *child,
                        new_snapshot,
                        new_epoch,
                        *now,
                        max_staleness,
                        clist_commitment,
                        [0u8; 64],
                    ));
                }
            }
        }
    }
    Ok(())
}

/// THE EXTRACTOR. Reconstitute a `cell::Ledger` from a verified-executor-produced `WireState`.
///
/// `inv_id_map` inverts the pre-state Nat labelling; `template` is the pre-state ledger whose cells
/// carry the identity/permission/capability fields the wire does not (pk, token_id, permissions,
/// c-list, program). For each produced cell we clone its template and overwrite the
/// balance/nonce/state-fields the verified executor produced.
///
/// `cap_ops` are the deterministic cap mutations the committed turn performs (see [`CapOp`]); when
/// `committed`, [`apply_cap_ops`] replays them onto the touched holders' EXACT pre-state c-lists so
/// `cap_root` is byte-exact (the cap-fidelity root-gap close), overriding the lossy wire-edge
/// rebuild for those holders. `state_ops` are the non-cap commitment-field mutations (see
/// [`StateOp`]): lifecycle/permissions/vk/revoke-epoch replay per-cell ([`apply_state_ops`]);
/// the `MakeSovereign` structural removal replays here at ledger-build time.
///
/// Cells present in the template but ABSENT from the produced state (the verified executor left
/// them out of its output cell list) are carried forward UNCHANGED — the kernel's `cellsOfState`
/// only re-emits the cells it was given, so an unlisted template cell is unedited, not deleted.
pub fn wire_state_to_ledger(
    ws: &WireState,
    inv_id_map: &HashMap<u64, CellId>,
    template: &Ledger,
    cap_ops: &[CapOp],
    state_ops: &[StateOp],
    committed: bool,
) -> Result<Ledger, ExtractError> {
    let mut produced_ids = std::collections::HashSet::new();
    let mut out_cells: HashMap<CellId, Cell> = HashMap::new();

    // The cells a COMMITTED MakeSovereign rebinds. The verified `sovereignRebind` re-emits the
    // target as a commitment-ONLY record (`[(commitmentField, .dig …)]` — no readable
    // `balance`/`nonce` Ints), so the cells loop below must SKIP its record rather than fail-close
    // on the missing scalars; the cell is removed from the ledger at build time anyway (the
    // `Ledger::make_sovereign` replay), exactly as `apply_make_sovereign` removes it.
    let sovereign_removed: std::collections::HashSet<CellId> = if committed {
        state_ops
            .iter()
            .filter_map(|op| match op {
                StateOp::MakeSovereign { cell } => Some(*cell),
                _ => None,
            })
            .collect()
    } else {
        Default::default()
    };

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

    // The produced LIFECYCLE side-table, keyed by cell Nat (the wire `lifecycle` carries the
    // post-state discriminant 0=Live / 1=Sealed / 3=Destroyed; a Live cell carries NO entry — the
    // kernel's `cellNatsOfFun` drops zero, so "absent ⇒ Live"). `compute_canonical_state_commitment`
    // folds the cell's `lifecycle` in, so for the Lean-produced `.root()` to equal Rust's we must
    // install the produced discriminant onto the reconstituted cell.
    //
    // BYTE-FIDELITY: only `CellLifecycle::Live` has NO payload, so it is the only discriminant the
    // WIRE alone reconstitutes byte-exactly (it carries the discriminant, not
    // `reason_hash`/`sealed_at`/`destroyed_at`). A produced `Live` is installed directly. A
    // produced Sealed(1)/Destroyed(3) keeps the TEMPLATE lifecycle HERE — its full payload is then
    // replayed from the TURN+HOST data by [`apply_state_ops`] (the lifecycle root-gap close:
    // `Cell::seal(reason, block_height)` / `Cell::destroy(certificate)` on the kernel's committed
    // decision), so the commitment bytes match Rust's without fabricating an unbound payload. A
    // non-zero disc with NO collected lifecycle op (a pre-state Sealed/Destroyed cell the turn did
    // not transition) correctly keeps the template payload.
    let mut lifecycle_disc_by_nat: HashMap<u64, u64> = HashMap::new();
    for (cell_nat, disc) in &ws.lifecycle {
        lifecycle_disc_by_nat.insert(*cell_nat, *disc);
    }

    for (nat, value) in &ws.cells {
        let cell_id = *inv_id_map
            .get(nat)
            .ok_or(ExtractError::UnknownCellNat(*nat))?;
        // A committed-MakeSovereign target's record is the commitment-only rebind (no readable
        // scalars) — skip it; the `make_sovereign` replay below removes the cell structurally.
        if sovereign_removed.contains(&cell_id) {
            continue;
        }
        produced_ids.insert(cell_id);

        // Start from the pre-state template so identity/permissions/c-list/program survive.
        let mut cell = template
            .get(&cell_id)
            .cloned()
            .ok_or(ExtractError::NoTemplateCell {
                nat: *nat,
                cell: cell_id,
            })?;

        // nonce is carried as a named scalar Int field in the cell record.
        let nonce = record_int(value, "nonce").ok_or(ExtractError::NonIntScalar {
            nat: *nat,
            field: "nonce",
        })?;
        // balance: prefer the authoritative asset-0 `bal` entry; fall back to the record scalar.
        let bal = asset0_bal
            .get(nat)
            .copied()
            .or_else(|| record_int(value, "balance"))
            .ok_or(ExtractError::NonIntScalar {
                nat: *nat,
                field: "balance",
            })?;
        // THE EPOCH §5: the Rust balance is now SIGNED, so the Lean kernel's
        // ℤ balance (including a well's −supply) marshals FAITHFULLY — the
        // old `.max(0)` clamp silently zeroed negative wells. The i64 clamp
        // is a range artifact only (kernel balances never approach ±2^63).
        cell.state
            .set_balance(bal.clamp(i64::MIN as i128, i64::MAX as i128) as i64);
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

        // Install the produced LIFECYCLE discriminant (→ the cell commitment's `lifecycle` fold).
        // The wire carries the discriminant ONLY; `CellLifecycle::Live` (absent ⇒ disc 0) is the
        // single payload-free state, so we reconstitute it byte-exactly (CellUnseal: Sealed→Live).
        // A produced Sealed(1)/Destroyed(3) keeps the TEMPLATE lifecycle here; the full payload —
        // turn `reason`/certificate + host `block_height` — is replayed by `apply_state_ops`
        // below (the CellSeal/CellDestroy root-gap close), never fabricated from the bare disc.
        match lifecycle_disc_by_nat.get(nat).copied() {
            None | Some(0) => {
                cell.lifecycle = dregg_cell::lifecycle::CellLifecycle::Live;
            }
            Some(_) => { /* payload not wire-carried — template now, state-op replay below. */ }
        }

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
            .ok_or(ExtractError::NoTemplateCell {
                nat: *holder_nat,
                cell: cell_id,
            })?;
        cell.capabilities = rebuild_capabilities(edges, inv_id_map)?;
        produced_ids.insert(cell_id);
        out_cells.insert(cell_id, cell);
    }

    // SURVIVOR-EFFECT ROOT-GAP CLOSE: replay the committed turn's lifecycle/permissions/vk/
    // revoke-epoch mutations onto the touched cells' template pre-state. Runs BEFORE the cap
    // replay so a same-turn cap mutation still lands on top of the state-op's c-list reset.
    apply_state_ops(&mut out_cells, template, state_ops, committed)?;

    // CAP-FIDELITY ROOT-GAP CLOSE: replay the committed turn's Grant/Introduce/Attenuate mutations
    // onto the touched holders' EXACT pre-state c-lists, overriding the lossy wire-edge rebuild so
    // each touched cell's `cap_root` is byte-exact with the Rust producer's.
    apply_cap_ops(&mut out_cells, template, cap_ops, committed)?;
    for op in cap_ops {
        produced_ids.insert(op.holder());
    }

    // Reconstitute the ledger: start from a CLONE of the template (so off-merkle-root ledger state
    // — `sovereign_commitments`, witness sequences, registrations — survives the swap, exactly as
    // the in-place Rust producer preserves it) and overwrite the produced/replayed cells. Template
    // cells the executor did not list are thereby carried unchanged (the kernel's `cellsOfState`
    // only re-emits the cells it was given — an unlisted cell is unedited, not deleted).
    let mut ledger = template.clone();
    for (id, cell) in &out_cells {
        if let Some(slot) = ledger.get_mut(id) {
            *slot = cell.clone();
        } else {
            // A produced cell NOT in the template (should be impossible given UnknownCellNat
            // guards the Nat, but defend against a fresh template-absent id).
            let _ = ledger.insert_cell(cell.clone());
        }
    }

    // MAKE-SOVEREIGN STRUCTURAL REPLAY (the root-gap close for the cell-SET move): mirror
    // `apply_make_sovereign` → `Ledger::make_sovereign(cell)` — remove the cell from
    // `Ledger::cells` (its merkle leaf disappears, exactly as Rust's post-root drops it) and park
    // its state commitment in `sovereign_commitments`. A missing cell (already removed / never
    // present) made Rust roll back; the commit-bit divergence surfaces, so the failed replay is
    // ignored rather than fabricated. RESIDUAL (off-root, characterized): for a COMPOSITE turn
    // that mutates the cell and THEN makes it sovereign, the parked commitment is computed from
    // the template-seeded working cell (the rebound wire record is unreadable), so the
    // `sovereign_commitments` VALUE — never the merkle root — can lag the Rust one.
    if committed {
        for op in state_ops {
            if let StateOp::MakeSovereign { cell } = op {
                let _ = ledger.make_sovereign(cell);
            }
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
    let committed = shadow_state.verdict.committed;
    // The deterministic cap mutations this turn performs (Grant/Introduce/Attenuate). An
    // `Introduce` stamps `expires_at = block_height + max_introduction_lifetime` (the host fields),
    // matching `apply_introduce`. Applied ONLY when the kernel COMMITTED (`wire_state_to_ledger`).
    let intro_expiry = host.block_height.saturating_add(host.intro_lifetime);
    let cap_ops = collect_cap_ops(turn, intro_expiry);
    // The deterministic non-cap commitment-field mutations (lifecycle/permissions/vk/sovereign/
    // revoke-epoch — the SURVIVOR-effect root-gap close). A `CellSeal` stamps
    // `sealed_at = block_height` (the host clock), matching `apply_cell_seal`.
    let state_ops = collect_state_ops(turn, host.block_height, host.current_timestamp);
    let ledger = wire_state_to_ledger(
        &shadow_state.state,
        &inv,
        pre_ledger,
        &cap_ops,
        &state_ops,
        committed,
    )?;
    Ok((ledger, committed))
}

/// THE DENOTATIONAL DIFFERENTIAL leg used by [`crate::lean_shadow::maybe_shadow_turn`]: reconstitute
/// the verified Lean executor's FULL post-state from an already-run [`ShadowState`] and return its
/// `.root()` — the per-cell-state digest (balance / nonce / 8 fields / cap_root / lifecycle residue)
/// the shadow compares against the Rust executor's `post_state_hash`.
///
/// Unlike [`execute_via_lean`] this takes the pre-state as the captured [`lean_shadow::ShadowPreLedger`]
/// snapshot (the only pre-state the live shadow path retains; the mutable `ledger` it has is already
/// the POST-state) and the ALREADY-EXECUTED `ShadowState`, so it does NOT re-run the FFI. It builds a
/// template `Ledger` from the snapshotted pre-state cells, then runs the SAME reconstitution
/// (`wire_state_to_ledger` with the turn's deterministic cap/state ops) that `execute_via_lean` and
/// `produce_via_lean` use — so the root it returns is the genuine verified post-state root.
#[cfg(not(feature = "no-lean-link"))]
pub(crate) fn lean_post_state_root(
    turn: &Turn,
    pre: &lean_shadow::ShadowPreLedger,
    host: &ShadowHostCtx,
    shadow_state: &dregg_lean_ffi::ShadowState,
) -> Result<[u8; 32], ExtractError> {
    // The template ledger the reconstitution starts from = the snapshotted PRE-state cells (so
    // identity / permissions / c-list / program survive into the produced post-state, exactly as
    // `wire_state_to_ledger`'s template contract requires).
    let mut template = Ledger::new();
    for cell in pre.cells.values() {
        // A duplicate id cannot occur (the snapshot is keyed by CellId); ignore the (impossible)
        // already-exists error rather than fail the whole comparison.
        let _ = template.insert_cell(cell.clone());
    }

    let inv = invert_id_map(&pre.id_map);
    let committed = shadow_state.verdict.committed;
    let intro_expiry = host.block_height.saturating_add(host.intro_lifetime);
    let cap_ops = collect_cap_ops(turn, intro_expiry);
    let state_ops = collect_state_ops(turn, host.block_height, host.current_timestamp);
    let mut ledger = wire_state_to_ledger(
        &shadow_state.state,
        &inv,
        &template,
        &cap_ops,
        &state_ops,
        committed,
    )?;
    Ok(ledger.root())
}

/// Which executor produced the committed state, plus the verified-vs-Rust differential, for one
/// producer-mode commit.
#[derive(Debug, Clone)]
pub enum ProducerOutcome {
    /// THE AUTHORITY INVERSION (Stage 0 / CRITICAL-1). On the COVERED (root-agreeing) set the
    /// VERIFIED Lean executor is AUTHORITATIVE: its post-state and its commit VERDICT are installed
    /// UNCONDITIONALLY into `ledger`, and the legacy Rust `TurnExecutor` is demoted to a checked
    /// REFERENCE. `committed` is the AUTHORITATIVE (Lean) commit bit — the one the returned
    /// `TurnResult` and `ledger` reflect. `lean_root` is the authoritative post-state root;
    /// `rust_root` / `rust_committed` are the demoted reference's outputs.
    ///
    /// `rust_agreed` is whether the Rust reference reproduced the verified verdict (commit bit AND
    /// root). A `false` `rust_agreed` is a REAL Rust BUG surfaced as a finding — it does NOT change
    /// what was committed (Lean still won). The Rust executor is the artifact dregg2 exists to
    /// REPLACE because it is buggy; on the covered path a Lean↔Rust disagreement is, by definition,
    /// the Rust path being wrong, NEVER a reason to override the verified producer.
    LeanAuthoritative {
        committed: bool,
        rust_agreed: bool,
        lean_root: [u8; 32],
        rust_root: [u8; 32],
        rust_committed: bool,
    },
    /// The turn was NOT in the COVERED set for the default-on verified producer (either its forest
    /// has an effect with no wire arm, or it touches a characterized root-GAP effect whose
    /// Lean-reconstituted root provably diverges from Rust). Producer mode fell back to the Rust
    /// producer for THIS turn; `ledger` already carries the Rust post-state. `reason` says why the
    /// verified producer was skipped (so the fallback is never silent).
    ///
    /// This is the explicitly-FENCED uncovered boundary. Until the covered set is total (Stage 2's
    /// "empty the partition"), these shapes ride the legacy Rust path — a labeled, surfaced gap, not
    /// a silent Rust-authoritative-everywhere default.
    Fallback { reason: ExtractError },
}

impl ProducerOutcome {
    /// `true` iff the verified producer ran on the covered path AND the demoted Rust reference
    /// DISAGREED with the authoritative (Lean) verdict — i.e. a surfaced Rust BUG. Committed state
    /// is unaffected (Lean is authoritative); this only reports the differential finding.
    pub fn rust_bug_surfaced(&self) -> bool {
        matches!(
            self,
            ProducerOutcome::LeanAuthoritative {
                rust_agreed: false,
                ..
            }
        )
    }
}

/// PRODUCER MODE — THE AUTHORITY INVERSION (Stage 0 / CRITICAL-1). On the COVERED set the VERIFIED
/// Lean executor is the AUTHORITATIVE state producer AND verdict, installed UNCONDITIONALLY; the
/// legacy Rust `TurnExecutor` is demoted to a checked REFERENCE that is verified AGAINST, never an
/// override.
///
/// # Why "unconditional" is the whole point
///
/// The earlier shape ran both producers and installed the Lean post-state ONLY when its root matched
/// the Rust executor's — a DIFFERENTIAL, not a refinement. A verified producer that commits only
/// when it agrees with the *buggy* executor cannot tighten a wrong Rust accept that yields the same
/// root, cannot override a Rust reject, and is not the reason to trust the transition. Stage 0
/// inverts the authority: on a covered turn the Lean verdict (commit bit + post-state) is what gets
/// committed, and a Lean↔Rust disagreement is — by definition, since Rust is the artifact dregg2
/// replaces *because it is buggy* — a surfaced RUST BUG, not a fallback to Rust.
///
/// # Mechanics
///   1. Build the host admission ctx from `executor` (clock / freeze-set / chain-head / budget) —
///      the SAME ctx the Rust reference uses, so the comparison is meaningful.
///   2. AUTHORITATIVE PRODUCER: drive the turn through the Lean FFI from the CURRENT pre-state
///      (before Rust mutates `ledger`); reconstitute the post-state ledger + the verified commit bit.
///   3. REFERENCE: run `executor.execute(turn, ledger)` — it mutates `ledger` to the Rust
///      post-state AND yields a `TurnResult` (receipt/events substrate). We snapshot the Rust root
///      and commit bit as the demoted cross-check.
///   4. INSTALL THE AUTHORITATIVE VERDICT — UNCONDITIONALLY on the covered path:
///        * Lean COMMITTED → `*ledger = lean_ledger`; the returned `TurnResult` is a `Committed`
///          whose receipt's `post_state_hash` is the AUTHORITATIVE (Lean) root. When Rust also
///          committed we reuse its receipt (re-stamping the post-state hash to Lean's root, which
///          equals it on agreement and overrides it on a Rust bug). When Rust REJECTED but Lean
///          committed, we still commit Lean and surface the Rust bug.
///        * Lean REJECTED → leave `ledger` at the pre-state (a verified rejection is NO state edit)
///          and return `Rejected`. When Rust had COMMITTED, that Rust accept is OVERRIDDEN by the
///          verified veto ([`TurnError::LeanShadowVeto`]) and the surfaced bug is the Rust accept.
///
/// # Coverage boundary (be precise; fail-closed off it)
///
/// "Covered" = [`lean_shadow::forest_is_root_agreeing`]: marshallable AND every effect is in the
/// swap-safe `producer_root_agreeing_effects` set, where the Lean-reconstituted `.root()` provably
/// equals Rust's (pinned by the `lean_state_producer_*` differentials). For ANY uncovered shape — a
/// characterized root-GAP effect (Refusal / ReceiptArchive / …) or an unmappable effect — we do NOT
/// silently let Rust be authoritative-everywhere: we take the legacy Rust path but FENCE it with an
/// explicit, surfaced [`ProducerOutcome::Fallback`] naming the precise reason. That uncovered set is
/// the named, burning-down partition (Stage 2), not a hidden Rust default.
pub fn produce_via_lean(
    executor: &TurnExecutor,
    turn: &Turn,
    ledger: &mut Ledger,
) -> (TurnResult, ProducerOutcome) {
    // COVERAGE GATE: the verified producer is AUTHORITATIVE only for the root-agreeing (swap-safe)
    // set. A turn that is unmappable OR touches a characterized root-gap effect is FENCED on the
    // legacy Rust path — surfaced as a `Fallback` with a precise reason, never a silent commit of a
    // Lean root known to disagree with the rest of the chain (and never a silent Rust-everywhere).
    if !lean_shadow::forest_is_root_agreeing(turn) {
        let result = executor.execute(turn, ledger);
        let reason = if lean_shadow::forest_is_marshallable(turn) {
            // Marshallable but NOT root-agreeing ⇒ a characterized root-GAP effect. Name the first
            // offending kind so the fence is honest about WHICH gap blocked the producer.
            ExtractError::RootGap {
                kind: lean_shadow::first_root_gap_kind(turn).unwrap_or("unknown"),
            }
        } else {
            ExtractError::Ineligible
        };
        return (result, ProducerOutcome::Fallback { reason });
    }

    let host = executor.build_shadow_host_ctx(turn, ledger);

    // AUTHORITATIVE PRODUCER: drive the turn through the Lean FFI and reconstitute the post-state
    // from the CURRENT pre-state (before the Rust reference mutates `ledger`).
    let lean = match execute_via_lean(turn, ledger, &host) {
        Ok(pair) => pair,
        // A reconstitution error (e.g. a marshaller gap the eligibility gate did not catch) means we
        // have no authoritative verdict to install — FENCE this turn onto the Rust path and surface
        // the error, rather than committing an unverified Rust root as if it were covered.
        Err(e) => {
            let result = executor.execute(turn, ledger);
            return (result, ProducerOutcome::Fallback { reason: e });
        }
    };
    let (mut lean_ledger, lean_committed) = lean;
    let lean_root = lean_ledger.root();

    // PRE-STATE SNAPSHOT: capture the pre-state (and its root) BEFORE the Rust reference mutates
    // `ledger`. The verdict is already known (`lean_committed`), so we only pay the clone when the
    // authoritative verdict is REJECT — the branch that must restore EXACTLY the pre-state a verified
    // rejection mandates (a verified reject = no state edit). `pre_root` (cheap) is always taken for
    // the synthesized-receipt `pre_state_hash`. Mirrors the strict-veto snapshot in
    // `executor::execute_with_shadow`, but lazily — the agreeing commit path pays no clone.
    let pre_root = ledger.root();
    let pre_snapshot = if lean_committed {
        None
    } else {
        Some(ledger.clone())
    };

    // REFERENCE: run the Rust executor in place — it mutates `ledger` to the Rust post-state and
    // yields the `TurnResult` (receipt/events) that is the commit-path substrate. This is the
    // DEMOTED cross-check, not the authority.
    let rust_result = executor.execute(turn, ledger);
    let rust_committed = matches!(rust_result, TurnResult::Committed { .. });
    let rust_root = ledger.root();
    let rust_agreed = lean_committed == rust_committed && lean_root == rust_root;

    let outcome = ProducerOutcome::LeanAuthoritative {
        committed: lean_committed,
        rust_agreed,
        lean_root,
        rust_root,
        rust_committed,
    };

    if lean_committed {
        // INSTALL THE VERIFIED POST-STATE UNCONDITIONALLY — the authoritative verdict is COMMIT.
        *ledger = lean_ledger;
        // Build the authoritative `TurnResult`. The receipt MUST attest the installed (Lean) root,
        // so we re-stamp `post_state_hash` to `lean_root` (equal to the Rust root on agreement; the
        // authoritative override on a surfaced Rust bug). When Rust REJECTED, there is no Rust
        // receipt to carry — the verified COMMIT overrides the Rust reject — so we synthesize the
        // authoritative receipt from the turn + installed ledger.
        let result =
            authoritative_committed_result(turn, pre_root, lean_root, executor, rust_result);
        (result, outcome)
    } else {
        // The authoritative verdict is REJECT: a verified rejection is NO state edit. The Rust
        // reference already mutated `ledger` to its (possibly committed) post-state; restore the
        // exact pre-state the verified rejection mandates. `pre_snapshot` is `Some` here (taken
        // exactly on the `!lean_committed` path above).
        *ledger = pre_snapshot.expect("pre-state snapshot is taken on the verified-reject path");
        let result = match rust_result {
            // Rust agreed (also rejected): carry its rejection reason unchanged.
            r @ TurnResult::Rejected { .. } => r,
            // Rust ACCEPTED where the verified kernel REJECTED — the verified veto overrides the
            // buggy Rust accept (the kernel can only TIGHTEN; never launder a wrong accept).
            _ => TurnResult::Rejected {
                reason: crate::error::TurnError::LeanShadowVeto,
                at_action: vec![],
            },
        };
        (result, outcome)
    }
}

/// Build the AUTHORITATIVE `Committed` `TurnResult` for the inversion's commit branch: the verified
/// Lean executor committed, `ledger` now holds the installed Lean post-state, and `lean_root` is its
/// authoritative root.
///
///   * `rust_result == Committed{..}` (Rust agreed, or disagreed only on the root): reuse the Rust
///     receipt/delta — it is the correct receipt substrate — but RE-STAMP its `post_state_hash` to
///     the authoritative `lean_root` so the receipt attests the state actually committed. On
///     agreement this is a no-op; on a surfaced Rust root-bug it is the authoritative override.
///   * `rust_result` is a reject/expired/pending (Rust DISAGREED on the commit bit): there is no
///     Rust receipt — the verified COMMIT overrides the buggy Rust non-commit — so synthesize the
///     receipt from the turn + the pre-state root via the executor's receipt builder, with
///     `post_state_hash = lean_root`.
fn authoritative_committed_result(
    turn: &Turn,
    pre_root: [u8; 32],
    lean_root: [u8; 32],
    executor: &TurnExecutor,
    rust_result: TurnResult,
) -> TurnResult {
    match rust_result {
        TurnResult::Committed {
            ledger_delta,
            receipt,
            computrons_used,
        } => {
            // Re-stamp `post_state_hash` to the authoritative installed (Lean) root and re-sign.
            // (`restamp_committed_receipt` lives on the executor so it can re-sign with the
            // executor's key; equal to Rust's root on agreement, the override on a surfaced bug.)
            let receipt = executor.restamp_committed_receipt(receipt, lean_root);
            TurnResult::Committed {
                ledger_delta,
                receipt,
                computrons_used,
            }
        }
        _ => {
            // Rust did not commit; build the authoritative receipt for the verified commit.
            executor.build_producer_committed_result(turn, pre_root, lean_root)
        }
    }
}
