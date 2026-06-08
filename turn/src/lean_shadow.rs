//! Optional Lean FFI shadow execution — compares Rust commit decisions against the
//! verified Lean kernel without affecting [`crate::turn::TurnResult`].
//!
//! Enabled when `DREGG_LEAN_SHADOW=1` and `dregg_lean_ffi::lean_available()`.
//!
//! # Scope: full multi-action FORESTS (no longer single-`SetField`)
//!
//! The shadow marshals the WHOLE Rust call-forest through the gated FFI
//! `shadow_exec_full_forest_auth`. A turn's forest is pre-order flattened into a chain
//! of wire actions; the chain is carried as a single root `WForest` whose tail nodes are
//! `null`-cap delegation children — the Lean executor runs `null`-cap children
//! SEQUENTIALLY against the evolving state WITHOUT invoking the cap-handoff gate
//! (`execFullChildrenA`'s `capTarget = none` branch), which is exactly "run these actions
//! in order, all-or-nothing." That faithfully models the Rust executor's pre-order forest
//! walk for the `DelegationMode::None` default (every node acts under its own authority).
//!
//! A turn is shadowed only when EVERY effect maps to a wire action and every referenced
//! cell has a ledger snapshot — anything unmappable makes the turn INELIGIBLE (skipped,
//! never silently mis-encoded; a dropped effect is worse than no shadow at all).
//!
//! The credential WHO-leg crosses faithfully: `Signature`/`Custom`/`Token`/`Bearer`/…
//! carry their FULL 256-bit digests via `marshal::Digest` (not a zeroed low-u64), so the
//! gate is genuinely exercised through the wire.

use std::cell::RefCell;
use std::collections::HashMap;

#[cfg(feature = "lean-shadow")]
use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, CellId, Ledger};

#[cfg(feature = "lean-shadow")]
use crate::action::{Authorization, DelegationProofData};
use crate::action::Effect;
use crate::forest::CallTree;
use crate::turn::{Turn, TurnResult};

/// Minimal pre-execution ledger snapshot for shadow marshalling.
///
/// The fields are read only by the FFI-build marshaller (`ledger_to_wire_state` /
/// `turn_to_wire_turn`); the non-feature build still captures the snapshot so eligibility
/// is decided identically, hence the conditional `allow(dead_code)`.
#[derive(Clone, Debug)]
#[cfg_attr(not(feature = "lean-shadow"), allow(dead_code))]
pub(crate) struct ShadowPreLedger {
    pub(crate) cells: HashMap<CellId, Cell>,
    pub(crate) id_map: HashMap<CellId, u64>,
}

/// The HOST/NODE-fed admission context (boundary-P1 bug-1). These come from the EXECUTOR's own
/// state — NOT the turn — so the verified gate's clock / freeze-set / chain-head / budget legs are
/// decided by the node, exactly as `admissible` reads `AdmCtx`. The production node (and the
/// in-process executor) builds this from `self.block_height` / `self.cell_migrations` (frozen) /
/// `self.get_last_receipt_hash(agent)` (stored head) / `self.budget_gate.remaining()` (budget).
///
/// Defaults (via [`ShadowHostCtx::diag`]) are the DIAGNOSTIC values that never spuriously reject
/// (clock 0, no frozen cells, genesis head, large budget) — used by tests/round-trips. The
/// security of bug-1 is that the EXECUTOR overrides every field from its own state.
#[derive(Clone, Debug)]
#[cfg_attr(not(feature = "lean-shadow"), allow(dead_code))]
pub struct ShadowHostCtx {
    /// The executor's current chain block height (`self.block_height`).
    pub block_height: u64,
    /// The migration freeze-set as raw `CellId`s (`self.cell_migrations` frozen cells). Only the
    /// subset referenced by the turn (and thus in the wire id map) crosses; a frozen agent /
    /// write-set cell then trips the verified `admissible` frozen leg, matching apply.rs.
    pub frozen: Vec<CellId>,
    /// The agent's stored receipt-chain head (`self.get_last_receipt_hash(agent)`), or `None` =
    /// genesis. The verified `admissible` ChainHead leg requires the turn's claimed `prev` to
    /// EQUAL this — a forked / replayed turn (`prev ≠ stored_head`) is rejected.
    pub stored_head: Option<[u8; 32]>,
    /// The Stingray silo budget slice the fee must fit (`self.budget_gate.remaining()`). The
    /// verified `admissible` Budget leg rejects `fee > budget`.
    pub budget: u64,
}

impl ShadowHostCtx {
    /// The DIAGNOSTIC host context — never spuriously rejects. The PRODUCTION executor MUST
    /// override every field from its own state (that override is what makes bug-1 real).
    pub fn diag() -> Self {
        ShadowHostCtx { block_height: 0, frozen: vec![], stored_head: None, budget: 1_000_000_000 }
    }
}

thread_local! {
    static SHADOW_PRE: RefCell<Option<ShadowPreLedger>> = const { RefCell::new(None) };
    static SHADOW_BLOCK_HEIGHT: RefCell<u64> = const { RefCell::new(0) };
    static SHADOW_HOST: RefCell<Option<ShadowHostCtx>> = const { RefCell::new(None) };
}

/// Capture a minimal pre-state snapshot when shadow mode may run later.
///
/// Call at the start of [`crate::executor::TurnExecutor::execute`] before any ledger mutation so
/// the Lean oracle sees the same admission inputs as Rust. `host` carries the NODE-fed admission
/// context (clock / freeze-set / stored head / budget) — the bug-1 seam.
pub fn capture_pre_state_if_eligible(turn: &Turn, ledger: &Ledger, host: ShadowHostCtx) {
    let snapshot = if shadow_env_enabled() && forest_is_marshallable(turn) {
        Some(build_pre_ledger(turn, ledger))
    } else {
        None
    };
    let block_height = host.block_height;
    SHADOW_PRE.with(|slot| *slot.borrow_mut() = snapshot);
    SHADOW_BLOCK_HEIGHT.with(|h| *h.borrow_mut() = block_height);
    SHADOW_HOST.with(|slot| *slot.borrow_mut() = Some(host));
}

/// Shadow-execute eligible turns against the Lean kernel and log divergences.
///
/// Uses the pre-execution snapshot stored by [`capture_pre_state_if_eligible`].
/// The `ledger` argument matches the public API; marshalling uses the captured pre-state.
///
/// Returns the Lean commit verdict (`Some(true/false)`) when the turn was comparable (eligible +
/// the FFI ran), else `None`. The verified Lean executor is the swap's TARGET decision-maker; this
/// verdict lets the caller (boundary-P1 / THE SWAP) treat a Lean REJECTION as a binding VETO under
/// strict mode (`lean_vetoes` below) — the Lean kernel can only TIGHTEN the commit decision (reject
/// what Rust accepts), never loosen it (it never launders a Rust rejection to a commit).
pub fn maybe_shadow_turn(
    turn: &Turn,
    ledger: &Ledger,
    result: &TurnResult,
    block_height: u64,
) -> Option<bool> {
    let _ = (ledger, block_height);
    if !shadow_env_enabled() {
        SHADOW_PRE.with(|slot| slot.borrow_mut().take());
        SHADOW_BLOCK_HEIGHT.with(|h| *h.borrow_mut() = 0);
        SHADOW_HOST.with(|slot| slot.borrow_mut().take());
        return None;
    }

    #[cfg(feature = "lean-shadow")]
    {
        if !dregg_lean_ffi::lean_available() {
            tracing::debug!("lean shadow: Lean lib unavailable, skipping");
            SHADOW_PRE.with(|slot| slot.borrow_mut().take());
            SHADOW_HOST.with(|slot| slot.borrow_mut().take());
            return None;
        }

        let Some(pre) = SHADOW_PRE.with(|slot| slot.borrow_mut().take()) else {
            return None;
        };
        // The NODE-fed admission context captured alongside the pre-state (bug-1 seam). Falls back
        // to the diagnostic default only if the executor did not provide one (should not happen on
        // the production path, which always passes a real `ShadowHostCtx`).
        let host = SHADOW_HOST
            .with(|slot| slot.borrow_mut().take())
            .unwrap_or_else(ShadowHostCtx::diag);

        if !forest_is_marshallable(turn) {
            return None;
        }

        let kinds = turn_effect_kinds(turn).join("+");
        match run_shadow(turn, &pre, &host) {
            Ok(lean_committed) => {
                let rust_committed = result.is_committed();
                if lean_committed != rust_committed {
                    // A live RUST↔LEAN divergence. Logged with the effect kinds so the operator
                    // can map it straight to the divergence ledger / a marshaller gap.
                    tracing::warn!(
                        target: "dregg::lean_shadow::divergence",
                        agent = ?turn.agent,
                        effects = %kinds,
                        lean_committed,
                        rust_committed,
                        "RUST↔LEAN divergence: commit-bit mismatch (apply.rs vs verified Lean executor)"
                    );
                } else {
                    tracing::debug!(
                        target: "dregg::lean_shadow",
                        agent = ?turn.agent,
                        effects = %kinds,
                        committed = lean_committed,
                        "lean shadow agrees"
                    );
                }
                Some(lean_committed)
            }
            Err(e) => {
                tracing::warn!(
                    target: "dregg::lean_shadow",
                    agent = ?turn.agent,
                    effects = %kinds,
                    error = %e,
                    "lean shadow: marshal/exec failed (turn NOT compared)"
                );
                None
            }
        }
    }

    #[cfg(not(feature = "lean-shadow"))]
    {
        SHADOW_PRE.with(|slot| slot.borrow_mut().take());
        SHADOW_HOST.with(|slot| slot.borrow_mut().take());
        let _ = (turn, result);
        None
    }
}

/// Whether STRICT shadow mode (`DREGG_LEAN_SHADOW_STRICT=1`) is enabled — the SWAP beachhead. When
/// on (and `DREGG_LEAN_SHADOW=1`), the verified Lean executor becomes a binding REJECTION authority
/// on the commit path: a turn the Rust executor COMMITTED but the verified Lean executor REJECTED
/// is VETOED (converted to a rejection). The Lean kernel can ONLY tighten the decision — it never
/// turns a Rust rejection into a commit — so a divergence can only make the node MORE conservative
/// (the "kernel-vs-NEW-Rust, never match a buggy oracle" direction). OFF by default: the live path
/// stays Rust-decided until the marshaller covers every effect (so a still-GAP effect is never
/// spuriously vetoed — only COMPARABLE turns can be vetoed).
pub fn strict_veto_enabled() -> bool {
    shadow_env_enabled() && std::env::var("DREGG_LEAN_SHADOW_STRICT").as_deref() == Ok("1")
}

/// Decide whether the verified Lean verdict VETOES a Rust commit. Returns `true` ONLY when strict
/// mode is on, the turn was COMPARABLE (`lean_verdict = Some(_)`), the Rust executor COMMITTED, and
/// the verified Lean executor REJECTED. A `None` verdict (GAP / FFI off) NEVER vetoes (we cannot
/// veto what we did not compare). The veto is one-directional: `lean=false ∧ rust=true` only.
pub fn lean_vetoes(rust_committed: bool, lean_verdict: Option<bool>) -> bool {
    strict_veto_enabled() && rust_committed && lean_verdict == Some(false)
}

fn shadow_env_enabled() -> bool {
    std::env::var("DREGG_LEAN_SHADOW").as_deref() == Ok("1")
}

/// Whether shadow execution is enabled (`DREGG_LEAN_SHADOW=1`). The executor uses this to AVOID
/// building the host-fed admission context (which locks the migration / budget mutexes) on the hot
/// path when the shadow is off.
pub fn shadow_enabled() -> bool {
    shadow_env_enabled()
}

// ===================================================================
// STRUCTURED DIVERGENCE REPORT — for the corpus divergence-finder.
//
// `maybe_shadow_turn` logs divergences via `tracing` (side-effect only). The divergence
// LEDGER harness needs a structured per-turn outcome so it can build an effect-by-effect
// map of where the verified Lean executor models the Rust `apply.rs` executor and whether
// the two agree. `shadow_report` runs the SAME marshal+exec path and returns that outcome.
// ===================================================================

/// Per-turn outcome of running the Lean FFI shadow alongside the real Rust executor.
#[derive(Clone, Debug)]
pub struct ShadowReport {
    /// The distinct effect variant names present in the turn's forest (pre-order).
    pub effect_kinds: Vec<&'static str>,
    /// Whether EVERY effect in the turn maps to a Lean wire action (turn is Lean-eligible).
    pub lean_eligible: bool,
    /// The Rust `apply.rs` commit decision.
    pub rust_committed: bool,
    /// The Lean executor commit decision (`Some` iff eligible AND the FFI ran).
    pub lean_committed: Option<bool>,
    /// `Some(true)` agree, `Some(false)` DIVERGE, `None` not comparable (ineligible / FFI off).
    pub agree: Option<bool>,
    /// Marshal/exec error, if the FFI path failed for an eligible turn.
    pub error: Option<String>,
}

impl ShadowReport {
    /// True when the turn was comparable and the two executors DISAGREED on commit.
    pub fn diverged(&self) -> bool {
        self.agree == Some(false)
    }
}

/// Static variant name for an effect (used to characterise the corpus per effect).
pub fn effect_kind(eff: &Effect) -> &'static str {
    match eff {
        Effect::SetField { .. } => "SetField",
        Effect::Transfer { .. } => "Transfer",
        Effect::GrantCapability { .. } => "GrantCapability",
        Effect::RevokeCapability { .. } => "RevokeCapability",
        Effect::EmitEvent { .. } => "EmitEvent",
        Effect::IncrementNonce { .. } => "IncrementNonce",
        Effect::CreateCell { .. } => "CreateCell",
        Effect::SetPermissions { .. } => "SetPermissions",
        Effect::SetVerificationKey { .. } => "SetVerificationKey",
        Effect::NoteSpend { .. } => "NoteSpend",
        Effect::NoteCreate { .. } => "NoteCreate",
        Effect::CreateSealPair { .. } => "CreateSealPair",
        Effect::Seal { .. } => "Seal",
        Effect::Unseal { .. } => "Unseal",
        Effect::SpawnWithDelegation { .. } => "SpawnWithDelegation",
        Effect::RefreshDelegation => "RefreshDelegation",
        Effect::RevokeDelegation { .. } => "RevokeDelegation",
        Effect::BridgeMint { .. } => "BridgeMint",
        Effect::BridgeLock { .. } => "BridgeLock",
        Effect::BridgeFinalize { .. } => "BridgeFinalize",
        Effect::BridgeCancel { .. } => "BridgeCancel",
        Effect::Introduce { .. } => "Introduce",
        Effect::PipelinedSend { .. } => "PipelinedSend",
        Effect::CreateObligation { .. } => "CreateObligation",
        Effect::FulfillObligation { .. } => "FulfillObligation",
        Effect::SlashObligation { .. } => "SlashObligation",
        Effect::CreateEscrow { .. } => "CreateEscrow",
        Effect::ReleaseEscrow { .. } => "ReleaseEscrow",
        Effect::RefundEscrow { .. } => "RefundEscrow",
        Effect::CreateCommittedEscrow { .. } => "CreateCommittedEscrow",
        Effect::ReleaseCommittedEscrow { .. } => "ReleaseCommittedEscrow",
        Effect::RefundCommittedEscrow { .. } => "RefundCommittedEscrow",
        Effect::ExerciseViaCapability { .. } => "ExerciseViaCapability",
        Effect::MakeSovereign { .. } => "MakeSovereign",
        Effect::CreateCellFromFactory { .. } => "CreateCellFromFactory",
        Effect::QueueAllocate { .. } => "QueueAllocate",
        Effect::QueueEnqueue { .. } => "QueueEnqueue",
        Effect::QueueDequeue { .. } => "QueueDequeue",
        Effect::QueueResize { .. } => "QueueResize",
        Effect::QueueAtomicTx { .. } => "QueueAtomicTx",
        Effect::QueuePipelineStep { .. } => "QueuePipelineStep",
        Effect::ExportSturdyRef { .. } => "ExportSturdyRef",
        Effect::EnlivenRef { .. } => "EnlivenRef",
        Effect::DropRef { .. } => "DropRef",
        Effect::ValidateHandoff { .. } => "ValidateHandoff",
        Effect::Refusal { .. } => "Refusal",
        Effect::CellSeal { .. } => "CellSeal",
        Effect::CellUnseal { .. } => "CellUnseal",
        Effect::CellDestroy { .. } => "CellDestroy",
        Effect::Burn { .. } => "Burn",
        Effect::AttenuateCapability { .. } => "AttenuateCapability",
        Effect::ReceiptArchive { .. } => "ReceiptArchive",
        #[allow(unreachable_patterns)]
        _ => "Unknown",
    }
}

/// THE SWAP — the MAPPABLE producer surface: the effect kinds the marshaller PROJECTS to a wire
/// action (`effect_is_mappable`'s supported set, mirroring the FFI's `effect_to_wire`). A turn whose
/// every effect is in this set is ELIGIBLE for the VERIFIED Lean producer on the commit path; the
/// Lean executor produces the committed state and the Rust executor is demoted to a differential
/// cross-check. A turn with ANY effect outside this set falls back to the Rust producer.
///
/// "Mappable" (the producer RUNS) is NOT the same as "root-agreeing" (the Lean-produced `.root()`
/// EQUALS Rust's). Some mappable effects touch a commitment field the wire model drops or are
/// structurally re-shaped by Rust, so their reconstituted root DIVERGES — those are the SWAP-GAPS in
/// [`producer_root_gap_effects`]. The genuinely swap-safe subset (producer runs AND root agrees) is
/// [`producer_root_agreeing_effects`]. This honest partition (mappable = root-agreeing ∪ root-gap)
/// is asserted by the `lean_state_producer_coverage` differential — neither list can drift vacuous.
///
/// MUST be kept in sync with [`effect_is_mappable`] (the actual gate). Names match [`effect_kind`].
pub fn producer_mappable_effects() -> &'static [&'static str] {
    &[
        "SetField",
        "Transfer",
        "SetPermissions",
        "SetVerificationKey",
        "EmitEvent",
        "MakeSovereign",
        "RevokeDelegation",
        "NoteSpend",
        "NoteCreate",
        "IncrementNonce",
        "Refusal",
        "ReceiptArchive",
        "RefreshDelegation",
        "CellSeal",
        "CellUnseal",
        "CellDestroy",
        "Burn",
        "RevokeCapability",
        "QueueAllocate",
        "GrantCapability",
        "AttenuateCapability",
        // §SIDE-TABLE families: the off-cell-merkle-root holding-store effects. Create debits a
        // `bal` (reconstitutes) + parks an off-root record; the cell commitment is otherwise
        // untouched, so these are root-AGREEING (see `producer_root_agreeing_effects`). The settle
        // effects reference an existing record (exercised via a create+settle forest).
        "CreateEscrow",
        "ReleaseEscrow",
        "RefundEscrow",
        "CreateObligation",
    ]
}

/// The SWAP-SAFE subset of the mappable surface: the producer runs AND the Lean-reconstituted
/// ledger provably AGREES with the legacy Rust executor on full cell state + `cap_root` + `.root()`
/// (proved by the `lean_state_producer_widen` + `lean_state_producer_coverage` differentials). For a
/// turn whose effects are ALL in this set, the verified Lean producer can replace the Rust state
/// producer with ZERO post-state divergence — the true cutover-ready set.
///
/// Every entry is pinned by a round-trip differential test; an entry whose test stops agreeing FAILS
/// the suite, forcing it into [`producer_root_gap_effects`]. NoteSpend/NoteCreate edit the note SET
/// (a side-table OFF the cell merkle root) and leave cell commitment fields untouched, so they
/// agree on the cell-ledger `.root()`. QueueAllocate's structural insert is likewise off the cell
/// root and bal-neutral in the funded case.
pub fn producer_root_agreeing_effects() -> &'static [&'static str] {
    &[
        "SetField",
        "Transfer",
        "EmitEvent",
        "NoteSpend",
        "NoteCreate",
        "IncrementNonce",
        "RefreshDelegation",
        "Burn",
        "RevokeCapability",
        "QueueAllocate",
        // §SIDE-TABLE holding-store families — the off-cell-merkle-root escrow/obligation effects.
        // `apply_create_escrow`/`apply_create_obligation` debit ONE cell's `balance` (which the `bal`
        // side-table carries → reconstitutes) and park the value in the off-root `escrows`/
        // `obligations` store; the verified `createEscrowKAsset` (and the `createObligationA`
        // dispatch-alias) do the SAME single-cell `bal` debit + record insert, gated on the same
        // transfer-authority + balance + account + id-uniqueness legs. Only the CREATE effects are
        // root-AGREEING here: the side-table records never feed `cell::Ledger::root()`, so the
        // reconstituted `.root()` AGREES with Rust (only the `bal` debit changes, and it
        // reconstitutes). The SETTLE effects (release/refund) are characterized root/commit-bit gaps:
        // Rust gates release on a condition PROOF and refund on a PAST timeout, neither expressible
        // within a single create+settle forest at one block height, and the verified settle-auth gate
        // differs — see `producer_root_gap_effects`.
        "CreateEscrow",
        "CreateObligation",
    ]
}

/// The CHARACTERIZED SWAP-GAPS: mappable effects (the producer RUNS) whose Lean-reconstituted
/// `.root()` DIVERGES from Rust because the wire model is lossier than the cell commitment, or
/// because Rust re-shapes the ledger structurally. Each is pinned by a NEGATIVE-tooth differential
/// (`lean_state_producer_widen` + `lean_state_producer_coverage`) that asserts the SPECIFIC
/// divergence, so the gap is named, never a silent pass. The honest residual of THE SWAP:
///   * `CellSeal`/`CellUnseal`/`CellDestroy` — the wire `WState` has no `lifecycle` field, and the
///     Rust commitment binds the lifecycle PAYLOAD (reason hash, sealed/destroyed-at height, death
///     cert), which the Lean kernel models only as a discriminant `Nat`. Closing this needs the
///     Lean kernel to model the lifecycle payload, not just a wire codec field.
///   * `SetPermissions`/`SetVerificationKey` — the wire carries a COLLAPSED scalar, not the full
///     `Permissions`/`VerificationKey` struct the commitment binds.
///   * `GrantCapability` — the wire `caps` model carries `(target[,rights])` per edge; the Rust
///     `cap_root` binds `(target, slot, permissions, breadstuff, expires_at, allowed_effects)`.
///   * `MakeSovereign` — Rust REMOVES the cell from `Ledger::cells` (→ a different leaf set); the
///     wire state model has no sovereign-removal transition, so the reconstitution keeps the cell.
///   * `Refusal`/`ReceiptArchive` — Rust writes an audit-field / lifecycle-Archived commitment the
///     wire `refusal`/`rarchive` arms do not reproduce byte-for-byte.
///   * `RevokeDelegation` — a COMMITTING revoke bumps the PARENT cell's `delegation_epoch`, which is
///     folded into `compute_canonical_state_commitment` (commitment.rs hashes `state.delegation_epoch`).
///     The wire `WState` cell record carries no `delegation_epoch` field, and the verified
///     `revokeDelegationA` edits only the `caps` edge set (no epoch counter), so the reconstitution
///     keeps the parent's pre-state epoch → `.root()` diverges. (The no-op self-revoke that Rust
///     REJECTS trivially agrees, but a real commit diverges — so the effect is a gap.) Closing this
///     needs the Lean kernel to model the per-cell delegation epoch and carry it on the wire.
pub fn producer_root_gap_effects() -> &'static [&'static str] {
    &[
        "SetPermissions",
        "SetVerificationKey",
        "MakeSovereign",
        "Refusal",
        "ReceiptArchive",
        "CellSeal",
        "CellUnseal",
        "CellDestroy",
        "GrantCapability",
        "RevokeDelegation",
        // AttenuateCapability narrows a held `CapabilityRef`'s `AuthRequired`/expiry in Rust (→
        // `cap_root` changes); the wire `caps` model carries only `Cap::Node` edges and Lean's
        // `attenuate` is a no-op on a `node` cap, so the reconstruction keeps the edge unchanged →
        // `cap_root` diverges. Same cap-fidelity gap class as GrantCapability.
        "AttenuateCapability",
        // §SIDE-TABLE settle effects: the producer RUNS but the COMMIT-BIT diverges. Rust gates
        // `ReleaseEscrow` on a satisfied condition (ZK proof / all-signers / predicate) and
        // `RefundEscrow` on a PAST timeout (`block_height > timeout_height`); the verified
        // `releaseEscrowChainA`/`refundEscrowChainA` gate only on settle-actor authority over the
        // recipient/creator + record-present-and-unresolved. With no condition proof / before the
        // timeout the two executors disagree on whether the settle commits — a characterized
        // commit-bit gap (the condition/timeout crypto-&-clock legs are the §8 portal the wire model
        // does not carry), surfaced by the differential, never a silent pass. Closing this needs the
        // condition-proof / timeout legs modelled in the verified settle gate.
        "ReleaseEscrow",
        "RefundEscrow",
    ]
}

/// Back-compat alias for [`producer_mappable_effects`] — the set of effect kinds for which the
/// verified Lean producer RUNS on the commit path. Prefer [`producer_root_agreeing_effects`] when
/// you mean "the swap-safe, zero-divergence set" and [`producer_root_gap_effects`] for the residual.
pub fn producer_covered_effects() -> &'static [&'static str] {
    producer_mappable_effects()
}

/// Whether the producer RUNS (defaults to Lean) for a given effect-kind name.
/// `name` should be an [`effect_kind`] / [`producer_mappable_effects`] string.
pub fn producer_covers_kind(name: &str) -> bool {
    producer_mappable_effects().contains(&name)
}

/// Whether the verified producer's reconstituted `.root()` provably AGREES with Rust for the given
/// effect kind (the swap-safe set). A `false` for a mappable effect means the producer runs but the
/// post-state root is a characterized gap (see [`producer_root_gap_effects`]).
pub fn producer_root_agrees_kind(name: &str) -> bool {
    producer_root_agreeing_effects().contains(&name)
}

/// Every on-chain effect KIND name (the full `Effect` enum surface, as named by
/// [`effect_kind`]). Used to report the honest producer boundary: the kinds in
/// this list but NOT in [`producer_covered_effects`] are the effects that still
/// fall back to the Rust producer.
pub fn all_effect_kinds() -> &'static [&'static str] {
    &[
        "SetField",
        "Transfer",
        "GrantCapability",
        "RevokeCapability",
        "EmitEvent",
        "IncrementNonce",
        "CreateCell",
        "SetPermissions",
        "SetVerificationKey",
        "NoteSpend",
        "NoteCreate",
        "CreateSealPair",
        "Seal",
        "Unseal",
        "SpawnWithDelegation",
        "RefreshDelegation",
        "RevokeDelegation",
        "BridgeMint",
        "BridgeLock",
        "BridgeFinalize",
        "BridgeCancel",
        "Introduce",
        "PipelinedSend",
        "CreateObligation",
        "FulfillObligation",
        "SlashObligation",
        "CreateEscrow",
        "ReleaseEscrow",
        "RefundEscrow",
        "CreateCommittedEscrow",
        "ReleaseCommittedEscrow",
        "RefundCommittedEscrow",
        "ExerciseViaCapability",
        "MakeSovereign",
        "CreateCellFromFactory",
        "QueueAllocate",
        "QueueEnqueue",
        "QueueDequeue",
        "QueueResize",
        "QueueAtomicTx",
        "QueuePipelineStep",
        "ExportSturdyRef",
        "EnlivenRef",
        "DropRef",
        "ValidateHandoff",
        "Refusal",
        "CellSeal",
        "CellUnseal",
        "CellDestroy",
        "Burn",
        "AttenuateCapability",
        "ReceiptArchive",
    ]
}

/// The effect kinds NOT yet projected to the wire — a turn touching any of these
/// falls back to the Rust producer for that turn. The honest "blocks the full
/// Lean-producer default" list.
pub fn producer_uncovered_effects() -> Vec<&'static str> {
    all_effect_kinds()
        .iter()
        .copied()
        .filter(|k| !producer_covers_kind(k))
        .collect()
}

fn turn_effect_kinds(turn: &Turn) -> Vec<&'static str> {
    let mut out = Vec::new();
    fn walk(tree: &CallTree, out: &mut Vec<&'static str>) {
        for eff in &tree.action.effects {
            out.push(effect_kind(eff));
        }
        for c in &tree.children {
            walk(c, out);
        }
    }
    for r in &turn.call_forest.roots {
        walk(r, &mut out);
    }
    out
}

/// Run the Lean FFI shadow against the real Rust result and return a STRUCTURED outcome.
///
/// Unlike [`maybe_shadow_turn`] (which only logs), this returns a [`ShadowReport`] for the
/// corpus divergence-finder. Must be called with the SAME `ledger` and `block_height` as the
/// `execute` call that produced `result`; it internally re-snapshots the pre-state from the
/// post-state would be wrong, so callers should snapshot BEFORE executing (see the harness).
#[cfg(feature = "lean-shadow")]
pub fn shadow_report(
    turn: &Turn,
    pre_ledger: &Ledger,
    rust_committed: bool,
    block_height: u64,
) -> ShadowReport {
    let effect_kinds = turn_effect_kinds(turn);
    let eligible = forest_is_marshallable(turn);

    if !eligible {
        return ShadowReport {
            effect_kinds,
            lean_eligible: false,
            rust_committed,
            lean_committed: None,
            agree: None,
            error: None,
        };
    }

    if !dregg_lean_ffi::lean_available() {
        return ShadowReport {
            effect_kinds,
            lean_eligible: true,
            rust_committed,
            lean_committed: None,
            agree: None,
            error: Some("lean unavailable".into()),
        };
    }

    let pre = build_pre_ledger(turn, pre_ledger);
    // The corpus runs each turn as the FIRST in its agent's receipt chain (genesis stored head =
    // the turn's `prev: None`), with no frozen cells and a generous budget — the DIAGNOSTIC host
    // context at the harness's chosen `block_height`. The ChainHead leg is still REAL (genesis
    // matches the corpus turn's `previous_receipt_hash: None`); the production node feeds the
    // advancing head / freeze-set / budget via `maybe_shadow_turn`'s `ShadowHostCtx`.
    let host = ShadowHostCtx { block_height, ..ShadowHostCtx::diag() };
    match run_shadow(turn, &pre, &host) {
        Ok(lean_committed) => ShadowReport {
            effect_kinds,
            lean_eligible: true,
            rust_committed,
            lean_committed: Some(lean_committed),
            agree: Some(lean_committed == rust_committed),
            error: None,
        },
        Err(e) => ShadowReport {
            effect_kinds,
            lean_eligible: true,
            rust_committed,
            lean_committed: None,
            agree: None,
            error: Some(e),
        },
    }
}

/// Non-FFI build: shadow report is always "ineligible to compare" (no Lean linked).
#[cfg(not(feature = "lean-shadow"))]
pub fn shadow_report(
    turn: &Turn,
    _pre_ledger: &Ledger,
    rust_committed: bool,
    _block_height: u64,
) -> ShadowReport {
    ShadowReport {
        effect_kinds: turn_effect_kinds(turn),
        lean_eligible: forest_is_marshallable(turn),
        rust_committed,
        lean_committed: None,
        agree: None,
        error: Some("lean-shadow feature off".into()),
    }
}

// ===================================================================
// ELIGIBILITY — a turn is shadowed iff its WHOLE forest marshals.
// ===================================================================

/// True when every effect in the forest maps to a wire action and the cell-id set is
/// closed (so a Nat id can be assigned). Any unmappable effect ⇒ ineligible (the turn is
/// skipped rather than silently mis-encoded). Decided identically in both builds.
pub(crate) fn forest_is_marshallable(turn: &Turn) -> bool {
    if turn.call_forest.roots.is_empty() {
        return false;
    }
    let id_map = collect_id_map(turn);
    let mut any = false;
    let ok = turn
        .call_forest
        .roots
        .iter()
        .all(|r| tree_is_marshallable(r, &id_map, &mut any));
    ok && any
}

/// THE COVERED SET for the DEFAULT-ON verified producer. A turn is covered iff it marshals AND
/// EVERY effect it carries is in [`producer_root_agreeing_effects`] — the swap-safe subset where the
/// Lean-reconstituted `.root()` provably EQUALS the legacy Rust executor's (pinned positive teeth in
/// `lean_state_producer_widen` + `lean_state_producer_coverage`).
///
/// This is the STRICTER gate the producer-mode commit path uses to decide whether to INSTALL the
/// verified post-state. `forest_is_marshallable` (the producer merely RUNS) is a SUPERSET: it admits
/// the 10 characterized root-GAP effects (SetPermissions / SetVerificationKey / MakeSovereign /
/// Refusal / ReceiptArchive / CellSeal / CellUnseal / CellDestroy / GrantCapability /
/// AttenuateCapability) whose Lean-reconstituted root provably DIVERGES from Rust because the wire
/// model is lossier than the cell commitment. Installing a Lean-produced root for one of those on
/// the live commit path would commit state that DISAGREES with every other node's Rust root (and the
/// proving machinery) — a silent divergence. So the default-on producer covers ONLY the root-agreeing
/// set; a turn touching ANY root-gap (or unmappable) effect falls back to the Rust producer with a
/// logged warning, NEVER a silent commit of divergent state.
///
/// Decided identically in both builds; empty forests are uncovered (same as `forest_is_marshallable`).
pub fn forest_is_root_agreeing(turn: &Turn) -> bool {
    if !forest_is_marshallable(turn) {
        return false;
    }
    turn_effect_kinds(turn)
        .iter()
        .all(|k| producer_root_agrees_kind(k))
}

/// The FIRST effect kind in `turn` that is a characterized root-GAP (mappable but not root-agreeing)
/// — i.e. the effect that pushed the turn out of the default-on covered set. `None` if every effect
/// is root-agreeing (or the turn is unmappable for some other reason). Used by `produce_via_lean` to
/// name the precise gap in its Rust-fallback reason, so the fallback is never a silent skip.
pub fn first_root_gap_kind(turn: &Turn) -> Option<&'static str> {
    turn_effect_kinds(turn)
        .into_iter()
        .find(|k| producer_covers_kind(k) && !producer_root_agrees_kind(k))
}

fn tree_is_marshallable(tree: &CallTree, id_map: &HashMap<CellId, u64>, any: &mut bool) -> bool {
    if !id_map.contains_key(&tree.action.target) {
        return false;
    }
    for eff in &tree.action.effects {
        if !effect_is_mappable(eff, id_map) {
            return false;
        }
        *any = true;
    }
    tree.children
        .iter()
        .all(|c| tree_is_marshallable(c, id_map, any))
}

/// Whether an effect projects to a wire action with all referenced cells in the id map.
/// MUST agree with `effect_to_wire`'s supported set (the FFI projector).
fn effect_is_mappable(eff: &Effect, id_map: &HashMap<CellId, u64>) -> bool {
    let has = |c: &CellId| id_map.contains_key(c);
    match eff {
        Effect::SetField { cell, .. } => has(cell),
        Effect::Transfer { from, to, .. } => has(from) && has(to),
        Effect::SetPermissions { cell, .. } => has(cell),
        Effect::SetVerificationKey { cell, .. } => has(cell),
        Effect::EmitEvent { cell, .. } => has(cell),
        Effect::MakeSovereign { cell } => has(cell),
        Effect::RevokeDelegation { child } => has(child),
        // Note set-transitions: the actor is the action target (already in the id map),
        // the nullifier/commitment are intrinsic to the effect — always mappable.
        Effect::NoteSpend { .. } => true,
        Effect::NoteCreate { .. } => true,
        // ─── Widened GAP effects (MUST mirror effect_to_wire's supported set) ────────
        Effect::IncrementNonce { cell } => has(cell),
        Effect::Refusal { cell, .. } => has(cell),
        // ReceiptArchive / RefreshDelegation target the action's own cell (always in the map).
        Effect::ReceiptArchive { .. } => true,
        Effect::RefreshDelegation => true,
        Effect::CellSeal { target, .. } => has(target),
        Effect::CellUnseal { target } => has(target),
        Effect::CellDestroy { target, .. } => has(target),
        // Burn: ONLY the canonical balance slot (`slot == 0`) is modelled; other slots are
        // left unmapped (skip the turn rather than mis-encode).
        Effect::Burn { target, slot: 0, .. } => has(target),
        Effect::RevokeCapability { cell, .. } => has(cell),
        // AttenuateCapability: dregg1 narrows a HELD c-list slot in place (apply.rs requires
        // `cell == actor`). The verified `attenuateStepA actor idx keep` narrows the actor's own
        // `idx`-th held cap (a TOTAL self-narrowing — always commits, `List.modify` is a no-op for an
        // out-of-range slot). The action target is the actor's own cell; we require it in the id map.
        // NOTE: this is a cap-fidelity ROOT-GAP (the wire `caps` model carries `Cap::Node` edges, so
        // Lean's `attenuate` — which only filters `.endpoint` rights — is a no-op, while Rust narrows
        // the held `CapabilityRef`'s `AuthRequired`/expiry → `cap_root` diverges). Mappable (producer
        // RUNS) but characterized as a gap by the coverage differential, never a silent pass.
        Effect::AttenuateCapability { cell, .. } => has(cell),
        // ─── GAP-shrink batch (the swap surface, MUST mirror effect_to_wire) ─────────────
        // QueueAllocate: the action target IS the gate cell (always in the map). The fresh
        // queue id is intrinsic (assigned deterministically), so the effect is always mappable.
        Effect::QueueAllocate { .. } => true,
        // GrantCapability: dregg1 `del`. The granter `from`, grantee `to`, and the cap target
        // must all be in the id map (the wire `del` carries delegator + recipient + target Nats).
        Effect::GrantCapability { from, to, cap } => has(from) && has(to) && has(&cap.target),
        // ─── §SIDE-TABLE families (the holding-store batch — MUST mirror effect_to_wire) ────────
        // ESCROW (root-AGREEING). `apply_create_escrow` debits the creator's `balance` and parks the
        // value in the off-cell-merkle-root `escrows` store; the verified `createEscrowKAsset` does
        // the SAME single-cell `bal` debit (recDebit) + record insert, gated on the same `authorizedB`
        // transfer leg + balance + account + id-uniqueness. The debit reconstitutes via the `bal`
        // side-table and the record is off-root, so the reconstituted `.root()` AGREES with Rust.
        Effect::CreateEscrow { cell, recipient, escrow_id, .. } => {
            has(cell) && has(recipient) && !escrow_id.iter().all(|&b| b == 0)
        }
        // release/refund settle effects look the record up by id (off-root) and single-cell CREDIT
        // the recipient/creator (`recCredit` ⟺ `set_balance(old + amount)`). Mappable when the id is
        // non-null; the credited cell is read from the record (no extra cells to name).
        Effect::ReleaseEscrow { escrow_id, .. } => !escrow_id.iter().all(|&b| b == 0),
        Effect::RefundEscrow { escrow_id } => !escrow_id.iter().all(|&b| b == 0),
        // OBLIGATION CREATE (root-AGREEING). `apply_create_obligation` debits the obligor
        // (action target) `balance` + inserts an off-root `ObligationRecord`; the verified
        // `createObligationA` dispatch-aliases to `createEscrowChainA` (the SAME single-cell debit +
        // record insert). A create-only obligation turn therefore round-trips: only `bal` changes
        // (reconstitutes) and the record is off-root. The settle effects (fulfill/slash) reference
        // the Rust-DERIVED obligation id, which the wire-id collapse cannot reproduce, so they are
        // characterized root-gaps (record-lookup divergence), not mapped here.
        Effect::CreateObligation { beneficiary, stake, stake_amount, .. } => {
            has(beneficiary) && !stake.0.iter().all(|&b| b == 0) && *stake_amount > 0
        }
        // Everything else (escrows/bridge/seal-pairs/captp/factory/introduce/CreateCell/…) not
        // yet projected. NOTE on CreateCell: deliberately NOT projected — the verified
        // `createCellChainA` gate requires `mintAuthorizedB actor newCell` (cell creation is
        // mint-privileged), which a fresh-id new cell can never satisfy from the marshalled
        // c-list, so it would always diverge from apply.rs's unconditional insert. Modelling it
        // honestly needs a creation-authority wire leg, not a marshaller shim.
        _ => false,
    }
}

/// Assign a Nat to every CellId referenced by the turn (agent + every effect target),
/// in a deterministic order (sorted) so the kernel sees a stable labelling.
fn collect_id_map(turn: &Turn) -> HashMap<CellId, u64> {
    let mut ids: Vec<CellId> = vec![turn.agent];
    for root in &turn.call_forest.roots {
        collect_tree_ids(root, &mut ids);
    }
    ids.sort();
    ids.dedup();
    let mut map = HashMap::new();
    for (i, id) in ids.iter().enumerate() {
        map.insert(*id, i as u64);
    }
    map
}

fn collect_tree_ids(tree: &CallTree, ids: &mut Vec<CellId>) {
    ids.push(tree.action.target);
    for eff in &tree.action.effects {
        for c in effect_cells(eff) {
            ids.push(c);
        }
    }
    for child in &tree.children {
        collect_tree_ids(child, ids);
    }
}

/// The cell ids an effect references (so they can be assigned wire Nats). Only the
/// effects we can marshal need to list cells; an unlisted effect is simply not projected.
fn effect_cells(eff: &Effect) -> Vec<CellId> {
    match eff {
        Effect::SetField { cell, .. } => vec![*cell],
        Effect::Transfer { from, to, .. } => vec![*from, *to],
        Effect::IncrementNonce { cell } => vec![*cell],
        Effect::SetPermissions { cell, .. } => vec![*cell],
        Effect::SetVerificationKey { cell, .. } => vec![*cell],
        Effect::EmitEvent { cell, .. } => vec![*cell],
        Effect::Introduce {
            introducer,
            recipient,
            target,
            ..
        } => vec![*introducer, *recipient, *target],
        Effect::RevokeDelegation { child } => vec![*child],
        Effect::MakeSovereign { cell } => vec![*cell],
        // Widened GAP effects — register their referenced cells so a Nat is assigned.
        Effect::Refusal { cell, .. } => vec![*cell],
        Effect::CellSeal { target, .. } => vec![*target],
        Effect::CellUnseal { target } => vec![*target],
        Effect::CellDestroy { target, .. } => vec![*target],
        Effect::Burn { target, .. } => vec![*target],
        Effect::RevokeCapability { cell, .. } => vec![*cell],
        // AttenuateCapability narrows the actor's OWN held slot (`cell == actor`); register the cell.
        Effect::AttenuateCapability { cell, .. } => vec![*cell],
        // GAP-shrink: GrantCapability references granter/grantee/cap-target — all need wire Nats.
        Effect::GrantCapability { from, to, cap } => vec![*from, *to, cap.target],
        // ─── §SIDE-TABLE families (escrow/obligation/committed-escrow) ───────────────────────
        // The off-cell-merkle-root holding-store effects: the cells whose `balance` the
        // create debits / the settle credits need wire Nats (the side-table record itself is
        // off-root, so only the touched cells must be named).
        Effect::CreateEscrow { cell, recipient, .. } => vec![*cell, *recipient],
        // Settle effects (release/refund/fulfill/slash) carry only an id; the credited cell is
        // read from the record, so the actor (action target) — already collected — suffices.
        Effect::ReleaseEscrow { .. } => vec![],
        Effect::RefundEscrow { .. } => vec![],
        Effect::CreateObligation { beneficiary, .. } => vec![*beneficiary],
        Effect::FulfillObligation { .. } => vec![],
        Effect::SlashObligation { .. } => vec![],
        Effect::ReleaseCommittedEscrow { recipient, .. } => vec![*recipient],
        Effect::RefundCommittedEscrow { creator, .. } => vec![*creator],
        // QueueAllocate creates a FRESH queue cell whose id is NOT in the pre-state id map; only
        // the actor (the action target) needs a Nat, collected by `collect_tree_ids` already. The
        // fresh id is assigned deterministically in `effect_to_wire` (above the pre-id-map range)
        // so it never collides with a snapshot id.
        Effect::QueueAllocate { .. } => vec![],
        _ => vec![],
    }
}

/// A deterministic FRESH wire Nat for a created cell/queue, placed ABOVE the pre-state id-map
/// range so it never collides with a snapshotted cell's Nat. The id map assigns `0..n`; we
/// offset created ids by `FRESH_ID_BASE + seq` where `seq` is the created-thing's index in the
/// pre-order walk. Both executors then see a never-before-used id, so the insert always succeeds
/// (no spurious duplicate-id rejection on either side).
#[cfg(feature = "lean-shadow")]
const FRESH_ID_BASE: u64 = 1_000_000;

// ===================================================================
// PRE-STATE — snapshot every referenced cell present in the ledger.
// ===================================================================

pub(crate) fn build_pre_ledger(turn: &Turn, ledger: &Ledger) -> ShadowPreLedger {
    let id_map = collect_id_map(turn);
    let mut cells = HashMap::new();
    for id in id_map.keys() {
        if let Some(cell) = ledger.get(id) {
            cells.insert(*id, cell.clone());
        }
    }
    ShadowPreLedger { cells, id_map }
}

// ===================================================================
// FOREST PROJECTION — pre-order flatten the Rust forest to wire actions.
//
// Each Rust effect ⇒ one wire action. The forest is walked pre-order (a node's action
// effects, then its children left-to-right), exactly the order the Rust executor applies
// them. Returns `None` if ANY effect is unmappable (the turn is then ineligible).
// ===================================================================

/// Project ONE Rust effect to ONE wire action. The supported subset is the algebraic core
/// the Lean per-asset executor models faithfully; unsupported effects return `None` (the
/// turn is then skipped rather than mis-encoded). MUST agree with `effect_is_mappable`.
#[cfg(feature = "lean-shadow")]
fn effect_to_wire(
    actor: u64,
    eff: &Effect,
    pre: &ShadowPreLedger,
    fresh_seq: &mut u64,
    agent: &CellId,
) -> Option<WireAction> {
    let id_map = &pre.id_map;
    let id = |c: &CellId| id_map.get(c).copied();
    Some(match eff {
        Effect::SetField { cell, index, value } => WireAction::SetField {
            actor,
            cell: id(cell)?,
            field: field_index_to_name(*index),
            v: field_to_i128(value),
        },
        Effect::Transfer { from, to, amount } => WireAction::Balance {
            actor,
            src: id(from)?,
            dst: id(to)?,
            amt: *amount as i128,
            asset: 0,
        },
        Effect::SetPermissions { cell, new_permissions } => WireAction::SetPerms {
            actor,
            cell: id(cell)?,
            perms: permissions_to_i128(new_permissions),
        },
        // The verified Lean executor models `SetVk` directly (see
        // `Dregg2/Circuit/Inst/setVKA.lean` + the `setvk` wire arm). The VK is a
        // structured `{hash, data}`; the wire arm carries a scalar, so we collapse to
        // the low 64 bits of the canonical vk hash — the same digest-collapse the
        // `SetField`/`SetPerms` arms use. A cleared VK (`None`) maps to the `0` marker,
        // matching the executor's "no verification key" sentinel.
        Effect::SetVerificationKey { cell, new_vk } => WireAction::SetVk {
            actor,
            cell: id(cell)?,
            vk: new_vk
                .as_ref()
                .map(|vk| bytes32_to_nat(&vk.hash) as i128)
                .unwrap_or(0),
        },
        // The verified Lean executor models the privacy note-set transitions
        // (`Dregg2/Circuit/Inst/noteSpendA.lean` / `noteCreateA.lean` + the
        // `notespend`/`notecreate` wire arms). The Lean side enforces the
        // nullifier-set / commitment-set membership transition + anti-double-spend
        // guard bit; the STARK preimage/Merkle-membership stays the Rust circuit's
        // job. We carry the 32-byte nullifier / commitment collapsed to its low 64
        // bits — the same digest-collapse used for fields and vks. This is a
        // faithful projection of the SET decision (the only thing the executor's
        // commit-bit depends on), not of the proof bytes.
        //
        // §8 NOTE-SPENDING-PROOF FLAG (closes the headline NoteSpend drift): the `nspend` wire
        // arm carries a third field, the spending-proof WITNESS flag. The verified
        // `noteSpendChainA` REJECTS when the flag is `0` (the proved
        // `noteSpendChainA_fails_without_proof` teeth — a note-spend cannot commit without the §8
        // proof). dregg1's `apply.rs` likewise REJECTS a NoteSpend whose `spending_proof` is empty
        // ("NoteSpend missing spending proof"). So we set the flag = whether the effect carried a
        // NON-EMPTY `spending_proof`; the two executors then AGREE on the commit bit (both reject a
        // proofless spend, both proceed to the SET transition when a proof is present). The proof
        // BYTES (and the STARK Merkle-membership) remain the circuit's concern — only the
        // PRESENCE bit, which the commit decision turns on, crosses the wire.
        Effect::NoteSpend { nullifier, spending_proof, .. } => WireAction::NoteSpend {
            nf: bytes32_to_nat(&nullifier.0),
            actor,
            spend_proof: !spending_proof.is_empty(),
        },
        Effect::NoteCreate { commitment, .. } => WireAction::NoteCreate {
            cm: bytes32_to_nat(&commitment.0),
            actor,
        },
        Effect::EmitEvent { cell, event } => WireAction::Emit {
            actor,
            cell: id(cell)?,
            topic: field_to_i128(&event.topic),
            data: event_data_to_i128(event),
        },
        Effect::MakeSovereign { cell } => WireAction::MakeSovereign {
            actor,
            cell: id(cell)?,
        },
        Effect::RevokeDelegation { child } => WireAction::RevokeDelegation {
            holder: actor,
            target: id(child)?,
        },
        // ─── Widened GAP effects (the swap surface) ──────────────────────────────────
        //
        // IncrementNonce: dregg1 bumps the cell nonce by 1 (`apply.rs` IncrementNonce). The
        // verified `.incrementNonceA` routes to the authority-gated `stateStep` (`stateAuthB ∧
        // target∈accounts ∧ cellLive`), which SETS the nonce field to the carried value.
        //
        // PROLOGUE-TICK INTERACTION (real swap-gap found by the producer differential, fixed
        // here): the turn PROLOGUE — run by BOTH executors and NEVER rolled back — already ticks
        // the AGENT's nonce by 1 (Rust `execute.rs` PHASE 1; the verified `admissible`/prologue
        // does the same). So when the incremented `cell` IS the agent, its post-state nonce is
        // `pre_nonce + 2` (prologue tick + the effect's increment); for any OTHER cell the
        // prologue did not touch it, so the post-state nonce is `pre_nonce + 1`. Carrying a flat
        // `pre_nonce + 1` for a self-increment CLOBBERS the prologue tick — the differential caught
        // exactly this (`rust=2 lean=1`). We add the prologue tick iff `cell == agent`.
        Effect::IncrementNonce { cell } => WireAction::IncNonce {
            actor,
            cell: id(cell)?,
            new_nonce: (pre_nonce_of(pre, cell) as i128)
                + 1
                + if cell == agent { 1 } else { 0 },
        },
        // Refusal: the proof-of-non-action bumps the target cell's nonce + records the refusal
        // (dregg1 `apply.rs` Refusal). `.refusalA` routes to `stateStep` on the refusal field
        // (authority-gated, same gate as IncrementNonce) — a self-owned live cell commits.
        Effect::Refusal { cell, .. } => WireAction::Refusal {
            actor,
            cell: id(cell)?,
        },
        // ReceiptArchive: declares the cell's receipt-prefix archived; `.receiptArchiveA` routes
        // to `stateStep` on the lifecycle field (authority-gated). The action target IS the
        // archived cell (its `checkpoint.cell_id` must equal `action.target`).
        Effect::ReceiptArchive { .. } => WireAction::ReceiptArchive {
            actor,
            cell: actor,
        },
        // CellSeal / CellUnseal: the lifecycle state machine. `.cellSealA`/`.cellUnsealA` gate on
        // `stateAuthB ∧ acceptsEffects`/`== Sealed` — a self-owned live cell SEALS; only a sealed
        // cell UNSEALS. The target IS the sealed cell (`target` must equal `action.target`).
        Effect::CellSeal { target, .. } => WireAction::CellSeal {
            actor,
            cell: id(target)?,
        },
        Effect::CellUnseal { target } => WireAction::CellUnseal {
            actor,
            cell: id(target)?,
        },
        // CellDestroy: any non-terminal → Destroyed, binding the death-certificate hash.
        // `.cellDestroyA` gates on `stateAuthB ∧ lifecycle != Destroyed`. The death-cert hash is
        // carried collapsed to its low 64 bits (the gate's commit-bit reads the lifecycle, not
        // the hash bytes; the hash is bound into the post-state faithfully).
        Effect::CellDestroy { target, certificate } => WireAction::CellDestroy {
            actor,
            cell: id(target)?,
            cert_hash: bytes32_to_nat(&certificate.certificate_hash()),
        },
        // Burn: dregg1 reduces a cell's balance with no destination credit (provable supply
        // reduction). `.burnA` routes to the PRIVILEGED `recKBurnAsset` (`mintAuthorizedB ∧
        // 0≤amt ∧ amt≤bal ∧ cell∈accounts`). Only the canonical balance slot (`slot == 0`) is
        // modelled (Silver-Vision rejects other slots); a non-zero slot is left UNMAPPED so the
        // turn is skipped rather than mis-encoded. NOTE: the verified kernel requires an explicit
        // mint/burn CAP (`node`/`control`-endpoint) on the cell — bare ownership does NOT suffice
        // — so a cell whose marshalled c-list lacks that cap correctly FAILS the Lean gate (the
        // genuine, non-vacuous authority test). This is a real model difference from apply.rs
        // (ownership-suffices) for cells without the cap; it is recorded by the ledger, not hidden.
        Effect::Burn { target, slot: 0, amount } => WireAction::Burn {
            actor,
            cell: id(target)?,
            asset: 0,
            amt: *amount as i128,
        },
        // RevokeCapability: dregg1 drops a c-list slot. `.revoke` routes to `recCRevoke`
        // (TOTAL — always commits, the revocation registry edit). The `t` is the revoked
        // target/slot; we carry the slot index.
        Effect::RevokeCapability { cell, slot } => WireAction::Revoke {
            holder: id(cell)?,
            t: *slot as u64,
        },
        // AttenuateCapability: dregg1 narrows a HELD c-list slot in place (`apply.rs` requires
        // `cell == actor`). `.attenuateA actor idx keep` routes to `attenuateStepA`, narrowing the
        // actor's own `idx`-th held cap (a TOTAL self-narrowing — always commits). The wire `atten`
        // arm carries `(actor, idx, keep)`; the `keep` rights-subset has NO faithful image of the
        // Rust `narrower_permissions: AuthRequired` (the `AuthRequired` lattice does not map onto the
        // wire `Auth` rights list), AND the marshalled c-list edges are bare `Cap::Node` (which Lean's
        // `attenuate` leaves UNCHANGED — it only filters `.endpoint` rights). So we carry `keep = []`:
        // the Lean post-state is the unchanged Node cap regardless. This makes AttenuateCapability a
        // characterized cap-fidelity ROOT-GAP (Rust narrows the held `CapabilityRef` → `cap_root`
        // changes; the Lean reconstruction keeps the Node edge → `cap_root` diverges), pinned by the
        // coverage differential's negative tooth — the producer RUNS, the divergence is named.
        Effect::AttenuateCapability { cell, slot, .. } => WireAction::Attenuate {
            actor: id(cell)?,
            idx: *slot as u64,
            keep: vec![],
        },
        // RefreshDelegation: the child refreshes its delegation snapshot from its parent
        // (self-refresh — the actor IS the child). `.refreshDelegationA` routes to the chained
        // refresh step. The action target is the refreshing child cell.
        Effect::RefreshDelegation => WireAction::RefreshDelegation {
            actor,
            child: actor,
        },
        // ─── GAP-shrink batch (was the swap surface) ─────────────────────────────────────
        //
        // QueueAllocate: dregg1 creates a fresh FIFO queue cell, debiting `capacity` computrons
        // from the actor (`apply.rs:3242`, balance ≥ capacity required). `.queueAllocateA id
        // actor cell cap` routes to `queueAllocateChainA` — gated on `stateAuthB actor cell`
        // (self-authority for a self-targeted allocate) and `queueAllocateK` (rejects a DUPLICATE
        // id, else inserts the fresh queue record). The gate cell is the actor (the action
        // target). The fresh queue id is assigned ABOVE the snapshot range so it never collides.
        // NOTE: the verified queue model is bal-NEUTRAL (it does not debit `capacity` from the
        // actor — only `queues` is touched), so the COMMIT decisions agree EXACTLY when the actor
        // has authority AND balance ≥ capacity; for an UNDER-funded allocate apply.rs rejects
        // (InsufficientBalance) while the verified executor commits — a characterised model
        // difference (the verified queue is a pure structural insert; the deposit accounting is a
        // separate `bal` concern). The corpus exercises the FUNDED case (agree) so this is sound.
        Effect::QueueAllocate { capacity, .. } => {
            let fresh = FRESH_ID_BASE + *fresh_seq;
            *fresh_seq += 1;
            WireAction::QueueAllocate {
                id: fresh,
                actor,
                cell: actor,
                capacity: *capacity,
            }
        }
        // GrantCapability: dregg1 `apply_grant_capability` (`apply.rs:595`) copies a held cap (or,
        // for a SELF-grant `cap.target == from`, the implicit strongest self-cap — no c-list
        // lookup) into the grantee `to`'s c-list. `.delegate del rec t` routes to `recCDelegate`
        // / `recKDelegate`, gated on `(caps del).any (confersEdgeTo t)` — the delegator must HOLD
        // an edge to `t`. The marshaller carries the cell's REAL c-list as `Cap::Node(target)`
        // edges (see `ledger_to_wire_state`), so a SELF-grant on a cell holding a self-`node` cap
        // passes the verified gate exactly as apply.rs's implicit-self-cap path commits; a grant
        // whose delegator lacks the edge correctly FAILS the verified gate (the non-vacuous WHO
        // leg). `t` is the cap's TARGET cell (the thing being delegated), not the slot.
        Effect::GrantCapability { from, to, cap } => WireAction::Delegate {
            delegator: id(from)?,
            recipient: id(to)?,
            t: id(&cap.target)?,
        },
        // ─── §SIDE-TABLE families (the holding-store batch) ────────────────────────────────
        //
        // ESCROW create: dregg1 `apply_create_escrow` (`apply.rs:1674`) debits the creator's
        // `balance` by `amount` and parks an unresolved record in the off-root `escrows` store.
        // `.createEscrowA id actor creator recipient asset amount` routes to `createEscrowChainA` →
        // `createEscrowKAsset`, gated on the SAME `authorizedB {actor,creator,recipient,amount}`
        // transfer-authority leg + `0≤amount≤bal creator` + `creator∈accounts` + id-uniqueness. The
        // wire `id` is the escrow_id collapsed to its low 64 bits (the create+settle pair carries the
        // SAME explicit `escrow_id`, so the collapsed wire ids coincide across a forest). asset 0.
        Effect::CreateEscrow { cell, recipient, amount, escrow_id, .. } => WireAction::CreateEscrow {
            id: bytes32_to_nat(escrow_id),
            actor,
            creator: id(cell)?,
            recipient: id(recipient)?,
            asset: 0,
            amount: *amount as i128,
        },
        // ESCROW release/refund: look the record up by id, single-cell CREDIT the recipient/creator
        // (`recCredit` ⟺ `set_balance(old + amount)`), mark resolved. The credited cell is read from
        // the record (off-root), so only the id + actor cross the wire.
        Effect::ReleaseEscrow { escrow_id, .. } => WireAction::ReleaseEscrow {
            id: bytes32_to_nat(escrow_id),
            actor,
        },
        Effect::RefundEscrow { escrow_id } => WireAction::RefundEscrow {
            id: bytes32_to_nat(escrow_id),
            actor,
        },
        // OBLIGATION create: dregg1 `apply_create_obligation` debits the OBLIGOR (= action target)
        // `balance` by `stake_amount` + inserts an off-root `ObligationRecord`. `.createObligationA id
        // actor obligor beneficiary asset stake` dispatch-aliases to `createEscrowChainA` (the SAME
        // single-cell debit + record insert). The obligor IS the action target (`actor`); the
        // beneficiary is the record's `recipient`. The wire `id` is the STAKE commitment collapsed —
        // a fresh-enough id for the create gate's uniqueness leg (the settle effects, which reference
        // the Rust-derived obligation id, are characterized root-gaps, not routed here).
        Effect::CreateObligation { beneficiary, stake, stake_amount, .. } => {
            WireAction::CreateObligation {
                id: bytes32_to_nat(&stake.0),
                actor,
                obligor: actor,
                beneficiary: id(beneficiary)?,
                asset: 0,
                stake: *stake_amount as i128,
            }
        }
        // CreateCell: dregg1 inserts a fresh cell with the given balance (`apply.rs` CreateCell).
        // `.createcell actor newCell` routes to the cell-creation chained step, gated on the
        // actor's authority over its own action. The new cell's wire Nat is assigned ABOVE the
        // snapshot range (fresh ⇒ no duplicate-insert rejection on either side).
        Effect::CreateCell { .. } => {
            let fresh = FRESH_ID_BASE + *fresh_seq;
            *fresh_seq += 1;
            WireAction::CreateCell {
                actor,
                new_cell: fresh,
            }
        }
        // Everything else (bridge, seal-pairs, captp swiss, factory, introduce, …) is not yet
        // projected here. Returning None marks the turn ineligible rather than silently dropping the
        // effect. NOTE on BridgeLock: dregg1's `apply_bridge_lock` is NOTE-based (it parks a
        // `pending_bridge` keyed by nullifier and does NOT debit any cell — the value already left via a
        // note-spend), while the verified `bridgeLockKAsset` DEBITS the originator's `bal`. That is a
        // genuine MODEL divergence (Rust note-bridge vs Lean bal-bridge), so BridgeLock is deliberately
        // NOT projected here — it would diverge on the originator's balance, not round-trip.
        _ => return None,
    })
}

/// The pre-state nonce of a cell in the snapshot (0 if absent — a fresh cell's nonce).
#[cfg(feature = "lean-shadow")]
fn pre_nonce_of(pre: &ShadowPreLedger, cell: &CellId) -> u64 {
    pre.cells.get(cell).map(|c| c.state.nonce()).unwrap_or(0)
}

#[cfg(feature = "lean-shadow")]
use dregg_lean_ffi::marshal::WireAction;

#[cfg(feature = "lean-shadow")]
fn run_shadow(turn: &Turn, pre: &ShadowPreLedger, host: &ShadowHostCtx) -> Result<bool, String> {
    use dregg_lean_ffi::marshal::marshal_turn_hosted;

    let block_height = host.block_height;
    let wire_state = ledger_to_wire_state(pre)?;
    let wire_turn = turn_to_wire_turn(turn, pre, block_height)?;
    // boundary-P1 (bug 1): the admission context is HOST/NODE-fed, NOT taken from the turn. The
    // executor supplies its OWN clock / freeze-set / stored chain-head / budget via `ShadowHostCtx`
    // (the agent cannot set its own). The turn's claimed `valid_until` / `prev` cross IN the turn
    // and are CHECKED against the host clock / stored head by the verified `admissible` gate.
    //
    //   * `now`/`block_height` — the chain clock (`self.block_height`);
    //   * `frozen`            — the migration freeze-set, projected to wire Nats (only the cells
    //                           referenced by THIS turn — i.e. present in the id map — can be named
    //                           by a wire action; a frozen agent/write-set cell trips the verified
    //                           frozen leg exactly as apply.rs's `check_not_frozen` rejects it);
    //   * `stored_head`       — the agent's stored receipt-chain head, folded the SAME way the
    //                           turn's `prev` is (`bytes32_to_nat`), so the verified ChainHead leg
    //                           (`prevReceipt = storedHead`) rejects a forked/replayed turn whose
    //                           claimed `prev` ≠ the host's stored head;
    //   * `budget`            — the Stingray silo budget slice (`fee ≤ budget`).
    let frozen_nats: Vec<u64> = host
        .frozen
        .iter()
        .filter_map(|c| pre.id_map.get(c).copied())
        .collect();
    let stored_head_nat = host.stored_head.map(|h| bytes32_to_nat(&h)).unwrap_or(0);
    let host_wire = dregg_lean_ffi::marshal::WireHostCtx {
        now: block_height,
        block_height,
        frozen: frozen_nats,
        stored_head: stored_head_nat,
        budget: host.budget,
    };
    let wire = marshal_turn_hosted(&host_wire, &wire_state, &wire_turn).map_err(|e| e.to_string())?;
    if std::env::var("DREGG_LEAN_SHADOW_DEBUG").as_deref() == Ok("1") {
        eprintln!("[shadow wire IN ] {wire}");
    }
    let out = dregg_lean_ffi::shadow_exec_full_forest_auth(&wire)?;
    if std::env::var("DREGG_LEAN_SHADOW_DEBUG").as_deref() == Ok("1") {
        eprintln!("[shadow wire OUT] {out}");
    }
    let verdict = dregg_lean_ffi::decode_shadow_verdict(&out)?;
    Ok(verdict.committed)
}

/// THE SWAP state-producing path: marshal the turn, run the VERIFIED Lean executor, and return
/// the full decoded post-state (NOT just the commit bit). This is the half `run_shadow` throws
/// away — the verified executor's produced `WireState`, which `lean_apply` reconstitutes into the
/// authoritative `Ledger`. The pre-snapshot id_map is returned alongside so the caller can invert
/// the wire Nats back to real `CellId`s.
#[cfg(feature = "lean-shadow")]
pub(crate) fn run_shadow_state(
    turn: &Turn,
    pre: &ShadowPreLedger,
    host: &ShadowHostCtx,
) -> Result<dregg_lean_ffi::ShadowState, String> {
    use dregg_lean_ffi::marshal::marshal_turn_hosted;

    let block_height = host.block_height;
    let wire_state = ledger_to_wire_state(pre)?;
    let wire_turn = turn_to_wire_turn(turn, pre, block_height)?;
    let frozen_nats: Vec<u64> = host
        .frozen
        .iter()
        .filter_map(|c| pre.id_map.get(c).copied())
        .collect();
    let stored_head_nat = host.stored_head.map(|h| bytes32_to_nat(&h)).unwrap_or(0);
    let host_wire = dregg_lean_ffi::marshal::WireHostCtx {
        now: block_height,
        block_height,
        frozen: frozen_nats,
        stored_head: stored_head_nat,
        budget: host.budget,
    };
    let wire = marshal_turn_hosted(&host_wire, &wire_state, &wire_turn).map_err(|e| e.to_string())?;
    if std::env::var("DREGG_LEAN_SHADOW_DEBUG").as_deref() == Ok("1") {
        eprintln!("[shadow wire IN ] {wire}");
    }
    let out = dregg_lean_ffi::shadow_exec_full_forest_auth(&wire)?;
    if std::env::var("DREGG_LEAN_SHADOW_DEBUG").as_deref() == Ok("1") {
        eprintln!("[shadow wire OUT] {out}");
    }
    dregg_lean_ffi::decode_shadow_state(&out)
}

#[cfg(feature = "lean-shadow")]
fn ledger_to_wire_state(pre: &ShadowPreLedger) -> Result<dregg_lean_ffi::marshal::WireState, String> {
    use dregg_lean_ffi::marshal::{WireState, WireValue};

    use dregg_lean_ffi::marshal::Cap;

    let mut cells = Vec::new();
    let mut bal = Vec::new();
    let mut caps: Vec<(u64, Vec<Cap>)> = Vec::new();
    // The PER-CELL lifecycle/death-cert side-tables the cell commitment folds in (the
    // CellSeal/Unseal/Destroy root-gap close): carry the pre-state discriminant + bound cert hash
    // so the verified executor's post-state lifecycle reconstitutes onto the Rust cell.
    let mut lifecycle: Vec<(u64, u64)> = Vec::new();
    let mut death_cert: Vec<(u64, u64)> = Vec::new();

    let mut sorted: Vec<_> = pre.id_map.iter().collect();
    sorted.sort_by_key(|(_, nat)| *nat);

    for (cell_id, nat) in sorted {
        // A referenced cell absent from the ledger (e.g. a fresh-create target) gets an
        // empty record; the gate decides admissibility. We only emit cells we snapshotted.
        let Some(cell) = pre.cells.get(cell_id) else {
            continue;
        };
        let mut fields = Vec::new();
        fields.push((
            "balance".to_string(),
            WireValue::Int(cell.state.balance() as i128),
        ));
        fields.push((
            "nonce".to_string(),
            WireValue::Int(cell.state.nonce() as i128),
        ));
        for (idx, value) in cell.state.fields.iter().enumerate() {
            if field_is_zero(value) {
                continue;
            }
            let name = field_index_to_name(idx);
            fields.push((name, WireValue::Int(field_to_i128(value))));
        }
        cells.push((*nat, WireValue::Record(fields)));
        bal.push((*nat, 0, cell.state.balance() as i128));

        // Carry the cell's REAL c-list (`capabilities`) as wire `caps` so the verified
        // kernel's authority gates (`authorizedB` / `mintAuthorizedB`) read the actual
        // edges the actor holds — NOT a fabricated table. Each `CapabilityRef { target, … }`
        // is an edge to `target`; we project it to `Cap::Node(target_id)` (the `node` cap the
        // Lean gate reads as full authority over the target). An edge whose target is not in
        // the turn's id map is dropped (it cannot be referenced by any wire action), keeping
        // the table closed. An empty c-list (the corpus default) yields no entry — so a
        // cap-PRIVILEGED effect (Burn/RevokeCapability) correctly FAILS the Lean gate, which
        // is the genuine, non-vacuous test of the authority leg.
        let edges: Vec<Cap> = cell
            .capabilities
            .iter()
            .filter_map(|cref| id_map_lookup(pre, &cref.target).map(Cap::Node))
            .collect();
        if !edges.is_empty() {
            caps.push((*nat, edges));
        }

        // Per-cell lifecycle discriminant (0=Live, 1=Sealed, 3=Destroyed); a Live cell carries no
        // entry (the wire stays minimal, matching the kernel's `cellNatsOfFun` drop-zero filter).
        let lc_disc = lifecycle_discriminant(&cell.lifecycle);
        if lc_disc != 0 {
            lifecycle.push((*nat, lc_disc));
        }
        if let dregg_cell::lifecycle::CellLifecycle::Destroyed {
            death_certificate_hash,
            ..
        } = &cell.lifecycle
        {
            death_cert.push((*nat, low_u64_be(death_certificate_hash)));
        }
    }

    Ok(WireState {
        cells,
        caps,
        bal,
        escrows: vec![],
        nullifiers: vec![],
        commitments: vec![],
        queues: vec![],
        swiss: vec![],
        revoked: vec![],
        lifecycle,
        death_cert,
    })
}

/// The kernel-model lifecycle discriminant for a Rust `CellLifecycle` (mirrors
/// `CellLifecycle::discriminant`: 0=Live, 1=Sealed, 3=Destroyed; the kernel models only these three
/// Wave-3 states, so Migrated(2)/Archived(4) fall back as their own discriminant).
#[cfg(feature = "lean-shadow")]
fn lifecycle_discriminant(lc: &dregg_cell::lifecycle::CellLifecycle) -> u64 {
    use dregg_cell::lifecycle::CellLifecycle;
    match lc {
        CellLifecycle::Live => 0,
        CellLifecycle::Sealed { .. } => 1,
        CellLifecycle::Migrated { .. } => 2,
        CellLifecycle::Destroyed { .. } => 3,
        CellLifecycle::Archived { .. } => 4,
    }
}

/// The low 64 bits (big-endian) of a 32-byte digest — the kernel models hashes as `Nat` and the wire
/// carries the low `u64` for the death-cert table (the high 192 bits are the residual hash-fidelity
/// gap the kernel's `Nat` payload model does not yet carry).
#[cfg(feature = "lean-shadow")]
fn low_u64_be(h: &[u8; 32]) -> u64 {
    u64::from_be_bytes(h[24..32].try_into().unwrap())
}

/// Look up a `CellId`'s wire Nat in the snapshot's id map (for c-list edge projection).
#[cfg(feature = "lean-shadow")]
fn id_map_lookup(pre: &ShadowPreLedger, c: &CellId) -> Option<u64> {
    pre.id_map.get(c).copied()
}

#[cfg(feature = "lean-shadow")]
fn turn_to_wire_turn(
    turn: &Turn,
    pre: &ShadowPreLedger,
    block_height: u64,
) -> Result<dregg_lean_ffi::marshal::WireTurn, String> {
    use dregg_lean_ffi::marshal::{Cap, WForest, WChild, WireTurn};

    let agent = *pre
        .id_map
        .get(&turn.agent)
        .ok_or_else(|| "shadow: agent cell not in id map".to_string())?;

    let valid_until = turn
        .valid_until
        .and_then(|v| u64::try_from(v).ok())
        .ok_or_else(|| "shadow: turn.valid_until required for wire marshal".to_string())?;

    let prev_hash = turn
        .previous_receipt_hash
        .map(digest_of)
        .unwrap_or_default();

    // The WHOLE forest, pre-order, as (wire action, originating credential) pairs.
    let mapped = flatten_forest_actions_full(turn, pre)
        .ok_or_else(|| "shadow: forest not fully marshallable".to_string())?;

    let mut iter = mapped.into_iter();
    let head = iter
        .next()
        .ok_or_else(|| "shadow: empty mapped forest".to_string())?;

    // The tail actions become `null`-cap delegation children of the root, run SEQUENTIALLY
    // by the Lean executor against the evolving state (no cap handoff). Each child still
    // carries its own credential and is gated per-node by `execFullA`.
    let children: Vec<WChild> = iter
        .map(|m| WChild {
            holder: agent,
            keep: vec![],
            parent_cap: Cap::Null,
            sub: WForest {
                auth: m.wire_auth,
                caveats: vec![],
                action: m.action,
                children: vec![],
            },
        })
        .collect();

    Ok(WireTurn {
        agent,
        nonce: turn.nonce,
        fee: turn.fee as i128,
        valid_until,
        block_height,
        prev_hash,
        root: WForest {
            auth: head.wire_auth,
            caveats: vec![],
            action: head.action,
            children,
        },
    })
}

/// A fully-resolved wire action with its credential (FFI build only).
#[cfg(feature = "lean-shadow")]
struct FullMapped {
    action: WireAction,
    wire_auth: dregg_lean_ffi::marshal::WireAuth,
}

/// Flatten the forest into wire actions paired with their originating credential. Each
/// Rust action's auth decorates every effect-node it produced.
#[cfg(feature = "lean-shadow")]
fn flatten_forest_actions_full(
    turn: &Turn,
    pre: &ShadowPreLedger,
) -> Option<Vec<FullMapped>> {
    let mut out = Vec::new();
    // A single fresh-id counter threaded across the WHOLE pre-order walk, so each created
    // cell/queue gets a distinct never-snapshotted wire Nat (no cross-effect id collision).
    let mut fresh_seq: u64 = 0;
    for root in &turn.call_forest.roots {
        flatten_tree_full(root, pre, &mut out, &mut fresh_seq, &turn.agent)?;
    }
    if out.is_empty() {
        return None;
    }
    Some(out)
}

#[cfg(feature = "lean-shadow")]
fn flatten_tree_full(
    tree: &CallTree,
    pre: &ShadowPreLedger,
    out: &mut Vec<FullMapped>,
    fresh_seq: &mut u64,
    agent: &CellId,
) -> Option<()> {
    let actor = *pre.id_map.get(&tree.action.target)?;
    let wire_auth = auth_to_wire(&tree.action.authorization);
    for eff in &tree.action.effects {
        let action = effect_to_wire(actor, eff, pre, fresh_seq, agent)?;
        out.push(FullMapped {
            action,
            wire_auth: wire_auth.clone(),
        });
    }
    for child in &tree.children {
        flatten_tree_full(child, pre, out, fresh_seq, agent)?;
    }
    Some(())
}

// ===================================================================
// AUTH — carry the credential WHO-leg in FULL (no zeroed digests).
// ===================================================================

#[cfg(feature = "lean-shadow")]
fn auth_to_wire(auth: &Authorization) -> dregg_lean_ffi::marshal::WireAuth {
    use dregg_lean_ffi::marshal::{Digest, WireAuth};
    match auth {
        Authorization::Signature(pk, sig) => WireAuth::Signature {
            pubkey: digest_from_halves(pk, sig),
            sig: bytes32_to_nat(sig),
        },
        // dregg1's `Unchecked` means "no signature presented; authority is decided by the
        // c-list / ownership, NOT a credential" — apply.rs admits it when the cell's
        // permission tier is `None` (open) or the actor owns/holds a cap on the target. The
        // verified gated kernel's `portalVerify .unchecked = false` is a FAIL-CLOSED §8 anchor
        // (a turn carrying NO credential cannot pass the WHO leg), so marshalling `Unchecked`
        // to the Lean `.unchecked` would roll EVERY such turn back at the gate — diverging from
        // apply.rs on every authority-by-ownership move (the marshaller-faithfulness gap the
        // ledger records). The faithful projection is the `.breadstuff` credential: it passes
        // the WHO leg (`portalVerify .breadstuff = true`, "pure c-list read; the WHAT leg
        // gates") and DEFERS the real authority decision to `execFullA`'s `authorizedB`
        // (actor owns `src`, or holds a `node`/`write`-endpoint cap) — exactly the
        // ownership/c-list check apply.rs runs for an `Unchecked` move. So an authorized
        // ownership move COMMITS in both; an unauthorized one (`actor ≠ src`, no cap) or an
        // overspend still FAILS inside `recKExecAsset` (body rolls back ⇒ `ok:0`), matching
        // apply.rs's rejection — the gap closes WITHOUT weakening either gate.
        Authorization::Unchecked => WireAuth::Breadstuff { token: 0 },
        Authorization::Breadstuff(token) => WireAuth::Breadstuff {
            token: bytes32_to_nat(token),
        },
        Authorization::Proof {
            proof_bytes,
            bound_action,
            bound_resource,
        } => WireAuth::Proof {
            vk: Digest::from_bytes(blake3_of(proof_bytes)),
            proof: bytes_to_nat(proof_bytes),
            bound_action: str_to_nat(bound_action),
            bound_resource: str_to_nat(bound_resource),
        },
        Authorization::Bearer(proof) => {
            let (deleg_msg, deleg_sig, stark) = match &proof.delegation_proof {
                DelegationProofData::SignedDelegation {
                    delegator_pk,
                    signature,
                    ..
                } => (
                    Digest::from_bytes(*delegator_pk),
                    sig64_to_nat(signature),
                    false,
                ),
                DelegationProofData::StarkDelegation {
                    proof_bytes,
                    root_issuer_commitment,
                } => (
                    Digest::from_bytes(*root_issuer_commitment),
                    bytes_to_nat(proof_bytes),
                    true,
                ),
            };
            WireAuth::Bearer {
                deleg_msg,
                deleg_sig,
                stark,
            }
        }
        Authorization::CapTpDelivered {
            introducer_pk,
            sender_pk,
            sender_signature,
            ..
        } => WireAuth::CapTpDelivered {
            intro_msg: Digest::from_bytes(*introducer_pk),
            sender_msg: Digest::from_bytes(*sender_pk),
            intro_sig: 0,
            sender_sig: sig64_to_nat(sender_signature),
        },
        // The predicate's commitment is the credential WHO-leg the gate reads; carry it in
        // full rather than collapsing to {0,0}.
        Authorization::Custom { predicate } => WireAuth::Custom {
            kind_stmt: Digest::from_bytes(predicate_commitment(predicate)),
            proof: predicate_proof_nat(predicate),
        },
        Authorization::OneOf {
            candidates,
            proof_index,
        } => WireAuth::OneOf {
            candidates: candidates.iter().map(auth_to_wire).collect(),
            proof_index: *proof_index as u64,
        },
        Authorization::Stealth {
            one_time_pubkey,
            ephemeral_pubkey,
            signature,
            ..
        } => WireAuth::Stealth {
            one_time_pk: Digest::from_bytes(*one_time_pubkey),
            ephemeral_pk: Digest::from_bytes(*ephemeral_pubkey),
            sig: sig64_to_nat(signature),
        },
        // The token's issuer key / cell-scoped anchor is the WHO-leg; carry it in full.
        Authorization::Token { key_ref, .. } => match key_ref {
            crate::action::TokenKeyRef::BiscuitIssuer { issuer_pubkey } => WireAuth::Token {
                issuer_key: Digest::from_bytes(*issuer_pubkey),
                sig: 0,
            },
            crate::action::TokenKeyRef::CellScopedMacaroon { cell } => WireAuth::Custom {
                kind_stmt: Digest::from_bytes(cell.0),
                proof: 0,
            },
        },
    }
}

#[cfg(feature = "lean-shadow")]
fn predicate_commitment(p: &dregg_cell::predicate::WitnessedPredicate) -> [u8; 32] {
    // Hash the predicate's serialized form as a stable WHO-commitment. The exact preimage
    // need not match the kernel byte-for-byte (the kernel only reads the digest as an
    // opaque WHO label); what matters is that it is NON-ZERO and tamper-sensitive.
    let bytes = postcard::to_allocvec(p).unwrap_or_default();
    blake3_of(&bytes)
}

#[cfg(feature = "lean-shadow")]
fn predicate_proof_nat(p: &dregg_cell::predicate::WitnessedPredicate) -> u64 {
    let bytes = postcard::to_allocvec(p).unwrap_or_default();
    bytes_to_nat(&bytes)
}

// ---- digest / nat helpers ----

#[cfg(feature = "lean-shadow")]
fn digest_of(hash: [u8; 32]) -> dregg_lean_ffi::marshal::Digest {
    dregg_lean_ffi::marshal::Digest::from_bytes(hash)
}

/// A signature is two 32-byte halves; the "pubkey/message" digest the wire carries for the
/// `Signature` arm is the R half (the first 32 bytes), preserved in full.
#[cfg(feature = "lean-shadow")]
fn digest_from_halves(r: &[u8; 32], _s: &[u8; 32]) -> dregg_lean_ffi::marshal::Digest {
    dregg_lean_ffi::marshal::Digest::from_bytes(*r)
}

#[cfg(feature = "lean-shadow")]
fn blake3_of(bytes: &[u8]) -> [u8; 32] {
    *blake3::hash(bytes).as_bytes()
}

#[cfg(feature = "lean-shadow")]
fn field_index_to_name(index: usize) -> String {
    match index {
        2 => "name".into(),
        3 => "owner".into(),
        4 => "expiry".into(),
        5 => "revoked".into(),
        6 => "target".into(),
        other => format!("field_{other}"),
    }
}

#[cfg(feature = "lean-shadow")]
fn field_to_i128(field: &FieldElement) -> i128 {
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&field[24..32]);
    u64::from_be_bytes(bytes) as i128
}

#[cfg(feature = "lean-shadow")]
fn field_is_zero(field: &FieldElement) -> bool {
    field.iter().all(|&b| b == 0)
}

#[cfg(feature = "lean-shadow")]
fn bytes32_to_nat(bytes: &[u8; 32]) -> u64 {
    let mut buf = [0u8; 8];
    buf.copy_from_slice(&bytes[24..32]);
    u64::from_be_bytes(buf)
}

#[cfg(feature = "lean-shadow")]
fn sig64_to_nat(sig: &[u8; 64]) -> u64 {
    let mut buf = [0u8; 8];
    buf.copy_from_slice(&sig[56..64]);
    u64::from_be_bytes(buf)
}

#[cfg(feature = "lean-shadow")]
fn bytes_to_nat(bytes: &[u8]) -> u64 {
    let mut buf = [0u8; 8];
    let n = bytes.len().min(8);
    buf[8 - n..].copy_from_slice(&bytes[bytes.len() - n..]);
    u64::from_be_bytes(buf)
}

#[cfg(feature = "lean-shadow")]
fn str_to_nat(s: &str) -> u64 {
    bytes_to_nat(s.as_bytes())
}

#[cfg(feature = "lean-shadow")]
fn permissions_to_i128(_perms: &dregg_cell::Permissions) -> i128 {
    // Permissions are a structured value; the wire `setperms` arm carries a scalar. We
    // encode 0 as a neutral marker (the executor models perms abstractly). This is the one
    // place a structured field collapses; SetPermissions turns are still shadowed for the
    // commit-bit decision, which does not depend on the exact perms scalar.
    0
}

#[cfg(feature = "lean-shadow")]
fn event_data_to_i128(_event: &crate::action::Event) -> i128 {
    0
}

#[cfg(test)]
mod producer_coverage_tests {
    use super::*;

    /// The public coverage list must stay non-empty, deduplicated, and every entry must be a
    /// real effect-kind name. Guards against silent shrinkage of the producer-default surface
    /// (a shrink would quietly demote effects back to the Rust producer).
    #[test]
    fn covered_effects_are_well_formed() {
        let covered = producer_covered_effects();
        assert!(!covered.is_empty(), "producer coverage must not be empty");
        let mut seen = std::collections::HashSet::new();
        for name in covered {
            assert!(seen.insert(*name), "duplicate effect in coverage list: {name}");
            assert!(producer_covers_kind(name), "producer_covers_kind disagrees for {name}");
        }
        // Twenty-one effect kinds are projected to the wire today (mirrors effect_is_mappable).
        assert_eq!(covered.len(), 21, "producer coverage count changed — update the report and confirm effect_is_mappable agrees");
    }

    /// Every covered effect must appear in the full enumeration, and the
    /// uncovered list must be exactly the complement (no overlaps, full cover).
    #[test]
    fn coverage_partitions_the_effect_surface() {
        let all: std::collections::HashSet<&str> = all_effect_kinds().iter().copied().collect();
        assert_eq!(all.len(), all_effect_kinds().len(), "all_effect_kinds has duplicates");
        for c in producer_covered_effects() {
            assert!(all.contains(c), "covered effect {c} missing from all_effect_kinds");
        }
        let uncovered: std::collections::HashSet<&str> =
            producer_uncovered_effects().into_iter().collect();
        // Partition: covered ∪ uncovered = all, covered ∩ uncovered = ∅.
        assert_eq!(
            producer_covered_effects().len() + uncovered.len(),
            all.len(),
            "covered + uncovered must equal the full effect surface"
        );
        for c in producer_covered_effects() {
            assert!(!uncovered.contains(c), "{c} is both covered and uncovered");
        }
    }
}
