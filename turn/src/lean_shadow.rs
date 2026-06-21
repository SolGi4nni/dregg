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

#[cfg(not(feature = "no-lean-link"))]
use dregg_cell::state::FieldElement;
use dregg_cell::{Cell, CellId, Ledger};

use crate::action::Effect;
#[cfg(not(feature = "no-lean-link"))]
use crate::action::{Authorization, DelegationProofData};
use crate::forest::CallTree;
use crate::turn::{Turn, TurnResult};

/// Minimal pre-execution ledger snapshot for shadow marshalling.
///
/// The fields are read only by the FFI-build marshaller (`ledger_to_wire_state` /
/// `turn_to_wire_turn`); the non-feature build still captures the snapshot so eligibility
/// is decided identically, hence the conditional `allow(dead_code)`.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "no-lean-link", allow(dead_code))]
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
///
/// # The host obligation (Lean: `Dregg2.Exec.HostCorrespondence`, AssuranceCase seam §2)
///
/// The verified gate's conditional soundness lemma `admissible_sound_of_reflects` proves: IF this
/// context FAITHFULLY REFLECTS the node's true runtime facts (`HostFacts`: true clock / freeze-set /
/// stored head / budget) THEN the gate decides EXACTLY as the node's own state would. The teeth
/// (`{stored_head,budget,freeze,clock}_obligation_teeth`) show each field is load-bearing: an unsafe
/// under-report (omit a truly-frozen referenced cell, advance the head to a forked turn's `prev`,
/// inflate the budget, retard the clock) ADMITS a turn the true-facts gate REJECTS. So the production
/// executor MUST override every field below from its own `self` state — never `diag()`. The only
/// residual is producer-coverage: every cell the freeze gate reads (agent + write-set) must get a
/// wire id; the `frozen` projection here (`run_shadow`'s `filter_map(id_map.get)`) is faithful on
/// exactly those read cells (`marshalled_admission_sound`).
#[derive(Clone, Debug)]
#[cfg_attr(feature = "no-lean-link", allow(dead_code))]
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
    /// The executor's `max_introduction_lifetime` (`self.max_introduction_lifetime`). An
    /// `Introduce` stamps the granted cap's `expires_at = block_height + max_introduction_lifetime`;
    /// the cap-fidelity reconstitution (`lean_apply::collect_cap_ops`) needs the SAME value to
    /// rebuild the introduced cap's leaf byte-exactly. Defaults to the executor default (1000).
    pub intro_lifetime: u64,
    /// The executor's local federation id (`self.local_federation_id`). The `Authorization::Signature`
    /// WHO leg binds the ed25519 signing message to THIS federation
    /// (`compute_signing_message`/`compute_partial_signing_message`), so the producer marshaller must
    /// recompute the SAME message the executor's `verify_ed25519_signature` checks. A genuine sig is
    /// then folded into the wire as a self-echoing `(statement, proof)` pair (admits); a forged /
    /// cross-federation / tampered one fails the recomputed `verify_strict` and the wire DOES NOT echo
    /// (the gate's WHO leg fail-closes). Defaults to the all-zero id (the test/round-trip federation).
    pub federation_id: [u8; 32],
}

impl ShadowHostCtx {
    /// The DIAGNOSTIC host context — never spuriously rejects. The PRODUCTION executor MUST
    /// override every field from its own state (that override is what makes bug-1 real).
    pub fn diag() -> Self {
        ShadowHostCtx {
            block_height: 0,
            frozen: vec![],
            stored_head: None,
            budget: 1_000_000_000,
            intro_lifetime: 1000,
            federation_id: [0u8; 32],
        }
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

    #[cfg(not(feature = "no-lean-link"))]
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

    #[cfg(feature = "no-lean-link")]
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

        Effect::SpawnWithDelegation { .. } => "SpawnWithDelegation",
        Effect::RefreshDelegation { .. } => "RefreshDelegation",
        Effect::RevokeDelegation { .. } => "RevokeDelegation",
        Effect::BridgeMint { .. } => "BridgeMint",

        Effect::Introduce { .. } => "Introduce",
        Effect::PipelinedSend { .. } => "PipelinedSend",

        Effect::ExerciseViaCapability { .. } => "ExerciseViaCapability",
        Effect::MakeSovereign { .. } => "MakeSovereign",
        Effect::CreateCellFromFactory { .. } => "CreateCellFromFactory",

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
        "GrantCapability",
        "AttenuateCapability",
        "Introduce",
        // §FACTORY-DISSOLVED: the escrow/obligation/queue/bridge-3phase/caps-in-slots
        // families no longer EXIST as Effect variants (the verb lockstep deleted them);
        // their semantics live in factory-born cells (cell::blueprint + sdk::factories,
        // Lean contracts in Dregg2/Apps/*Factory + CapSlotFactory).
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
/// agree on the cell-ledger `.root()`.
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
        // (F2b: QueueAllocate left this set with the FACTORY-DISSOLVED queue family — the verified
        // kernel no longer parses queue wire actions; queue behavior is the factory story.)
        // CAP-FIDELITY ROOT-GAP CLOSE (the cap-reshape lever). GrantCapability / Introduce /
        // AttenuateCapability are now root-AGREEING: the verified kernel DECIDES the commit bit (the
        // delegator/introducer must hold the edge; the attenuation must be a monotone narrowing —
        // the non-amplification / production-authority gate), and `lean_apply::apply_cap_ops` replays
        // the turn's deterministic, turn-specified cap mutation onto the EXACT pre-state c-list
        // (`grant_ref` / `grant_with_expiry` / `attenuate_in_place`, mirroring `executor::apply`
        // byte-for-byte). So the reconstituted `cap_root` (= `compute_canonical_capability_root` over
        // the rebuilt 7-field leaves) EQUALS the Rust producer's. The leaf-field VALUES are not
        // kernel state — they come from the turn — so carrying them on the wire is unnecessary; the
        // kernel's verified authority decision is the load-bearing leg, and the commit-gated replay
        // is the faithful, deterministic install. Pinned by the `lean_state_producer_capfidelity`
        // differential (Lean root == Rust differential == canonical cap-root; a forged/over-amplified
        // grant is REJECTED so the c-list does not move).
        "GrantCapability",
        "Introduce",
        "AttenuateCapability",
        // CellUnseal (Sealed→Live): the verified `cellUnsealChainA` flips the lifecycle discriminant
        // back to `lcLive` (0), and `CellLifecycle::Live` is the ONE lifecycle state with NO payload —
        // so the wire (which carries the discriminant alone) reconstitutes it BYTE-EXACTLY. The
        // reconstitution (`lean_apply::wire_state_to_ledger`) installs `CellLifecycle::Live`, clearing
        // the template's Sealed payload, so `compute_canonical_state_commitment`'s `lifecycle` fold
        // produces the SAME bytes as Rust's `Cell::unseal` (which sets `lifecycle = Live`).
        "CellUnseal",
        // LIFECYCLE ROOT-GAP CLOSE (the SURVIVOR-effect lever, same shape as the cap-fidelity
        // close). CellSeal/CellDestroy install a lifecycle PAYLOAD the wire's bare discriminant
        // cannot carry — but the payload is TURN + HOST data, not kernel state: `Sealed
        // { reason_hash, sealed_at }` = the turn's `CellSeal { reason }` + the host block height;
        // `Destroyed { death_certificate_hash, destroyed_at }` = the turn's FULL DeathCertificate
        // (`certificate_hash()` / `destroyed_at_height` — never the lossy low-64 wire `death_cert`
        // value). The verified kernel DECIDES the commit (`cellSealA`/`cellDestroyA`:
        // `stateAuthB ∧ acceptsEffects` / `≠ Destroyed`), and `lean_apply::apply_state_ops` replays
        // `Cell::seal`/`Cell::destroy` — the SAME cell-side primitives `apply_cell_seal`/
        // `apply_cell_destroy` call — onto the template pre-state, so the commitment's lifecycle
        // fold is byte-exact. An unauthorized/terminal transition is rejected by BOTH executors
        // and the lifecycle does not move (the non-vacuous tooth, pinned in the widen tests).
        "CellSeal",
        "CellDestroy",
        // PERM/VK-STRUCT ROOT-GAP CLOSE. The wire `setperms`/`setvk` arms carry a collapsed scalar,
        // but the full 8-field `Permissions` struct / `VerificationKey { hash, data }` is entirely
        // TURN-supplied. The verified `setPermissionsA`/`setVKA` gates (`stateAuthB`-routed
        // stateStep) decide the commit; `lean_apply::apply_state_ops` installs the turn's exact
        // struct (mirroring `apply_set_permissions`/`apply_set_verification_key`, including the
        // blake3 vk-integrity refusal), so the commitment's permissions/vk folds are byte-exact.
        "SetPermissions",
        "SetVerificationKey",
        // STRUCTURAL ROOT-GAP CLOSE for MakeSovereign. Rust REMOVES the cell from `Ledger::cells`
        // (→ its merkle leaf disappears) and parks `state_commitment()` in `sovereign_commitments`
        // (off-root); the verified `makeSovereignStep` performs the SAME regime move
        // (`sovereignRebind`: the readable record is dropped behind a commitment), gated on
        // `stateAuthB`. The reconstitution replays `Ledger::make_sovereign` at build time, so the
        // reconstituted leaf SET — and therefore `.root()` — equals Rust's. (The rebound wire
        // record is commitment-only, so the extractor skips it rather than fail-closing.)
        "MakeSovereign",
        // DELEGATION-EPOCH ROOT-GAP CLOSE for RevokeDelegation. A committing revoke bumps the
        // PARENT's `delegation_epoch` and clears the CHILD's `delegation` snapshot (both folded
        // into `compute_canonical_state_commitment`); neither crosses the wire, but the mutation
        // is fully deterministic from the turn (`bump_delegation_epoch()` + `delegation = None`,
        // mirrored from `apply_revoke_delegation` including its pre-state
        // `child.delegate == Some(parent)` gate). The replay also restores the parent's template
        // c-list (Rust's revoke arm never edits the c-list; the verified `revokeDelegationA` is
        // the cap-graph `removeEdge`, whose lossy wire echo must not leak into `cap_root`).
        // RESIDUAL (characterized): the verified guard is `True` (revocation is unconditional)
        // while Rust rejects a revoke of a non-delegated child — for such a turn the commit bits
        // differ. Under THE AUTHORITY INVERSION (Stage 0) the verified Lean verdict is
        // AUTHORITATIVE: the disagreement surfaces as a Rust bug (`LeanAuthoritative
        // { rust_agreed: false }`) and the LEAN verdict is committed (Rust does NOT win). The
        // replay's edge gate leaves every field at its pre-state, so the authoritative post-state
        // still equals the pre-state — only the commit bit / finding is Lean-driven.
        "RevokeDelegation",
        // §SIDE-TABLE holding-store families — the off-cell-merkle-root escrow/obligation effects.
        // `apply_create_escrow`/`apply_create_obligation` debit ONE cell's `balance` (which the `bal`
        // side-table carries → reconstitutes) and park the value in the off-root `escrows`/
        // `obligations` store; the verified `createEscrowKAsset` (and the `createObligationA`
        // dispatch-alias) do the SAME single-cell `bal` debit + record insert, gated on the same
        // transfer-authority + balance + account + id-uniqueness legs. Only the CREATE effects are
        // root-AGREEING here: the side-table records never feed `cell::Ledger::root()`, so the
        // reconstituted `.root()` AGREES with Rust (only the `bal` debit changes, and it
        // reconstitutes). NOTE the escrow/obligation family is FACTORY-DISSOLVED (see
        // `producer_mappable_effects`): the verified kernel does not parse those actions, so they
        // are no longer in the producer surface at all.
    ]
}

/// The CHARACTERIZED SWAP-GAPS: mappable effects (the producer RUNS) whose Lean-reconstituted
/// `.root()` (or commit bit) DIVERGES from Rust. Each is pinned by a NEGATIVE-tooth differential
/// (`lean_state_producer_widen` + `lean_state_producer_coverage`) that asserts the SPECIFIC
/// divergence, so the gap is named, never a silent pass. The honest residual of THE SWAP:
///   * `Refusal`/`ReceiptArchive` — Rust writes an audit-field / lifecycle-Archived commitment the
///     wire `refusal`/`rarchive` arms do not reproduce byte-for-byte.
///   * `ReleaseEscrow`/`RefundEscrow` — commit-bit gaps (condition-proof / past-timeout legs), see
///     below. (Effect family slated for kernel deletion in the dregg3 reduction.)
///
/// NO LONGER GAPS (each closed by the commit-gated turn/host-replay lever, the values the wire
/// drops being turn/host data rather than kernel state — see `producer_root_agreeing_effects`):
/// the cap-fidelity trio (GrantCapability/Introduce/AttenuateCapability via `apply_cap_ops`), the
/// lifecycle pair (CellSeal/CellDestroy via `apply_state_ops`' `Cell::seal`/`Cell::destroy`
/// replay), the struct pair (SetPermissions/SetVerificationKey — full turn-supplied structs), the
/// structural MakeSovereign (`Ledger::make_sovereign` replay), and RevokeDelegation (the
/// deterministic parent-epoch bump + child-snapshot clear).
pub fn producer_root_gap_effects() -> &'static [&'static str] {
    &[
        "Refusal",
        "ReceiptArchive",
        // (The escrow/obligation settle effects are FACTORY-DISSOLVED — out of the producer
        // surface entirely; see `producer_mappable_effects`. Their condition/timeout gates are
        // enforced by the factory cell programs now.)
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
        "SpawnWithDelegation",
        "RefreshDelegation",
        "RevokeDelegation",
        "BridgeMint",
        "Introduce",
        "PipelinedSend",
        "ExerciseViaCapability",
        "MakeSovereign",
        "CreateCellFromFactory",
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
#[cfg(not(feature = "no-lean-link"))]
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
    let host = ShadowHostCtx {
        block_height,
        ..ShadowHostCtx::diag()
    };
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
#[cfg(feature = "no-lean-link")]
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
/// the characterized root-GAP effects (Refusal / ReceiptArchive / the escrow-settle pair) whose
/// Lean-reconstituted root (or commit bit) provably DIVERGES from Rust because the wire
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
    // A child edge is marshallable only when `tree_to_wforest` can faithfully (and SOUNDLY)
    // reconstruct it — the two MUST agree (eligibility ⟺ marshallable). A cross-cell, non-bearer
    // child has no verdict-equivalent cap-install image on this wire (the executor's delegate-chain
    // authority differs from `recKDelegateAtten`), so the turn is ineligible for the shadow rather
    // than marshalled as committable (which could admit what the executor denies — the unsound veto
    // direction). Same-cell and bearer children ARE marshallable (direct null-cap subtrees).
    for child in &tree.children {
        let cross_cell = child.action.target != tree.action.target;
        let is_bearer = matches!(
            &child.action.authorization,
            crate::action::Authorization::Bearer(_)
        );
        if cross_cell && !is_bearer {
            return false;
        }
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
        Effect::RefreshDelegation { child, .. } => has(child),
        Effect::CellSeal { target, .. } => has(target),
        Effect::CellUnseal { target } => has(target),
        Effect::CellDestroy { target, .. } => has(target),
        // Burn: ONLY the canonical balance slot (`slot == 0`) is modelled; other slots are
        // left unmapped (skip the turn rather than mis-encode).
        Effect::Burn {
            target, slot: 0, ..
        } => has(target),
        Effect::RevokeCapability { cell, .. } => has(cell),
        // AttenuateCapability: dregg1 narrows a HELD c-list slot in place (apply.rs requires
        // `cell == actor`). The verified `attenuateStepA actor idx keep` narrows the actor's own
        // `idx`-th held cap (a TOTAL self-narrowing — always commits, `List.modify` is a no-op for an
        // out-of-range slot). The action target is the actor's own cell; we require it in the id map.
        // Root-AGREEING via the cap-fidelity lever: the narrowed leaf is reconstructed exactly by
        // the commit-gated turn-driven replay (`lean_apply::apply_cap_ops` → `attenuate_in_place`).
        Effect::AttenuateCapability { cell, .. } => has(cell),
        // ─── GAP-shrink batch (the swap surface, MUST mirror effect_to_wire) ─────────────
        // QueueAllocate: the action target IS the gate cell (always in the map). The fresh
        // queue id is intrinsic (assigned deterministically), so the effect is always mappable.

        // GrantCapability: dregg1 `del`. The granter `from`, grantee `to`, and the cap target
        // must all be in the id map (the wire `del` carries delegator + recipient + target Nats).
        Effect::GrantCapability { from, to, cap } => has(from) && has(to) && has(&cap.target),
        // Introduce: dregg1 three-party introduction. The wire `introduce` arm carries
        // (introducer, recipient, target) Nats; all three must be in the id map. The verified
        // `introduceA` routes to `recCDelegate introducer recipient target`, gated on the
        // introducer holding an edge to `target` (the production-authority leg). The granted leaf
        // (target, permissions, host-derived expiry) is reconstructed EXACTLY by the commit-gated
        // turn-driven replay (`lean_apply::apply_cap_ops`), so the cap_root agrees. RESIDUAL: the
        // verified gate is the edge-existence leg only — Rust ALSO requires introducer↦recipient
        // access + monotone-attenuation + target consent. For a turn where those diverge the
        // commit bits differ; under THE AUTHORITY INVERSION (Stage 0) the verified Lean verdict is
        // AUTHORITATIVE and the disagreement surfaces as a Rust bug (`LeanAuthoritative
        // { rust_agreed: false }`), the LEAN verdict committed (Rust does NOT win).
        Effect::Introduce {
            introducer,
            recipient,
            target,
            ..
        } => has(introducer) && has(recipient) && has(target),
        // ─── §SIDE-TABLE families (the holding-store batch — MUST mirror effect_to_wire) ────────
        // ESCROW (root-AGREEING). `apply_create_escrow` debits the creator's `balance` and parks the
        // value in the off-cell-merkle-root `escrows` store; the verified `createEscrowKAsset` does
        // the SAME single-cell `bal` debit (recDebit) + record insert, gated on the same `authorizedB`
        // transfer leg + balance + account + id-uniqueness. The debit reconstitutes via the `bal`
        // side-table and the record is off-root, so the reconstituted `.root()` AGREES with Rust.

        // release/refund settle effects look the record up by id (off-root) and single-cell CREDIT
        // the recipient/creator (`recCredit` ⟺ `set_balance(old + amount)`). Mappable when the id is
        // non-null; the credited cell is read from the record (no extra cells to name).

        // OBLIGATION CREATE (root-AGREEING). `apply_create_obligation` debits the obligor
        // (action target) `balance` + inserts an off-root `ObligationRecord`; the verified
        // `createObligationA` dispatch-aliases to `createEscrowChainA` (the SAME single-cell debit +
        // record insert). A create-only obligation turn therefore round-trips: only `bal` changes
        // (reconstitutes) and the record is off-root. The settle effects (fulfill/slash) reference
        // the Rust-DERIVED obligation id, which the wire-id collapse cannot reproduce, so they are
        // characterized root-gaps (record-lookup divergence), not mapped here.

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

        // Settle effects (release/refund/fulfill/slash) carry only an id; the credited cell is
        // read from the record, so the actor (action target) — already collected — suffices.

        // QueueAllocate creates a FRESH queue cell whose id is NOT in the pre-state id map; only
        // the actor (the action target) needs a Nat, collected by `collect_tree_ids` already. The
        // fresh id is assigned deterministically in `effect_to_wire` (above the pre-id-map range)
        // so it never collides with a snapshot id.
        _ => vec![],
    }
}

/// A deterministic FRESH wire Nat for a created cell/queue, placed ABOVE the pre-state id-map
/// range so it never collides with a snapshotted cell's Nat. The id map assigns `0..n`; we
/// offset created ids by `FRESH_ID_BASE + seq` where `seq` is the created-thing's index in the
/// pre-order walk. Both executors then see a never-before-used id, so the insert always succeeds
/// (no spurious duplicate-id rejection on either side).
#[cfg(not(feature = "no-lean-link"))]
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
#[cfg(not(feature = "no-lean-link"))]
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
        Effect::SetPermissions {
            cell,
            new_permissions,
        } => WireAction::SetPerms {
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
        Effect::NoteSpend {
            nullifier,
            spending_proof,
            ..
        } => WireAction::NoteSpend {
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
            new_nonce: (pre_nonce_of(pre, cell) as i128) + 1 + if cell == agent { 1 } else { 0 },
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
        Effect::ReceiptArchive { .. } => WireAction::ReceiptArchive { actor, cell: actor },
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
        Effect::CellDestroy {
            target,
            certificate,
        } => WireAction::CellDestroy {
            actor,
            cell: id(target)?,
            cert_hash: bytes32_to_nat(&certificate.certificate_hash()),
        },
        // Burn: dregg1 reduces a cell's balance with no destination credit (scalar supply
        // destruction). W1 (issuer-supply, DREGG3 §2.2): the verified `.burnA` is a
        // RETURN-TO-WELL move — `recKBurnAsset` transfers the amount from the holder back to
        // the asset's ISSUER cell (`AssetId := CellId`), gated on the issuer capability
        // (`mintAuthorizedB actor asset` ∧ holder availability ∧ `cell ≠ asset`), conserving
        // `Σ_c bal c a` EXACTLY. The Rust scalar burn has NO conserving image on this wire
        // (asset 0's "issuer" is whatever cell the snapshot numbered 0), so the verified
        // executor REFUSES these turns — a characterised SAFE-direction divergence (Lean
        // stricter; recorded by the ledger, vetoed under strict mode). Agreement returns when
        // the staged Rust value-model migration gives the native asset a genesis issuer well
        // (signed well balance) and apply.rs's burn becomes the well move. Only the canonical
        // balance slot (`slot == 0`) is modelled; a non-zero slot is left UNMAPPED so the turn
        // is skipped rather than mis-encoded.
        Effect::Burn {
            target,
            slot: 0,
            amount,
        } => WireAction::Burn {
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
        // the Lean post-state is the unchanged Node cap regardless. The EXACT narrowed leaf is
        // reconstructed instead by the commit-gated turn-driven replay (`lean_apply::apply_cap_ops`
        // → `attenuate_in_place`), which is what makes AttenuateCapability root-AGREEING.
        Effect::AttenuateCapability { cell, slot, .. } => WireAction::Attenuate {
            actor: id(cell)?,
            idx: *slot as u64,
            keep: vec![],
        },
        // RefreshDelegation: the child refreshes its delegation snapshot from its parent
        // (self-refresh — the actor IS the child). `.refreshDelegationA` routes to the chained
        // refresh step. The action target is the refreshing child cell.
        Effect::RefreshDelegation { child, .. } => WireAction::RefreshDelegation {
            actor,
            child: id(child)?,
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
        // Introduce: dregg1 three-party introduction. `.introduce introducer recipient target`
        // routes to `recCDelegate introducer recipient target` (the SAME generative delegation as
        // `del`), gated on the introducer holding an edge to `target`. The granted cap's leaf
        // (target + permissions + host-derived expiry) is not kernel state — it is reconstructed
        // EXACTLY by `lean_apply::apply_cap_ops` (`grant_with_expiry`), so cap_root agrees.
        Effect::Introduce {
            introducer,
            recipient,
            target,
            ..
        } => WireAction::Introduce {
            introducer: id(introducer)?,
            recipient: id(recipient)?,
            target: id(target)?,
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

        // ESCROW release/refund: look the record up by id, single-cell CREDIT the recipient/creator
        // (`recCredit` ⟺ `set_balance(old + amount)`), mark resolved. The credited cell is read from
        // the record (off-root), so only the id + actor cross the wire.

        // OBLIGATION create: dregg1 `apply_create_obligation` debits the OBLIGOR (= action target)
        // `balance` by `stake_amount` + inserts an off-root `ObligationRecord`. `.createObligationA id
        // actor obligor beneficiary asset stake` dispatch-aliases to `createEscrowChainA` (the SAME
        // single-cell debit + record insert). The obligor IS the action target (`actor`); the
        // beneficiary is the record's `recipient`. The wire `id` is the STAKE commitment collapsed —
        // a fresh-enough id for the create gate's uniqueness leg (the settle effects, which reference
        // the Rust-derived obligation id, are characterized root-gaps, not routed here).

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
#[cfg(not(feature = "no-lean-link"))]
fn pre_nonce_of(pre: &ShadowPreLedger, cell: &CellId) -> u64 {
    pre.cells.get(cell).map(|c| c.state.nonce()).unwrap_or(0)
}

#[cfg(not(feature = "no-lean-link"))]
use dregg_lean_ffi::marshal::WireAction;

#[cfg(not(feature = "no-lean-link"))]
fn run_shadow(turn: &Turn, pre: &ShadowPreLedger, host: &ShadowHostCtx) -> Result<bool, String> {
    use dregg_lean_ffi::marshal::marshal_turn_hosted;

    let block_height = host.block_height;
    let wire_state = ledger_to_wire_state(pre)?;
    let wire_turn = turn_to_wire_turn(turn, pre, host)?;
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
    let wire =
        marshal_turn_hosted(&host_wire, &wire_state, &wire_turn).map_err(|e| e.to_string())?;
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
#[cfg(not(feature = "no-lean-link"))]
pub(crate) fn run_shadow_state(
    turn: &Turn,
    pre: &ShadowPreLedger,
    host: &ShadowHostCtx,
) -> Result<dregg_lean_ffi::ShadowState, String> {
    use dregg_lean_ffi::marshal::marshal_turn_hosted;

    let block_height = host.block_height;
    let wire_state = ledger_to_wire_state(pre)?;
    let wire_turn = turn_to_wire_turn(turn, pre, host)?;
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
    let wire =
        marshal_turn_hosted(&host_wire, &wire_state, &wire_turn).map_err(|e| e.to_string())?;
    if std::env::var("DREGG_LEAN_SHADOW_DEBUG").as_deref() == Ok("1") {
        eprintln!("[shadow wire IN ] {wire}");
    }
    let out = dregg_lean_ffi::shadow_exec_full_forest_auth(&wire)?;
    if std::env::var("DREGG_LEAN_SHADOW_DEBUG").as_deref() == Ok("1") {
        eprintln!("[shadow wire OUT] {out}");
    }
    dregg_lean_ffi::decode_shadow_state(&out)
}

#[cfg(not(feature = "no-lean-link"))]
fn ledger_to_wire_state(
    pre: &ShadowPreLedger,
) -> Result<dregg_lean_ffi::marshal::WireState, String> {
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
#[cfg(not(feature = "no-lean-link"))]
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
#[cfg(not(feature = "no-lean-link"))]
fn low_u64_be(h: &[u8; 32]) -> u64 {
    u64::from_be_bytes(h[24..32].try_into().unwrap())
}

/// Look up a `CellId`'s wire Nat in the snapshot's id map (for c-list edge projection).
#[cfg(not(feature = "no-lean-link"))]
fn id_map_lookup(pre: &ShadowPreLedger, c: &CellId) -> Option<u64> {
    pre.id_map.get(c).copied()
}

#[cfg(not(feature = "no-lean-link"))]
fn turn_to_wire_turn(
    turn: &Turn,
    pre: &ShadowPreLedger,
    host: &ShadowHostCtx,
) -> Result<dregg_lean_ffi::marshal::WireTurn, String> {
    use dregg_lean_ffi::marshal::{Cap, WChild, WireTurn};

    let block_height = host.block_height;

    let agent = *pre
        .id_map
        .get(&turn.agent)
        .ok_or_else(|| "shadow: agent cell not in id map".to_string())?;

    let valid_until = turn
        .valid_until
        .and_then(|v| u64::try_from(v).ok())
        .ok_or_else(|| "shadow: turn.valid_until required for wire marshal".to_string())?;

    // The previous-receipt hash crosses as the SAME low-64 projection the host's `stored_head` uses
    // (`bytes32_to_nat`), so the verified `admissible` ChainHead leg (`h.prevReceipt = ctx.storedHead`)
    // compares like-for-like. `stored_head` is plumbed as a `u64` (the `WireHostCtx`/`AdmCtx` width), so
    // marshalling `prev` as a FULL 256-bit digest (the old `digest_of`) made `h.prevReceipt` (full Nat)
    // never equal `ctx.storedHead` (low-64) for ANY non-genesis receipt — rejecting every turn that
    // links to a real prior receipt (`status:0`). Folded the same way, a genesis `None` → `0` =
    // `genesisSentinel` (the prologue's `prevReceiptOf` maps it to `none`), and a real prev echoes the
    // host head. (Both sides truncate identically; the full collision-resistance of the head is the
    // §8 circuit's job, not this admission-bit projection.)
    let prev_hash = turn
        .previous_receipt_hash
        .map(|h| dregg_lean_ffi::marshal::Digest::from_u64(bytes32_to_nat(&h)))
        .unwrap_or_default();

    // Build the WHOLE call-FOREST recursively, preserving the tree's delegation EDGES (no longer
    // flattened to a linear null-cap chain). A single fresh-id counter is threaded across the entire
    // pre-order walk so every created cell/queue gets a distinct never-snapshotted wire Nat.
    //
    // dregg1's `Turn` carries a `CallForest` (a LIST of root `CallTree`s). The Lean `WForest` is a
    // SINGLE rooted node, so a multi-root forest is marshalled as: the FIRST root is the wire root,
    // and each SUBSEQUENT root becomes a `null`-cap sibling child of it (run sequentially against the
    // evolving state under its OWN authority — faithful to the executor's pre-order forest walk, where
    // each root acts on its own target cell with no inter-root cap handoff). Within each root, the
    // REAL `CallTree` child edges are reconstructed (`tree_to_wforest`), so the parent→child cap
    // handoff the verified gate enforces is no longer lost.
    let mut fresh_seq: u64 = 0;
    // The signing-message context the `Authorization::Signature` WHO leg binds to: the federation id
    // (cross-federation replay defense) and the turn nonce (within-federation replay defense) the
    // executor's `verify_ed25519_signature` consumes. `position` is the per-ROOT index in the forest
    // (`compute_partial_signing_message`'s placement binding — `verify_ed25519_signature` reads it as
    // `path.first()`), so each root tree carries its own position; every node within a tree shares it.
    let sig_ctx = SigCtx {
        federation_id: host.federation_id,
        turn_nonce: turn.nonce,
    };
    let mut roots = turn.call_forest.roots.iter().enumerate();
    let (_, first) = roots
        .next()
        .ok_or_else(|| "shadow: empty call forest".to_string())?;
    let mut root = tree_to_wforest(first, pre, &mut fresh_seq, &turn.agent, &sig_ctx, 0)
        .ok_or_else(|| "shadow: forest not fully marshallable".to_string())?;
    // Subsequent forest roots: null-cap sibling subtrees of the wire root (sequential, own authority).
    for (position, sibling) in roots {
        let sib = tree_to_wforest(
            sibling,
            pre,
            &mut fresh_seq,
            &turn.agent,
            &sig_ctx,
            position,
        )
        .ok_or_else(|| "shadow: forest not fully marshallable".to_string())?;
        root.children.push(WChild {
            holder: agent,
            keep: vec![],
            parent_cap: Cap::Null,
            sub: sib,
        });
    }

    Ok(WireTurn {
        agent,
        nonce: turn.nonce,
        fee: turn.fee as i128,
        valid_until,
        block_height,
        prev_hash,
        root,
    })
}

/// Recursively marshal ONE Rust `CallTree` node (its action + its REAL child edges) into a Lean
/// `WForest`, PRESERVING the delegation TREE structure rather than flattening the whole forest to a
/// linear null-cap chain. This is the §WG2 dual on the producer side: the kernel's
/// `execFullChildrenG` walks the same nested edges the executor's `execute_tree` does.
///
/// ## The action → node mapping
///
/// A dregg1 `Action` carries a LIST of effects; the Lean `FullActionA` is ONE per-asset action per
/// node. So an N-effect action becomes N wire nodes: the FIRST effect is THIS node's `action`; each
/// REMAINING effect is a `null`-cap child (intra-action sequencing — same target cell, own authority,
/// no cap handoff — faithful to the executor running the effects in order against the evolving state).
/// Every effect-node carries the SAME credential (`auth_to_wire`) AND the same transported caveats
/// (`action_caveats`, the `min_balance` lift) — the action's WHO + discharge legs gate each of them.
///
/// ## The child edges → subtree mapping (the WELD)
///
/// Each Rust `CallTree` child becomes a `WChild { holder, keep, parentCap, sub }`. The faithful and
/// SOUND mapping mirrors the executor's `DelegationMode` walk (`execute_tree.rs:1058-1134`) while
/// respecting the shadow's veto direction (the Lean verdict may only TIGHTEN — it must never admit a
/// turn the executor refuses):
///   * **same-cell child** (`child.target == this.target`): `parentCap = null` ⇒ the subtree runs
///     DIRECTLY under its own credential (no cap install). Faithful to EVERY `DelegationMode` for a
///     same-cell child — the executor confers nothing; the child acts on the parent's own cell. THIS
///     is the structural win: a multi-level same-cell delegation tree now crosses as a tree (the
///     gate fires per node, all-or-nothing) instead of a flattened sequential chain.
///   * **bearer-authorized child**: `parentCap = null` ⇒ the subtree runs directly; the bearer WHO
///     leg (its own carried delegation proof, now full-sig faithful) gates it, not a c-list install.
///   * **cross-cell, non-bearer child**: the executor's cross-cell authority model (the
///     `SnapshotRefresh` delegate-chain-walk + frozen snapshot, or the `None`/`ParentsOwn`/`Inherit`
///     fail-closed) does NOT have a verdict-equivalent `recKDelegateAtten` image on this wire (the
///     delegator-holds-cap gate is a DIFFERENT authority predicate than the delegate-pointer
///     chain-walk). Marshalling it as a committable edge could admit what the executor denies (the
///     unsound veto direction), so the turn is INELIGIBLE for the shadow (returns `None`). True
///     cross-cell delegation FIDELITY is the cap-reshape lane's (`#103`); this weld closes the
///     STRUCTURAL flattening without overclaiming the cross-cell authority match.
#[cfg(not(feature = "no-lean-link"))]
fn tree_to_wforest(
    tree: &CallTree,
    pre: &ShadowPreLedger,
    fresh_seq: &mut u64,
    agent: &CellId,
    sig_ctx: &SigCtx,
    position: usize,
) -> Option<dregg_lean_ffi::marshal::WForest> {
    use dregg_lean_ffi::marshal::{Cap, WChild, WForest};

    let actor = *pre.id_map.get(&tree.action.target)?;
    // The `Authorization::Signature` WHO leg is realized against the REAL ed25519 check the executor
    // runs (`verify_ed25519_signature`: the TARGET cell's pubkey, the federation/nonce/position-bound
    // signing message, the full 64-byte sig). `auth_to_wire_ctx` folds that verdict into a self-echoing
    // wire `(statement, proof)` for a genuine sig and a NON-echoing pair for a forged/tampered one.
    let target_cell = pre.cells.get(&tree.action.target);
    let wire_auth = auth_to_wire_ctx(
        &tree.action.authorization,
        &tree.action,
        target_cell,
        sig_ctx,
        position,
    );
    let caveats = action_caveats(&tree.action, actor);

    // The action's effects → this node's action + intra-action `null`-cap sequencing children.
    let mut eff_iter = tree.action.effects.iter();
    let head_eff = eff_iter.next()?;
    let head_action = effect_to_wire(actor, head_eff, pre, fresh_seq, agent)?;

    let mut children: Vec<WChild> = Vec::new();
    for eff in eff_iter {
        let action = effect_to_wire(actor, eff, pre, fresh_seq, agent)?;
        children.push(WChild {
            holder: actor,
            keep: vec![],
            parent_cap: Cap::Null,
            sub: WForest {
                auth: wire_auth.clone(),
                caveats: caveats.clone(),
                action,
                children: vec![],
            },
        });
    }

    // The REAL `CallTree` child edges → nested subtrees (the structural weld).
    for child in &tree.children {
        let same_cell = child.action.target == tree.action.target;
        let is_bearer = matches!(&child.action.authorization, Authorization::Bearer(_));
        if !same_cell && !is_bearer {
            // Cross-cell non-bearer: no verdict-equivalent cap install on this wire (see doc). Skip
            // the whole turn rather than risk the unsound veto direction.
            return None;
        }
        let holder = *pre.id_map.get(&child.action.target)?;
        // Children inherit their root tree's `position` (the executor reads `path.first()` — the ROOT
        // index — for EVERY node in the tree, so a child's signing message uses the same placement).
        let sub = tree_to_wforest(child, pre, fresh_seq, agent, sig_ctx, position)?;
        // Same-cell / bearer: the subtree runs directly under its own credential (no cap handoff).
        children.push(WChild {
            holder,
            keep: vec![],
            parent_cap: Cap::Null,
            sub,
        });
    }

    Some(WForest {
        auth: wire_auth,
        caveats,
        action: head_action,
        children,
    })
}

// ===================================================================
// CAVEATS — carry the action's within-cell preconditions so the verified
// gate's `caveatsDischarged` leg ENFORCES them (no longer admit-by-construction).
// ===================================================================

/// Lift an `Action`'s within-cell preconditions into the wire caveats the gated executor's
/// `caveatsDischarged` leg reads on the node's PRE-state.
///
/// The faithful source is `Action.preconditions.cell_state.min_balance` — the dregg1 executor
/// enforces it as `target.balance ≥ min_balance` on the action's OWN target cell (strictly
/// intra-cell, monotone, see `cell/src/preconditions.rs:386`). That is EXACTLY the verified
/// `WCaveat { tier: monotone, cell, asset, min }` semantics: `bal cell asset ≥ min` on the node's
/// pre-state (`FullForestAuth.GatedCaveat.holds`, `liftCaveatW`). The cell's primary `balance` is
/// wire `bal cell 0` (asset 0 — see `ledger_to_wire_state`'s `bal.push((nat, 0, balance))`), so the
/// caveat reads asset 0 on the actor cell. A turn whose target is UNDER `min_balance` therefore
/// fails the verified caveat leg → whole-forest rollback → `ok:0`, matching apply.rs's
/// `InsufficientBalance` rejection — the leg the wire previously dropped (`caveats: vec![]`).
///
/// Tier `monotone` (0) is correct: a `min_balance` floor is a drift-stable, within-cell read (a
/// concurrent turn can only RAISE the balance toward the floor, never invalidate a satisfied one
/// mid-turn within the single-machine atomic snapshot). Preconditions with no `min_balance` yield
/// no caveat (the wire stays minimal; the action is then gated by the WHO/WHAT legs alone).
#[cfg(not(feature = "no-lean-link"))]
fn action_caveats(
    action: &crate::action::Action,
    actor: u64,
) -> Vec<dregg_lean_ffi::marshal::WireCaveat> {
    use dregg_lean_ffi::marshal::WireCaveat;
    let mut out = Vec::new();
    if let Some(cs) = &action.preconditions.cell_state {
        if let Some(min_bal) = cs.min_balance {
            out.push(WireCaveat {
                // monotone (drift-stable, within-cell): the dregg1 `min_balance` floor.
                tier: 0,
                cell: actor,
                // asset 0 = the cell's primary `balance` slot (ledger_to_wire_state).
                asset: 0,
                min: min_bal as i128,
            });
        }
    }
    out
}

// ===================================================================
// AUTH — carry the credential WHO-leg in FULL (no zeroed digests).
// ===================================================================

/// The signing-message context the `Authorization::Signature` WHO leg binds to (mirrors the inputs
/// `TurnExecutor::verify_ed25519_signature` consumes beyond the action itself): the local federation
/// id and the turn nonce. `position` (the per-root forest index) is threaded separately because it is
/// per-node, not per-turn.
#[cfg(not(feature = "no-lean-link"))]
pub(crate) struct SigCtx {
    pub(crate) federation_id: [u8; 32],
    pub(crate) turn_nonce: u64,
}

/// Marshal an `Authorization` to the wire WHO-leg WITH the per-node context the `Signature` arm needs
/// to reproduce the executor's real ed25519 check. Every non-`Signature` arm is identical to
/// [`auth_to_wire`]; the `Signature` arm is realized by [`sig_echo_wire`] (the REAL `verify_strict`
/// against the target cell's pubkey over the federation/nonce/position-bound signing message, folded
/// into a self-echoing wire pair for a genuine sig and a non-echoing one for a forged/tampered sig).
///
/// `target_cell` is the action's target cell (the holder of the verifying pubkey
/// `verify_ed25519_signature` reads). When it is absent (cell not in the pre-snapshot) the signature
/// CANNOT be verified, so the wire fails closed (a non-echoing pair ⇒ the gate's WHO leg rejects) —
/// never an admit-by-construction.
#[cfg(not(feature = "no-lean-link"))]
fn auth_to_wire_ctx(
    auth: &Authorization,
    action: &crate::action::Action,
    target_cell: Option<&Cell>,
    sig_ctx: &SigCtx,
    position: usize,
) -> dregg_lean_ffi::marshal::WireAuth {
    match auth {
        Authorization::Signature(r, s) => {
            sig_echo_wire(action, target_cell, r, s, sig_ctx, position)
        }
        // `OneOf` may carry a `Signature` candidate: recurse with the SAME node context so a nested
        // signature is realized against the real check too (the chosen-slot verdict still gates).
        Authorization::OneOf {
            candidates,
            proof_index,
        } => dregg_lean_ffi::marshal::WireAuth::OneOf {
            candidates: candidates
                .iter()
                .map(|c| auth_to_wire_ctx(c, action, target_cell, sig_ctx, position))
                .collect(),
            proof_index: *proof_index as u64,
        },
        // Every other arm is context-free (its WHO data is self-contained in the credential).
        other => auth_to_wire(other),
    }
}

/// Realize an `Authorization::Signature(r, s)` WHO leg as a self-echoing wire `(statement, proof)`
/// pair under the `Crypto.Reference` portal oracle (`verify stmt proof = (stmt == proof)`), driven by
/// the EXECUTOR'S OWN ed25519 check.
///
/// `verify_ed25519_signature` admits iff `VerifyingKey::from_bytes(target.public_key())
/// .verify_strict(message, r‖s)` succeeds, where `message` is the federation/nonce/position-bound
/// signing message (`compute_signing_message` for `Full`, `compute_partial_signing_message` for
/// `Partial`). We recompute EXACTLY that verdict here, then encode:
///
///   * `statement` (the wire `pubkey` digest) = a tamper-sensitive commitment to the
///     `(pubkey ‖ message)` IDENTITY of this signed node, narrowed to the low 64 bits and placed in a
///     digest whose high 24 bytes are zero — so it parses to the SAME `Nat` the `sig` `u64` carries
///     (the kernel's `Crypto.Reference` portal compares the FULL Nats; a 256-bit statement could
///     never equal a 64-bit proof — the exact stuck-veto bug this closes).
///   * `proof` (the wire `sig` `u64`) = that same low-64 commitment IFF the signature verifies, else
///     its bit-complement (guaranteed ≠ the statement).
///
/// So a GENUINE signature ⇒ `stmt == proof` ⇒ the gate's WHO leg ADMITS; a FORGED key, a
/// CROSS-FEDERATION replay (different `federation_id`), or a TAMPERED action/sig (the recomputed
/// `message` no longer matches what was signed, or `verify_strict` fails) ⇒ `stmt ≠ proof` ⇒ the gate
/// fail-closes ⇒ whole-forest rollback. The verdict is the REAL ed25519 check over the FULL signature,
/// not a truncated projection.
#[cfg(not(feature = "no-lean-link"))]
fn sig_echo_wire(
    action: &crate::action::Action,
    target_cell: Option<&Cell>,
    r: &[u8; 32],
    s: &[u8; 32],
    sig_ctx: &SigCtx,
    position: usize,
) -> dregg_lean_ffi::marshal::WireAuth {
    use crate::action::CommitmentMode;
    use dregg_lean_ffi::marshal::{Digest, WireAuth};

    // Recompute the EXACT signing message the executor's `verify_ed25519_signature` checks.
    let message = match action.commitment_mode {
        CommitmentMode::Partial => crate::executor::TurnExecutor::compute_partial_signing_message(
            action,
            position,
            &sig_ctx.federation_id,
            sig_ctx.turn_nonce,
        ),
        CommitmentMode::Full => {
            crate::executor::TurnExecutor::compute_signing_message(action, &sig_ctx.federation_id)
        }
    };

    let mut sig_bytes = [0u8; 64];
    sig_bytes[..32].copy_from_slice(r);
    sig_bytes[32..].copy_from_slice(s);

    // The REAL ed25519 verdict: the target cell's pubkey must be a valid point AND `verify_strict`
    // (rejects malleable / non-canonical R,S — same as the executor) must accept the FULL signature.
    let verdict = match target_cell {
        Some(cell) => match ed25519_dalek::VerifyingKey::from_bytes(cell.public_key()) {
            Ok(vk) => {
                let signature = ed25519_dalek::Signature::from_bytes(&sig_bytes);
                vk.verify_strict(&message, &signature).is_ok()
            }
            Err(_) => false,
        },
        None => false, // cell absent ⇒ cannot verify ⇒ fail-closed (non-echoing pair below).
    };

    // The IDENTITY commitment: bind the verifying pubkey + the (federation/nonce/position-bound)
    // signing message into one 32-byte digest, then narrow to the low 64 bits. Tamper-sensitive (any
    // change to the cell pubkey or the action/federation/nonce/position changes the message ⇒ a
    // different commitment) AND 64-bit-narrow (so the digest-statement and the u64-proof can coincide).
    let pk_bytes = target_cell.map(|c| *c.public_key()).unwrap_or([0u8; 32]);
    let mut hasher = blake3::Hasher::new_derive_key("dregg-lean-shadow-sig-bind-v1");
    hasher.update(&pk_bytes);
    hasher.update(&message);
    let commit = *hasher.finalize().as_bytes();
    let low = bytes32_to_nat(&commit); // low 64 bits (big-endian) — the echo width.

    // Place the low-64 commitment in a digest whose high 24 bytes are zero, so `parseHex32` yields
    // exactly `low` as the statement `Nat` (matching the `sig` `u64` width the proof carries).
    let mut stmt_digest = [0u8; 32];
    stmt_digest[24..32].copy_from_slice(&low.to_be_bytes());

    // Genuine ⇒ proof echoes the statement (admit); forged/tampered ⇒ bit-complement (≠ ⇒ veto).
    let proof = if verdict { low } else { !low };

    WireAuth::Signature {
        pubkey: Digest::from_bytes(stmt_digest),
        sig: proof,
    }
}

#[cfg(not(feature = "no-lean-link"))]
fn auth_to_wire(auth: &Authorization) -> dregg_lean_ffi::marshal::WireAuth {
    use dregg_lean_ffi::marshal::{Digest, WireAuth};
    match auth {
        // Context-free FAIL-CLOSED fallback: a `Signature` reaching this path has NO target cell /
        // signing message, so its ed25519 validity CANNOT be decided (the real verdict needs the
        // verifying pubkey + the federation/nonce/position-bound message — see `sig_echo_wire`). Every
        // verdict-path Signature is routed through `auth_to_wire_ctx` → `sig_echo_wire`; this arm is
        // reached only by a contextless caller (e.g. a unit test), where admitting would be unsound. So
        // emit a NON-echoing pair (a `1` statement vs a `0` proof) ⇒ `portalVerify .signature 1 0 =
        // (1 == 0) = false` ⇒ the gate's WHO leg fail-closes (the §8 no-credential anchor).
        Authorization::Signature(_, _) => WireAuth::Signature {
            pubkey: Digest::from_u64(1),
            sig: 0,
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
        // The bearer arm no longer collapses the delegation sig to a low-u64 (`sig64_to_nat` =
        // the last 8 bytes — a forged sig that shares its tail would have passed). The WHO-leg's
        // `deleg_sig` Nat is now the FULL signature/proof bytes hashed to a Digest (`bytes32_to_nat
        // (blake3(full_sig))`), so it is sensitive to the ENTIRE 64-byte ed25519 sig / STARK proof
        // blob: a single flipped sig byte changes the hash → the wire `deleg_sig` → the verified
        // WHO leg (`portalVerify .bearer msg sig = verify msg sig`) can REPRODUCE the bearer-auth
        // outcome rather than seeing a truncated stand-in. (`deleg_msg` stays the delegator/root
        // commitment; `stark` keeps the SignedDelegation|StarkDelegation discriminant.)
        Authorization::Bearer(proof) => {
            let (deleg_msg, deleg_sig, stark) = match &proof.delegation_proof {
                DelegationProofData::SignedDelegation {
                    delegator_pk,
                    signature,
                    ..
                } => (
                    Digest::from_bytes(*delegator_pk),
                    bytes32_to_nat(&blake3_of(signature)),
                    false,
                ),
                DelegationProofData::StarkDelegation {
                    proof_bytes,
                    root_issuer_commitment,
                } => (
                    Digest::from_bytes(*root_issuer_commitment),
                    bytes32_to_nat(&blake3_of(proof_bytes)),
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
        // The token's issuer key / cell-scoped anchor is the WHO-leg; carry it in full AND fold the
        // `encoded` credential + its `discharges` caveat-chain into the `sig`/`proof` Nat. Before,
        // `sig:0`/`proof:0` DROPPED the caveat chain — the verified gate authenticated the issuer
        // key but was BLIND to the discharges, so a turn carrying a BAD discharge (a forged /
        // missing third-party discharge the Rust `from_encoded_with_discharges` rejects,
        // `authorize.rs:1795`) passed the Lean WHO leg unchanged. Now the `sig`/`proof` Nat is
        // `bytes32_to_nat(blake3(encoded ‖ discharges))`, so it is sensitive to the ENTIRE caveat
        // chain: a tampered/absent discharge changes the hash → the wire Nat → the verified WHO leg
        // (`portalVerify .token key sig = verify key sig` / `.custom stmt pf`), so the gate can
        // REPRODUCE the discharge-chain outcome rather than ignoring it.
        Authorization::Token {
            key_ref,
            encoded,
            discharges,
        } => {
            let chain_nat = bytes32_to_nat(&token_chain_hash(encoded, discharges));
            match key_ref {
                crate::action::TokenKeyRef::BiscuitIssuer { issuer_pubkey } => WireAuth::Token {
                    issuer_key: Digest::from_bytes(*issuer_pubkey),
                    sig: chain_nat,
                },
                crate::action::TokenKeyRef::CellScopedMacaroon { cell } => WireAuth::Custom {
                    kind_stmt: Digest::from_bytes(cell.0),
                    proof: chain_nat,
                },
            }
        }
    }
}

#[cfg(not(feature = "no-lean-link"))]
fn predicate_commitment(p: &dregg_cell::predicate::WitnessedPredicate) -> [u8; 32] {
    // Hash the predicate's serialized form as a stable WHO-commitment. The exact preimage
    // need not match the kernel byte-for-byte (the kernel only reads the digest as an
    // opaque WHO label); what matters is that it is NON-ZERO and tamper-sensitive.
    let bytes = postcard::to_allocvec(p).unwrap_or_default();
    blake3_of(&bytes)
}

#[cfg(not(feature = "no-lean-link"))]
fn predicate_proof_nat(p: &dregg_cell::predicate::WitnessedPredicate) -> u64 {
    let bytes = postcard::to_allocvec(p).unwrap_or_default();
    bytes_to_nat(&bytes)
}

// ---- digest / nat helpers ----

#[cfg(not(feature = "no-lean-link"))]
fn blake3_of(bytes: &[u8]) -> [u8; 32] {
    *blake3::hash(bytes).as_bytes()
}

/// Hash a Token credential's `encoded` blob TOGETHER WITH its `discharges` caveat-chain into a
/// single 32-byte commitment (the WHO-leg's discharge-sensitive `sig`/`proof` Nat preimage). The
/// length-prefixing makes the fold injective in the discharge SET (a different number of
/// discharges, or a different discharge, yields a different commitment), so the verified gate's
/// WHO leg is sensitive to the FULL caveat chain the Rust verifier checks — not just the issuer
/// key. An EMPTY credential with no discharges hashes the empty preimage (a stable non-secret).
#[cfg(not(feature = "no-lean-link"))]
fn token_chain_hash(encoded: &[u8], discharges: &[Vec<u8>]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-lean-shadow-token-chain-v1");
    hasher.update(&(encoded.len() as u64).to_le_bytes());
    hasher.update(encoded);
    hasher.update(&(discharges.len() as u64).to_le_bytes());
    for d in discharges {
        hasher.update(&(d.len() as u64).to_le_bytes());
        hasher.update(d);
    }
    *hasher.finalize().as_bytes()
}

#[cfg(not(feature = "no-lean-link"))]
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

#[cfg(not(feature = "no-lean-link"))]
fn field_to_i128(field: &FieldElement) -> i128 {
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&field[24..32]);
    u64::from_be_bytes(bytes) as i128
}

#[cfg(not(feature = "no-lean-link"))]
fn field_is_zero(field: &FieldElement) -> bool {
    field.iter().all(|&b| b == 0)
}

#[cfg(not(feature = "no-lean-link"))]
fn bytes32_to_nat(bytes: &[u8; 32]) -> u64 {
    let mut buf = [0u8; 8];
    buf.copy_from_slice(&bytes[24..32]);
    u64::from_be_bytes(buf)
}

#[cfg(not(feature = "no-lean-link"))]
fn sig64_to_nat(sig: &[u8; 64]) -> u64 {
    let mut buf = [0u8; 8];
    buf.copy_from_slice(&sig[56..64]);
    u64::from_be_bytes(buf)
}

#[cfg(not(feature = "no-lean-link"))]
fn bytes_to_nat(bytes: &[u8]) -> u64 {
    let mut buf = [0u8; 8];
    let n = bytes.len().min(8);
    buf[8 - n..].copy_from_slice(&bytes[bytes.len() - n..]);
    u64::from_be_bytes(buf)
}

#[cfg(not(feature = "no-lean-link"))]
fn str_to_nat(s: &str) -> u64 {
    bytes_to_nat(s.as_bytes())
}

#[cfg(not(feature = "no-lean-link"))]
fn permissions_to_i128(_perms: &dregg_cell::Permissions) -> i128 {
    // Permissions are a structured value; the wire `setperms` arm carries a scalar. We
    // encode 0 as a neutral marker (the executor models perms abstractly). This is the one
    // place a structured field collapses; SetPermissions turns are still shadowed for the
    // commit-bit decision, which does not depend on the exact perms scalar.
    0
}

#[cfg(not(feature = "no-lean-link"))]
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
            assert!(
                seen.insert(*name),
                "duplicate effect in coverage list: {name}"
            );
            assert!(
                producer_covers_kind(name),
                "producer_covers_kind disagrees for {name}"
            );
        }
        // Twenty-one effect kinds are projected to the wire today (mirrors effect_is_mappable;
        // VERB-LOCKSTEP: the escrow/obligation §SIDE-TABLE batch died with its Effect variants).
        assert_eq!(
            covered.len(),
            21,
            "producer coverage count changed — update the report and confirm effect_is_mappable agrees"
        );
    }

    /// Every covered effect must appear in the full enumeration, and the
    /// uncovered list must be exactly the complement (no overlaps, full cover).
    #[test]
    fn coverage_partitions_the_effect_surface() {
        let all: std::collections::HashSet<&str> = all_effect_kinds().iter().copied().collect();
        assert_eq!(
            all.len(),
            all_effect_kinds().len(),
            "all_effect_kinds has duplicates"
        );
        for c in producer_covered_effects() {
            assert!(
                all.contains(c),
                "covered effect {c} missing from all_effect_kinds"
            );
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

/// Theme-2 LEAN-SHADOW AUTH-SHAPES: the producer marshaller now carries the HARD auth shapes
/// (caveats / bearer full-sig / token discharge-chain) the wire previously dropped, so the verified
/// Lean kernel evaluates them rather than seeing a weaker turn. These tests pin the Rust HALF of
/// each closure (the data crosses faithfully + is tamper-sensitive); the Lean HALF (the refusal
/// teeth) is `FFI.lean`'s `caveat_teeth_same_wire` / `bearer_teeth_same_wire` /
/// `discharge_teeth_same_wire`.
#[cfg(all(test, not(feature = "no-lean-link")))]
mod auth_shape_marshal_tests {
    use super::*;
    use crate::action::{Action, Authorization, DelegationProofData, TokenKeyRef};
    use dregg_cell::preconditions::{CellStatePrecondition, Preconditions};

    fn bare_action(target: CellId, auth: Authorization, pre: Preconditions) -> Action {
        Action {
            target,
            method: Default::default(),
            args: vec![],
            authorization: auth,
            preconditions: pre,
            effects: vec![],
            may_delegate: crate::action::DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
            witness_blobs: vec![],
        }
    }

    /// (1) CAVEATS: a `min_balance` precondition lifts to a monotone within-cell `WireCaveat`
    /// (`bal actor 0 ≥ min`) — the SAME read the verified gate's `caveatsDischarged` leg runs and
    /// the SAME read apply.rs enforces (`target.balance ≥ min_balance`). No precondition ⇒ no caveat.
    #[test]
    fn min_balance_precondition_lifts_to_monotone_caveat() {
        let cell = CellId([7u8; 32]);
        let actor: u64 = 42;
        let pre = Preconditions {
            cell_state: Some(CellStatePrecondition {
                min_balance: Some(500),
                ..Default::default()
            }),
            ..Default::default()
        };
        let cavs = action_caveats(&bare_action(cell, Authorization::Unchecked, pre), actor);
        assert_eq!(cavs.len(), 1, "min_balance must produce exactly one caveat");
        let c = &cavs[0];
        assert_eq!(
            c.tier, 0,
            "min_balance is a monotone (drift-stable) within-cell read"
        );
        assert_eq!(c.cell, actor, "caveat reads the action's own target cell");
        assert_eq!(c.asset, 0, "the cell's primary balance is wire asset 0");
        assert_eq!(c.min, 500i128, "the threshold is the min_balance floor");
    }

    #[test]
    fn no_precondition_yields_no_caveat() {
        let cell = CellId([1u8; 32]);
        let cavs = action_caveats(
            &bare_action(cell, Authorization::Unchecked, Preconditions::default()),
            9,
        );
        assert!(
            cavs.is_empty(),
            "an action with no min_balance carries no caveat (additive)"
        );
    }

    /// (2) TOKEN DISCHARGE: `token_chain_hash` is sensitive to the FULL `encoded ‖ discharges`
    /// chain — a tampered/added/removed discharge changes the commitment, so the verified WHO leg
    /// can no longer be blind to the chain (the `sig:0` drop the ledger named).
    #[test]
    fn token_chain_hash_is_discharge_sensitive() {
        let encoded = b"eb2_some_biscuit".to_vec();
        let d1 = vec![b"discharge-a".to_vec()];
        let d2 = vec![b"discharge-b".to_vec()]; // a DIFFERENT discharge
        let d_extra = vec![b"discharge-a".to_vec(), b"discharge-b".to_vec()]; // an ADDED discharge
        let h_none = token_chain_hash(&encoded, &[]);
        let h1 = token_chain_hash(&encoded, &d1);
        let h2 = token_chain_hash(&encoded, &d2);
        let h_extra = token_chain_hash(&encoded, &d_extra);
        assert_ne!(h1, h_none, "adding a discharge changes the commitment");
        assert_ne!(h1, h2, "a different discharge changes the commitment");
        assert_ne!(h1, h_extra, "the discharge SET cardinality is load-bearing");
        // ...and the `encoded` blob is load-bearing too:
        assert_ne!(
            token_chain_hash(&encoded, &d1),
            token_chain_hash(b"em2_other", &d1),
            "the encoded credential is part of the commitment"
        );
    }

    /// (2) TOKEN arm: the producer maps a biscuit Token to the wire `token` arm with a
    /// discharge-folded `sig` (NOT `sig:0`), so a turn with a different discharge marshals to a
    /// DIFFERENT wire credential (the verified WHO leg sees the change).
    #[test]
    fn biscuit_token_wire_is_discharge_sensitive() {
        use dregg_lean_ffi::marshal::WireAuth;
        let key = [3u8; 32];
        let mk = |discharges: Vec<Vec<u8>>| {
            auth_to_wire(&Authorization::Token {
                encoded: b"eb2_cred".to_vec(),
                key_ref: TokenKeyRef::BiscuitIssuer { issuer_pubkey: key },
                discharges,
            })
        };
        let a = mk(vec![b"good".to_vec()]);
        let b = mk(vec![b"bad".to_vec()]);
        match (&a, &b) {
            (WireAuth::Token { sig: sa, .. }, WireAuth::Token { sig: sb, .. }) => {
                assert_ne!(sa, sb, "a different discharge ⇒ a different wire token sig")
            }
            _ => panic!("biscuit Token must map to the wire token arm"),
        }
        // the issuer key still crosses in full (the WHO anchor is preserved):
        if let WireAuth::Token { issuer_key, .. } = &a {
            assert_eq!(issuer_key.0, key, "issuer pubkey crosses byte-exact");
        }
    }

    /// (3) BEARER: the producer now hashes the FULL delegation sig into `deleg_sig` (not the
    /// truncated last 8 bytes), so flipping ANY sig byte changes the wire credential — the verified
    /// WHO leg can reproduce the bearer-auth outcome instead of seeing a truncation a forged sig
    /// could share.
    #[test]
    fn bearer_wire_is_full_sig_sensitive() {
        use crate::action::BearerCapProof;
        use dregg_cell::AuthRequired;
        use dregg_lean_ffi::marshal::WireAuth;
        let mk = |sig: [u8; 64]| {
            auth_to_wire(&Authorization::Bearer(BearerCapProof {
                target: CellId([5u8; 32]),
                permissions: AuthRequired::None,
                delegation_proof: DelegationProofData::SignedDelegation {
                    delegator_pk: [9u8; 32],
                    signature: sig,
                    bearer_pk: [8u8; 32],
                },
                expires_at: 100,
                revocation_channel: None,
                allowed_effects: None,
            }))
        };
        let mut sig_a = [1u8; 64];
        let mut sig_b = [1u8; 64];
        // flip a byte in the HIGH half (the old `sig64_to_nat` only read the LOW 8 bytes [56..64],
        // so this forge was previously INVISIBLE on the wire):
        sig_a[0] = 0xAA;
        sig_b[0] = 0xBB;
        let a = mk(sig_a);
        let b = mk(sig_b);
        match (&a, &b) {
            (
                WireAuth::Bearer {
                    deleg_sig: da,
                    stark: false,
                    ..
                },
                WireAuth::Bearer {
                    deleg_sig: db,
                    stark: false,
                    ..
                },
            ) => assert_ne!(
                da, db,
                "a high-half sig byte flip must change deleg_sig (old truncation missed it)"
            ),
            _ => panic!("SignedDelegation must map to the wire bearer arm with stark=false"),
        }
    }
}
