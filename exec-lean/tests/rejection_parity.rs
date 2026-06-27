//! rejection_parity.rs — THE REJECTION-PARITY differential.
//!
//! The existing state-producer differential (`lean_state_producer_differential.rs`) proves the two
//! kernels AGREE on the post-state of turns BOTH executors ACCEPT. It says nothing about turns that
//! SHOULD be REJECTED: a soundness hole is precisely a turn the Rust `TurnExecutor` COMMITS while the
//! verified Lean kernel REFUSES (Rust under-enforces a gate). This harness builds a corpus of
//! adversarial turns — each crafted to violate ONE specific kernel gate — and runs BOTH kernels:
//!
//!   * the legacy Rust `TurnExecutor::execute` (`apply.rs`),
//!   * the verified Lean kernel (`dregg_exec_lean::lean_apply::execute_via_lean`),
//!
//! recording `(rust_committed, lean_committed)` for each. The verdicts are:
//!
//!   * AGREE-both-reject          — `¬rust ∧ ¬lean`. The GOOD result: no hole; both refuse.
//!   * ASYMMETRY-Rust-accepts     — ` rust ∧ ¬lean`. A CONFIRMED soundness hole: Rust commits what
//!                                  the verified kernel refuses (the dangerous direction).
//!   * ASYMMETRY-Rust-rejects     — `¬rust ∧  lean`. Rust is STRICTER than the verified kernel
//!                                  (a divergence, but the safe direction).
//!   * AGREE-both-accept          — ` rust ∧  lean`. The adversarial turn was NOT actually rejected
//!                                  by either gate — the suspicion was wrong / the gate is elsewhere.
//!   * WIRE-GAP                    — the turn could not be marshalled to Lean (`Ineligible`), so it
//!                                  cannot be differentially verified here. NOT faked — reported as a gap.
//!
//! This test is a CHARACTERISATION harness (it prints the table and only HARD-FAILS on the dangerous
//! `ASYMMETRY-Rust-accepts` direction, since that is a real soundness hole the maintainer must see).
//! Requires the linked Lean archive; self-skips when absent (it cannot run the verified kernel).
//!
//! Run: `cargo test -p dregg-exec-lean --test rejection_parity -- --nocapture`

use std::collections::HashMap;

use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_exec_lean::lean_apply::{self, execute_via_lean};
use dregg_exec_lean::lean_shadow::ShadowHostCtx;
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

// ---------------------------------------------------------------------------
// Fixture builders (shared with the accept-path differential)
// ---------------------------------------------------------------------------

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

/// Permissions where EVERY action requires a credential the adversarial `Unchecked` turn cannot
/// present (`Signature`). Used to test the permission-lattice gate for note/lifecycle/bridge.
fn locked_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::Signature,
        receive: AuthRequired::Signature,
        set_state: AuthRequired::Signature,
        set_permissions: AuthRequired::Signature,
        set_verification_key: AuthRequired::Signature,
        increment_nonce: AuthRequired::Signature,
        delegate: AuthRequired::Signature,
        access: AuthRequired::Signature,
    }
}

fn make_cell(seed: u8, balance: i64, perms: Permissions) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = perms;
    cell
}

fn make_open_cell(seed: u8, balance: i64) -> Cell {
    make_cell(seed, balance, open_permissions())
}

/// An open-permission cell pre-SEALED (lifecycle discriminant 1). The verified kernel's per-effect
/// liveness conjuncts (`cellLive` / `acceptsEffects`, both Live-ONLY) refuse every state-mutating
/// effect that targets / sources this cell, even though its permissions admit the action — the
/// gap the cross-cell liveness alignment closes.
fn make_sealed_cell(seed: u8, balance: i64) -> Cell {
    let mut c = make_open_cell(seed, balance);
    c.lifecycle = dregg_cell::lifecycle::CellLifecycle::Sealed {
        reason_hash: [7u8; 32],
        sealed_at: 1,
    };
    c
}

/// An open-permission cell in a TERMINAL lifecycle state (Destroyed). The verified kernel's
/// admission leg `cellLifecycleCanAuthor` (RecordKernel.lean) refuses a terminal cell as the AGENT
/// of a turn — the agent-lifecycle gate the Rust executor now mirrors at admission.
fn make_destroyed_cell(seed: u8, balance: i64) -> Cell {
    let mut c = make_open_cell(seed, balance);
    c.lifecycle = dregg_cell::lifecycle::CellLifecycle::Destroyed {
        death_certificate_hash: [9u8; 32],
        destroyed_at: 1,
    };
    c
}

fn field_from_u64(v: u64) -> FieldElement {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&v.to_be_bytes());
    out
}

/// A turn carrying `effects` under the given `auth`, with the single root action targeting `target`.
fn turn_with_auth(
    agent: CellId,
    target: CellId,
    nonce: u64,
    auth: Authorization,
    effects: Vec<Effect>,
) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: auth,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    };
    forest.add_root(action);
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: Some(1_000),
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn single_effect_turn(agent: CellId, target: CellId, nonce: u64, effect: Effect) -> Turn {
    turn_with_auth(agent, target, nonce, Authorization::Unchecked, vec![effect])
}

// ---------------------------------------------------------------------------
// One adversarial case
// ---------------------------------------------------------------------------

struct Case {
    /// The gate being attacked.
    gate: &'static str,
    /// Human description of the adversarial turn.
    desc: &'static str,
    /// Pre-state.
    ledger: Ledger,
    /// The adversarial turn.
    turn: Turn,
    /// If true, this is a CONTROL — a turn that SHOULD be rejected by both (the suspicion is that
    /// they already agree). Same machinery, just labelled so the report distinguishes them.
    control: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    AgreeBothReject,
    AgreeBothAccept,
    AsymRustAccepts,
    AsymRustRejects,
    WireGap,
}

impl Verdict {
    fn label(self) -> &'static str {
        match self {
            Verdict::AgreeBothReject => "AGREE-both-reject",
            Verdict::AgreeBothAccept => "AGREE-both-accept",
            Verdict::AsymRustAccepts => "ASYMMETRY-Rust-accepts",
            Verdict::AsymRustRejects => "ASYMMETRY-Rust-rejects",
            Verdict::WireGap => "WIRE-GAP",
        }
    }
}

/// Run both kernels over the case's turn + pre-state. Returns `(rust_committed, lean_status, verdict)`
/// where `lean_status` is `Some(committed)` or `None` for a wire gap.
fn run_case(case: &Case) -> (bool, Option<bool>, Verdict) {
    // --- (1) Rust executor (apply.rs). Fresh executor so each turn is first in its receipt chain. ---
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = case.ledger.clone();
    let rust_committed = executor
        .execute(&case.turn, &mut rust_ledger)
        .is_committed();

    // --- (2) Verified Lean kernel over the same turn + pre-state. ---
    let host = ShadowHostCtx::diag();
    let lean_status = match execute_via_lean(&case.turn, &case.ledger, &host) {
        Ok((_ledger, committed)) => Some(committed),
        Err(lean_apply::ExtractError::Ineligible) => None, // WIRE-GAP — cannot compare.
        Err(lean_apply::ExtractError::RootGap { .. }) => None, // root-gap — also a comparison gap.
        Err(e) => panic!("Lean kernel FAILED on '{}' ({}): {e}", case.gate, case.desc),
    };

    let verdict = match lean_status {
        None => Verdict::WireGap,
        Some(lean_committed) => match (rust_committed, lean_committed) {
            (false, false) => Verdict::AgreeBothReject,
            (true, true) => Verdict::AgreeBothAccept,
            (true, false) => Verdict::AsymRustAccepts,
            (false, true) => Verdict::AsymRustRejects,
        },
    };

    (rust_committed, lean_status, verdict)
}

// ---------------------------------------------------------------------------
// The adversarial corpus
// ---------------------------------------------------------------------------

/// Two open cells (A=agent, B=counterparty) with the given balances.
fn two_open(bal_a: i64, bal_b: i64) -> (Ledger, CellId, CellId) {
    let a = make_open_cell(1, bal_a);
    let b = make_open_cell(2, bal_b);
    let (ida, idb) = (a.id(), b.id());
    let mut l = Ledger::new();
    l.insert_cell(a).unwrap();
    l.insert_cell(b).unwrap();
    (l, ida, idb)
}

fn build_corpus() -> Vec<Case> {
    let mut cases: Vec<Case> = Vec::new();

    // ── (2) Permissionless self-burn, no mint cap (AUTHORITY asymmetry) ───────────────────────
    // A Burn on cell A's balance slot, A holds NO mint/burn cap. SUPPLY-MODEL Stage 1: apply.rs
    // now executes this as a CONSERVING holder→well move (per-asset well lazily derived), so the
    // conservation half is closed. The remaining asymmetry is AUTHORITY: Rust accepts the
    // permissionless self-redeem; Lean's `.burnA` gates on `mintAuthorizedB`. ASYMMETRY-Rust-
    // accepts (SAFE direction), closes in Stage 3.
    {
        let (l, a, _b) = two_open(100, 5);
        cases.push(Case {
            gate: "burn-no-well",
            desc: "Burn 10 from A (no issuer well, no mint cap)",
            turn: single_effect_turn(
                a,
                a,
                0,
                Effect::Burn {
                    target: a,
                    slot: 0,
                    amount: 10,
                },
            ),
            ledger: l,
            control: false,
        });
    }

    // ── (2-mint-a) UNAUTHORIZED mint: no mint-cap (AUTHORITY parity) ──────────────────────────
    // A mints into B with NO mint-cap over the asset's well. SUPPLY-MODEL Stage 2a: apply.rs's
    // `apply_mint` gates on a CONTROL-GRADE `EFFECT_MINT` cap over the issuer well (the Rust image
    // of Lean `mintAuthorizedB`); an empty c-list fails it ⇒ Rust REJECTS. Lean's `mintH`
    // (`Handlers/StateSupply.lean:90`) likewise gates `mintAuthorizedB k.caps actor (issuerOf a)`;
    // an empty c-list fails it ⇒ Lean REFUSES. Expected AGREE-both-reject — the verified
    // `mintAuthorizedB` MATCHES the Rust rejection.
    {
        let (l, a, b) = two_open(100, 5);
        cases.push(Case {
            gate: "mint-unauthorized",
            desc: "Mint 10 into B from A (no mint-cap over the issuer well)",
            turn: single_effect_turn(
                a,
                b,
                0,
                Effect::Mint {
                    target: b,
                    slot: 0,
                    amount: 10,
                },
            ),
            ledger: l,
            control: false,
        });
    }

    // ── (2-mint-b) AUTHORIZED mint: control-grade EFFECT_MINT cap held ────────────────────────
    // A holds a control-grade `EFFECT_MINT` cap over the asset's issuer well AND an access cap over
    // recipient B. apply.rs `apply_mint` ACCEPTS (well→holder conserving move). On the wire the
    // synthetic asset numbering (`asset: 0`, like burn) does not carry a faithful node cap over the
    // marshalled issuer, so the verified `mintH` gate `mintAuthorizedB` is not satisfied on the
    // wire ⇒ Lean refuses — the SAME synthetic-asset wire limitation `burn-no-well` documents
    // (CHARACTERISED below). The Rust commit is the CORRECT supply entry; the wire cannot yet
    // represent the issuer authority faithfully (it closes when the native asset carries a genesis
    // issuer well numbered on the wire).
    {
        let well_pubkey = blake3::derive_key("dregg-issuer-well-key-v1", &[0u8; 32]);
        let well_id = CellId::derive_raw(&well_pubkey, &[0u8; 32]);
        let mut a = make_open_cell(1, 100);
        let b = make_open_cell(2, 5);
        let (ida, idb) = (a.id(), b.id());
        a.capabilities
            .grant_faceted(well_id, AuthRequired::None, dregg_cell::EFFECT_MINT)
            .unwrap();
        a.capabilities.grant(idb, AuthRequired::None).unwrap();
        let mut l = Ledger::new();
        l.insert_cell(a).unwrap();
        l.insert_cell(b).unwrap();
        cases.push(Case {
            gate: "mint-authorized",
            desc: "Mint 10 into B from A (control-grade EFFECT_MINT cap over the issuer well)",
            turn: single_effect_turn(
                ida,
                idb,
                0,
                Effect::Mint {
                    target: idb,
                    slot: 0,
                    amount: 10,
                },
            ),
            ledger: l,
            control: false,
        });
    }

    // ── (3) Permission lattice not consulted: NoteCreate on a LOCKED cell ─────────────────────
    // Cell A requires Signature for everything; the turn presents Unchecked. Lean's gate should
    // fail-closed; does apply.rs's determine_required_permissions even consult the lattice for
    // NoteCreate? Suspected ASYMMETRY-Rust-accepts.
    {
        let a = make_cell(1, 100, locked_permissions());
        let b = make_cell(2, 5, locked_permissions());
        let (ida, _idb) = (a.id(), b.id());
        let mut l = Ledger::new();
        l.insert_cell(a).unwrap();
        l.insert_cell(b).unwrap();
        cases.push(Case {
            gate: "perm-lattice-notecreate",
            desc: "NoteCreate on a Signature-locked cell with Unchecked auth",
            turn: single_effect_turn(
                ida,
                ida,
                0,
                Effect::NoteCreate {
                    commitment: dregg_cell::NoteCommitment([0xBB; 32]),
                    value: 0,
                    asset_type: 0,
                    encrypted_note: vec![],
                    value_commitment: None,
                    range_proof: None,
                },
            ),
            ledger: l,
            control: false,
        });
    }
    // ── (3b) Permission lattice: CellSeal (lifecycle) on a LOCKED cell ────────────────────────
    {
        let a = make_cell(1, 100, locked_permissions());
        let ida = a.id();
        let mut l = Ledger::new();
        l.insert_cell(a).unwrap();
        cases.push(Case {
            gate: "perm-lattice-cellseal",
            desc: "CellSeal on a Signature-locked cell with Unchecked auth",
            turn: single_effect_turn(
                ida,
                ida,
                0,
                Effect::CellSeal {
                    target: ida,
                    reason: [9u8; 32],
                },
            ),
            ledger: l,
            control: false,
        });
    }

    // ── (4) Reserved-slot SetField ────────────────────────────────────────────────────────────
    // A developer SetField writing slot 0 (the balance/nonce-adjacent reserved region). Lean's
    // EffectsState rejects writes to reserved slots; does apply.rs? Try slot 0 and slot 1.
    {
        let (l, a, _b) = two_open(100, 5);
        cases.push(Case {
            gate: "reserved-setfield-slot0",
            desc: "SetField writing reserved slot 0",
            turn: single_effect_turn(
                a,
                a,
                0,
                Effect::SetField {
                    cell: a,
                    index: 0,
                    value: field_from_u64(999),
                },
            ),
            ledger: l,
            control: false,
        });
    }
    {
        let (l, a, _b) = two_open(100, 5);
        cases.push(Case {
            gate: "reserved-setfield-slot1",
            desc: "SetField writing reserved slot 1",
            turn: single_effect_turn(
                a,
                a,
                0,
                Effect::SetField {
                    cell: a,
                    index: 1,
                    value: field_from_u64(999),
                },
            ),
            ledger: l,
            control: false,
        });
    }

    // ── (9b) EmitEvent on a SEALED cell (lifecycle-liveness gate) ─────────────────────────────
    // The cell A is pre-SEALED (lifecycle discriminant 1). The verified kernel's emit arm
    // (`emitEventA`, TurnExecutorFull.lean:2529) admits an event ONLY when the target cell
    // `acceptsEffects` (lifecycle == lcLive == 0); a Sealed cell is REFUSED. apply.rs previously
    // checked only membership (`ledger.get(cell).is_some()`) — committing an emit on a Sealed cell.
    // After the §LIVENESS-GATE alignment, apply.rs's `apply_emit_event` fail-closes on
    // `!accepts_effects()`. Expected AGREE-both-reject.
    {
        let mut a = make_open_cell(1, 100);
        a.lifecycle = dregg_cell::lifecycle::CellLifecycle::Sealed {
            reason_hash: [7u8; 32],
            sealed_at: 1,
        };
        let ida = a.id();
        let mut l = Ledger::new();
        l.insert_cell(a).unwrap();
        cases.push(Case {
            gate: "emit-on-sealed",
            desc: "EmitEvent on a SEALED cell (lifecycle does not accept effects)",
            turn: single_effect_turn(
                ida,
                ida,
                0,
                Effect::EmitEvent {
                    cell: ida,
                    event: dregg_turn::Event::new([0u8; 32], vec![]),
                },
            ),
            ledger: l,
            control: false,
        });
    }
    // ── (9c) CONTROL — EmitEvent on a LIVE cell — both ACCEPT ─────────────────────────────────
    // The honest counterpart: an emit on a Live cell must still commit in BOTH kernels. Guards
    // against the liveness fix over-rejecting (a too-broad guard would turn this AGREE-both-reject).
    {
        let (l, a, _b) = two_open(100, 5);
        cases.push(Case {
            gate: "emit-on-live",
            desc: "EmitEvent on a LIVE cell (honest; both accept)",
            turn: single_effect_turn(
                a,
                a,
                0,
                Effect::EmitEvent {
                    cell: a,
                    event: dregg_turn::Event::new([0u8; 32], vec![]),
                },
            ),
            ledger: l,
            control: true,
        });
    }

    // ════════════════ CROSS-CELL / SELF LIFECYCLE-LIVENESS ALIGNMENT ═════════════════════════
    // The verified kernel gates EVERY state-mutating effect on the AFFECTED cell being Live-ONLY
    // (`cellLive`/`acceptsEffects`, discriminant 0). Rust previously gated ONLY emit. A live agent
    // could thus transfer-FROM / write-TO a SEALED cell — committed in Rust, rolled back in Lean.
    // Each rejection case is paired with a LIVE control proving the guard does NOT over-reject.

    // ── (T-from-sealed) Transfer FROM a SEALED source ─────────────────────────────────────────
    // Agent A is SEALED; it transfers to a LIVE B. Lean `recKExecAsset` (RecordKernel.lean:613)
    // gates `cellLifecycleLive turn.src` (Live-ONLY) ⇒ refuses. apply.rs's `apply_transfer` now
    // gates `from.is_live()`. Expected AGREE-both-reject.
    {
        let a = make_sealed_cell(1, 100);
        let b = make_open_cell(2, 5);
        let (ida, idb) = (a.id(), b.id());
        let mut l = Ledger::new();
        l.insert_cell(a).unwrap();
        l.insert_cell(b).unwrap();
        cases.push(Case {
            gate: "transfer-from-sealed",
            desc: "Transfer 30 from a SEALED source A to a LIVE B (src not live)",
            turn: single_effect_turn(
                ida,
                ida,
                0,
                Effect::Transfer {
                    from: ida,
                    to: idb,
                    amount: 30,
                },
            ),
            ledger: l,
            control: false,
        });
    }
    // ── (T-from-live) CONTROL — Transfer FROM a LIVE source — both ACCEPT ─────────────────────
    {
        let (l, a, b) = two_open(100, 5);
        cases.push(Case {
            gate: "transfer-from-live",
            desc: "Transfer 30 from a LIVE A to a LIVE B (honest; both accept)",
            turn: single_effect_turn(
                a,
                a,
                0,
                Effect::Transfer {
                    from: a,
                    to: b,
                    amount: 30,
                },
            ),
            ledger: l,
            control: true,
        });
    }

    // ── (SF-on-sealed) SetField ON a SEALED cell ─────────────────────────────────────────────
    // Self-targeted SetField on a SEALED agent A (developer slot 4, not a reserved slot). Lean
    // `stateStep` (EffectsState.lean:208) gates `cellLive target` (Live-ONLY) ⇒ refuses. apply.rs's
    // `apply_set_field` now gates `c.is_live()`. Expected AGREE-both-reject.
    {
        let a = make_sealed_cell(1, 100);
        let ida = a.id();
        let mut l = Ledger::new();
        l.insert_cell(a).unwrap();
        cases.push(Case {
            gate: "setfield-on-sealed",
            desc: "SetField (slot 4) on a SEALED cell (target not live)",
            turn: single_effect_turn(
                ida,
                ida,
                0,
                Effect::SetField {
                    cell: ida,
                    index: 4,
                    value: field_from_u64(42),
                },
            ),
            ledger: l,
            control: false,
        });
    }
    // ── (SF-on-live) CONTROL — SetField ON a LIVE cell — both ACCEPT ──────────────────────────
    {
        let (l, a, _b) = two_open(100, 5);
        cases.push(Case {
            gate: "setfield-on-live",
            desc: "SetField (slot 4) on a LIVE cell (honest; both accept)",
            turn: single_effect_turn(
                a,
                a,
                0,
                Effect::SetField {
                    cell: a,
                    index: 4,
                    value: field_from_u64(42),
                },
            ),
            ledger: l,
            control: true,
        });
    }

    // ── (SP-on-sealed) SetPermissions ON a SEALED cell ────────────────────────────────────────
    // Self-targeted SetPermissions on a SEALED agent. Lean `setPermissionsA` routes to `stateStep`
    // (EffectsState.lean:208) gating `cellLive target` ⇒ refuses. apply.rs now gates `c.is_live()`.
    {
        let a = make_sealed_cell(1, 100);
        let ida = a.id();
        let mut l = Ledger::new();
        l.insert_cell(a).unwrap();
        cases.push(Case {
            gate: "setperms-on-sealed",
            desc: "SetPermissions on a SEALED cell (target not live)",
            turn: single_effect_turn(
                ida,
                ida,
                0,
                Effect::SetPermissions {
                    cell: ida,
                    new_permissions: open_permissions(),
                },
            ),
            ledger: l,
            control: false,
        });
    }

    // ── (6) Attenuate out-of-bounds slot ────────────────────────────────────────────────────
    // AttenuateCapability on slot 5 of an actor with an EMPTY c-list. Lean's `attenuateStepA` is a
    // List.modify (no-op for an out-of-range slot ⇒ TOTAL ⇒ commits); apply.rs's
    // attenuate_in_place returns None for a missing slot ⇒ rejects. Suspected ASYMMETRY-Rust-rejects.
    {
        let (l, a, _b) = two_open(100, 5);
        cases.push(Case {
            gate: "attenuate-oob-slot",
            desc: "AttenuateCapability slot 5 on an empty c-list",
            turn: single_effect_turn(
                a,
                a,
                0,
                Effect::AttenuateCapability {
                    cell: a,
                    slot: 5,
                    narrower_permissions: AuthRequired::Impossible,
                    narrower_effects: None,
                    narrower_expiry: None,
                },
            ),
            ledger: l,
            control: false,
        });
    }

    // ── (7) Self-transfer (src == dst) ────────────────────────────────────────────────────────
    // Transfer from A to A. Lean's recordKernel rejects src==dst; apply.rs? Suspected ASYMMETRY.
    {
        let (l, a, _b) = two_open(100, 5);
        cases.push(Case {
            gate: "self-transfer",
            desc: "Transfer 30 from A to A (src==dst)",
            turn: single_effect_turn(
                a,
                a,
                0,
                Effect::Transfer {
                    from: a,
                    to: a,
                    amount: 30,
                },
            ),
            ledger: l,
            control: false,
        });
    }

    // ── (9) Negative-vk factory — CreateCellFromFactory ──────────────────────────────────────
    // The effect is deliberately NOT wire-mappable (see effect_is_mappable `_ => false`); expected
    // WIRE-GAP. We still run it so the report records the gap rather than silently omitting it.
    {
        let (l, a, _b) = two_open(100, 5);
        let params = dregg_cell::factory::FactoryCreationParams {
            mode: dregg_cell::CellMode::Hosted,
            program_vk: None,
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: [3u8; 32],
        };
        cases.push(Case {
            gate: "negative-vk-factory",
            desc: "CreateCellFromFactory (effect has no Lean wire arm)",
            turn: single_effect_turn(
                a,
                a,
                0,
                Effect::CreateCellFromFactory {
                    factory_vk: [0u8; 32],
                    owner_pubkey: [3u8; 32],
                    token_id: [0u8; 32],
                    params,
                },
            ),
            ledger: l,
            control: false,
        });
    }

    // ── IncrementNonce (monotone-nonce family) ───────────────────────────────────────────────
    // dregg's IncrementNonce carries NO target value — it strictly increments (+1), so the
    // "non-strictly-greater" attack (#5) is INEXPRESSIBLE in the effect grammar (safe-by-construction).
    // We still exercise the effect to confirm both kernels agree on its commit decision (control).
    {
        let (l, a, _b) = two_open(100, 5);
        cases.push(Case {
            gate: "increment-nonce",
            desc: "IncrementNonce on A (monotone +1; the regress attack is inexpressible)",
            turn: single_effect_turn(a, a, 0, Effect::IncrementNonce { cell: a }),
            ledger: l,
            control: true,
        });
    }

    // ════════════════════ CONTROLS (should AGREE-both-reject) ════════════════════════════════

    // (C1) Overspend transfer: A has 10, transfers 9999 to B. Both must reject.
    {
        let (l, a, b) = two_open(10, 5);
        cases.push(Case {
            gate: "control-overspend",
            desc: "Transfer 9999 from A (balance 10) to B",
            turn: single_effect_turn(
                a,
                a,
                0,
                Effect::Transfer {
                    from: a,
                    to: b,
                    amount: 9999,
                },
            ),
            ledger: l,
            control: true,
        });
    }

    // (C2) Proofless NoteSpend: empty spending_proof. Both must reject.
    {
        let (l, a, _b) = two_open(100, 5);
        cases.push(Case {
            gate: "control-proofless-notespend",
            desc: "NoteSpend with empty spending_proof",
            turn: single_effect_turn(
                a,
                a,
                0,
                Effect::NoteSpend {
                    nullifier: dregg_cell::Nullifier([0xAA; 32]),
                    note_tree_root: [0x11; 32],
                    value: 0,
                    asset_type: 0,
                    spending_proof: vec![],
                    value_commitment: None,
                },
            ),
            ledger: l,
            control: true,
        });
    }

    // (C3) Unauthorized cross-cell SetPermissions: A (agent) tries to SetPermissions on B.
    // apply.rs requires ownership/cap on B; A owns only A. Both should reject.
    {
        let (l, a, b) = two_open(100, 5);
        cases.push(Case {
            gate: "control-cross-cell-setperms",
            desc: "A sets B's permissions (A does not own B)",
            turn: turn_with_auth(
                a,
                b,
                0,
                Authorization::Unchecked,
                vec![Effect::SetPermissions {
                    cell: b,
                    new_permissions: open_permissions(),
                }],
            ),
            ledger: l,
            control: true,
        });
    }

    // ════════════════ AGENT-LIFECYCLE ADMISSION GATE (`cellLifecycleCanAuthor`) ══════════════════
    // The verified `admissible` (Admission.lean §2) gate-3 leg refuses a turn whose AGENT cell is in
    // a TERMINAL lifecycle state (Destroyed/Migrated). The per-effect target-liveness gates above
    // guard only the AFFECTED cell, NEVER the actor — so a terminal agent acting on a LIVE cell it
    // can reach slips past them. This pair pins the actor-side gate.

    // ── (DA-from-destroyed) Terminal (Destroyed) AGENT transfers to a LIVE B ──────────────────────
    // A is Destroyed; B is Live. The transfer's target/dest liveness gate would pass (B is Live) —
    // only the agent-admission gate catches it. Lean `cellLifecycleCanAuthor` (admission gate 3)
    // refuses; the Rust executor's admission now mirrors it. Expected AGREE-both-reject (the closed
    // safe-direction gap — before the gate, Rust ACCEPTED this).
    {
        let a = make_destroyed_cell(1, 100);
        let b = make_open_cell(2, 5);
        let (ida, idb) = (a.id(), b.id());
        let mut l = Ledger::new();
        l.insert_cell(a).unwrap();
        l.insert_cell(b).unwrap();
        cases.push(Case {
            gate: "agent-terminal-destroyed",
            desc: "Transfer 30 from a DESTROYED agent A to a LIVE B (agent not authorable)",
            turn: single_effect_turn(
                ida,
                idb,
                0,
                Effect::Transfer {
                    from: ida,
                    to: idb,
                    amount: 30,
                },
            ),
            ledger: l,
            control: false,
        });
    }
    // ── (DA-from-live) CONTROL — Transfer from a LIVE agent — both ACCEPT ─────────────────────────
    // The honest counterpart proves the agent-lifecycle gate does NOT over-reject a live agent.
    {
        let (l, a, b) = two_open(100, 5);
        cases.push(Case {
            gate: "agent-live-control",
            desc: "Transfer 30 from a LIVE agent A to a LIVE B (honest; both accept)",
            turn: single_effect_turn(
                a,
                a,
                0,
                Effect::Transfer {
                    from: a,
                    to: b,
                    amount: 30,
                },
            ),
            ledger: l,
            control: true,
        });
    }

    cases
}

// ---------------------------------------------------------------------------
// The harness
// ---------------------------------------------------------------------------

#[test]
fn rejection_parity_differential() {
    if !dregg_lean_ffi::lean_available() {
        eprintln!(
            "SKIP: Lean archive not linked (lean_available()==false) — cannot run the verified kernel"
        );
        return;
    }

    // CHARACTERISED-HOLE allowlist: confirmed `ASYMMETRY-Rust-accepts` cases whose exact Lean gate
    // is identified below. The harness RECORDS these (they ARE real Rust-under-enforcement, in the
    // SAFE operational direction — the verified kernel is STRICTER, so under the authority-inversion
    // the Lean verdict vetoes the Rust commit) and hard-fails ONLY on a NEW, uncharacterised hole.
    //
    //   * `burn-no-well` — `Effect::Burn` on an owned cell with no mint cap. The remaining
    //     asymmetry is PURELY AUTHORITY now (SUPPLY-MODEL Stage 1, docs/SUPPLY-MODEL.md):
    //       - CONSERVATION half CLOSED — apply.rs no longer commits a Σδ≠0 scalar destroy. EVERY
    //         asset resolves a per-asset issuer well (lazily derived if unregistered), so the burn
    //         is a CONSERVING holder→well MOVE (per-turn Σδ=0). The "no issuer well" precondition
    //         this case named no longer exists.
    //       - AUTHORITY half OPEN until Stage 3 — Rust still ACCEPTS the self-burn on ownership
    //         (permissionless self-redeem, the ratified Stage-1 policy), while the verified
    //         `execBurn` (Dregg2/Exec/Generators.lean:55) gates on `mintAuthorizedB k.caps actor
    //         cell = true`; a cap-less burn fails that gate (empty c-list) ⇒ Lean REFUSES. This is
    //         the SAFE direction (Lean stricter) and is the same divergence the
    //         `rust_lean_divergence_finder` `Burn` allowlist documents. It closes in Stage 3 (Lean
    //         authority split: self-redeem = holder-permissioned, mint = mint-cap-gated).
    //   * `self-transfer` — FIXED (apply.rs `apply_transfer` now rejects `from == to`, aligning with
    //     `Dregg2/Exec/RecordKernel.lean:495`); now AGREE-both-reject, no longer a hole. Removed from
    //     the allowlist (kept here as a record of the closed asymmetry).
    //   * `mint-authorized` — `Effect::Mint` with a control-grade `EFFECT_MINT` cap over the issuer
    //     well (SUPPLY-MODEL Stage 2a, docs/SUPPLY-MODEL.md). apply.rs `apply_mint` ACCEPTS the
    //     CORRECT supply entry (well→holder conserving move, cap-gated by the Rust image of
    //     `mintAuthorizedB`). The asymmetry is PURELY a WIRE-FAITHFULNESS limit, NOT under-
    //     enforcement: the shadow marshals `Mint` with the synthetic `asset: 0` (exactly as `Burn`,
    //     because the native scalar asset has no genesis issuer well numbered on the wire), so the
    //     verified `mintH` gate `mintAuthorizedB k.caps actor (issuerOf 0)` cannot see the held
    //     node-cap over the marshalled issuer ⇒ Lean refuses. SAFE direction (Lean stricter, vetoes
    //     the commit). The Rust gate IS the faithful image of the Lean predicate (the
    //     `mint-unauthorized` case proves they AGREE-reject when the cap is absent); the wire closes
    //     the same way `burn-no-well` does — when the native asset carries a genesis issuer well that
    //     the marshaller numbers. The DEDICATED authorized-mint conservation+authority check lives in
    //     `dregg-turn` tests (`conservation_mint_property.rs`), where the full cap graph is exercised
    //     natively without the wire's asset-numbering limit.
    let characterised_holes: &[&str] = &["burn-no-well", "mint-authorized"];

    let mut rows: Vec<String> = Vec::new();
    let mut holes: Vec<String> = Vec::new();
    let mut new_holes: Vec<String> = Vec::new();
    let mut gaps: Vec<&'static str> = Vec::new();

    for case in build_corpus() {
        let (rust, lean, verdict) = run_case(&case);
        let lean_s = match lean {
            Some(true) => "accepts",
            Some(false) => "rejects",
            None => "—(gap)",
        };
        let kind = if case.control { "control" } else { "suspicion" };
        rows.push(format!(
            "| {} | {} | {} | rust={} | lean={} | {} |",
            kind,
            case.gate,
            case.desc,
            if rust { "accepts" } else { "rejects" },
            lean_s,
            verdict.label(),
        ));
        if verdict == Verdict::AsymRustAccepts {
            let characterised = characterised_holes.contains(&case.gate);
            let note = format!(
                "  [{}]{} {} — Rust COMMITS, Lean REFUSES",
                case.gate,
                if characterised {
                    " (characterised)"
                } else {
                    " (NEW)"
                },
                case.desc,
            );
            if !characterised {
                new_holes.push(note.clone());
            }
            holes.push(note);
        }
        if verdict == Verdict::WireGap {
            gaps.push(case.gate);
        }
    }

    println!("\n=== REJECTION-PARITY DIFFERENTIAL ===\n");
    println!("| kind | gate | adversarial turn | rust | lean | verdict |");
    println!("|------|------|------------------|------|------|---------|");
    for r in &rows {
        println!("{r}");
    }

    if !gaps.is_empty() {
        println!(
            "\nWIRE-GAP (not differentially verifiable — effect has no Lean wire arm): {gaps:?}"
        );
    }

    if holes.is_empty() {
        println!(
            "\nNo ASYMMETRY-Rust-accepts (no confirmed soundness hole on the wire-mappable set)."
        );
    } else {
        println!(
            "\nCONFIRMED ASYMMETRY-Rust-accepts (Rust accepts what the verified kernel refuses):"
        );
        for h in &holes {
            println!("{h}");
        }
    }

    // HARD-FAIL only on a NEW (uncharacterised) hole in the dangerous direction: Rust commits a turn
    // the verified kernel refuses, NOT on the documented characterised-holes allowlist. The
    // characterised holes are REAL Rust under-enforcement, recorded above with their exact Lean gate;
    // they are in the SAFE operational direction (the verified kernel is stricter ⇒ vetoes the commit
    // under the authority-inversion) and close as the apply.rs migrations land. A NEW one is a hole
    // the maintainer has not yet seen and must investigate before allowlisting.
    assert!(
        new_holes.is_empty(),
        "NEW (uncharacterised) SOUNDNESS HOLE(S): Rust under-enforces a gate the verified Lean kernel \
         enforces, outside the documented allowlist {characterised_holes:?}. Investigate before \
         extending the allowlist:\n{}",
        new_holes.join("\n")
    );
}
