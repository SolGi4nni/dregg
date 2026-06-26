//! rust_lean_parity_gauntlet.rs — THE consolidated Rust↔Lean executor PARITY GAUNTLET.
//!
//! This is the single, runnable justification artifact behind shipping the RUST executor
//! (`dregg_turn::TurnExecutor::execute` → `turn/src/executor/apply.rs`) to the SDKs *by default*,
//! with the verified ~150MB Lean kernel (`Dregg2.Exec.recKExec`, reached via `dregg-lean-ffi`) as an
//! opt-in shadow. It runs ONE corpus of turns through BOTH executors and, turn-by-turn, records:
//!
//!   * accept/reject parity   — does the Rust commit bit equal the verified Lean commit bit?
//!   * post-state parity      — when BOTH commit, is the post-state BYTE-IDENTICAL? (per-cell
//!                              balance + nonce + the state fields + `cap_root`, AND the whole
//!                              ledger `.root()` — the Merkle commitment a light client checks).
//!
//! The corpus covers the full effect COHORT (transfer / set-field / grant / attenuate / mint /
//! burn / revoke / note / lifecycle / sovereign / refusal / archive), edge cases, and an adversarial
//! should-reject battery. Each turn classifies into one verdict:
//!
//!   * `BothAcceptStateAgree`   — both commit AND the post-states are byte-identical. THE good
//!                                result: Rust reproduced the verified kernel's exact transition.
//!   * `BothReject`             — both refuse. The good result for an adversarial turn.
//!   * `BothAcceptStateDiverge` — both commit but the post-states DIFFER. A SILENT STATE BUG: Rust
//!                                committed a *different* state than the verified spec. HARD FAIL —
//!                                this is the worst outcome for ship-Rust and must never occur.
//!   * `RustAcceptsLeanRejects` — Rust commits a turn the verified kernel REFUSES. The ship-Rust
//!                                under-enforcement direction. HARD FAIL unless the cohort is on the
//!                                documented `SAFE_DIRECTION_RESIDUALS` allowlist (each entry carries
//!                                its exact Lean gate + why it is a known, characterised residual; in
//!                                the deployed shadow-gated node the verified verdict is authoritative
//!                                and vetoes the commit, so these are SAFE there — for the pure-Rust
//!                                SDK they are the honestly-named residuals, see docs).
//!   * `RustRejectsLeanAccepts` — Rust is STRICTER than the verified kernel (the safe divergence
//!                                direction: Rust refuses some turns the spec would admit). Reported,
//!                                never failed.
//!   * `WireGap`                — the turn is not marshallable to the Lean wire, so it cannot be
//!                                differentially compared. Reported as a gap, never faked.
//!
//! HARD-FAIL conditions (the gauntlet's teeth):
//!   1. ANY `BothAcceptStateDiverge`                       — a silent state divergence.
//!   2. ANY `RustAcceptsLeanRejects` whose cohort is NOT on the allowlist — a NEW under-enforcement.
//! Plus a non-vacuity floor: the corpus must produce a meaningful number of `BothAcceptStateAgree`
//! and at least one `BothReject`, so the gauntlet cannot pass by trivially gapping/rejecting.
//!
//! Requires the linked Lean archive; self-skips (does not fail) when `lean_available()` is false —
//! it cannot run the verified kernel without it. The strengthened justification is documented in
//! `docs/RUST-LEAN-EXECUTOR-PARITY.md`.
//!
//! Run: `cargo test -p dregg-exec-lean --test rust_lean_parity_gauntlet -- --nocapture`

use std::collections::HashMap;

use dregg_cell::lifecycle::{ArchivalAttestation, CellLifecycle, DeathCertificate, DeathReason};
use dregg_cell::state::FieldElement;
use dregg_cell::{
    AuthRequired, CapabilityRef, Cell, CellId, Ledger, NoteCommitment, Permissions, VerificationKey,
};
use dregg_exec_lean::lean_apply::{self, execute_via_lean};
use dregg_exec_lean::lean_shadow::ShadowHostCtx;
use dregg_turn::action::{Event, RefusalReason, WitnessBlob, WitnessKind};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

// ---------------------------------------------------------------------------
// Fixture builders (mirroring the existing producer/rejection differentials).
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

/// Every action requires a `Signature` the adversarial `Unchecked` turn cannot present.
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

fn make_sealed_cell(seed: u8, balance: i64) -> Cell {
    let mut c = make_open_cell(seed, balance);
    c.lifecycle = CellLifecycle::Sealed {
        reason_hash: [7u8; 32],
        sealed_at: 1,
    };
    c
}

/// A self-`node` capability = the held edge the verified mint/burn/delegate gates read.
fn grant_self_cap(cell: &mut Cell) {
    let id = cell.id();
    let _ = cell.capabilities.grant(id, AuthRequired::None);
}

fn field_from_u64(v: u64) -> FieldElement {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&v.to_be_bytes());
    out
}

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
        // The wire marshaller REQUIRES valid_until; the diagnostic host clock is 0, so any future
        // expiry admits.
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

/// A single-`Refusal` turn carrying the one witness blob the refusal's `proof_witness_index: 0`
/// points at (the executor enforces the witness exists).
fn single_refusal_turn(agent: CellId, cell: CellId, reason: RefusalReason) -> Turn {
    let mut turn = single_effect_turn(
        agent,
        cell,
        0,
        Effect::Refusal {
            cell,
            offered_action_commitment: [3u8; 32],
            refusal_reason: reason,
            proof_witness_index: 0,
        },
    );
    turn.call_forest.roots[0].action.witness_blobs =
        vec![WitnessBlob::new(WitnessKind::Cleartext, vec![0xAB; 8])];
    turn
}

fn ledger_of(cells: Vec<Cell>) -> Ledger {
    let mut l = Ledger::new();
    for c in cells {
        l.insert_cell(c).unwrap();
    }
    l
}

// ---------------------------------------------------------------------------
// Post-state agreement (byte-identical): per-cell + the whole-ledger root.
// ---------------------------------------------------------------------------

/// Compare two ledgers on balance + nonce + the state fields + `cap_root` + `.root()`.
/// Returns Ok(()) on full agreement or Err(reason) on the first divergence.
fn ledgers_agree(rust: &mut Ledger, lean: &mut Ledger, ids: &[CellId]) -> Result<(), String> {
    for id in ids {
        match (rust.get(id), lean.get(id)) {
            (Some(r), Some(l)) => {
                if r.state.balance() != l.state.balance() {
                    return Err(format!(
                        "balance on {id:?}: rust={} lean={}",
                        r.state.balance(),
                        l.state.balance()
                    ));
                }
                if r.state.nonce() != l.state.nonce() {
                    return Err(format!(
                        "nonce on {id:?}: rust={} lean={}",
                        r.state.nonce(),
                        l.state.nonce()
                    ));
                }
                for slot in 0..dregg_cell::state::STATE_SLOTS {
                    if r.state.fields[slot] != l.state.fields[slot] {
                        return Err(format!(
                            "field[{slot}] on {id:?}: rust={:?} lean={:?}",
                            r.state.fields[slot], l.state.fields[slot]
                        ));
                    }
                }
                let rc = dregg_cell::compute_canonical_capability_root(&r.capabilities);
                let lc = dregg_cell::compute_canonical_capability_root(&l.capabilities);
                if rc != lc {
                    return Err(format!("cap_root on {id:?}: rust={rc:?} lean={lc:?}"));
                }
            }
            (None, Some(_)) => {
                return Err(format!("presence on {id:?}: absent RUST, present LEAN"));
            }
            (Some(_), None) => {
                return Err(format!("presence on {id:?}: present RUST, absent LEAN"));
            }
            (None, None) => {}
        }
    }
    let rr = rust.root();
    let lr = lean.root();
    if rr != lr {
        return Err(format!("ROOT: rust={rr:?} lean={lr:?}"));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Verdict + case.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    BothAcceptStateAgree,
    BothAcceptStateDiverge,
    BothReject,
    RustAcceptsLeanRejects,
    RustRejectsLeanAccepts,
    WireGap,
}

impl Verdict {
    fn label(self) -> &'static str {
        match self {
            Verdict::BothAcceptStateAgree => "BOTH-ACCEPT state=AGREE",
            Verdict::BothAcceptStateDiverge => "BOTH-ACCEPT state=DIVERGE",
            Verdict::BothReject => "BOTH-REJECT",
            Verdict::RustAcceptsLeanRejects => "ASYM Rust-accepts/Lean-rejects",
            Verdict::RustRejectsLeanAccepts => "ASYM Rust-rejects/Lean-accepts",
            Verdict::WireGap => "WIRE-GAP",
        }
    }
}

/// A corpus case: a name, the cohort effect it exercises, the pre-state, the turn, and the cell ids
/// whose post-state is compared.
struct Case {
    name: &'static str,
    cohort: &'static str,
    ledger: Ledger,
    turn: Turn,
    ids: Vec<CellId>,
}

/// Run both executors over a case; return `(verdict, detail)`.
fn run_case(case: &Case) -> (Verdict, String) {
    // (1) Rust executor (apply.rs). Fresh executor so each turn is first in its receipt chain.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let mut rust_ledger = case.ledger.clone();
    let rust_committed = executor
        .execute(&case.turn, &mut rust_ledger)
        .is_committed();

    // (2) Verified Lean kernel over the SAME turn + pre-state.
    let host = ShadowHostCtx::diag();
    match execute_via_lean(&case.turn, &case.ledger, &host) {
        Err(lean_apply::ExtractError::Ineligible)
        | Err(lean_apply::ExtractError::RootGap { .. }) => (Verdict::WireGap, String::new()),
        Err(e) => panic!("Lean kernel FAILED on '{}': {e}", case.name),
        Ok((mut lean_ledger, lean_committed)) => match (rust_committed, lean_committed) {
            (false, false) => (Verdict::BothReject, String::new()),
            (true, false) => (Verdict::RustAcceptsLeanRejects, String::new()),
            (false, true) => (Verdict::RustRejectsLeanAccepts, String::new()),
            (true, true) => match ledgers_agree(&mut rust_ledger, &mut lean_ledger, &case.ids) {
                Ok(()) => (Verdict::BothAcceptStateAgree, String::new()),
                Err(why) => (Verdict::BothAcceptStateDiverge, why),
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The corpus.
// ---------------------------------------------------------------------------

/// Cohorts whose `RustAcceptsLeanRejects` is a DOCUMENTED, characterised residual — Rust commits a
/// turn the verified kernel refuses, in the SAFE operational direction (the verified kernel is
/// STRICTER; the deployed shadow-gated node takes the Lean verdict as authoritative and vetoes the
/// commit). For the pure-Rust SDK these are the honestly-named residuals (see
/// `docs/RUST-LEAN-EXECUTOR-PARITY.md`). They do NOT fail the gauntlet; a NEW under-enforcement on
/// any OTHER cohort does.
///
///   * `Burn`              — the scalar `Effect::Burn` (destroy balance, no destination) has no
///                           conserving image in the verified issuer-supply kernel (DREGG3 §2.2:
///                           `.burnA` is a return-to-well move). On the 1-cell wire numbering it
///                           marshals to a self-burn of the well, which the kernel refuses outright.
///                           Closes when the staged Rust value-model migration makes apply.rs's burn
///                           the well move. (`lean_state_producer_widen::burn_refused_under_issuer_supply`.)
///   * `Mint`              — apply.rs `apply_mint` gates on a control-grade `EFFECT_MINT` cap over
///                           the issuer well (the faithful image of Lean `mintAuthorizedB`); the
///                           `mint-unauthorized` case below proves the gates AGREE-reject when the
///                           cap is absent. The authorized-mint asymmetry is purely a WIRE-
///                           faithfulness limit: the shadow marshals `Mint` with the synthetic
///                           `asset: 0`, so the verified gate cannot see the held node-cap over the
///                           marshalled issuer. Not under-enforcement; the native cap graph is
///                           exercised in `dregg-turn::conservation_mint_property`.
///   * `AttenuateCapability` / `CellUnseal` — cap-/lifecycle-reshape effects whose commit bit
///                           currently diverges in the SAFE direction (the verified kernel is
///                           STRICTER on the marshalled wire — the held cap / sealed payload the
///                           narrowing/unseal reasons over is not faithfully numbered on the wire,
///                           so the kernel fail-closes). The reconstituted post-state AGREES when
///                           both commit; only the commit bit diverges. Same wire-faithfulness class
///                           as `Mint`.
const SAFE_DIRECTION_RESIDUALS: &[&str] = &["Burn", "Mint", "AttenuateCapability", "CellUnseal"];

fn build_corpus() -> Vec<Case> {
    let mut cases: Vec<Case> = Vec::new();
    let mut push = |name, cohort, ledger, turn, ids: Vec<CellId>| {
        cases.push(Case {
            name,
            cohort,
            ledger,
            turn,
            ids,
        })
    };

    // ═══════════════════ ACCEPT-PATH COHORT — expect BOTH-ACCEPT state=AGREE ═══════════════════

    // Transfer A→B 30.
    {
        let a = make_open_cell(1, 100);
        let b = make_open_cell(2, 5);
        let (ida, idb) = (a.id(), b.id());
        push(
            "transfer",
            "Transfer",
            ledger_of(vec![a, b]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::Transfer {
                    from: ida,
                    to: idb,
                    amount: 30,
                },
            ),
            vec![ida, idb],
        );
    }

    // SetField — developer slot 6.
    {
        let a = make_open_cell(1, 100);
        let ida = a.id();
        push(
            "setfield-dev-slot6",
            "SetField",
            ledger_of(vec![a]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::SetField {
                    cell: ida,
                    index: 6,
                    value: field_from_u64(42),
                },
            ),
            vec![ida],
        );
    }

    // SetField — reserved slot 0 (edge case: the verified EffectsState does NOT reserve it; both accept).
    {
        let a = make_open_cell(1, 100);
        let ida = a.id();
        push(
            "setfield-reserved-slot0",
            "SetField",
            ledger_of(vec![a]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::SetField {
                    cell: ida,
                    index: 0,
                    value: field_from_u64(999),
                },
            ),
            vec![ida],
        );
    }

    // EmitEvent on a LIVE cell.
    {
        let a = make_open_cell(1, 100);
        let ida = a.id();
        push(
            "emit-event-live",
            "EmitEvent",
            ledger_of(vec![a]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::EmitEvent {
                    cell: ida,
                    event: Event {
                        topic: field_from_u64(11),
                        data: vec![field_from_u64(22)],
                    },
                },
            ),
            vec![ida],
        );
    }

    // IncrementNonce.
    {
        let a = make_open_cell(1, 100);
        let ida = a.id();
        push(
            "increment-nonce",
            "IncrementNonce",
            ledger_of(vec![a]),
            single_effect_turn(ida, ida, 0, Effect::IncrementNonce { cell: ida }),
            vec![ida],
        );
    }

    // NoteCreate (note set is off the cell root; both commit, root agrees).
    {
        let a = make_open_cell(1, 100);
        let ida = a.id();
        push(
            "note-create",
            "NoteCreate",
            ledger_of(vec![a]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::NoteCreate {
                    commitment: NoteCommitment([7u8; 32]),
                    value: 0,
                    asset_type: 0,
                    encrypted_note: vec![],
                    value_commitment: None,
                    range_proof: None,
                },
            ),
            vec![ida],
        );
    }

    // GrantCapability — self-cap held, grant a FULL (Signature + breadstuff) cap over A into B.
    {
        let mut a = make_open_cell(1, 100);
        grant_self_cap(&mut a);
        let ida = a.id();
        let b = make_open_cell(2, 5);
        let idb = b.id();
        let cap = CapabilityRef {
            target: ida,
            slot: 0,
            permissions: AuthRequired::Signature,
            breadstuff: Some([7u8; 32]),
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        };
        push(
            "grant-capability",
            "GrantCapability",
            ledger_of(vec![a, b]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::GrantCapability {
                    from: ida,
                    to: idb,
                    cap,
                },
            ),
            vec![ida, idb],
        );
    }

    // Introduce — A holds edges to both R (recipient) and T (target).
    {
        let mut a = make_open_cell(1, 100);
        let r = make_open_cell(2, 5);
        let t = make_open_cell(3, 5);
        let (ida, idr, idt) = (a.id(), r.id(), t.id());
        let _ = a.capabilities.grant(idr, AuthRequired::None);
        let _ = a.capabilities.grant(idt, AuthRequired::None);
        push(
            "introduce",
            "Introduce",
            ledger_of(vec![a, r, t]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::Introduce {
                    introducer: ida,
                    recipient: idr,
                    target: idt,
                    permissions: AuthRequired::None,
                },
            ),
            vec![ida, idr, idt],
        );
    }

    // RevokeCapability — empty c-list no-op (verified recCRevoke is total).
    {
        let a = make_open_cell(1, 100);
        let ida = a.id();
        push(
            "revoke-capability-empty",
            "RevokeCapability",
            ledger_of(vec![a]),
            single_effect_turn(ida, ida, 0, Effect::RevokeCapability { cell: ida, slot: 0 }),
            vec![ida],
        );
    }

    // RevokeDelegation — real parent(A)→child(B) edge; bumps A's delegation_epoch, clears B's snapshot.
    {
        let mut a = make_open_cell(1, 100);
        let mut b = make_open_cell(2, 5);
        let (ida, idb) = (a.id(), b.id());
        b.delegate = Some(ida);
        a.state.set_delegation_epoch(3);
        push(
            "revoke-delegation",
            "RevokeDelegation",
            ledger_of(vec![a, b]),
            single_effect_turn(ida, ida, 0, Effect::RevokeDelegation { child: idb }),
            vec![ida, idb],
        );
    }

    // CellSeal (Live → Sealed{reason, sealed_at}).
    {
        let a = make_open_cell(1, 100);
        let ida = a.id();
        push(
            "cell-seal",
            "CellSeal",
            ledger_of(vec![a]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::CellSeal {
                    target: ida,
                    reason: [9u8; 32],
                },
            ),
            vec![ida],
        );
    }

    // CellDestroy (Live → Destroyed{cert}).
    {
        let a = make_open_cell(1, 100);
        let ida = a.id();
        let cert = DeathCertificate {
            cell_id: ida,
            last_receipt_hash: [3u8; 32],
            final_state_commitment: [5u8; 32],
            destroyed_at_height: 42,
            reason: DeathReason::Voluntary,
        };
        push(
            "cell-destroy",
            "CellDestroy",
            ledger_of(vec![a]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::CellDestroy {
                    target: ida,
                    certificate: cert,
                },
            ),
            vec![ida],
        );
    }

    // CellUnseal (Sealed → Live) — self-cap held for the authority leg. CURRENT RESIDUAL.
    {
        let mut a = make_open_cell(1, 100);
        grant_self_cap(&mut a);
        a.seal([7u8; 32], 0).expect("seal the pre-state cell");
        let ida = a.id();
        push(
            "cell-unseal",
            "CellUnseal",
            ledger_of(vec![a]),
            single_effect_turn(ida, ida, 0, Effect::CellUnseal { target: ida }),
            vec![ida],
        );
    }

    // SetPermissions — change one field (set_state None → Signature).
    {
        let a = make_open_cell(1, 100);
        let ida = a.id();
        let mut new_perms = open_permissions();
        new_perms.set_state = AuthRequired::Signature;
        push(
            "set-permissions",
            "SetPermissions",
            ledger_of(vec![a]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::SetPermissions {
                    cell: ida,
                    new_permissions: new_perms,
                },
            ),
            vec![ida],
        );
    }

    // SetVerificationKey — install a full VK struct.
    {
        let a = make_open_cell(1, 100);
        let ida = a.id();
        #[allow(deprecated)]
        let vk = VerificationKey::new(vec![1, 2, 3, 4]);
        push(
            "set-verification-key",
            "SetVerificationKey",
            ledger_of(vec![a]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::SetVerificationKey {
                    cell: ida,
                    new_vk: Some(vk),
                },
            ),
            vec![ida],
        );
    }

    // MakeSovereign — A self-rebinds behind a commitment (removed from the readable leaf set).
    {
        let a = make_open_cell(1, 100);
        let ida = a.id();
        push(
            "make-sovereign",
            "MakeSovereign",
            ledger_of(vec![a]),
            single_effect_turn(ida, ida, 0, Effect::MakeSovereign { cell: ida }),
            vec![ida],
        );
    }

    // Refusal — carries the witness its proof_witness_index points at.
    {
        let a = make_open_cell(1, 100);
        let ida = a.id();
        push(
            "refusal",
            "Refusal",
            ledger_of(vec![a]),
            single_refusal_turn(ida, ida, RefusalReason::Declined),
            vec![ida],
        );
    }

    // ReceiptArchive — archive a prefix (Live → Archived).
    {
        let a = make_open_cell(1, 100);
        let ida = a.id();
        let att = ArchivalAttestation {
            cell_id: ida,
            archive_start_height: 0,
            archive_end_height: 0,
            archive_blob_hash: [4u8; 32],
            archive_terminal_commitment: [5u8; 32],
            archive_terminal_receipt_hash: [3u8; 32],
        };
        push(
            "receipt-archive",
            "ReceiptArchive",
            ledger_of(vec![a]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::ReceiptArchive {
                    prefix_end_height: 0,
                    checkpoint: att,
                },
            ),
            vec![ida],
        );
    }

    // ── COHORT residuals (Rust-accepts / Lean-rejects, allowlisted; see SAFE_DIRECTION_RESIDUALS) ──

    // Burn — self-cap held; the verified issuer-supply kernel refuses the scalar destroy.
    {
        let mut a = make_open_cell(1, 100);
        grant_self_cap(&mut a);
        let ida = a.id();
        push(
            "burn-with-cap",
            "Burn",
            ledger_of(vec![a]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::Burn {
                    target: ida,
                    slot: 0,
                    amount: 40,
                },
            ),
            vec![ida],
        );
    }

    // AttenuateCapability — narrow a held cap (None → Signature). CURRENT RESIDUAL (wire cap fidelity).
    {
        let mut a = make_open_cell(1, 100);
        let b = make_open_cell(2, 5);
        let idb = b.id();
        let slot = a
            .capabilities
            .grant(idb, AuthRequired::None)
            .expect("seed a held cap");
        let ida = a.id();
        push(
            "attenuate-capability",
            "AttenuateCapability",
            ledger_of(vec![a, b]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::AttenuateCapability {
                    cell: ida,
                    slot,
                    narrower_permissions: AuthRequired::Signature,
                    narrower_effects: None,
                    narrower_expiry: Some(500),
                },
            ),
            vec![ida, idb],
        );
    }

    // Mint — authorized (control-grade EFFECT_MINT cap over the issuer well). RESIDUAL (wire asset numbering).
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
        push(
            "mint-authorized",
            "Mint",
            ledger_of(vec![a, b]),
            single_effect_turn(
                ida,
                idb,
                0,
                Effect::Mint {
                    target: idb,
                    slot: 0,
                    amount: 10,
                },
            ),
            vec![ida, idb],
        );
    }

    // ═══════════════════ ADVERSARIAL / SHOULD-REJECT battery — expect BOTH-REJECT ═══════════════════

    // Overspend.
    {
        let a = make_open_cell(1, 10);
        let b = make_open_cell(2, 5);
        let (ida, idb) = (a.id(), b.id());
        push(
            "adv-overspend",
            "Transfer",
            ledger_of(vec![a, b]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::Transfer {
                    from: ida,
                    to: idb,
                    amount: 9999,
                },
            ),
            vec![ida, idb],
        );
    }

    // Self-transfer (src == dst).
    {
        let a = make_open_cell(1, 100);
        let ida = a.id();
        push(
            "adv-self-transfer",
            "Transfer",
            ledger_of(vec![a]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::Transfer {
                    from: ida,
                    to: ida,
                    amount: 30,
                },
            ),
            vec![ida],
        );
    }

    // Transfer FROM a SEALED source.
    {
        let a = make_sealed_cell(1, 100);
        let b = make_open_cell(2, 5);
        let (ida, idb) = (a.id(), b.id());
        push(
            "adv-transfer-from-sealed",
            "Transfer",
            ledger_of(vec![a, b]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::Transfer {
                    from: ida,
                    to: idb,
                    amount: 30,
                },
            ),
            vec![ida, idb],
        );
    }

    // SetField ON a SEALED cell.
    {
        let a = make_sealed_cell(1, 100);
        let ida = a.id();
        push(
            "adv-setfield-on-sealed",
            "SetField",
            ledger_of(vec![a]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::SetField {
                    cell: ida,
                    index: 4,
                    value: field_from_u64(42),
                },
            ),
            vec![ida],
        );
    }

    // EmitEvent ON a SEALED cell.
    {
        let a = make_sealed_cell(1, 100);
        let ida = a.id();
        push(
            "adv-emit-on-sealed",
            "EmitEvent",
            ledger_of(vec![a]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::EmitEvent {
                    cell: ida,
                    event: Event::new([0u8; 32], vec![]),
                },
            ),
            vec![ida],
        );
    }

    // Proofless NoteSpend.
    {
        let a = make_open_cell(1, 100);
        let ida = a.id();
        push(
            "adv-proofless-notespend",
            "NoteSpend",
            ledger_of(vec![a]),
            single_effect_turn(
                ida,
                ida,
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
            vec![ida],
        );
    }

    // Unauthorized Mint (no mint-cap) — both reject (the gate AGREES with Lean's mintAuthorizedB).
    {
        let a = make_open_cell(1, 100);
        let b = make_open_cell(2, 5);
        let (ida, idb) = (a.id(), b.id());
        push(
            "adv-mint-unauthorized",
            "Mint",
            ledger_of(vec![a, b]),
            single_effect_turn(
                ida,
                idb,
                0,
                Effect::Mint {
                    target: idb,
                    slot: 0,
                    amount: 10,
                },
            ),
            vec![ida, idb],
        );
    }

    // Cross-cell GrantCapability with NO held edge to the target — both reject.
    {
        let a = make_open_cell(1, 100);
        let b = make_open_cell(2, 5);
        let c = make_open_cell(3, 5);
        let (ida, idb, idc) = (a.id(), b.id(), c.id());
        let cap = CapabilityRef {
            target: idc,
            slot: 0,
            permissions: AuthRequired::None,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        };
        push(
            "adv-grant-no-edge",
            "GrantCapability",
            ledger_of(vec![a, b, c]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::GrantCapability {
                    from: ida,
                    to: idb,
                    cap,
                },
            ),
            vec![ida, idb, idc],
        );
    }

    // ── Rust-STRICTER-than-spec edge cases (RustRejectsLeanAccepts; the SAFE divergence direction) ──

    // Cross-cell SetPermissions (A does not own B): Rust requires ownership; the verified gate admits.
    {
        let a = make_open_cell(1, 100);
        let b = make_open_cell(2, 5);
        let (ida, idb) = (a.id(), b.id());
        push(
            "edge-cross-cell-setperms",
            "SetPermissions",
            ledger_of(vec![a, b]),
            turn_with_auth(
                ida,
                idb,
                0,
                Authorization::Unchecked,
                vec![Effect::SetPermissions {
                    cell: idb,
                    new_permissions: open_permissions(),
                }],
            ),
            vec![ida, idb],
        );
    }

    // NoteCreate on a Signature-locked cell with Unchecked auth: Rust consults the lattice; the
    // verified note arm does not gate it.
    {
        let a = make_cell(1, 100, locked_permissions());
        let ida = a.id();
        push(
            "edge-perm-lattice-notecreate",
            "NoteCreate",
            ledger_of(vec![a]),
            single_effect_turn(
                ida,
                ida,
                0,
                Effect::NoteCreate {
                    commitment: NoteCommitment([0xBB; 32]),
                    value: 0,
                    asset_type: 0,
                    encrypted_note: vec![],
                    value_commitment: None,
                    range_proof: None,
                },
            ),
            vec![ida],
        );
    }

    cases
}

// ---------------------------------------------------------------------------
// The gauntlet.
// ---------------------------------------------------------------------------

#[test]
fn rust_lean_parity_gauntlet() {
    if !dregg_lean_ffi::lean_available() {
        eprintln!(
            "SKIP: Lean archive not linked (lean_available()==false) — cannot run the verified kernel"
        );
        return;
    }

    let mut rows: Vec<String> = Vec::new();
    let mut state_diverges: Vec<String> = Vec::new();
    let mut new_under_enforcements: Vec<String> = Vec::new();
    let mut n_both_accept_agree = 0usize;
    let mut n_both_reject = 0usize;

    for case in build_corpus() {
        let (verdict, detail) = run_case(&case);
        rows.push(format!(
            "| {} | {} | {} |{}",
            case.name,
            case.cohort,
            verdict.label(),
            if detail.is_empty() {
                String::new()
            } else {
                format!(" {detail}")
            },
        ));
        match verdict {
            Verdict::BothAcceptStateAgree => n_both_accept_agree += 1,
            Verdict::BothReject => n_both_reject += 1,
            Verdict::BothAcceptStateDiverge => {
                state_diverges.push(format!(
                    "  [{}] cohort={} — {}",
                    case.name, case.cohort, detail
                ));
            }
            Verdict::RustAcceptsLeanRejects => {
                if !SAFE_DIRECTION_RESIDUALS.contains(&case.cohort) {
                    new_under_enforcements.push(format!(
                        "  [{}] cohort={} — Rust COMMITS what the verified kernel REFUSES (NEW)",
                        case.name, case.cohort
                    ));
                }
            }
            Verdict::RustRejectsLeanAccepts | Verdict::WireGap => {}
        }
    }

    println!("\n=== RUST↔LEAN PARITY GAUNTLET ===\n");
    println!("| case | cohort | verdict | detail |");
    println!("|------|--------|---------|--------|");
    for r in &rows {
        println!("{r}");
    }
    println!(
        "\nsummary: {n_both_accept_agree} BOTH-ACCEPT-state-AGREE, {n_both_reject} BOTH-REJECT, \
         {} new-under-enforcement, {} state-divergence",
        new_under_enforcements.len(),
        state_diverges.len(),
    );

    // TEETH (1): a silent state divergence — both commit but produce DIFFERENT states — is the
    // worst outcome for ship-Rust. There must be none.
    assert!(
        state_diverges.is_empty(),
        "STATE DIVERGENCE — Rust committed a DIFFERENT post-state than the verified kernel on a \
         co-accepted turn:\n{}",
        state_diverges.join("\n")
    );

    // TEETH (2): a NEW under-enforcement — Rust commits a turn the verified kernel refuses, on a
    // cohort NOT in the documented SAFE_DIRECTION_RESIDUALS allowlist.
    assert!(
        new_under_enforcements.is_empty(),
        "NEW UNDER-ENFORCEMENT outside the documented residual allowlist {SAFE_DIRECTION_RESIDUALS:?}:\n{}",
        new_under_enforcements.join("\n")
    );

    // NON-VACUITY FLOOR: the gauntlet must not pass by trivially gapping/rejecting. The cohort must
    // demonstrate real byte-identical post-state agreement and real shared rejection.
    assert!(
        n_both_accept_agree >= 12,
        "non-vacuity: expected ≥12 BOTH-ACCEPT-state-AGREE cohort cases, got {n_both_accept_agree}"
    );
    assert!(
        n_both_reject >= 5,
        "non-vacuity: expected ≥5 BOTH-REJECT adversarial cases, got {n_both_reject}"
    );
}
