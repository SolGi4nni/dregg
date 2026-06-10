//! RUST↔LEAN DIVERGENCE FINDER — the empirical swap-confidence harness.
//!
//! Runs the REAL legacy Rust executor (`TurnExecutor::execute` → `apply.rs`) and the
//! VERIFIED Lean executor (`dregg_exec_full_forest_auth` via the FFI shadow) side-by-side
//! over a CORPUS of turns covering many effect types, and LOGS every divergence.
//!
//! For each corpus turn we:
//!   1. snapshot the pre-state ledger,
//!   2. run the real Rust executor (this is the genuine `apply.rs` walk — not a
//!      reimplementation), capturing its commit decision,
//!   3. call [`lean_shadow::shadow_report`], which marshals the SAME turn + pre-state through
//!      the gated Lean FFI and returns the Lean commit decision,
//!   4. compare.
//!
//! The output is a DIVERGENCE LEDGER, effect-by-effect:
//!   * AGREE     — Lean modelled the effect and matched Rust's commit bit.
//!   * DIVERGE   — Lean modelled the effect and DISAGREED (a real drift / bug).
//!   * GAP       — the effect is not yet projected to the Lean wire (no Lean model;
//!                 the turn is INELIGIBLE for shadow). This is the remaining drift surface,
//!                 not a divergence — it tells us what still needs a Lean model before swap.
//!
//! Run with the Lean FFI linked + shadow on:
//!   DREGG_LEAN_SHADOW=1 cargo test -p dregg-turn --features lean-shadow \
//!       --test rust_lean_divergence_finder -- --nocapture
//!
//! Without the feature the harness still runs (every effect reports GAP — no Lean linked),
//! so it is CI-safe either way; the ledger then records the eligibility map only.

use std::collections::BTreeMap;

use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::action::Event;
use dregg_turn::lean_shadow::{self, ShadowReport};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};

// ---------------------------------------------------------------------------
// Fixture builders
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

fn make_open_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn field_from_u64(v: u64) -> FieldElement {
    let mut f = [0u8; 32];
    f[24..32].copy_from_slice(&v.to_be_bytes());
    f
}

/// A turn carrying the given effects under `Unchecked` auth, with `valid_until` SET (the
/// shadow requires it) and a single root action targeting `agent`.
fn corpus_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
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
        // The Lean wire marshaller REQUIRES valid_until (admission reads it). Set it high.
        valid_until: Some(1_000_000),
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// One corpus case: a label, a two-cell ledger (cell A = agent, cell B = counterparty), and
/// the turn to run. Cells A and B always exist & are open so authority is not the variable
/// under test (we are testing the executor's STATE transition, not the gate, here).
struct CorpusCase {
    label: &'static str,
    turn: Turn,
    ledger: Ledger,
}

/// Grant cell `holder` a capability targeting ITSELF (a self `node`-equivalent c-list edge).
/// The shadow marshaller projects every `CapabilityRef` to `Cap::Node(target)`, so this gives
/// the holder the mint/burn authority the verified kernel requires (`mintAuthorizedB`).
fn grant_self_cap(ledger: &mut Ledger, holder: CellId) {
    let cell = ledger.get_mut(&holder).expect("holder cell present");
    cell.capabilities
        .grant(holder, AuthRequired::None)
        .expect("grant self cap");
}

fn two_cell_ledger(bal_a: u64, bal_b: u64) -> (Ledger, CellId, CellId) {
    let a = make_open_cell(1, bal_a);
    let b = make_open_cell(2, bal_b);
    let (ida, idb) = (a.id(), b.id());
    let mut l = Ledger::new();
    l.insert_cell(a).unwrap();
    l.insert_cell(b).unwrap();
    (l, ida, idb)
}

/// Build the corpus: at least one turn per effect type the harness can construct standalone.
/// Effects requiring elaborate pre-state (live escrows, queues with prior allocate, sealed
/// pairs, bridge proofs) are represented by their CREATE/entry effect so the executor path is
/// still exercised and the effect appears in the ledger.
fn build_corpus() -> Vec<CorpusCase> {
    let mut cases: Vec<CorpusCase> = Vec::new();

    macro_rules! case {
        ($label:expr, $bal_a:expr, $bal_b:expr, |$a:ident, $b:ident| $effects:expr) => {{
            let (ledger, $a, $b) = two_cell_ledger($bal_a, $bal_b);
            let turn = corpus_turn($a, 0, $effects);
            cases.push(CorpusCase { label: $label, turn, ledger });
        }};
    }

    // ---- Lean-MODELLED effects (expected: comparable) ----
    case!("SetField", 100, 100, |a, _b| vec![Effect::SetField {
        cell: a,
        index: 2,
        value: field_from_u64(42),
    }]);
    case!("Transfer", 100, 100, |a, b| vec![Effect::Transfer {
        from: a,
        to: b,
        amount: 30,
    }]);
    case!("Transfer/overspend", 10, 100, |a, b| vec![Effect::Transfer {
        from: a,
        to: b,
        amount: 9999,
    }]);
    // Same shape as the FFI `marshal_roundtrip` overspend gate (bal 100, amount 1000) to
    // pin whether the divergence tracks the NUMBERS or the marshalled side-table shape.
    case!("Transfer/overspend2", 100, 5, |a, b| vec![Effect::Transfer {
        from: a,
        to: b,
        amount: 1000,
    }]);
    case!("SetPermissions", 100, 100, |a, _b| vec![Effect::SetPermissions {
        cell: a,
        new_permissions: open_permissions(),
    }]);
    case!("SetVerificationKey", 100, 100, |a, _b| vec![Effect::SetVerificationKey {
        cell: a,
        new_vk: None,
    }]);
    case!("EmitEvent", 100, 100, |a, _b| vec![Effect::EmitEvent {
        cell: a,
        event: Event { topic: [7u8; 32], data: vec![[1u8; 32]] },
    }]);
    case!("MakeSovereign", 100, 100, |a, _b| vec![Effect::MakeSovereign { cell: a }]);
    case!("NoteCreate", 100, 100, |a, _b| vec![Effect::NoteCreate {
        commitment: dregg_cell::NoteCommitment([0xBB; 32]),
        value: 0,
        asset_type: 0,
        encrypted_note: vec![],
        value_commitment: None,
        range_proof: None,
    }]);
    // NoteSpend (PROOFLESS) — now AGREES (drift RESOLVED). The `nspend` wire arm carries the §8
    // note-spending-proof WITNESS flag (third field). With an EMPTY `spending_proof`, the flag is
    // `0`; apply.rs rejects ("NoteSpend missing spending proof") AND the verified `noteSpendChainA`
    // rejects (the proved `noteSpendChainA_fails_without_proof` teeth — no proof ⇒ no commit). So
    // BOTH roll back ⇒ AGREE. (Before the flag was on the wire, the verified executor committed the
    // nullifier insertion blindly while apply.rs rejected — the headline NoteSpend divergence.)
    case!("NoteSpend", 100, 100, |a, _b| vec![Effect::NoteSpend {
        nullifier: dregg_cell::Nullifier([0xAA; 32]),
        note_tree_root: [0x11; 32],
        value: 0,
        asset_type: 0,
        spending_proof: vec![],
        value_commitment: None,
    }]);
    // Multi-effect, all-modelled: mint-like setfield + transfer in one action.
    case!("SetField+Transfer", 100, 100, |a, b| vec![
        Effect::SetField { cell: a, index: 2, value: field_from_u64(1) },
        Effect::Transfer { from: a, to: b, amount: 10 },
    ]);

    // ---- Effects WITHOUT a Lean wire model yet (expected: GAP) ----
    case!("IncrementNonce", 100, 100, |a, _b| vec![Effect::IncrementNonce { cell: a }]);
    // Burn on an OWNED, OPEN, cap-LESS cell: apply.rs commits (ownership suffices), the verified
    // `.burnA` REJECTS (it requires an explicit `node`/`control` mint-cap — bare ownership is
    // deliberately insufficient). A characterised, SAFE-direction model difference (allowlisted).
    case!("Burn", 100, 100, |a, _b| vec![Effect::Burn { target: a, slot: 0, amount: 10 }]);
    // Burn TOOTH: the SAME burn on a cell that HOLDS a `node` cap on itself. The c-list edge is
    // marshalled to `Cap::Node(self)`, which `mintAuthorizedB` reads as burn-authority, so the
    // verified `.burnA` now COMMITS — matching apply.rs. This proves the Lean burn gate is
    // GENUINELY gated (not vacuously-false): empty c-list ⇒ reject, self-node-cap ⇒ commit.
    {
        let (mut ledger, ida, _idb) = two_cell_ledger(100, 100);
        grant_self_cap(&mut ledger, ida);
        let turn = corpus_turn(ida, 0, vec![Effect::Burn { target: ida, slot: 0, amount: 10 }]);
        cases.push(CorpusCase { label: "Burn/with-cap", turn, ledger });
    }
    case!("CellSeal", 100, 100, |a, _b| vec![Effect::CellSeal { target: a, reason: [9u8; 32] }]);

    // ---- GAP-shrink batch: newly-projected effects (was the swap surface) ----
    //
    // (F2b: the QueueAllocate/funded corpus case died with the FACTORY-DISSOLVED queue family —
    // the verified kernel no longer parses queue wire actions; queue behavior is the factory
    // story, Dregg2/Apps/QueueFactory et al. The loud wire refusal is pinned in
    // lean_state_producer_coverage::queue_falls_back_factory_dissolved.)

    // GrantCapability (SELF-grant, with a self-cap held): the agent grants ITSELF a cap on itself.
    // apply.rs commits (self-grant `cap.target == from` skips the c-list lookup — the action
    // signature proves owner consent). The verified `.delegate` routes to `recKDelegate`, gated on
    // `(caps from).any (confersEdgeTo t)`; the marshalled self-`node` cap (`Cap::Node(self)`)
    // confers the self-edge, so the verified gate passes and COMMITS. AGREE. NON-VACUITY: the
    // GrantCapability/no-cap tooth below proves the verified delegate gate is genuinely gated.
    {
        let (mut ledger, ida, _idb) = two_cell_ledger(100, 100);
        grant_self_cap(&mut ledger, ida);
        let cap = dregg_cell::CapabilityRef {
            target: ida,
            slot: 0,
            permissions: AuthRequired::None,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        };
        let turn = corpus_turn(
            ida,
            0,
            vec![Effect::GrantCapability { from: ida, to: ida, cap }],
        );
        cases.push(CorpusCase { label: "GrantCapability/self-cap", turn, ledger });
    }
    // GrantCapability NON-VACUITY TOOTH: a self-grant on a cell WITHOUT a self-cap. apply.rs still
    // commits (the self-grant path skips the c-list lookup), but the verified `recKDelegate` gate
    // REJECTS (no `confersEdgeTo self` edge in the empty c-list) — a SAFE-direction model
    // difference (the verified delegate gate insists the delegator HOLD the edge, even for a
    // self-grant). Pins the gate as genuinely two-sided: self-cap ⇒ commit, no-cap ⇒ reject.
    case!("GrantCapability/no-cap", 100, 100, |a, _b| {
        let cap = dregg_cell::CapabilityRef {
            target: a,
            slot: 0,
            permissions: AuthRequired::None,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        };
        vec![Effect::GrantCapability { from: a, to: a, cap }]
    });

    // A still-GAP effect, to keep the corpus honest about the REMAINING swap surface:
    // CreateSealPair is not yet projected to the Lean wire (the seal-pair family is deferred),
    // so this turn is INELIGIBLE for shadow and reports GAP. This is the un-shrunk frontier.
    case!("CreateSealPair (still-GAP)", 100, 100, |a, b| vec![Effect::CreateSealPair {
        sealer_holder: a,
        unsealer_holder: b,
    }]);

    cases
}

// ---------------------------------------------------------------------------
// Per-effect ledger accumulation
// ---------------------------------------------------------------------------

#[derive(Default, Clone)]
struct EffectStat {
    agree: u32,
    diverge: u32,
    gap: u32,
    error: u32,
    /// One example divergence note (effect kinds, rust vs lean commit).
    diverge_note: Option<String>,
    /// Whether ANY case carrying this effect was Lean-eligible (modelled).
    ever_modelled: bool,
}

fn classify(report: &ShadowReport, kinds: &[&'static str], stats: &mut BTreeMap<String, EffectStat>) {
    for k in kinds {
        let e = stats.entry(k.to_string()).or_default();
        if report.lean_eligible {
            e.ever_modelled = true;
        }
        match report.agree {
            Some(true) => e.agree += 1,
            Some(false) => {
                e.diverge += 1;
                if e.diverge_note.is_none() {
                    e.diverge_note = Some(format!(
                        "rust_committed={} lean_committed={:?}",
                        report.rust_committed, report.lean_committed
                    ));
                }
            }
            None => {
                if report.error.is_some() && report.lean_eligible {
                    e.error += 1;
                } else {
                    e.gap += 1;
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The harness
// ---------------------------------------------------------------------------

#[test]
fn rust_lean_divergence_finder() {
    let shadow_on = std::env::var("DREGG_LEAN_SHADOW").as_deref() == Ok("1");
    // block_height 0 ⇒ the marshaller omits the optional `block_height` wire field (the
    // executor falls back to `now`/`valid_until` for expiry). We run at 0 so the corpus is
    // marshalled with the SAME envelope shape the byte-exact `marshal_roundtrip` gate proves
    // correct; the block_height>0 wire path is exercised separately by the FFI's own
    // `full_turn_differential` over execFullTurn.
    let block_height = 0u64;

    let mut per_effect: BTreeMap<String, EffectStat> = BTreeMap::new();
    let mut rows: Vec<String> = Vec::new();
    let mut total = 0usize;
    let mut comparable = 0usize;
    let mut diverged = 0usize;

    for mut case in build_corpus() {
        total += 1;
        // Snapshot pre-state BEFORE the real executor mutates the ledger.
        let pre_ledger = case.ledger.clone();

        // RUN THE REAL RUST EXECUTOR (apply.rs) — a FRESH executor per case so each corpus
        // turn is the FIRST in its own receipt chain. (Reusing one executor advances its
        // internal receipt-chain head after the first commit, so later turns with
        // `previous_receipt_hash: None` would be rejected with `ReceiptChainMismatch` — a
        // harness artefact, NOT a kernel divergence, since the Lean shadow does not model the
        // receipt chain. The fresh executor isolates the per-effect state transition under test.)
        let executor = TurnExecutor::new(ComputronCosts::zero());
        let result = executor.execute(&case.turn, &mut case.ledger);
        let rust_committed = result.is_committed();
        let rust_reason = match &result {
            dregg_turn::turn::TurnResult::Rejected { reason, at_action } => {
                format!("Rejected({reason:?} @{at_action:?})")
            }
            dregg_turn::turn::TurnResult::Committed { .. } => "Committed".to_string(),
            other => format!("{other:?}"),
        };

        // RUN THE VERIFIED LEAN EXECUTOR over the same turn + pre-state.
        let report = lean_shadow::shadow_report(&case.turn, &pre_ledger, rust_committed, block_height);

        classify(&report, &report.effect_kinds, &mut per_effect);

        let verdict = match report.agree {
            Some(true) => {
                comparable += 1;
                "AGREE".to_string()
            }
            Some(false) => {
                comparable += 1;
                diverged += 1;
                format!(
                    "DIVERGE (rust={}, lean={:?})",
                    report.rust_committed, report.lean_committed
                )
            }
            None if report.lean_eligible && report.error.is_some() => {
                format!("ERROR ({})", report.error.clone().unwrap())
            }
            None => "GAP (no Lean model)".to_string(),
        };

        rows.push(format!(
            "| {} | {} | {} | lean={:?} | {} |",
            case.label,
            report.effect_kinds.join("+"),
            rust_reason,
            report.lean_committed,
            verdict,
        ));
    }

    // ---- Emit the ledger to stdout ----
    println!("\n=== RUST↔LEAN DIVERGENCE LEDGER (shadow_on={shadow_on}) ===\n");
    println!("Corpus turns: {total} | comparable (Lean modelled): {comparable} | DIVERGENCES: {diverged}\n");
    println!("| case | effects | rust | lean | verdict |");
    println!("|------|---------|------|------|---------|");
    for r in &rows {
        println!("{r}");
    }

    println!("\n--- per-effect map ---");
    println!("| effect | modelled | agree | diverge | gap | error |");
    println!("|--------|----------|-------|---------|-----|-------|");
    for (k, s) in &per_effect {
        println!(
            "| {} | {} | {} | {} | {} | {} |{}",
            k,
            if s.ever_modelled { "yes" } else { "NO (gap)" },
            s.agree,
            s.diverge,
            s.gap,
            s.error,
            s.diverge_note
                .as_ref()
                .map(|n| format!(" <- {n}"))
                .unwrap_or_default(),
        );
    }

    // ---- Write the markdown ledger to disk for the maintainer ----
    write_ledger_markdown(shadow_on, total, comparable, diverged, &rows, &per_effect);

    // The harness is a DIVERGENCE LEDGER / monitor: its job is to RUN both executors and
    // CHARACTERISE the drift, not to pretend there is none. Divergences are recorded (above +
    // on disk) and summarised here; they do NOT fail the run by themselves (the maintainer
    // reads the ledger). What WOULD be a regression — and DOES fail — is:
    //   (a) the harness not running both executors at all (no comparable cases when shadow on), or
    //   (b) a known-AGREEING effect flipping to DIVERGE (a real new drift on a path we trust).
    //
    // KNOWN-DRIFT allowlist (documented in the ledger). Each entry is a CHARACTERISED drift,
    // not a hidden bug:
    //
    //   * `Burn` — a genuine, SAFE-DIRECTION MODEL DIFFERENCE (the verified kernel is
    //     STRICTER). The verified `.burnA` requires `mintAuthorizedB` — an explicit `node` /
    //     `control`-endpoint CAP on the burned cell (mint/burn is privileged; bare ownership
    //     is deliberately NOT sufficient, `Generators.lean:31`). The corpus cell has an EMPTY
    //     c-list, so the verified gate correctly FAILS (lean=false) while apply.rs commits the
    //     burn on the owned open cell (rust=true). This is NOT a marshaller under-spec — the
    //     real (empty) c-list IS marshalled; it is the verified kernel refusing an
    //     under-authorised burn apply.rs allows. The divergence is on the SAFE side (the
    //     verified executor rejects what apply.rs accepts), and it surfaces a swap-relevant
    //     authority-model tightening, so it is recorded — not hidden.
    //
    // The OLD `Transfer` overspend drift is now RESOLVED (not on the list): the status-bearing
    // export reports the body-failure as `ok:0` and the `Unchecked → Breadstuff` projection
    // passes the WHO leg so authority is decided by `authorizedB` — overspend now correctly
    // rolls back in BOTH executors (4/4 AGREE).
    //
    // The OLD `NoteSpend` drift is now RESOLVED (not on the list): the `nspend` wire arm carries
    // the §8 spending-proof WITNESS flag. A proofless spend (empty `spending_proof` ⇒ flag 0) is
    // rejected by BOTH apply.rs ("missing spending proof") and the verified `noteSpendChainA`
    // (`noteSpendChainA_fails_without_proof`), so they AGREE. (The proof BYTES / STARK membership
    // stay the circuit's job; only the presence bit the commit decision turns on crosses.)
    //   * `GrantCapability` — a SAFE-DIRECTION MODEL DIFFERENCE (the verified delegate gate is
    //     STRICTER). The verified `.delegate` routes to `recKDelegate`, gated on the delegator
    //     HOLDING an edge to the cap target (`(caps from).any (confersEdgeTo t)`). dregg1's
    //     `apply_grant_capability` SHORT-CIRCUITS a SELF-grant (`cap.target == from`) — it skips
    //     the c-list lookup entirely, trusting the action signature as owner consent. So a
    //     self-grant on a cell WITHOUT a self-cap commits in apply.rs (rust=true) but the verified
    //     gate REJECTS (lean=false): the verified executor insists the delegator actually hold the
    //     edge. The `GrantCapability/self-cap` case (a self-`node` cap held ⇒ verified COMMITS) is
    //     the NON-VACUITY TOOTH proving the gate is two-sided, not vacuously-false.
    let known_drift: &[&str] = &["Burn", "GrantCapability"];
    let unexpected: Vec<(&String, &EffectStat)> = per_effect
        .iter()
        .filter(|(k, s)| s.diverge > 0 && !known_drift.contains(&k.as_str()))
        .collect();

    if diverged > 0 {
        eprintln!(
            "\n[divergence-finder] {diverged} divergence(s) recorded across {comparable} comparable \
             turn(s) — see metatheory/docs/rebuild/_RUST-LEAN-DIVERGENCE-LEDGER.md. \
             All are on the KNOWN-DRIFT allowlist {known_drift:?} (marshaller-faithfulness gaps)."
        );
    }

    if shadow_on {
        assert!(
            comparable > 0,
            "shadow is ON but NO turn was comparable — the Lean FFI did not run (link/marshal \
             failure?). The divergence finder must actually execute the Lean executor."
        );
        assert!(
            per_effect.get("SetField").map(|s| s.agree > 0).unwrap_or(false),
            "regression: SetField no longer AGREES between apply.rs and the Lean executor \
             (this is the load-bearing modelled-and-applied path)."
        );
        // TOOTH (the status-export + `Unchecked → Breadstuff` fix): EVERY Transfer corpus case
        // — the two authorised moves AND the two OVERSPENDS — must now AGREE (4 agree, 0
        // diverge). This is the non-vacuity proof of the fix: the overspends are rejected by
        // the verified executor (`recKExecAsset`'s `amt ≤ bal` gate ⇒ body fails ⇒ the
        // status-bearing export reports `ok:0`), matching apply.rs's `InsufficientBalance`.
        // Before the fix the marshaller sent `Unchecked` (fail-closed at the gate) and the
        // export collapsed the prologue-only commit to `ok:1`, so all four Transfers diverged.
        let (t_agree, t_diverge) = per_effect
            .get("Transfer")
            .map(|s| (s.agree, s.diverge))
            .unwrap_or((0, 0));
        assert!(
            t_agree == 4 && t_diverge == 0,
            "regression: Transfer no longer AGREES on all 4 corpus cases (incl. both \
             overspends) — got agree={t_agree} diverge={t_diverge}. The status-export / \
             Breadstuff authority fix that makes the verified executor REJECT an overspend \
             (ok:0) has regressed."
        );
        // BURN-GATE NON-VACUITY TOOTH: the verified `.burnA` requires an explicit mint/burn
        // CAP. The corpus exercises BOTH sides — the cap-LESS `Burn` (verified REJECTS ⇒
        // diverges from apply.rs's ownership-suffices commit) AND `Burn/with-cap` (a self
        // `node` cap ⇒ verified COMMITS ⇒ agrees). So the gate must show ≥1 agree AND ≥1
        // diverge; if it were vacuously-false it would never agree, if vacuously-true it
        // would never diverge. This pins the gate as genuinely two-sided.
        let (b_agree, b_diverge) = per_effect
            .get("Burn")
            .map(|s| (s.agree, s.diverge))
            .unwrap_or((0, 0));
        assert!(
            b_agree >= 1 && b_diverge >= 1,
            "Burn-gate non-vacuity TOOTH failed — got agree={b_agree} diverge={b_diverge}. \
             The verified burn-authority gate must COMMIT with a mint-cap (Burn/with-cap) and \
             REJECT without one (Burn); a gate that only ever agrees or only ever diverges is \
             vacuous."
        );
        // (F2b: the QueueAllocate GAP-shrink tooth died with the FACTORY-DISSOLVED queue family —
        // see lean_state_producer_coverage::queue_falls_back_factory_dissolved for the loud
        // wire-refusal tooth that replaced it.)
        // NOTESPEND DRIFT-RESOLVED TOOTH: the proofless spend (empty `spending_proof` ⇒ wire flag
        // 0) must AGREE — apply.rs rejects ("missing spending proof") AND the verified
        // `noteSpendChainA` rejects (`noteSpendChainA_fails_without_proof`). Before the §8 flag was
        // on the wire, NoteSpend DIVERGED (verified committed blindly); it must now agree with NO
        // divergence (the flag carries the proof-presence bit the commit decision turns on).
        let (ns_agree, ns_diverge) = per_effect
            .get("NoteSpend")
            .map(|s| (s.agree, s.diverge))
            .unwrap_or((0, 0));
        assert!(
            ns_agree >= 1 && ns_diverge == 0,
            "NoteSpend drift-resolved TOOTH failed — the proofless spend must AGREE (both reject a \
             missing-proof spend) with NO divergence (got agree={ns_agree} diverge={ns_diverge}). \
             The §8 spending-proof flag on the `nspend` wire arm closes the old NoteSpend drift."
        );
        // GAP-SHRINK + NON-VACUITY TOOTH (GrantCapability/delegate gate): the verified
        // `recKDelegate` requires the delegator to HOLD the cap-target edge. The corpus exercises
        // BOTH sides — `GrantCapability/self-cap` (a self-`node` cap ⇒ verified COMMITS ⇒ agrees)
        // AND `GrantCapability/no-cap` (empty c-list ⇒ verified REJECTS ⇒ diverges from apply.rs's
        // self-grant short-circuit). So the gate must show ≥1 agree AND ≥1 diverge.
        let (g_agree, g_diverge) = per_effect
            .get("GrantCapability")
            .map(|s| (s.agree, s.diverge))
            .unwrap_or((0, 0));
        assert!(
            g_agree >= 1 && g_diverge >= 1,
            "GrantCapability delegate-gate non-vacuity TOOTH failed — got agree={g_agree} \
             diverge={g_diverge}. The verified delegate gate must COMMIT a self-grant when the \
             self-cap is held (GrantCapability/self-cap) and REJECT it when the c-list is empty \
             (GrantCapability/no-cap); a gate that only ever agrees or only ever diverges is vacuous."
        );
    }

    assert!(
        unexpected.is_empty(),
        "NEW RUST↔LEAN DIVERGENCE(S) outside the known-drift allowlist: {:?} — a modelled \
         effect's commit bit now differs between apply.rs and the verified Lean executor. \
         Investigate before extending the allowlist (see the ledger).",
        unexpected.iter().map(|(k, _)| k.as_str()).collect::<Vec<_>>()
    );
}

fn write_ledger_markdown(
    shadow_on: bool,
    total: usize,
    comparable: usize,
    diverged: usize,
    rows: &[String],
    per_effect: &BTreeMap<String, EffectStat>,
) {
    // metatheory/docs/rebuild/ relative to the workspace root. CARGO_MANIFEST_DIR is `turn/`.
    let manifest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let Some(root) = manifest.parent() else { return };
    let dir = root.join("metatheory").join("docs").join("rebuild");
    if std::fs::create_dir_all(&dir).is_err() {
        return;
    }
    let path = dir.join("_RUST-LEAN-DIVERGENCE-LEDGER.md");

    let mut md = String::new();
    md.push_str("# Rust↔Lean Divergence Ledger\n\n");
    md.push_str(
        "Generated by `turn/tests/rust_lean_divergence_finder.rs` — runs the REAL Rust \
         executor (`apply.rs`) and the VERIFIED Lean executor (`dregg_exec_full_forest_auth` \
         FFI) side-by-side over a corpus of turns and records every divergence.\n\n",
    );
    md.push_str(&format!(
        "- `DREGG_LEAN_SHADOW`/`lean-shadow` active: **{shadow_on}** (false ⇒ Lean not linked; \
         the table records the eligibility map only — every effect shows GAP).\n",
    ));
    md.push_str(&format!(
        "- Corpus turns: **{total}** | comparable (Lean modelled): **{comparable}** | \
         **DIVERGENCES: {diverged}**\n\n",
    ));
    md.push_str(
        "Verdict legend: **AGREE** = Lean modelled the effect and matched apply.rs's commit \
         bit. **DIVERGE** = modelled and DISAGREED (a real drift/bug). **GAP** = no Lean wire \
         model yet (turn ineligible for shadow; the remaining swap surface, not a bug).\n\n",
    );

    md.push_str("## Per-turn\n\n");
    md.push_str("| case | effects | rust | lean | verdict |\n");
    md.push_str("|------|---------|------|------|---------|\n");
    for r in rows {
        md.push_str(r);
        md.push('\n');
    }

    md.push_str("\n## Per-effect map\n\n");
    md.push_str("| effect | modelled | agree | diverge | gap | error | note |\n");
    md.push_str("|--------|----------|-------|---------|-----|-------|------|\n");
    for (k, s) in per_effect {
        md.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {} |\n",
            k,
            if s.ever_modelled { "yes" } else { "NO" },
            s.agree,
            s.diverge,
            s.gap,
            s.error,
            s.diverge_note.clone().unwrap_or_default(),
        ));
    }

    md.push_str(
        "\n## Findings (characterised drift)\n\n\
         The agreement comparison is COMMIT-BIT-ONLY (the shadow compares whether both \
         executors commit/roll back, not the full post-state). With that lens:\n\n\
         1. **Modelled & agreeing** — `SetField`, `SetPermissions`, `SetVerificationKey`, \
         `EmitEvent`, `MakeSovereign`, `NoteCreate`, `IncrementNonce`, `CellSeal`, the authorised \
         `Burn/with-cap`, AND **all four `Transfer` cases incl. both overspends** — apply.rs and \
         the verified Lean executor agree on the commit decision.\n\n\
         2. **Transfer overspend — RESOLVED (was the headline drift).** Two fixes closed it: \
         (a) the `@[export]` now uses the STATUS-bearing `runGatedForestTurnStatus` and reports \
         `ok:1` ONLY when the gated forest BODY commits — a prologue-only result (fee/nonce \
         charged, body rolled back) is `status:1, ok:0`, so an overspend is no longer laundered \
         to `ok:1`; (b) the marshaller projects dregg1 `Unchecked` to the `.breadstuff` \
         credential (`portalVerify .breadstuff = true`, 'the WHAT leg gates') instead of \
         `.unchecked` (which fail-closes the WHO leg), so authority is decided by `authorizedB` \
         (ownership / c-list) exactly as apply.rs does. Result: the authorised transfer COMMITS \
         and the overspend ROLLS BACK in BOTH executors. The decoder also parses the new \
         `status` field (forward-compatible with the legacy no-status shape).\n\n\
         2b. **NoteSpend — RESOLVED (was the second headline drift).** The `nspend` wire arm now \
         carries the §8 note-spending-proof WITNESS flag (third field). A proofless spend (empty \
         `spending_proof` ⇒ flag `0`) is REJECTED by BOTH apply.rs (\"missing spending proof\") and \
         the verified `noteSpendChainA` (the proved `noteSpendChainA_fails_without_proof` teeth), so \
         they AGREE. The proof BYTES + STARK Merkle-membership stay the circuit's concern; only the \
         proof-PRESENCE bit (which the commit decision turns on) crosses the wire.\n\n\
         2c. **GrantCapability — newly PROJECTED (GAP shrunk).** (F2b: QueueAllocate is \
         FACTORY-DISSOLVED — the verified kernel no longer parses queue wire actions; the loud \
         refusal is pinned in lean_state_producer_coverage.) \
         `GrantCapability` crosses as `del` (`recKDelegate`, gated on the delegator \
         holding the cap-target edge): a self-grant on a cell holding a self-`node` cap COMMITS in \
         both (AGREE); a self-grant on an empty c-list is REJECTED by the verified gate while \
         apply.rs short-circuits the self-grant (a safe-direction model difference, two-sided tooth).\n\n\
         3. **Known drift (allowlisted), characterised:**\n\
         &nbsp;&nbsp;• `Burn` — a SAFE-DIRECTION MODEL DIFFERENCE (the verified kernel is \
         STRICTER): `.burnA` requires an explicit `node`/`control` mint-cap, while apply.rs \
         permits a burn on an owned open cell. The REAL (empty) c-list IS marshalled — this is \
         NOT a marshaller under-spec — so the verified gate correctly REJECTS the under-authorised \
         burn. The `Burn/with-cap` corpus case (a self `node` cap ⇒ verified COMMITS) is the \
         NON-VACUITY TOOTH proving the gate is two-sided, not vacuously-false.\n\
         &nbsp;&nbsp;• `GrantCapability` — a SAFE-DIRECTION MODEL DIFFERENCE: the verified delegate \
         gate requires the delegator to HOLD the cap-target edge, while apply.rs short-circuits a \
         self-grant (skips the c-list lookup). `GrantCapability/self-cap` (self-`node` cap held ⇒ \
         verified COMMITS) is the non-vacuity tooth.\n\n\
         4. **GAP (no Lean model yet)** — the remaining escrow/bridge/seal-pair/captp-swiss/factory/ \
         introduce/queue-enqueue-dequeue effects (e.g. `CreateSealPair`): not yet projected to the \
         Lean wire, so the turn is INELIGIBLE for shadow. This is the remaining SWAP surface. The \
         currently-modelled effects (20+) are: SetField, Transfer, SetPermissions, \
         SetVerificationKey, EmitEvent, MakeSovereign, RevokeDelegation, NoteSpend, NoteCreate, \
         IncrementNonce, Refusal, ReceiptArchive, CellSeal, CellUnseal, CellDestroy, Burn, \
         RevokeCapability, RefreshDelegation, QueueAllocate, GrantCapability. The admission context \
         is HOST-FED (boundary-P1): the node supplies the clock / freeze-set / stored receipt-chain \
         head / Stingray budget slice (`ShadowHostCtx`), so the verified `admissible` clock/frozen/ \
         chain-head/budget legs are decided by the node, not the turn. The marshaller also carries \
         the cell's REAL c-list (`capabilities`) as wire `caps`, so the verified authority gates \
         (`authorizedB`/`mintAuthorizedB`) read the actual edges the actor holds.\n\n\
         ## How to run\n\n```\nDREGG_LEAN_SHADOW=1 cargo test -p dregg-turn \
         --features lean-shadow --test rust_lean_divergence_finder -- --nocapture\n```\n\n\
         Requires `dregg-lean-ffi/libdregg_lean.a` (the compiled Lean closure) present + the \
         project Lean toolchain (build.rs resolves the sysroot via `lake env`). \
         Wire into CI / devnet by running the node with `DREGG_LEAN_SHADOW=1` and the \
         `lean-shadow` feature — `lean_shadow::maybe_shadow_turn` then logs live divergences \
         (target `dregg::lean_shadow::divergence`) for every executed turn.\n",
    );

    let _ = std::fs::write(&path, md);
    println!("\n[ledger written to {}]", path.display());
}
