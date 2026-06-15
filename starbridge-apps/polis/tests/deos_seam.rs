//! THE SEAM CLOSED, per family — the deos-native `fire_*` paths drive each polis
//! governance family's INSTALLED program through the embedded executor, so the family's
//! OWN verified lifecycle caveat BITES in the fire path itself (a REAL executor refusal),
//! and the happy path commits a REAL verified turn.
//!
//! `docs/deos/DEOS.md` + `Dregg2/Deos/{GatedAffordance,WorkflowBridge}.lean`: a deos fire is
//! the TWO-TEMPO bridge — (1) the deos cap∧state PRECONDITION gate decides the button IN-BAND
//! (anti-ghost: nothing submitted on a miss), and (2) on a pass the FULL state-parameterized
//! turn is submitted and the executor RE-ENFORCES the family's installed `CellProgram` on the
//! produced transition. This file proves that seam CLOSED for all five families:
//!
//!   * council    — `Monotonic(approval_slot)`: an un-approve (1 -> 0) is REFUSED;
//!   * amendment  — cooling `TemporalGate` on ENACT: a ratify before the cooling height is REFUSED;
//!   * constitution — supersession provenance: an ANON supersede (no successor) is REFUSED;
//!   * mandate    — the pinned `SLICE` literal: a slice-inflation (overspend) is REFUSED;
//!   * identity   — the `KeyRotationGate` cooling window: a rotation inside cooling is REFUSED.
//!
//! Every fire is a real verified turn through the embedded executor; both gates are genuine
//! (`is_attenuation` + `CellProgram::evaluate`). No parallel model.
//!
//! The deos surface (`src/deos.rs`) is compiled INTO THIS TEST BINARY via `#[path]` — it is
//! NOT a library module, because `dregg-sdk` depends on `starbridge-polis` and
//! `dregg-app-framework` depends on `dregg-sdk`, so a normal `polis -> app-framework` edge
//! would close an illegal package cycle. Cargo permits the cycle ONLY across the
//! dev-dependency edge this test binary uses. See `Cargo.toml`'s `[features].deos` comment.

#![cfg(feature = "deos")]
#![allow(dead_code)] // the included `src/deos.rs` has pub items each test binary uses a subset of

#[path = "../src/deos.rs"]
mod deos;

use deos::*;
use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, EmbeddedExecutor, FireExecuteError,
};
use starbridge_polis::{
    STATE_SLOT,
    constitution::ConstitutionParams,
    council::{AmendmentTerms, CouncilCharter},
    identity::{IdentityCharter, key_set_commitment},
    mandate::{WorkerMandate, tool_scope_commitment},
};

use dregg_app_framework::CellId;

const OWNER: AuthRequired = AuthRequired::None; // the AUTHORITY tier (root)
const PARTICIPANT: AuthRequired = AuthRequired::Either; // the PARTICIPANT tier

fn agent(seed: u8) -> (AppCipherclerk, EmbeddedExecutor) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    (cclerk, executor)
}

fn council_2of3() -> CouncilCharter {
    CouncilCharter::new(
        vec![
            CellId::from_bytes([0x11; 32]),
            CellId::from_bytes([0x22; 32]),
            CellId::from_bytes([0x33; 32]),
        ],
        2,
    )
}

// =============================================================================
// COUNCIL — happy approve commits; the `Monotonic(approval_slot)` un-approve tooth bites.
// =============================================================================

#[test]
fn council_approve_commits_then_unapprove_is_a_real_executor_refusal() {
    let (cclerk, executor) = agent(0xC0);
    let charter = council_2of3();
    let app = council_app(&cclerk, &executor);
    seed_council(
        &executor,
        &charter,
        *blake3::hash(b"a-staged-proposal").as_bytes(),
    );

    // HAPPY PATH: a PARTICIPANT casts member 0's approval — the council is PROPOSED (cap∧state
    // pass), and the executor re-enforces the installed program ({0,1} + Monotonic + BoundedBy
    // on the staged proposal all hold for 0 -> 1). A real verified turn.
    let receipt = fire_council_approve(&app, &PARTICIPANT, 0, &cclerk, &executor)
        .expect("a participant approves on a staged proposal (caps ∧ state ∧ program all pass)");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real verified approve turn");
    // The approval slot advanced 0 -> 1 (the delivery committed).
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[(starbridge_polis::council::FIRST_APPROVAL_SLOT) as usize],
        dregg_app_framework::field_from_u64(1),
        "approve flipped member 0's slot 0 -> 1",
    );

    // THE TOOTH: an UN-APPROVE (member 0's slot 1 -> 0) is a REAL executor refusal — the
    // installed program's `Monotonic(approval_slot)` bites on the produced transition. The deos
    // gate passes (still PROPOSED); the executor declines the retraction.
    let refused = fire_council_unapprove_attempt(&app, &PARTICIPANT, 0, &cclerk, &executor);
    assert!(
        matches!(refused, Err(FireExecuteError::Executor(_))),
        "an un-approve is refused by the executor's Monotonic(approval_slot), got {refused:?}",
    );
    // Anti-ghost: the refused retraction committed nothing — the slot still holds 1.
    let after = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        after.fields[(starbridge_polis::council::FIRST_APPROVAL_SLOT) as usize],
        dregg_app_framework::field_from_u64(1),
        "the refused un-approve committed nothing — the slot still holds 1",
    );
}

// =============================================================================
// AMENDMENT — a cooled ratify commits; the cooling `TemporalGate` refuses an early enact.
// =============================================================================

fn amendment_terms() -> AmendmentTerms {
    AmendmentTerms {
        charter: council_2of3(),
        new_constitution_hash: dregg_app_framework::field_from_u64(0xC0457),
        enact_not_before: 500, // the cooling gate height
    }
}

#[test]
fn amendment_ratify_after_cooling_commits() {
    // GREEN: an executor running PAST the cooling gate (height 1000 >= 500). The amendment is
    // seeded APPROVED (threshold met); the RATIFIER enacts → EXECUTED. The executor's cooling
    // `TemporalGate` is satisfied (1000 >= 500). A real verified turn.
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0xA1; 32]);
    let executor = embedded_executor_at(&cclerk, 1_000);
    let terms = amendment_terms();
    let app = amendment_app(&cclerk, &executor);
    seed_amendment_approved(&executor, &terms);

    let receipt = fire_amendment_ratify(&app, &OWNER, 1_000, &cclerk, &executor)
        .expect("the ratifier enacts past the cooling gate (1000 >= 500)");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real verified enact turn");
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[STATE_SLOT as usize],
        dregg_app_framework::field_from_u64(starbridge_polis::council::STATE_EXECUTED),
        "ratify stepped the amendment APPROVED -> EXECUTED",
    );
}

#[test]
fn amendment_ratify_before_cooling_is_a_real_executor_refusal() {
    // THE TOOTH: an executor at height 0 — BEFORE the cooling gate (0 < 500). The deos gate
    // passes (the amendment is APPROVED), but the executor's cooling `TemporalGate` on the
    // EXECUTED transition REFUSES the early enact. A real executor refusal in the fire path.
    let (cclerk, executor) = agent(0xA2); // EmbeddedExecutor::new starts at height 0
    let terms = amendment_terms();
    let app = amendment_app(&cclerk, &executor);
    seed_amendment_approved(&executor, &terms);

    let refused = fire_amendment_ratify(&app, &OWNER, 0, &cclerk, &executor);
    assert!(
        matches!(refused, Err(FireExecuteError::Executor(_))),
        "enacting before the cooling height is refused by the executor's TemporalGate, got {refused:?}",
    );
    // Anti-ghost: the refused enact committed nothing — still APPROVED.
    let after = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        after.fields[STATE_SLOT as usize],
        dregg_app_framework::field_from_u64(starbridge_polis::council::STATE_APPROVED),
        "the refused enact committed nothing — the amendment is still APPROVED",
    );
}

// =============================================================================
// CONSTITUTION — a named supersession commits; an ANON supersede (no successor) is refused.
// =============================================================================

fn params_v1() -> ConstitutionParams {
    ConstitutionParams {
        version: 1,
        council_threshold: 2,
        amendment_delay: 50,
        treasury_cap: 1_000,
    }
}

#[test]
fn constitution_named_supersede_commits_then_anon_supersede_is_refused() {
    let (cclerk, executor) = agent(0xC2);
    let params = params_v1();
    let app = constitution_app(&cclerk, &executor);
    seed_constitution_active(&executor, &params);

    // THE TOOTH FIRST (on the live ACTIVE cell): an ANON supersede (ACTIVE -> SUPERSEDED with
    // NO successor hash) is a REAL executor refusal — the installed program demands a nonzero
    // successor at SUPERSEDED (the forward certification). The deos gate passes (still ACTIVE).
    let refused = fire_constitution_anon_supersede_attempt(&app, &OWNER, &cclerk, &executor);
    assert!(
        matches!(refused, Err(FireExecuteError::Executor(_))),
        "an anonymous supersede is refused by the executor (nonzero-successor-at-supersede), got {refused:?}",
    );
    let after = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        after.fields[STATE_SLOT as usize],
        dregg_app_framework::field_from_u64(starbridge_polis::constitution::STATE_ACTIVE),
        "the refused anon supersede committed nothing — the constitution is still ACTIVE",
    );

    // HAPPY PATH: a NAMED supersede (records a nonzero successor + steps ACTIVE -> SUPERSEDED).
    // The executor re-enforces the installed program (the params are pinned, the successor is
    // nonzero) — a real verified turn.
    let successor = *blake3::hash(b"constitution-v2-descriptor").as_bytes();
    let receipt = fire_constitution_amend(&app, &OWNER, successor, &cclerk, &executor)
        .expect("a named supersede commits (nonzero successor recorded)");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "a real verified supersede turn"
    );
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[STATE_SLOT as usize],
        dregg_app_framework::field_from_u64(starbridge_polis::constitution::STATE_SUPERSEDED),
        "amend stepped the constitution ACTIVE -> SUPERSEDED",
    );
    assert_eq!(
        state.fields[starbridge_polis::constitution::SUCCESSOR_HASH_SLOT as usize],
        successor,
        "the successor hash is recorded (the forward certification)",
    );
}

// =============================================================================
// MANDATE — an invoke commits; the pinned `SLICE` slice-inflation (overspend) is refused.
// =============================================================================

fn worker_mandate() -> WorkerMandate {
    WorkerMandate {
        orchestrator: CellId::from_bytes([0xAA; 32]),
        slice: 30,
        tool_scope: tool_scope_commitment(&["search", "fetch"]),
        worker_tag: dregg_app_framework::field_from_u64(1),
    }
}

#[test]
fn mandate_invoke_commits_then_overspend_is_a_real_executor_refusal() {
    let (cclerk, executor) = agent(0x3D);
    let m = worker_mandate();
    let app = mandate_app(&cclerk, &executor);
    seed_mandate_active(&executor, &m);

    // HAPPY PATH: a WORKER fires one mandated step — a self-touch under the pins (ACTIVE ->
    // ACTIVE, slice/scope pins hold). A real verified turn.
    let receipt = fire_mandate_invoke(&app, &PARTICIPANT, &cclerk, &executor)
        .expect("a worker invokes one mandated step (caps ∧ state ∧ pins all pass)");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a real verified invoke turn");

    // THE TOOTH: a slice-INFLATION (a worker widening its own published budget) is a REAL
    // executor refusal — the installed program's `pin_term(SLICE)` bites. The deos gate passes
    // (still ACTIVE).
    let refused = fire_mandate_overspend_attempt(&app, &PARTICIPANT, 9_999, &cclerk, &executor);
    assert!(
        matches!(refused, Err(FireExecuteError::Executor(_))),
        "inflating the pinned slice is refused by the executor's pin_term(SLICE), got {refused:?}",
    );
    // Anti-ghost: the published slice is unchanged.
    let after = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        after.fields[starbridge_polis::mandate::SLICE_SLOT as usize],
        dregg_app_framework::field_from_u64(m.slice),
        "the refused inflation committed nothing — the slice still holds its pinned literal",
    );

    // And `revoke` (the AUTHORITY's terminal step) commits ACTIVE -> REVOKED.
    let revoke = fire_mandate_revoke(&app, &OWNER, &cclerk, &executor)
        .expect("the grantor revokes (ACTIVE -> REVOKED)");
    assert_ne!(revoke.turn_hash, [0u8; 32]);
    let revoked = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        revoked.fields[STATE_SLOT as usize],
        dregg_app_framework::field_from_u64(starbridge_polis::mandate::STATE_REVOKED),
        "revoke stepped the mandate ACTIVE -> REVOKED",
    );
    // After revoke the cell is terminally inert: another invoke is refused (no outgoing row).
    let post_revoke = fire_mandate_invoke(&app, &PARTICIPANT, &cclerk, &executor);
    assert!(
        post_revoke.is_err(),
        "a post-revoke touch is refused (REVOKED is terminal/inert), got {post_revoke:?}",
    );
}

// =============================================================================
// IDENTITY — a cooled rotation (preimage exhibit) commits; a rotation inside cooling is refused.
// =============================================================================

fn identity_charter() -> IdentityCharter {
    IdentityCharter {
        council: CouncilCharter::new(
            vec![
                CellId::from_bytes([0xD1; 32]),
                CellId::from_bytes([0xD2; 32]),
            ],
            2,
        ),
        cooling_period: 50,
    }
}

/// Key generations: G0 (birth), G1 (pre-committed at genesis), G2 (the rotation target).
fn generations() -> ([u8; 32], [u8; 32], [u8; 32]) {
    (
        key_set_commitment(&[[0x10; 32], [0x11; 32]]),
        key_set_commitment(&[[0x20; 32], [0x21; 32]]),
        key_set_commitment(&[[0x30; 32], [0x31; 32]]),
    )
}

#[test]
fn identity_rotate_after_cooling_commits_exhibiting_the_preimage() {
    // GREEN: an executor running past the cooling window (height 1000 >= 0 + 50). Genesis
    // pre-commits to G1's digest; the RECOVERY AUTHORITY rotates, EXHIBITING G1 (the
    // pre-committed preimage), installing it as the new current commitment, re-committing G2's
    // digest forward, and stamping the height. The executor's `KeyRotationGate` admits the
    // exhibit (`blake3(G1) == old[NEXT_KEYS_DIGEST]`) and the cooling (1000 >= 50). A real turn.
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x1D; 32]);
    let executor = embedded_executor_at(&cclerk, 1_000);
    let charter = identity_charter();
    let (g0, g1, g2) = generations();
    let app = identity_app(&cclerk, &executor);
    let first_digest = seed_identity_active(&executor, &charter, g0, g1);
    assert_eq!(
        first_digest,
        starbridge_polis::identity::next_keys_digest(&g1),
        "genesis pre-commits to G1's digest",
    );

    let receipt = fire_identity_rotate(&app, &OWNER, g1, g2, 1_000, &cclerk, &executor)
        .expect("a cooled rotation exhibiting the pre-committed preimage commits");
    assert_ne!(
        receipt.turn_hash, [0u8; 32],
        "a real verified rotation turn"
    );
    let state = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        state.fields[starbridge_polis::identity::CURRENT_KEYS_COMMIT_SLOT as usize],
        g1,
        "rotate installed the exhibited preimage as the new current commitment",
    );
    assert_eq!(
        state.fields[starbridge_polis::identity::NEXT_KEYS_DIGEST_SLOT as usize],
        starbridge_polis::identity::next_keys_digest(&g2),
        "rotate re-committed G2's digest forward (the chain never ends)",
    );
}

#[test]
fn identity_rotate_inside_cooling_is_a_real_executor_refusal() {
    // THE TOOTH: an executor at height 0 — INSIDE the cooling window (0 < 0 + 50). The deos
    // gate passes (the identity is ACTIVE), but the executor's `KeyRotationGate` cooling clause
    // REFUSES the rotation even though it exhibits the correct preimage. A real executor refusal.
    let (cclerk, executor) = agent(0x1E); // height 0
    let charter = identity_charter();
    let (g0, g1, g2) = generations();
    let app = identity_app(&cclerk, &executor);
    let _ = seed_identity_active(&executor, &charter, g0, g1);

    let refused = fire_identity_rotate(&app, &OWNER, g1, g2, 0, &cclerk, &executor);
    assert!(
        matches!(refused, Err(FireExecuteError::Executor(_))),
        "a rotation inside the cooling window is refused by the KeyRotationGate, got {refused:?}",
    );
    // Anti-ghost: the key registers are unchanged (genesis still in force).
    let after = executor.cell_state(cclerk.cell_id()).unwrap();
    assert_eq!(
        after.fields[starbridge_polis::identity::CURRENT_KEYS_COMMIT_SLOT as usize],
        g0,
        "the refused rotation committed nothing — the genesis current commitment still holds",
    );
}
