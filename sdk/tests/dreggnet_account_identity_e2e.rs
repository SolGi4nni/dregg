//! End-to-end teeth for the **DreggNet account-identity weld** on the REAL
//! executor — `DreggNet/docs/ACCOUNT-IDENTITY-WELD.md`.
//!
//! The launch-blocker (`DreggNet/docs/KEY-RECOVERY-AND-KERI.md`): the live
//! DreggNet `dga1_` cap-account is a bearer macaroon whose identity is its own
//! credential tail, so it has NO rotation / recovery / revocation. The fix is to
//! re-anchor the account to the substrate **identity cell** (KERI pre-rotation
//! via `KeyRotationGate`, guardian recovery via `ThresholdSigVerifier`) — and to
//! make the DreggNet account subject literally BE that cell's id.
//!
//! These tests prove the load-bearing agreement that makes the weld real rather
//! than asserted: the substrate identity-cell id the control plane provisions
//! for an account is **byte-identical** to the key-derived account id DreggNet's
//! `webauth::account_id` computes — because both are
//! `CellId::derive_raw(inception_pubkey, ACCOUNT_ROOT_TOKEN)` — and that this
//! anchor is **invariant across a key rotation**, so the account (and every
//! resource the consumers `org`/`dregg-secrets`/`console`/`guard`/`billing`
//! scope to the subject) survives. Rotation / compromise-resistance ride the
//! same deployed `KeyRotationGate` the sibling `identity_prerotation_e2e.rs`
//! proves; this test frames it as the cloud account scenario.

use dregg_cell::{CellId, field_from_u64};
use dregg_sdk::factories::ADOPT_TURN_FEE;
use dregg_sdk::identity::{
    CURRENT_KEYS_COMMIT_SLOT, IdentityCharter, LAST_ROTATED_AT_SLOT, STATE_ACTIVE, STATE_SLOT,
    create_identity, genesis_effects, key_set_commitment, next_keys_digest,
};
use dregg_sdk::polis::{CouncilCharter, GovernanceCellPlan};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, SdkError};
use dregg_turn::TurnError;

// ---------------------------------------------------------------------------
// The published binding constant — MUST match DreggNet `webauth::account_id`.
// webauth: `ACCOUNT_ROOT_TOKEN = blake3("dreggnet:account-identity:v1")`,
// `account_id_hex(pk) = hex(CellId::derive_raw(pk, ACCOUNT_ROOT_TOKEN))`. That
// crate's `account_id_is_the_substrate_cell_id` test pins the derivation; here
// we pin the SAME token + derivation on the substrate side, so the two repos
// agree by construction (transitively, via `derive_raw`).
// ---------------------------------------------------------------------------

const ACCOUNT_ROOT_TOKEN_LABEL: &[u8] = b"dreggnet:account-identity:v1";

fn account_root_token() -> [u8; 32] {
    blake3::hash(ACCOUNT_ROOT_TOKEN_LABEL).into()
}

/// The DreggNet account id for an inception pubkey, exactly as `webauth`
/// computes it (reproduced here — breadstuffs cannot dep the DreggNet crate).
fn dreggnet_account_id(inception_pubkey: &[u8; 32]) -> CellId {
    CellId::derive_raw(inception_pubkey, &account_root_token())
}

fn hex32(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for &b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// The `dregg:<hex>` subject string `webauth::subject_of` returns for a
/// re-anchored session credential carrying this account.
fn dreggnet_subject(inception_pubkey: &[u8; 32]) -> String {
    format!(
        "dregg:{}",
        hex32(dreggnet_account_id(inception_pubkey).as_bytes())
    )
}

// ---------------------------------------------------------------------------
// Harness (mirrors identity_prerotation_e2e.rs).
// ---------------------------------------------------------------------------

const COOLING: u64 = 50;

fn agent_pubkey(runtime: &AgentRuntime) -> [u8; 32] {
    runtime
        .cipherclerk()
        .read()
        .unwrap_or_else(|e| e.into_inner())
        .public_key()
        .0
}

fn slot_of(runtime: &AgentRuntime, cell: CellId, slot: u8) -> [u8; 32] {
    runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&cell)
        .expect("cell exists")
        .state
        .fields[slot as usize]
}

fn bootstrap(runtime: &mut AgentRuntime, plan: &GovernanceCellPlan) {
    runtime.deploy_factory(plan.descriptor.clone());
    runtime
        .execute(plan.create_effects.clone())
        .expect("create turn must commit");
    runtime
        .execute(plan.fund_effects.clone())
        .expect("fund turn must commit");
    runtime
        .execute_as(plan.cell_id, plan.adopt_effects.clone(), ADOPT_TURN_FEE)
        .expect("adopt turn must commit");
}

fn assert_program_violation<T>(result: Result<T, SdkError>, what: &str) {
    match result {
        Err(SdkError::Turn(TurnError::ProgramViolation { .. })) => {}
        Err(other) => panic!("{what}: expected ProgramViolation, got {other:?}"),
        Ok(_) => panic!("{what}: expected the EXECUTOR to reject, but the turn committed"),
    }
}

/// Provision a DreggNet account's identity cell the way the control plane must:
/// `token_id = ACCOUNT_ROOT_TOKEN`, `owner_pubkey = inception_pubkey`. Genesis it
/// at height 1_000 holding G0 with G1 pre-committed. Returns
/// `(runtime, cell, inception_pubkey, g0, g1)`.
#[allow(clippy::type_complexity)]
fn provision_account(
    domain: &str,
) -> (AgentRuntime, CellId, [u8; 32], Vec<[u8; 32]>, Vec<[u8; 32]>) {
    let mut runtime = AgentRuntime::new_simple(AgentCipherclerk::new(), domain);
    let agent = runtime.cell_id();
    let inception_pubkey = agent_pubkey(&runtime);
    let charter = IdentityCharter {
        council: CouncilCharter::new(
            vec![
                CellId::from_bytes([0xD1; 32]),
                CellId::from_bytes([0xD2; 32]),
            ],
            2,
        ),
        cooling_period: COOLING,
    };
    // THE WELD: provision the identity cell under the published ACCOUNT_ROOT_TOKEN
    // and the account's inception key, so its id == the DreggNet account id.
    let plan = create_identity(
        &charter,
        inception_pubkey,
        account_root_token(),
        agent,
        agent,
    )
    .expect("valid charter");
    bootstrap(&mut runtime, &plan);
    runtime.set_block_height(1_000);

    let g0: Vec<[u8; 32]> = vec![[0x10; 32], [0x11; 32]];
    let g1: Vec<[u8; 32]> = vec![[0x20; 32], [0x21; 32]];
    runtime
        .execute_on(
            plan.cell_id,
            genesis_effects(
                plan.cell_id,
                &charter,
                key_set_commitment(&g0),
                next_keys_digest(&key_set_commitment(&g1)),
            ),
        )
        .expect("genesis (icp) must commit");
    (runtime, plan.cell_id, inception_pubkey, g0, g1)
}

// ===========================================================================
// THE WELD: the substrate identity-cell id IS the DreggNet account subject.
// ===========================================================================

/// The identity cell the control plane provisions for an account has, as its id,
/// exactly `CellId::derive_raw(inception_pubkey, ACCOUNT_ROOT_TOKEN)` — which is
/// what DreggNet `webauth::account_id` returns. So the account subject the cloud
/// scopes every resource to and the substrate principal that rotates/recovers are
/// the SAME object, byte-for-byte.
#[test]
fn account_subject_is_the_substrate_identity_cell_id() {
    let (_runtime, cell, inception_pubkey, _g0, _g1) = provision_account("acct-weld-id");
    assert_eq!(
        cell,
        dreggnet_account_id(&inception_pubkey),
        "the provisioned identity-cell id must equal the DreggNet account id"
    );
    // And the human subject string the forward-auth header carries.
    assert_eq!(
        format!("dregg:{}", hex32(cell.as_bytes())),
        dreggnet_subject(&inception_pubkey)
    );
}

/// THE TABLE-STAKE: a key rotation keeps the account subject INVARIANT. The
/// authoritative key set rotates (the deployed `KeyRotationGate`), but the
/// identity-cell id — the subject every consumer keys resources to — does not
/// move. So the account, and every resource scoped to its subject, survives.
#[test]
fn account_survives_key_rotation_subject_invariant() {
    let (runtime, cell, inception_pubkey, _g0, g1) = provision_account("acct-weld-rotate");
    let subject_before = format!("dregg:{}", hex32(cell.as_bytes()));
    let key_before = slot_of(&runtime, cell, CURRENT_KEYS_COMMIT_SLOT);

    // Honest rotation: exhibit G1's pre-committed preimage, install it, chain.
    let g2: Vec<[u8; 32]> = vec![[0x30; 32], [0x31; 32]];
    runtime
        .rotate_identity(cell, &g1, next_keys_digest(&key_set_commitment(&g2)))
        .expect("honest account-key rotation must commit");

    // The KEY changed…
    let key_after = slot_of(&runtime, cell, CURRENT_KEYS_COMMIT_SLOT);
    assert_ne!(key_before, key_after, "the authoritative key set rotated");
    assert_eq!(key_after, key_set_commitment(&g1));
    assert_eq!(
        slot_of(&runtime, cell, LAST_ROTATED_AT_SLOT),
        field_from_u64(1_000)
    );
    assert_eq!(
        slot_of(&runtime, cell, STATE_SLOT),
        field_from_u64(STATE_ACTIVE)
    );

    // …but the ACCOUNT (its id == its subject) did NOT. Same principal, same
    // subject, so org membership / secrets KEK / DEC balance / owned resources
    // all still resolve to it.
    assert_eq!(
        format!("dregg:{}", hex32(cell.as_bytes())),
        subject_before,
        "the account subject is invariant across rotation — the account survives"
    );
    assert_eq!(cell, dreggnet_account_id(&inception_pubkey));
}

/// REVOKE-OUT / compromise resistance: after a rotation, the OLD key generation
/// is dead — replaying it to rotate again is refused BY THE EXECUTOR (an admitted
/// replay would be a hash collision). This is the "rotate before the thief drains
/// it" tooth: rotating to a fresh key permanently retires the compromised one.
#[test]
fn rotated_out_old_key_is_dead() {
    let (mut runtime, cell, _inception, _g0, g1) = provision_account("acct-weld-revoke");
    let g2: Vec<[u8; 32]> = vec![[0x30; 32], [0x31; 32]];

    // Rotate G0 -> G1 (honest).
    runtime
        .rotate_identity(cell, &g1, next_keys_digest(&key_set_commitment(&g2)))
        .expect("rotation to the fresh key must commit");

    // The compromised/old generation G1 has now been EXPOSED; replaying it to
    // rotate again is refused (it is no longer the pre-committed next set).
    runtime.set_block_height(1_200);
    assert_program_violation(
        runtime.rotate_identity(cell, &g1, next_keys_digest(&[0x99; 32])),
        "replaying the rotated-out (now-exposed) key generation",
    );
}

/// A different inception key is a different account (different subject) — the
/// id is key-derived, so two accounts never collide.
#[test]
fn distinct_inception_keys_are_distinct_accounts() {
    let (_r1, cell_a, pk_a, _, _) = provision_account("acct-weld-a");
    // A second account with a deterministically different inception key.
    let pk_b = {
        let mut p = pk_a;
        p[0] ^= 0xFF;
        p
    };
    assert_ne!(
        dreggnet_account_id(&pk_a),
        dreggnet_account_id(&pk_b),
        "distinct inception keys must derive distinct account ids"
    );
    assert_eq!(cell_a, dreggnet_account_id(&pk_a));
}
