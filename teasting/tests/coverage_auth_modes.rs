//! Executor-path coverage for the wave-2 `Authorization` modes:
//! `Authorization::Stealth` (one-time-key invocation) and
//! `Authorization::Token` (first-class biscuit/macaroon credential).
//!
//! These two modes regressed the authorization ratchet in
//! `protocol_coverage_gate.rs` from 4 → 6 when they landed without
//! executor-invoking coverage. This file pays that debt: every test drives a
//! REAL full `TurnExecutor::execute` — Phase 1 (fee+nonce) + Phase 2 (call
//! forest, where `verify_authorization` runs) — and asserts a real outcome:
//! a committed receipt with an observable ledger mutation, or a precise
//! `TurnError` refusal with the state untouched.
//!
//! The accept cases are made LOAD-BEARING by setting the target cell's
//! `set_state` permission to `AuthRequired::Signature`: a control turn with
//! `Authorization::Unchecked` on the very same cell REFUSES, so the commit
//! is attributable to the presented stealth/token credential and not to open
//! permissions.
//!
//! Crafting recipes mirror the executor's own adversarial suite
//! (`turn/src/executor/authorize.rs::anonymity_tests`) so the bound messages
//! (`Authorization::stealth_signing_message`, the token `AuthRequest`) match
//! the executor's verification exactly:
//!
//! - Stealth: spend key `S = s·G` is the target cell's `public_key`; the
//!   one-time key is `P = c·G + S`, signed with the raw scalar `k = c + s`
//!   (dalek hazmat `raw_sign`), message bound to
//!   (federation, action-hash, R, c, position, turn-nonce).
//! - Token (biscuit): minted via `dregg_token::BiscuitToken::mint_dregg`
//!   granting `(service = hex(cell-id), action = hex(method))`; trust anchor
//!   is the target cell's `verification_key` carrying the issuer pubkey.

use curve25519_dalek::constants::ED25519_BASEPOINT_TABLE;
use curve25519_dalek::scalar::Scalar;
use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions, Preconditions};
use dregg_turn::{
    TurnBuilder, TurnError, TurnResult,
    action::{Action, Authorization, CommitmentMode, DelegationMode, Effect, TokenKeyRef},
    executor::{ComputronCosts, TurnExecutor},
};
use ed25519_dalek::SigningKey;

/// The federation every executor in this file runs as. The stealth signing
/// message and the token `AuthRequest` both bind it.
const FED: [u8; 32] = [7u8; 32];

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

/// Permissions where state mutation REQUIRES a signature-class credential —
/// this is what makes the accept cases load-bearing (Unchecked refuses).
fn signature_gated_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::Signature,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn exec_at(block_height: u64) -> TurnExecutor {
    let mut e = TurnExecutor::new(ComputronCosts::zero());
    e.block_height = block_height;
    e.local_federation_id = FED;
    e
}

/// Build the canonical single-effect action this file submits: one
/// `SetField { index: 0, value: [9u8; 32] }` on `target` (so a commit is
/// observable as slot[0] flipping to `[9u8; 32]`), carrying `authorization`.
fn action_for(target: CellId, method: [u8; 32], authorization: Authorization) -> Action {
    Action {
        target,
        method,
        args: vec![],
        authorization,
        preconditions: Preconditions::default(),
        effects: vec![Effect::SetField {
            cell: target,
            index: 0,
            value: MUTATED,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    }
}

/// Submit `action` as the single root of a turn from `agent` at `nonce`,
/// chained from `prev_hash`, through the FULL executor.
fn exec_action(
    executor: &TurnExecutor,
    ledger: &mut Ledger,
    agent: CellId,
    nonce: u64,
    action: Action,
    prev_hash: Option<[u8; 32]>,
) -> TurnResult {
    let mut builder = TurnBuilder::new(agent, nonce);
    builder.add_action(action);
    let mut turn = builder.fee(0).build();
    turn.previous_receipt_hash = prev_hash;
    executor.execute(&turn, ledger)
}

fn assert_committed(result: &TurnResult, ctx: &str) {
    assert!(
        result.is_committed(),
        "{ctx}: expected committed, got {result:?}"
    );
}

/// Assert the result is `Rejected` and hand the `TurnError` to a matcher.
fn assert_rejected_with(result: &TurnResult, ctx: &str, matcher: impl FnOnce(&TurnError) -> bool) {
    match result {
        TurnResult::Rejected { reason, .. } => {
            assert!(
                matcher(reason),
                "{ctx}: unexpected rejection reason {reason:?}"
            );
        }
        other => panic!("{ctx}: expected rejected, got {other:?}"),
    }
}

/// Read slot[0] of `cell`. The 16 state slots are zero-initialised, so an
/// untouched slot reads `Some(PRISTINE)`; a committed
/// `SetField { index: 0, value: MUTATED }` flips it to `Some(MUTATED)`.
/// `None` only if the cell is absent.
fn slot0(ledger: &Ledger, cell: &CellId) -> Option<[u8; 32]> {
    ledger.get(cell).and_then(|c| c.state.get_field(0).copied())
}

/// The zero-initialised baseline of slot[0] on a freshly created cell — what a
/// REFUSED turn must leave it at (the `MUTATED` value must never appear).
const PRISTINE: [u8; 32] = [0u8; 32];
/// The value a committed `action_for` turn writes into slot[0].
const MUTATED: [u8; 32] = [9u8; 32];

// ---------------------------------------------------------------------------
// Stealth crafting (mirrors turn/src/executor/authorize.rs::anonymity_tests)
// ---------------------------------------------------------------------------

/// `(spend_pubkey S, spend_scalar s)` with `S = s·G`, derived from an Ed25519
/// seed exactly the way `cell::stealth` does, so `P = c·G + S` is signable
/// with `k = c + s`.
fn spend_keypair(seed: u8) -> ([u8; 32], Scalar) {
    let sk = SigningKey::from_bytes(&[seed; 32]);
    let s = sk.to_scalar();
    let s_point = &s * ED25519_BASEPOINT_TABLE;
    (s_point.compress().to_bytes(), s)
}

/// Sign `msg` with the raw Ed25519 scalar `k` whose public key is `pubkey =
/// k·G`. The one-time stealth secret is a scalar, not a seed, so the dalek
/// hazmat raw-key API is required.
fn sign_with_scalar(k: &Scalar, pubkey: &[u8; 32], msg: &[u8]) -> [u8; 64] {
    use ed25519_dalek::VerifyingKey;
    use ed25519_dalek::hazmat::{ExpandedSecretKey, raw_sign};
    use sha2::Sha512;
    let mut prefix = [0u8; 32];
    prefix.copy_from_slice(&blake3::hash(&k.to_bytes()).as_bytes()[..32]);
    let esk = ExpandedSecretKey {
        scalar: *k,
        hash_prefix: prefix,
    };
    let vk = VerifyingKey::from_bytes(pubkey).expect("valid one-time pubkey P");
    let sig = raw_sign::<Sha512>(&esk, msg, &vk);
    sig.to_bytes()
}

/// Craft a valid `Authorization::Stealth` for the canonical `action_for`
/// shape: blinding scalar `c` from `c_seed`, one-time key `P = c·G + s·G`,
/// signature by `k = c + s` over the executor's exact bound message
/// (federation, action-hash, R, c, position, turn-nonce). The signing message
/// binds `action.hash()`, which excludes the signature bytes, so hashing the
/// placeholder-signature action equals hashing the final one.
fn make_stealth_auth(
    spend_scalar: &Scalar,
    c_seed: u8,
    target: CellId,
    method: [u8; 32],
    turn_nonce: u64,
    position: usize,
) -> Authorization {
    let c = Scalar::from_bytes_mod_order([c_seed; 32]);
    let p_point = (&c * ED25519_BASEPOINT_TABLE) + (spend_scalar * ED25519_BASEPOINT_TABLE);
    let one_time_pubkey = p_point.compress().to_bytes();
    let k = c + spend_scalar;
    let ephemeral_pubkey = [c_seed.wrapping_add(1); 32];
    let blinding_scalar = c.to_bytes();

    let placeholder = Authorization::Stealth {
        one_time_pubkey,
        ephemeral_pubkey,
        blinding_scalar,
        signature: [0u8; 64],
    };
    let action_hash = action_for(target, method, placeholder).hash();
    let msg = Authorization::stealth_signing_message(
        &FED,
        &action_hash,
        &ephemeral_pubkey,
        &blinding_scalar,
        position,
        turn_nonce,
    );
    let signature = sign_with_scalar(&k, &one_time_pubkey, &msg);

    Authorization::Stealth {
        one_time_pubkey,
        ephemeral_pubkey,
        blinding_scalar,
        signature,
    }
}

/// A fresh ledger holding one signature-gated cell whose spend key is `s_pub`.
fn stealth_world(seed: u8) -> (Ledger, CellId, Scalar, [u8; 32]) {
    let (s_pub, s_scalar) = spend_keypair(seed);
    let mut cell = Cell::new(s_pub, [0u8; 32]);
    cell.permissions = signature_gated_permissions();
    let cid = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();
    (ledger, cid, s_scalar, s_pub)
}

// ---------------------------------------------------------------------------
// Stealth: accept — a valid one-time-key invocation COMMITS through the
// executor and mutates state, with the persistent spend key absent from the
// wire; the Unchecked control on the same cell REFUSES.
// ---------------------------------------------------------------------------

#[test]
fn stealth_valid_invocation_commits_and_unchecked_control_refuses() {
    let (mut ledger, cid, s_scalar, s_pub) = stealth_world(11);
    let executor = exec_at(0);
    let method = [1u8; 32];

    // Control tooth: Unchecked auth cannot move a Signature-gated slot — so
    // the later commit is attributable to the stealth credential.
    let control = exec_action(
        &executor,
        &mut ledger,
        cid,
        0,
        action_for(cid, method, Authorization::Unchecked),
        None,
    );
    assert_rejected_with(&control, "unchecked control", |e| {
        matches!(e, TurnError::PermissionDenied { .. })
    });
    assert_eq!(
        slot0(&ledger, &cid),
        Some(PRISTINE),
        "control must not mutate state"
    );

    // The control's Phase 1 (fee+nonce) is final even on rejection, so the
    // agent cell's nonce advanced to 1: craft the stealth auth bound to
    // turn-nonce 1, position 0.
    let auth = make_stealth_auth(&s_scalar, 3, cid, method, 1, 0);
    if let Authorization::Stealth {
        one_time_pubkey, ..
    } = &auth
    {
        assert_ne!(
            one_time_pubkey, &s_pub,
            "persistent spend key must not appear on the wire"
        );
    }
    let result = exec_action(
        &executor,
        &mut ledger,
        cid,
        1,
        action_for(cid, method, auth),
        None,
    );
    assert_committed(&result, "valid stealth invocation");
    assert_eq!(
        slot0(&ledger, &cid),
        Some(MUTATED),
        "committed stealth turn must have mutated slot[0]"
    );
}

// ---------------------------------------------------------------------------
// Stealth: reject — replaying the SAME auth bytes at the next turn nonce
// refuses (the signing message binds the nonce), state unmoved.
// ---------------------------------------------------------------------------

#[test]
fn stealth_replayed_auth_refuses() {
    let (mut ledger, cid, s_scalar, _s_pub) = stealth_world(13);
    let executor = exec_at(0);
    let method = [3u8; 32];

    // Turn 1: valid stealth auth bound to nonce 0 — commits.
    let auth = make_stealth_auth(&s_scalar, 7, cid, method, 0, 0);
    let action = action_for(cid, method, auth);
    let first = exec_action(&executor, &mut ledger, cid, 0, action.clone(), None);
    assert_committed(&first, "stealth turn 1");
    assert_eq!(slot0(&ledger, &cid), Some(MUTATED));

    // Turn 2: the SAME action (identical auth bytes) replayed at nonce 1,
    // correctly chained from turn 1's receipt — the bound message no longer
    // matches, so the executor refuses.
    let prev = executor.get_last_receipt_hash(&cid);
    let replay = exec_action(&executor, &mut ledger, cid, 1, action, prev);
    assert_rejected_with(&replay, "stealth replay at next nonce", |e| {
        matches!(e, TurnError::StealthAuthInvalid { .. })
    });
}

// ---------------------------------------------------------------------------
// Stealth: reject — a forger who does NOT hold the cell's spend scalar
// cannot satisfy P == c·G + S; refused, state untouched.
// ---------------------------------------------------------------------------

#[test]
fn stealth_forged_by_nonowner_refuses() {
    let (mut ledger, cid, _real_s, _s_pub) = stealth_world(14);
    let (_attacker_pub, attacker_s) = spend_keypair(99);
    let executor = exec_at(0);
    let method = [4u8; 32];

    // Attacker crafts a structurally-valid stealth auth with THEIR scalar:
    // P = c·G + attacker·G ≠ c·G + S.
    let auth = make_stealth_auth(&attacker_s, 8, cid, method, 0, 0);
    let result = exec_action(
        &executor,
        &mut ledger,
        cid,
        0,
        action_for(cid, method, auth),
        None,
    );
    assert_rejected_with(&result, "forged stealth auth", |e| {
        matches!(e, TurnError::StealthAuthInvalid { .. })
    });
    assert_eq!(
        slot0(&ledger, &cid),
        Some(PRISTINE),
        "forgery must not mutate state"
    );
}

// ---------------------------------------------------------------------------
// Token crafting (biscuit; mirrors authorize.rs::anonymity_tests)
// ---------------------------------------------------------------------------

/// Mint a biscuit granting `(service = hex(cell), action = hex(method))`,
/// optionally height-expiring at `not_after`. Returns (encoded, issuer pk).
fn mint_biscuit_for(cell: CellId, method: [u8; 32], not_after: Option<i64>) -> (Vec<u8>, [u8; 32]) {
    use dregg_token::BiscuitToken;
    use dregg_token::biscuit_auth::KeyPair;
    use dregg_token::traits::{Attenuation, AuthToken};
    let kp = KeyPair::new();
    let issuer: [u8; 32] = kp
        .public()
        .to_bytes()
        .try_into()
        .expect("32-byte ed25519 pubkey");
    let svc = hex::encode(cell.as_bytes());
    let act = hex::encode(method);
    let mut tok: Box<dyn AuthToken> =
        Box::new(BiscuitToken::mint_dregg(&kp, &[], &[(svc, act)], &[], &[], &[], None).unwrap());
    if let Some(na) = not_after {
        let att = Attenuation {
            not_after: Some(na),
            ..Default::default()
        };
        tok = tok.attenuate(&att).unwrap();
    }
    let encoded = tok.to_encoded().unwrap().into_bytes();
    (encoded, issuer)
}

fn vk_with_data(data: Vec<u8>) -> dregg_cell::VerificationKey {
    let hash = *blake3::hash(&data).as_bytes();
    dregg_cell::VerificationKey { hash, data }
}

/// A fresh ledger holding one signature-gated cell trusting `issuer` (when
/// given) as its verification-key granting authority.
fn token_world(seed: u8, issuer: Option<[u8; 32]>) -> (Ledger, CellId) {
    let mut cell = Cell::new([seed; 32], [0u8; 32]);
    cell.permissions = signature_gated_permissions();
    if let Some(pk) = issuer {
        cell.verification_key = Some(vk_with_data(pk.to_vec()));
    }
    let cid = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();
    (ledger, cid)
}

fn token_auth(encoded: Vec<u8>, issuer: [u8; 32]) -> Authorization {
    Authorization::Token {
        encoded,
        key_ref: TokenKeyRef::BiscuitIssuer {
            issuer_pubkey: issuer,
        },
        discharges: vec![],
    }
}

// ---------------------------------------------------------------------------
// Token: accept — a valid biscuit whose caveats cover THIS call COMMITS
// through the executor and mutates state; the Unchecked control refuses.
// ---------------------------------------------------------------------------

#[test]
fn token_biscuit_valid_commits_and_unchecked_control_refuses() {
    let method = [5u8; 32];
    // Pre-derive the cell id to mint a token bound to it: the id depends only
    // on (public_key, token_id), not on permissions/VK.
    let cid = Cell::new([21u8; 32], [0u8; 32]).id();
    let (encoded, issuer) = mint_biscuit_for(cid, method, None);
    let (mut ledger, cid) = token_world(21, Some(issuer));
    let executor = exec_at(100);

    // Control tooth: Unchecked refuses on the Signature-gated slot.
    let control = exec_action(
        &executor,
        &mut ledger,
        cid,
        0,
        action_for(cid, method, Authorization::Unchecked),
        None,
    );
    assert_rejected_with(&control, "unchecked control", |e| {
        matches!(e, TurnError::PermissionDenied { .. })
    });
    assert_eq!(slot0(&ledger, &cid), Some(PRISTINE));

    // The presented credential carries the turn (nonce advanced to 1 by the
    // control's final Phase 1).
    let result = exec_action(
        &executor,
        &mut ledger,
        cid,
        1,
        action_for(cid, method, token_auth(encoded, issuer)),
        None,
    );
    assert_committed(&result, "valid biscuit token");
    assert_eq!(
        slot0(&ledger, &cid),
        Some(MUTATED),
        "committed token turn must have mutated slot[0]"
    );
}

// ---------------------------------------------------------------------------
// Token: reject — expired by block height (deterministic, no wall-clock).
// The SAME token commits before its expiry height.
// ---------------------------------------------------------------------------

#[test]
fn token_biscuit_expired_by_height_refuses_and_commits_before_expiry() {
    let method = [8u8; 32];
    let cid = Cell::new([24u8; 32], [0u8; 32]).id();
    // not_after = 5 (a block height).
    let (encoded, issuer) = mint_biscuit_for(cid, method, Some(5));

    // At height 10 the token is expired: refused, state untouched.
    let (mut ledger, cid) = token_world(24, Some(issuer));
    let executor = exec_at(10);
    let result = exec_action(
        &executor,
        &mut ledger,
        cid,
        0,
        action_for(cid, method, token_auth(encoded.clone(), issuer)),
        None,
    );
    assert_rejected_with(&result, "expired token", |e| {
        matches!(e, TurnError::TokenInsufficientCapability { .. })
    });
    assert_eq!(
        slot0(&ledger, &cid),
        Some(PRISTINE),
        "expired token must not mutate"
    );

    // The SAME token bytes at height 3 (< 5): commits.
    let (mut ledger_ok, cid_ok) = token_world(24, Some(issuer));
    let executor_ok = exec_at(3);
    let result_ok = exec_action(
        &executor_ok,
        &mut ledger_ok,
        cid_ok,
        0,
        action_for(cid_ok, method, token_auth(encoded, issuer)),
        None,
    );
    assert_committed(&result_ok, "token before height expiry");
    assert_eq!(slot0(&ledger_ok, &cid_ok), Some(MUTATED));
}

// ---------------------------------------------------------------------------
// Token: reject — tampered credential (byte flipped) fails the signature
// check; refused, state untouched.
// ---------------------------------------------------------------------------

#[test]
fn token_biscuit_tampered_refuses() {
    let method = [10u8; 32];
    let cid = Cell::new([25u8; 32], [0u8; 32]).id();
    let (mut encoded, issuer) = mint_biscuit_for(cid, method, None);
    let mid = encoded.len() / 2;
    encoded[mid] ^= 0xFF;

    let (mut ledger, cid) = token_world(25, Some(issuer));
    let executor = exec_at(100);
    let result = exec_action(
        &executor,
        &mut ledger,
        cid,
        0,
        action_for(cid, method, token_auth(encoded, issuer)),
        None,
    );
    assert_rejected_with(&result, "tampered token", |e| {
        matches!(e, TurnError::TokenAuthInvalid { .. })
    });
    assert_eq!(slot0(&ledger, &cid), Some(PRISTINE));
}

// ---------------------------------------------------------------------------
// Token: reject — replaying a token against an action its caveats do not
// cover fails the capability-cover check (the bound AuthRequest differs).
// ---------------------------------------------------------------------------

#[test]
fn token_biscuit_replay_against_other_action_refuses() {
    let granted_method = [6u8; 32];
    let cid = Cell::new([22u8; 32], [0u8; 32]).id();
    let (encoded, issuer) = mint_biscuit_for(cid, granted_method, None);

    let (mut ledger, cid) = token_world(22, Some(issuer));
    let executor = exec_at(100);
    // Present the token on a DIFFERENT method than the one it grants.
    let other_method = [0x99u8; 32];
    let result = exec_action(
        &executor,
        &mut ledger,
        cid,
        0,
        action_for(cid, other_method, token_auth(encoded, issuer)),
        None,
    );
    assert_rejected_with(&result, "token replayed on other action", |e| {
        matches!(e, TurnError::TokenInsufficientCapability { .. })
    });
    assert_eq!(slot0(&ledger, &cid), Some(PRISTINE));
}

// ---------------------------------------------------------------------------
// Token: reject — an issuer the target cell does not trust (no VK match, pk
// mismatch) is refused even though the token verifies cryptographically.
// ---------------------------------------------------------------------------

#[test]
fn token_biscuit_untrusted_issuer_refuses() {
    let method = [7u8; 32];
    let cid = Cell::new([23u8; 32], [0u8; 32]).id();
    let (encoded, issuer) = mint_biscuit_for(cid, method, None);

    // Cell does NOT carry the issuer as VK and its pk differs from the issuer.
    let (mut ledger, cid) = token_world(23, None);
    let executor = exec_at(100);
    let result = exec_action(
        &executor,
        &mut ledger,
        cid,
        0,
        action_for(cid, method, token_auth(encoded, issuer)),
        None,
    );
    assert_rejected_with(&result, "untrusted issuer", |e| {
        matches!(e, TurnError::TokenAuthInvalid { .. })
    });
    assert_eq!(slot0(&ledger, &cid), Some(PRISTINE));
}

// ---------------------------------------------------------------------------
// Token: reject — a cell-scoped-macaroon key_ref naming a DIFFERENT cell than
// the action's target is refused outright (the verifier may only hold the
// target cell's own derived secret).
// ---------------------------------------------------------------------------

#[test]
fn token_macaroon_cross_cell_key_ref_refuses() {
    use dregg_token::MacaroonToken;
    use dregg_token::traits::AuthToken;

    let method = [11u8; 32];
    let (mut ledger, cid) = token_world(26, None);
    let other_cell = Cell::new([27u8; 32], [0u8; 32]).id();

    // Mint a macaroon under the OTHER cell's derived secret and present it
    // with a key_ref naming that other cell: rejected before any HMAC check.
    let secret = dregg_turn::derive_cell_macaroon_secret(&FED, &other_cell);
    let mac = MacaroonToken::mint(secret, b"kid", "dregg");
    let encoded = mac.to_encoded().unwrap().into_bytes();

    let executor = exec_at(100);
    let auth = Authorization::Token {
        encoded,
        key_ref: TokenKeyRef::CellScopedMacaroon { cell: other_cell },
        discharges: vec![],
    };
    let result = exec_action(
        &executor,
        &mut ledger,
        cid,
        0,
        action_for(cid, method, auth),
        None,
    );
    assert_rejected_with(&result, "cross-cell macaroon key_ref", |e| {
        matches!(e, TurnError::TokenAuthInvalid { .. })
    });
    assert_eq!(slot0(&ledger, &cid), Some(PRISTINE));
}
