//! ADVERSARIAL: does the live executor's `CapTpDelivered` authorization gate admit an
//! AMPLIFYING / UNTRUSTED handoff that the verified Lean kernel (and the captp
//! `validate_handoff` swiss gate) reject?
//!
//! The Lean spec (`Dregg2.Exec.AuthModes`, lines 16-25) documents the suspicion verbatim:
//! "dregg1 currently FAILS to enforce `granted ≤ held` here (it verifies the two
//! signatures and the cert/target binding, but never re-checks that the cert's conferred
//! permissions attenuate what the introducer held)."
//!
//! The structural reality: the executor has NO swiss table — the introducer's authoritative
//! `held` record (the swiss entry) lives ONLY in the captp/wire layer, consulted ONLY by
//! `validate_handoff`. So the executor's image of "held" is the TARGET CELL's own declared
//! permission lattice: a CapTpDelivered cert short-circuits that lattice entirely. Two gaps:
//!
//!   (A) INTRODUCER-TRUST: `verify_captp_delivered` takes `introducer_pk` from the
//!       recipient-supplied turn and verifies the cert is signed by THAT key — but never
//!       checks the introducer is a TRUSTED federation. An adversary self-signs a cert.
//!   (B) NON-AMPLIFICATION: the cert short-circuits the target cell's permission lattice
//!       (`verify_authorization` returns Ok early), so the cert confers authority to perform
//!       ANY action on the target regardless of the cell's declared `AuthRequired` — without
//!       any `granted ≤ held` (here: granted ≤ the cell's required tier) check.
//!
//! This test fixes a Signature-LOCKED target cell, then has an UNTRUSTED adversary (its own
//! fresh keypair = the "introducer") self-sign a handoff cert naming itself recipient and
//! submit a CapTpDelivered turn that mutates the locked cell. If the executor COMMITS, the
//! hole is CONFIRMED. After the fix it must REJECT (the locked cell's lattice is honored /
//! the untrusted introducer is refused), while a LEGITIMATE attenuating handoff still passes.

use dregg_captp::HandoffCertificate;
use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnExecutor,
    turn::Turn,
};
use dregg_types::{SigningKey, sign};

const LOCAL_FED: [u8; 32] = [0u8; 32];

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

fn executor() -> TurnExecutor {
    let mut e = TurnExecutor::new(ComputronCosts::zero());
    e.set_local_federation_id(LOCAL_FED);
    e
}

/// The rejection reason, by variant, or `None` when the turn COMMITTED.
fn rejection(result: &dregg_turn::TurnResult) -> Option<&dregg_turn::TurnError> {
    match result {
        dregg_turn::TurnResult::Rejected { reason, .. } => Some(reason),
        _ => None,
    }
}

/// Build a CapTpDelivered turn whose `recipient_key` self-signs the canonical delivery
/// message — exactly as the wire builder does, so the executor's signature checks PASS.
/// `target` is the cell being mutated; `granted` is the cert's claimed permission tier.
#[allow(clippy::too_many_arguments)]
fn captp_turn(
    agent: CellId,
    target: CellId,
    effect: Effect,
    nonce: u64,
    introducer_sk: &SigningKey,
    introducer_fed: dregg_captp::FederationId,
    introducer_pk: [u8; 32],
    recipient_sk: &SigningKey,
    recipient_pk: [u8; 32],
    granted: AuthRequired,
) -> Turn {
    let cert = HandoffCertificate::create(
        introducer_sk,
        introducer_fed,
        dregg_captp::FederationId(LOCAL_FED),
        target,
        recipient_pk,
        granted,
        None, // no allowed_effects restriction
        None, // no expiry
        None, // unlimited uses
        [0u8; 32],
    );
    let effects = vec![effect];
    let signing_msg = Authorization::captp_delivered_signing_message_for_federation(
        &LOCAL_FED,
        &cert.nonce,
        &target,
        &target,
        nonce,
        &effects,
    );
    let sender_signature = sign(recipient_sk, &signing_msg).0;

    let action = Action {
        target,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::CapTpDelivered {
            handoff_cert: cert,
            introducer_pk,
            sender_pk: recipient_pk,
            sender_signature,
        },
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: dregg_turn::action::CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let mut forest = CallForest::new();
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

/// THE CONFIRM/REFUTE TEST. An UNTRUSTED adversary self-signs a cert granting itself
/// `None` (the loosest tier = MORE authority than the held `Signature`-locked cell), and
/// mutates the locked cell via SetField. Pre-fix: the executor COMMITS (hole). Post-fix:
/// the executor REJECTS (untrusted introducer / amplification).
#[test]
fn adversary_amplifying_captp_handoff_is_rejected() {
    // The locked target cell: every action requires Signature.
    let target = make_cell(1, 100, locked_permissions());
    let target_id = target.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(target).unwrap();

    // The ADVERSARY: a fresh keypair that is NOT a trusted federation. It plays BOTH
    // introducer and recipient (self-handoff). It HOLDS a coarse access cap over `target`
    // (so the cap-graph gate at effect time passes) but CANNOT satisfy the cell's
    // Signature-tier permission lattice — which `verify_authorization` enforces for every
    // mode EXCEPT the short-circuiting CapTpDelivered. The exploit is the lattice BYPASS:
    // the self-signed cert lets the adversary perform a Signature-gated SetField it could
    // not authorize via any honest mode.
    let adversary_sk = SigningKey::from_bytes(&[7u8; 32]);
    let adversary_pk = adversary_sk.public_key().0;
    let adversary_fed = dregg_captp::FederationId(adversary_pk);

    // The adversary's OWN cell (the turn agent / recipient) must exist in the ledger so the
    // turn reaches the authorization gate. It holds a bare access cap over the locked target.
    let mut agent_cell = Cell::with_balance(adversary_pk, [0u8; 32], 1_000);
    agent_cell.permissions = {
        let mut p = locked_permissions();
        p.access = AuthRequired::None;
        p
    };
    // Grant the agent a coarse access cap over the locked target (passes the cap-graph gate).
    agent_cell
        .capabilities
        .grant(target_id, AuthRequired::None)
        .unwrap();
    let agent_id = agent_cell.id();
    ledger.insert_cell(agent_cell).unwrap();

    let turn = captp_turn(
        agent_id,
        target_id,
        Effect::SetField {
            cell: target_id,
            index: 4, // a developer slot (not reserved)
            value: [0x42; 32],
        },
        0,
        &adversary_sk,
        adversary_fed,
        adversary_pk,
        &adversary_sk,
        adversary_pk,
        AuthRequired::None, // GRANTS the loosest tier — amplification over the locked cell
    );

    let committed = executor()
        .execute(&turn, &mut ledger.clone())
        .is_committed();
    assert!(
        !committed,
        "SOUNDNESS HOLE: the executor COMMITTED an amplifying CapTpDelivered turn from an \
         UNTRUSTED self-signed introducer against a Signature-LOCKED cell — Rust admits what \
         the verified Lean kernel (captp_granted_le_held / handoff_non_amplifying) refuses."
    );
}

/// POSITIVE CONTROL — a LEGITIMATE handoff (granted tier matches the cell's required tier;
/// no amplification) on an OPEN cell still commits. Guards against the fix over-rejecting.
#[test]
fn legitimate_captp_handoff_still_accepted() {
    // OPEN target cell: every action requires None (so a granted-None cert does NOT amplify).
    let open = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };

    let target = make_cell(2, 100, open.clone());
    let target_id = target.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(target).unwrap();

    // A handoff granting the SAME tier the open cell requires (None ≤ None: attenuating,
    // not amplifying).
    //
    // ⚠ FIXTURE REPAIRED 2026-07-28, and the repair is the finding. This test used to set
    // `introducer_fed = FederationId(LOCAL_FED)` — i.e. `[0u8; 32]` — while signing with a
    // key whose public bytes are NOT `[0u8; 32]`, and gave the introducer no authority over
    // the target at all. Under the canonical convention the rest of the tree uses
    // (`FederationId == raw ed25519 pk bytes`, `node/src/mcp/handlers_delegate.rs:1096`)
    // that certificate names a federation which did not sign it — it is the very
    // impersonation `a2_*` exercises — and it delegated authority nobody held. It passed
    // only because NEITHER check existed on the executor path. `dregg_captp::validate_handoff`
    // has refused this exact shape since 2026-07-25 (`IntroducerKeyMismatch`).
    //
    // So the fixture is now an honest handoff: the introducer's id IS its key, and the
    // introducer genuinely holds a capability over the target. The assertion is unchanged
    // and un-weakened — a legitimate non-amplifying handoff must still commit.
    let intro_sk = SigningKey::from_bytes(&[3u8; 32]);
    let intro_pk = intro_sk.public_key().0;
    let recip_sk = SigningKey::from_bytes(&[9u8; 32]);
    let recip_pk = recip_sk.public_key().0;

    // The INTRODUCER's cell, holding a real capability over the open target — the `held`
    // the certificate's `granted` attenuates.
    let mut intro_cell = Cell::with_balance(intro_pk, [0u8; 32], 1_000);
    intro_cell.permissions = open.clone();
    intro_cell
        .capabilities
        .grant(target_id, AuthRequired::None)
        .unwrap();
    ledger.insert_cell(intro_cell).unwrap();

    // The recipient's OWN cell (the turn agent) must exist in the ledger and hold an access
    // cap over the OPEN target (passes the cap-graph gate). The target's lattice is None, so
    // the granted-None cert does NOT amplify — an honest, non-amplifying handoff.
    let mut agent_cell = Cell::with_balance(recip_pk, [0u8; 32], 1_000);
    agent_cell.permissions = open;
    agent_cell
        .capabilities
        .grant(target_id, AuthRequired::None)
        .unwrap();
    let agent_id = agent_cell.id();
    ledger.insert_cell(agent_cell).unwrap();

    let turn = captp_turn(
        agent_id,
        target_id,
        Effect::EmitEvent {
            cell: target_id,
            event: dregg_turn::Event::new([0u8; 32], vec![]),
        },
        0,
        &intro_sk,
        dregg_captp::FederationId(intro_pk), // id == pk: the canonical convention
        intro_pk,
        &recip_sk,
        recip_pk,
        AuthRequired::None, // matches the open cell's required tier — no amplification
    );

    let committed = executor()
        .execute(&turn, &mut ledger.clone())
        .is_committed();
    assert!(
        committed,
        "REGRESSION: a LEGITIMATE non-amplifying CapTpDelivered handoff on an OPEN cell was \
         REJECTED — the non-amplification fix is over-rejecting honest handoffs."
    );
}

// ════════════════════════════════════════════════════════════════════════════════════
// GAP (A) — INTRODUCER-TRUST. The gap this file's own header NAMED in 2026 and never
// closed: "`verify_captp_delivered` takes `introducer_pk` from the recipient-supplied
// turn and verifies the cert is signed by THAT key — but never checks the introducer is
// a TRUSTED federation. An adversary self-signs a cert."
//
// The two live tests above close gap (B) ONLY (granted ⊄ the target cell's declared
// floor). Gap (A) is orthogonal and strictly worse: nothing ties the certificate to any
// authority that exists. `dregg_captp::validate_handoff` binds all three legs —
// id↔pk (`handoff.rs:1005`), the known-federations roster (`:1035`) and the swiss-entry
// `held` (`:1060`) — but it is reached ONLY from `wire/src/server.rs`'s PresentHandoff
// handler, which returns a routing token and builds NO Turn. The path that actually
// reaches the executor ("turns the recipient submits itself" — `POST /turns/submit` and
// the finalized-block replay) re-derives NONE of them. The two halves are disjoint.
// ════════════════════════════════════════════════════════════════════════════════════

/// A cell owned by a REAL ed25519 identity (so `target_cell.public_key()` is a key some
/// party can actually sign under), carrying `perms`.
fn cell_for(sk: &SigningKey, balance: i64, perms: Permissions) -> Cell {
    let mut cell = Cell::with_balance(sk.public_key().0, [0u8; 32], balance);
    cell.permissions = perms;
    cell
}

/// ⚑ FALSIFIER (A1) — **THE CERTIFICATE'S INTRODUCER NEED NOT EXIST.**
///
/// Mallory holds only a COARSE access capability over Victim's `Signature`-locked cell
/// (a plausible low-privilege grant: "you may reference this cell"). She cannot perform a
/// `Signature`-gated `SetField` honestly: `check_single_auth_requirement` routes
/// `AuthRequired::Signature` to `verify_ed25519_signature`, which verifies against
/// **`target_cell.public_key()` — VICTIM'S key** (`authorize.rs:963`). Leg 1 of this test
/// asserts exactly that refusal, so the setup is proven adversarially meaningful and not
/// accidentally authorized.
///
/// Leg 2 is the hole. Mallory attaches a handoff certificate whose `introducer` is a key
/// that exists NOWHERE in the ledger and holds NOTHING, signs it with that key (she made
/// it up, so she has its secret), and submits `Authorization::CapTpDelivered`.
/// `verify_authorization` returns `Ok(())` at `authorize.rs:144` — the cell's lattice is
/// never consulted — and the only substitute, §5b, merely checks the cert's DECLARED tier
/// against the cell's floor (`Signature ≤ Signature` ✓). So a certificate that merely
/// SAYS "Signature", signed by a stranger, discharges a requirement for VICTIM'S
/// signature. Victim never signed anything.
///
/// PRE-FIX this COMMITS. POST-FIX it must be refused as `CapTpIntroducerLacksCapability`
/// — asserted BY VARIANT, because "some rejection occurred" would also be satisfied by
/// the cap-graph gate, the expiry check, or a malformed-key error, none of which is the
/// property under test.
#[test]
fn a1_captp_cert_from_an_introducer_who_holds_nothing_cannot_discharge_the_owners_signature_tier() {
    let victim_sk = SigningKey::from_bytes(&[11u8; 32]);
    let victim = cell_for(&victim_sk, 100, locked_permissions());
    let victim_id = victim.id();

    let mallory_sk = SigningKey::from_bytes(&[22u8; 32]);
    let mallory_pk = mallory_sk.public_key().0;
    let mut mallory = cell_for(&mallory_sk, 1_000, locked_permissions());
    // Mallory's ONLY authority over the victim: a coarse access capability. This is what
    // lets her past the cap-graph gate (`execute_tree.rs`'s `CapabilityNotHeld`) — it is
    // NOT authority to perform the victim's `Signature`-gated actions, as leg 1 proves.
    mallory
        .capabilities
        .grant(victim_id, AuthRequired::None)
        .unwrap();
    let mallory_id = mallory.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(victim).unwrap();
    ledger.insert_cell(mallory).unwrap();

    let hostile_effect = Effect::SetField {
        cell: victim_id,
        index: 4,
        value: [0x42; 32],
    };

    // ── LEG 1: the HONEST attempt is refused. Mallory signs with her OWN key; the cell
    //    requires VICTIM's. Proves the action is genuinely gated and the cap-graph gate
    //    is not what stops her.
    let mut honest_action = Action {
        target: victim_id,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![hostile_effect.clone()],
        may_delegate: DelegationMode::None,
        commitment_mode: dregg_turn::action::CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let msg = TurnExecutor::compute_signing_message(&honest_action, &LOCAL_FED, 0);
    let sig = sign(&mallory_sk, &msg).0;
    let mut r = [0u8; 32];
    let mut s = [0u8; 32];
    r.copy_from_slice(&sig[..32]);
    s.copy_from_slice(&sig[32..]);
    honest_action.authorization = Authorization::Signature(r, s);
    let mut honest_forest = CallForest::new();
    honest_forest.add_root(honest_action);
    let honest_turn = Turn {
        agent: mallory_id,
        nonce: 0,
        call_forest: honest_forest,
        fee: 0,
        memo: None,
        valid_until: Some(1_000),
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
    };
    let honest = executor().execute(&honest_turn, &mut ledger.clone());
    assert!(
        !honest.is_committed(),
        "SETUP INVALID: Mallory's own signature was accepted on a Signature-locked cell she \
         does not own — then leg 2 would prove nothing. Got: {honest:?}"
    );

    // ── LEG 2: the same action, wearing a self-signed handoff certificate from an
    //    introducer that exists nowhere.
    let ghost_sk = SigningKey::from_bytes(&[99u8; 32]);
    let ghost_pk = ghost_sk.public_key().0;
    assert!(
        ledger.cell_by_pubkey(&ghost_pk).is_none(),
        "the ghost introducer must hold NO cell in the ledger — that is the whole point"
    );

    let turn = captp_turn(
        mallory_id,
        victim_id,
        hostile_effect,
        0,
        &ghost_sk,                           // the ghost signs its own certificate
        dregg_captp::FederationId(ghost_pk), // canonical convention: FederationId == pk
        ghost_pk,
        &mallory_sk,
        mallory_pk,
        // EXACTLY the cell's floor, so §5b's `granted.is_narrower_or_equal(required)`
        // PASSES. The existing `adversary_amplifying_*` test grants the LOOSEST tier and
        // is caught by §5b; this one is not, which is why it needs its own falsifier.
        AuthRequired::Signature,
    );

    let result = executor().execute(&turn, &mut ledger.clone());
    let reason = rejection(&result).unwrap_or_else(|| {
        panic!(
            "⚑ AUTHORIZATION BYPASS: the executor COMMITTED a CapTpDelivered turn whose handoff \
             certificate was signed by a key holding NO cell and NO capability in this ledger. \
             The victim cell requires ITS OWNER's signature for set_state (leg 1 proved that); a \
             self-signed certificate that merely names the tier discharged it. Nothing on the \
             executor path binds introducer_pk to cert.introducer, consults a federation roster, \
             or looks up the introducer's held authority — dregg_captp::validate_handoff does all \
             three but is never reached from here."
        )
    });
    assert!(
        matches!(
            reason,
            dregg_turn::TurnError::CapTpIntroducerLacksCapability { .. }
        ),
        "the refusal must be the RIGHT refusal: the introducer holds no authority over the \
         target. Got a different variant, which means the turn was stopped by something other \
         than the property under test: {reason:?}"
    );
}

/// ⚑ FALSIFIER (A2) — **INTRODUCER IMPERSONATION (the executor-side twin of captp F-1).**
///
/// `dregg_captp::validate_handoff` closed this on 2026-07-25 (`560af5d40`) with an id↔pk
/// binding at `captp/src/handoff.rs:1005` and the `IntroducerKeyMismatch` variant. The
/// executor's parallel check was never given one: it verifies the certificate under a
/// **wire-supplied** `introducer_pk` and never asks whether that key is `cert.introducer`.
///
/// So Mallory signs a certificate with her OWN key while naming a reputable federation as
/// the `introducer`. The signature verifies (she really did sign it) and the delivery is
/// ATTRIBUTED — in the action hash, which commits `introducer_pk`, and in the receipt — to
/// a federation that never signed anything.
///
/// Note `node/src/mcp/handlers_delegate.rs:1072` asserts in a comment that "the executor
/// will reject when the override does not match the cert's `introducer.0`". No such
/// comparison exists; it rejects only when the SIGNATURE fails, which it does not here.
///
/// Refusal asserted BY VARIANT (`CapTpIntroducerKeyMismatch`), not merely "rejected".
#[test]
fn a2_captp_cert_naming_a_federation_that_did_not_sign_it_is_refused() {
    let victim_sk = SigningKey::from_bytes(&[33u8; 32]);
    let victim = cell_for(&victim_sk, 100, locked_permissions());
    let victim_id = victim.id();

    let mallory_sk = SigningKey::from_bytes(&[44u8; 32]);
    let mallory_pk = mallory_sk.public_key().0;
    let mut mallory = cell_for(&mallory_sk, 1_000, locked_permissions());
    // Give Mallory a GENUINE capability over the victim, so the ledger-grounding leg of
    // the fix is SATISFIED and the ONLY thing left to refuse her is the id↔pk binding.
    // Without this the test could pass for A1's reason and prove nothing about A2.
    mallory
        .capabilities
        .grant(victim_id, AuthRequired::Signature)
        .unwrap();
    let mallory_id = mallory.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(victim).unwrap();
    ledger.insert_cell(mallory).unwrap();

    // A reputable federation Mallory wants the delivery credited to. She does NOT have
    // its key — she signs with her own and merely NAMES it.
    let reputable = dregg_captp::FederationId([0xF1; 32]);
    assert_ne!(
        reputable.0, mallory_pk,
        "the impersonated federation must differ from the signer"
    );

    let turn = captp_turn(
        mallory_id,
        victim_id,
        Effect::SetField {
            cell: victim_id,
            index: 4,
            value: [0x77; 32],
        },
        0,
        &mallory_sk, // signs with HER key ...
        reputable,   // ... while naming a federation that never signed
        mallory_pk,  // and supplies her own pk, so the signature check PASSES
        &mallory_sk,
        mallory_pk,
        AuthRequired::Signature,
    );

    let result = executor().execute(&turn, &mut ledger.clone());
    let reason = rejection(&result).unwrap_or_else(|| {
        panic!(
            "⚑ IMPERSONATION ADMITTED: a certificate naming introducer={reputable:?} but signed \
             under an unrelated key, presented with the signer's own pk, was COMMITTED. The \
             receipt now attributes this delivery to a federation that never signed it."
        )
    });
    assert!(
        matches!(
            reason,
            dregg_turn::TurnError::CapTpIntroducerKeyMismatch { .. }
        ),
        "the refusal must name the UNBOUND KEY, not some incidental failure: {reason:?}"
    );
}

/// ⚑ POSITIVE POLE (A3) — an HONEST delegated handoff is still ADMITTED.
///
/// Alice genuinely holds a `Signature`-tier capability over the target cell, and
/// introduces Bob at an ATTENUATING tier. Every leg of the fix is satisfied: the cert's
/// `introducer` IS Alice's key (id↔pk bound), Alice's cell holds a real capability over
/// the target (ledger-grounded `held`), and `granted ≤ held`. This must COMMIT — a fix
/// that refuses this is over-rejecting, and the two falsifiers above would then be
/// passing vacuously.
#[test]
fn a3_honest_delegated_handoff_from_a_real_cap_holder_still_commits() {
    let owner_sk = SigningKey::from_bytes(&[55u8; 32]);
    let target = cell_for(&owner_sk, 100, locked_permissions());
    let target_id = target.id();

    // ALICE — the introducer. Holds a genuine `Signature`-tier cap over the target.
    let alice_sk = SigningKey::from_bytes(&[66u8; 32]);
    let alice_pk = alice_sk.public_key().0;
    let mut alice = cell_for(&alice_sk, 1_000, locked_permissions());
    alice
        .capabilities
        .grant(target_id, AuthRequired::Signature)
        .unwrap();

    // BOB — the recipient, and the turn's agent. Needs his own cap to clear the
    // cap-graph gate, exactly as the honest wire flow would leave him.
    let bob_sk = SigningKey::from_bytes(&[77u8; 32]);
    let bob_pk = bob_sk.public_key().0;
    let mut bob = cell_for(&bob_sk, 1_000, locked_permissions());
    bob.capabilities
        .grant(target_id, AuthRequired::Signature)
        .unwrap();
    let bob_id = bob.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(target).unwrap();
    ledger.insert_cell(alice).unwrap();
    ledger.insert_cell(bob).unwrap();

    let turn = captp_turn(
        bob_id,
        target_id,
        Effect::SetField {
            cell: target_id,
            index: 4,
            value: [0x01; 32],
        },
        0,
        &alice_sk,
        dregg_captp::FederationId(alice_pk), // id == pk: the canonical convention
        alice_pk,
        &bob_sk,
        bob_pk,
        AuthRequired::Signature, // granted == held: attenuating, not amplifying
    );

    let result = executor().execute(&turn, &mut ledger.clone());
    assert!(
        result.is_committed(),
        "REGRESSION: an HONEST handoff — introducer id bound to its key, introducer holding a \
         real capability over the target, granted == held — was REFUSED. The fix is \
         over-rejecting and the falsifiers above are passing vacuously. Got: {result:?}"
    );
}

/// ⚑ POSITIVE POLE (A4) — the CELL'S OWN OWNER may still introduce.
///
/// The owner of the target cell holds every authority over it without needing a c-list
/// entry pointing at itself. `has_access_including_delegation_at` already encodes this
/// (self-access is inherent); the fix must not lose it.
#[test]
fn a4_the_target_cells_own_owner_may_still_introduce_a_recipient() {
    let owner_sk = SigningKey::from_bytes(&[88u8; 32]);
    let owner_pk = owner_sk.public_key().0;
    let target = cell_for(&owner_sk, 100, locked_permissions());
    let target_id = target.id();

    let bob_sk = SigningKey::from_bytes(&[100u8; 32]);
    let bob_pk = bob_sk.public_key().0;
    let mut bob = cell_for(&bob_sk, 1_000, locked_permissions());
    bob.capabilities
        .grant(target_id, AuthRequired::Signature)
        .unwrap();
    let bob_id = bob.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(target).unwrap();
    ledger.insert_cell(bob).unwrap();

    let turn = captp_turn(
        bob_id,
        target_id,
        Effect::SetField {
            cell: target_id,
            index: 4,
            value: [0x02; 32],
        },
        0,
        &owner_sk,
        dregg_captp::FederationId(owner_pk),
        owner_pk,
        &bob_sk,
        bob_pk,
        AuthRequired::Signature,
    );

    let result = executor().execute(&turn, &mut ledger.clone());
    assert!(
        result.is_committed(),
        "REGRESSION: the target cell's OWN OWNER was refused as an introducer. Got: {result:?}"
    );
}
