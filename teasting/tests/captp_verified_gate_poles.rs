//! BOTH POLES of §6 handoff non-amplification, decided by the REAL verified Lean gate.
//!
//! # What this binary exists to stop
//!
//! `dregg_captp::validate_handoff` decides §6 non-amplification ONLY through the verified Lean
//! export `dregg_captp_validate_handoff` (= `Dregg2.Exec.CapTPConcrete.handoffNonAmplifyingC`);
//! the twin-deletion sweep (`e3f0e7b92`) deleted the hand-written Rust rights lattice from that
//! live decision. So there are exactly two ways for this suite's handoff tests to be worthless,
//! and they are opposite:
//!
//! * **No gate registered.** Every handoff is refused, including honest ones. That was the state
//!   of `dregg-teasting` until `tests/common/mod.rs` was added — `test_handoff_certificate_flow`
//!   and `test_byzantine_certificate_replay_rejected` failed on a first, honest,
//!   `granted == held` presentation, and nothing in the tree said why.
//! * **A permissive stand-in registered.** Every handoff is admitted, including amplifying ones.
//!   That is what `captp/tests/common/mod.rs`'s `AssumeNonAmplifyingGate` does deliberately — it
//!   answers `Some(true)` unconditionally — which is correct for tests probing OTHER properties of
//!   the handoff path and catastrophic if it ever leaked into a test probing THIS one.
//!
//! A suite that only ever proves refusals cannot tell the first from correct behaviour; a suite
//! that only ever proves admissions cannot tell the second. So this file asserts both directions
//! against the SAME installed gate, and asserts the SHAPE of each refusal, not merely that it is
//! an `Err`.
//!
//! # The two poles are not equally important
//!
//! A gate that starts accepting everything is worse than one that refuses everything: the second
//! is a dead vat, the first is a capability system that has stopped being one. The amplifying
//! poles below are the load-bearing half.
//!
//! # Anti-vacuity
//!
//! Every refusal here is asserted to be `Amplification` — the gate RAN and returned "amplifies" —
//! and explicitly NOT `VerifiedGateUnavailable`, which is what `validate_handoff` returns when it
//! could not decide at all. Without that distinction an amplification assertion passes for a suite
//! with no gate installed, which is exactly how `dregg-redteam`'s CapTP attack suites announced
//! `[ATTACK 2] permission amplification: DEFENDED` while the defence never ran. Deleting the
//! `install_verified_captp_gate()` call from this file turns all four amplifying poles red with
//! that name in the message, and the two admitting poles red as well.
//!
//! The gate is `dregg-exec-lean`'s Lean-backed implementation over the linked archive — the same
//! object `node/src/lib.rs::install_verified_distributed_gates` installs in production, not a
//! stand-in. An archive that lacks the export PANICS (`dregg_lean_ffi::demand_lean`) rather than
//! letting this file report `ok`.

use dregg_captp::sturdy::SwissTable;
use dregg_captp::{
    FederationId, HandoffCertificate, HandoffError, HandoffPresentation, validate_handoff,
};
use dregg_cell::{AuthRequired, EFFECT_EMIT_EVENT, EFFECT_TRANSFER, EffectMask};
use dregg_types::{CellId, generate_keypair};

mod common;

/// Drive one full handoff through the real entry point: the target's swiss table records `held`
/// (its authoritative record of what the introducer actually has), the certificate grants
/// `granted`, and `validate_handoff` runs every check including §6.
///
/// Returns `Ok(the granted permission the target resolved)` on admission.
fn run_handoff(
    held: AuthRequired,
    held_effects: Option<EffectMask>,
    granted: AuthRequired,
    granted_effects: Option<EffectMask>,
) -> Result<AuthRequired, HandoffError> {
    let (intro_sk, intro_pk) = generate_keypair();
    // The classical path binds id ↔ pk (F-1): a legacy ed25519 introducer id IS its pk.
    let intro_fed = FederationId(intro_pk.0);
    let (recip_sk, recip_pk) = generate_keypair();
    let target_fed = FederationId([0xDD; 32]);
    let target_cell = CellId([0xEE; 32]);

    let mut swiss_table = SwissTable::new();
    let swiss = swiss_table.export_with_options(target_cell, held, 100, None, held_effects, None);

    let cert = HandoffCertificate::create(
        &intro_sk,
        intro_fed,
        target_fed,
        target_cell,
        recip_pk.0,
        granted,
        granted_effects,
        None,
        None,
        swiss,
    );
    let presentation = HandoffPresentation::create(cert, &recip_sk);
    let known = vec![intro_fed];

    validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150)
        .map(|acceptance| acceptance.permissions)
}

/// Assert a handoff was REFUSED by a §6 verdict that actually ran.
///
/// The second assertion is the one that keeps this suite honest: `VerifiedGateUnavailable` is the
/// refusal `validate_handoff` returns when NO verified gate is registered, and it refuses every
/// handoff — attenuating, equal, and amplifying alike. Accepting it here would make each pole below
/// pass in a process where the amplification rule never executed.
fn assert_refused_as_amplification(outcome: Result<AuthRequired, HandoffError>, what: &str) {
    let err = match outcome {
        Err(e) => e,
        Ok(perm) => panic!(
            "SAFETY: {what} was ADMITTED (resolved permission {perm:?}). The verified §6 gate must \
             refuse a certificate granting more than the target's swiss entry records as held."
        ),
    };
    assert_ne!(
        err,
        HandoffError::VerifiedGateUnavailable,
        "ANTI-VACUITY: {what} was refused because §6 could not be DECIDED (no verified gate \
         registered in this process), not because the verified rule judged it amplifying. This \
         binary's refusals would then prove nothing about the amplification check — install the \
         gate via `common::install_verified_captp_gate()`."
    );
    assert_eq!(
        err,
        HandoffError::Amplification,
        "{what} must be refused as Amplification by the verified §6 verdict"
    );
}

// ===========================================================================
// POLE 1 — the HONEST presentation is ADMITTED
// ===========================================================================

/// `granted == held`: the introducer hands on exactly what it holds. Nothing is amplified, and the
/// verified rule must ADMIT it. This is the presentation the whole suite was failing on.
#[test]
fn equal_rights_handoff_is_admitted_by_the_verified_gate() {
    if !common::install_verified_captp_gate() {
        return;
    }
    let resolved = run_handoff(AuthRequired::Signature, None, AuthRequired::Signature, None)
        .expect("granted == held is not an amplification and must be ADMITTED");
    assert_eq!(resolved, AuthRequired::Signature);
}

/// Strict attenuation: the introducer holds `Either` (signature OR proof satisfies it) and hands on
/// the strictly narrower `Signature`. Admitted.
#[test]
fn attenuating_handoff_is_admitted_by_the_verified_gate() {
    if !common::install_verified_captp_gate() {
        return;
    }
    let resolved = run_handoff(AuthRequired::Either, None, AuthRequired::Signature, None)
        .expect("granted ⊂ held is an attenuation and must be ADMITTED");
    assert_eq!(resolved, AuthRequired::Signature);
}

/// Effect-facet attenuation: held `{transfer, emit}`, granted `{emit}` — a strict subset of the
/// effect mask. Admitted on both legs of the two-leg predicate.
#[test]
fn effect_mask_attenuating_handoff_is_admitted_by_the_verified_gate() {
    if !common::install_verified_captp_gate() {
        return;
    }
    run_handoff(
        AuthRequired::Signature,
        Some(EFFECT_TRANSFER | EFFECT_EMIT_EVENT),
        AuthRequired::Signature,
        Some(EFFECT_EMIT_EVENT),
    )
    .expect("a granted effect mask that is a subset of the held mask must be ADMITTED");
}

// ===========================================================================
// POLE 2 — the AMPLIFYING presentation is still REFUSED (the load-bearing half)
// ===========================================================================

/// The headline amplification: held `Signature`, granted `None`. `None` is a strictly EASIER
/// requirement to satisfy, i.e. strictly MORE authority — the introducer gifts an unauthenticated
/// cap over a signature-gated one. Refused (Lean `grant_none_over_nonnone_amplifies`).
#[test]
fn granting_none_over_held_signature_is_refused() {
    if !common::install_verified_captp_gate() {
        return;
    }
    assert_refused_as_amplification(
        run_handoff(AuthRequired::Signature, None, AuthRequired::None, None),
        "granting None over a held Signature",
    );
}

/// The extreme case: held `Impossible` (a locked cap the introducer can never exercise), granted
/// `Signature` — conjuring authority out of nothing. Refused (Lean
/// `grant_signature_over_impossible_amplifies`).
#[test]
fn granting_signature_over_held_impossible_is_refused() {
    if !common::install_verified_captp_gate() {
        return;
    }
    assert_refused_as_amplification(
        run_handoff(
            AuthRequired::Impossible,
            None,
            AuthRequired::Signature,
            None,
        ),
        "granting Signature over a held Impossible (locked) cap",
    );
}

/// Effect-facet amplification: held `{emit}`, granted `{transfer, emit}` — the certificate adds an
/// effect bit the introducer never held. The permission lattice leg PASSES here (Signature ⊆
/// Signature), so this pole is specifically the facet leg of the two-leg predicate.
#[test]
fn granting_a_superset_effect_mask_is_refused() {
    if !common::install_verified_captp_gate() {
        return;
    }
    assert_refused_as_amplification(
        run_handoff(
            AuthRequired::Signature,
            Some(EFFECT_EMIT_EVENT),
            AuthRequired::Signature,
            Some(EFFECT_TRANSFER | EFFECT_EMIT_EVENT),
        ),
        "granting an effect mask that adds a bit the introducer never held",
    );
}

/// The other facet-leg amplification, and the one an implementor is most likely to get backwards:
/// held is a RESTRICTED mask, granted is `None`. `None` means UNRESTRICTED (every effect), so the
/// absent field is the maximal grant, not the minimal one. Refused.
#[test]
fn granting_an_unrestricted_effect_mask_over_a_restricted_hold_is_refused() {
    if !common::install_verified_captp_gate() {
        return;
    }
    assert_refused_as_amplification(
        run_handoff(
            AuthRequired::Signature,
            Some(EFFECT_EMIT_EVENT),
            AuthRequired::Signature,
            None,
        ),
        "granting an unrestricted (None) effect mask over a restricted hold",
    );
}
