//! HANDOFF NON-AMPLIFICATION ⟷ LEAN DIFFERENTIAL — the drift-catching tooth across the FFI
//! gap for the captp Granovetter non-amplification check.
//!
//! `captp/src/handoff.rs::validate_handoff` decides cross-vat non-amplification (granted ⊆
//! held) on the CONCRETE `AuthRequired` rights lattice via `AuthRequired::is_narrower_or_equal`
//! plus the `u32` effect-mask subset (`is_facet_attenuation`). The Lean
//! `Dregg2.Exec.CapTP.handoff_non_amplifying` proves `granted ≤ held` — but ABSTRACTLY, over
//! any order. `Dregg2/Exec/CapTPConcrete.lean` now pins the CONCRETE lattice: it defines
//! `authNarrowerOrEqual` mirroring this Rust method clause-for-clause, PROVES it is a genuine
//! bounded meet-semilattice (so the abstract keystone instantiates at the concrete carrier —
//! `handoff_non_amplifying_concrete`), and emits a `#guard`-PINNED 49-bit `decisionTable`.
//!
//! This test reconstructs the IDENTICAL 49-bit table from the Rust `is_narrower_or_equal` over
//! the SAME 7-variant corpus and asserts it equals `LEAN_DECISION_TABLE` — the literal copied
//! from the Lean `#guard`. A drift on EITHER side fails:
//!   * change the Rust lattice  → the reconstructed Rust table ≠ `LEAN_DECISION_TABLE`  → FAIL;
//!   * change the Lean lattice   → its `#guard decisionTable == [...]` trips at Lean build, AND
//!     someone must edit `LEAN_DECISION_TABLE` here to match, re-exposing any Rust drift.
//!
//! It ALSO drives the FULL runtime entry point (`validate_handoff`) over every (held, granted)
//! pair. Since `validate_handoff`'s §6 verdict now comes ONLY from the verified Lean gate (the
//! hand-written Rust lattice was deleted from the live path) and this binary registers NO gate, that
//! runtime tooth asserts `validate_handoff` FAILS CLOSED — refuses every pair, including attenuating
//! pairs the old Rust fallback would have admitted.
//!
//! ⚠ **What this binary can and cannot see.** A gate-less process refuses every handoff, so a
//! refusal HERE is not evidence about the amplification rule: it is returned identically for an
//! attenuating pair. `validate_handoff` now names that case `HandoffError::VerifiedGateUnavailable`
//! rather than `Amplification`, and the runtime tooth below asserts that exact variant — which is
//! strictly more than it asserted before, because "refused for want of a checker" and "refused by
//! the checker" are no longer the same observation. Two tests here that used to assert
//! `Amplification` for the headline amplifying pairs were reading the fail-closed refusal and would
//! have passed with the rule deleted; they are renamed to claim only what a gate-less binary can
//! establish. The ADMIT-IFF-LATTICE decision is pinned Rust↔Lean by the two pure teeth here, and
//! both runtime poles over a linked archive — attenuating ADMITTED, amplifying REFUSED as
//! `Amplification` — are proved in `teasting/tests/captp_verified_gate_poles.rs`,
//! `node/src/captp_handoff_e2e.rs`, and `dregg-redteam`'s CapTP attack suites.

use dregg_captp::{
    FederationId, HandoffCertificate, HandoffError, HandoffPresentation, SwissTable,
    validate_handoff,
};
use dregg_cell::{AuthRequired, EFFECT_EMIT_EVENT, EFFECT_TRANSFER, is_facet_attenuation};
use dregg_types::{CellId, generate_keypair};

/// The 7 probe variants, in the SAME order as Lean `CapTPConcrete.probes`:
/// none, signature, proof, either, impossible, custom 7, custom 9.
fn probes() -> Vec<AuthRequired> {
    let mut c7 = [0u8; 32];
    c7[0] = 7;
    let mut c9 = [0u8; 32];
    c9[0] = 9;
    vec![
        AuthRequired::None,
        AuthRequired::Signature,
        AuthRequired::Proof,
        AuthRequired::Either,
        AuthRequired::Impossible,
        AuthRequired::Custom { vk_hash: c7 },
        AuthRequired::Custom { vk_hash: c9 },
    ]
}

/// The PINNED 49-bit truth table, copied VERBATIM from the Lean
/// `Dregg2.Exec.CapTPConcrete.decisionTable` `#guard`. Row-major over `probes × probes`:
/// entry[i*7 + j] = `authNarrowerOrEqual probes[i] probes[j]` = "probes[i] is narrower-or-equal
/// to probes[j]".
#[rustfmt::skip]
const LEAN_DECISION_TABLE: [bool; 49] = [
    //          n      sig    prf    eit    imp    c7     c9
    /* none */  true,  false, false, false, false, false, false,
    /* sig  */  true,  true,  false, true,  false, false, false,
    /* prf  */  true,  false, true,  true,  false, false, false,
    /* eit  */  true,  false, false, true,  false, false, false,
    /* imp  */  true,  true,  true,  true,  true,  true,  true,
    /* c7   */  true,  false, false, false, false, true,  false,
    /* c9   */  true,  false, false, false, false, false, true,
];

/// THE LATTICE TOOTH: the Rust `is_narrower_or_equal` decision over the corpus must equal the
/// Lean-pinned table exactly. Drift in either lattice is caught here.
#[test]
fn rust_is_narrower_or_equal_matches_lean_decision_table() {
    let ps = probes();
    let mut rust_table = Vec::with_capacity(49);
    for a in &ps {
        for b in &ps {
            rust_table.push(a.is_narrower_or_equal(b));
        }
    }
    assert_eq!(
        rust_table.as_slice(),
        &LEAN_DECISION_TABLE[..],
        "Rust AuthRequired::is_narrower_or_equal DRIFTED from the proven Lean \
         CapTPConcrete.decisionTable. Either the Rust rights lattice changed (a possible \
         amplification loophole) or the Lean order proof changed. Reconcile both."
    );
}

/// Effect-mask facet leg: `is_facet_attenuation` mirrors Lean `facetAttenuation` (bitwise
/// subset). Pin the load-bearing rows.
#[test]
fn rust_facet_attenuation_matches_lean() {
    // {transfer,emit} ⊇ {emit}: attenuating.
    assert!(is_facet_attenuation(
        EFFECT_TRANSFER | EFFECT_EMIT_EVENT,
        EFFECT_EMIT_EVENT
    ));
    // {emit} ⊉ {transfer,emit}: amplifying.
    assert!(!is_facet_attenuation(
        EFFECT_EMIT_EVENT,
        EFFECT_TRANSFER | EFFECT_EMIT_EVENT
    ));
    // self-attenuation.
    assert!(is_facet_attenuation(EFFECT_TRANSFER, EFFECT_TRANSFER));
    // empty (deny-all) child attenuates anything.
    assert!(is_facet_attenuation(EFFECT_TRANSFER, 0));
}

// ---------------------------------------------------------------------------
// THE RUNTIME-ENTRY-POINT TOOTH: every (held, granted) pair, driven through the FULL
// `validate_handoff`, must accept iff the lattice says granted ⊆ held.
// ---------------------------------------------------------------------------

/// Run a full handoff with `held` registered at the swiss entry and `granted` on the cert.
/// Returns `Ok(())` if `validate_handoff` accepts, `Err(HandoffError)` otherwise.
fn run_handoff(held: AuthRequired, granted: AuthRequired) -> Result<(), HandoffError> {
    let (intro_sk, intro_pk) = generate_keypair();
    let intro_fed = FederationId(intro_pk.0);
    let (recip_sk, recip_pk) = generate_keypair();
    let target_fed = FederationId([0xDD; 32]);
    let target_cell = CellId([0xEE; 32]);

    let mut swiss_table = SwissTable::new();
    let swiss = swiss_table.export_with_options(target_cell, held, 100, None, None, None);

    let cert = HandoffCertificate::create(
        &intro_sk,
        intro_fed,
        target_fed,
        target_cell,
        recip_pk.0,
        granted,
        None,
        None,
        None,
        swiss,
    );
    let presentation = HandoffPresentation::create(cert, &recip_sk);
    let known = vec![intro_fed];
    validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150).map(|_| ())
}

/// THE FAIL-CLOSED TOOTH: `validate_handoff`'s §6 non-amplification verdict now comes ONLY from the
/// verified Lean gate (`dregg_captp_validate_handoff`); the hand-written Rust rights lattice was
/// deleted from the live path. With NO verified gate registered — the state of this test binary —
/// `validate_handoff` FAILS CLOSED at §6: EVERY handoff over the corpus, attenuating AND amplifying,
/// is REFUSED. In particular a legitimately ATTENUATING handoff (which the deleted Rust fallback
/// would have admitted) is refused, proving the twin is gone from the live path.
///
/// The refusal must be `VerifiedGateUnavailable`, NOT `Amplification`. That is the whole content of
/// the fail-closed posture: the handoff is turned away because the check could not RUN, and a
/// validator that reports it as an amplification attempt is accusing an honest presenter of the
/// receiver's own misconfiguration. Asserting the exact variant is also what stops this file from
/// laundering "no gate here" into evidence about the amplification rule — the two pure teeth above
/// pin the Rust↔Lean lattice agreement, and the runtime ADMIT/REFUSE poles over a linked archive
/// live in `teasting/tests/captp_verified_gate_poles.rs`.
#[test]
fn validate_handoff_fails_closed_over_corpus_without_gate() {
    let ps = probes();
    for held in &ps {
        for granted in &ps {
            let verdict = run_handoff(held.clone(), granted.clone());
            assert_eq!(
                verdict,
                Err(HandoffError::VerifiedGateUnavailable),
                "without the verified gate, validate_handoff must FAIL CLOSED and say WHY — \
                 held={held:?} granted={granted:?}; including attenuating pairs the deleted Rust \
                 lattice would have admitted, and never blaming the presenter with Amplification"
            );
        }
    }
}

/// The headline amplification — granting `None` (unauthenticated) over a held `Signature` (Lean
/// `grant_none_over_nonnone_amplifies`) — does not slip through the runtime entry point.
///
/// ⚠ Read the assertion, not the scenario. This binary registers no gate, so the refusal observed
/// here is `VerifiedGateUnavailable` and is returned for EVERY pair; it establishes only that the
/// amplifying handoff is not admitted, which is a fortiori true when nothing is admitted. It is NOT
/// evidence that the non-amplification rule rejected this pair — that claim needs a process where
/// attenuating pairs are admitted, and it is proved over the real Lean gate by
/// `teasting/tests/captp_verified_gate_poles.rs::granting_none_over_held_signature_is_refused`.
/// (This test asserted `Amplification` until the variant split made the difference visible; it was
/// green with the rule deleted.)
#[test]
fn grant_none_over_signature_not_admitted_at_runtime() {
    assert_eq!(
        run_handoff(AuthRequired::Signature, AuthRequired::None),
        Err(HandoffError::VerifiedGateUnavailable)
    );
}

/// Conjuring `Signature` from a held `Impossible` (locked cap) does not slip through either (Lean
/// `grant_signature_over_impossible_amplifies`). Same caveat as above: without a gate this is the
/// fail-closed refusal, and the rule-decided refusal is proved in
/// `teasting/tests/captp_verified_gate_poles.rs::granting_signature_over_held_impossible_is_refused`.
#[test]
fn grant_signature_over_impossible_not_admitted_at_runtime() {
    assert_eq!(
        run_handoff(AuthRequired::Impossible, AuthRequired::Signature),
        Err(HandoffError::VerifiedGateUnavailable)
    );
}
