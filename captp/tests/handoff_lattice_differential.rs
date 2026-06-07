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
//! pair and asserts the accept/reject verdict matches the lattice — the negative tooth lands on
//! the actual admission path, not just the helper.

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

/// THE ADMISSION TOOTH: for every (held, granted) over the corpus, `validate_handoff` accepts
/// iff `granted.is_narrower_or_equal(held)` (the Lean-pinned lattice). An amplifying pair MUST
/// be rejected with `Amplification`; an attenuating pair MUST be accepted.
#[test]
fn validate_handoff_admission_matches_lattice_over_corpus() {
    let ps = probes();
    for held in &ps {
        for granted in &ps {
            let lattice_ok = granted.is_narrower_or_equal(held);
            let verdict = run_handoff(held.clone(), granted.clone());
            match (lattice_ok, &verdict) {
                (true, Ok(())) => {}
                (false, Err(HandoffError::Amplification)) => {}
                (true, Err(e)) => panic!(
                    "ATTENUATING handoff (granted={granted:?} ⊆ held={held:?}) was REJECTED ({e:?}); \
                     validate_handoff is stricter than the proven lattice"
                ),
                (false, Ok(())) => panic!(
                    "AMPLIFYING handoff (granted={granted:?} ⊄ held={held:?}) was ACCEPTED; \
                     NON-AMPLIFICATION BREACH — validate_handoff admits more than held"
                ),
                (false, Err(e)) => panic!(
                    "amplifying handoff (granted={granted:?}, held={held:?}) rejected with {e:?}, \
                     expected Amplification — wrong rejection reason masks the lattice check"
                ),
            }
        }
    }
}

/// Spot-check the headline amplification: granting `None` (unauthenticated) over a held
/// `Signature` is rejected as `Amplification` at the runtime entry point. Mirrors Lean
/// `grant_none_over_nonnone_amplifies`.
#[test]
fn grant_none_over_signature_rejected_at_runtime() {
    assert_eq!(
        run_handoff(AuthRequired::Signature, AuthRequired::None),
        Err(HandoffError::Amplification)
    );
}

/// Conjuring `Signature` from a held `Impossible` (locked cap) is rejected. Mirrors Lean
/// `grant_signature_over_impossible_amplifies`.
#[test]
fn grant_signature_over_impossible_rejected_at_runtime() {
    assert_eq!(
        run_handoff(AuthRequired::Impossible, AuthRequired::Signature),
        Err(HandoffError::Amplification)
    );
}
