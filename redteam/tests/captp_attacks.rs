//! Adversarial tests against CapTP: swiss-table confinement (Lean B1 /
//! `Exec/CapTP` confinement), handoff non-amplification (Lean
//! `handoff_non_amplifying` / B3), handoff unforgeability (B2), and a
//! resource-griefing finding on the validation ordering.
//!
//! Adversary model: a "malicious agent holding a (weaker) capability" who tries
//! to amplify it, plus a network attacker who intercepts a handoff certificate.

use dregg_captp::handoff::{
    validate_handoff, HandoffCertificate, HandoffError, HandoffPresentation,
};
use dregg_captp::sturdy::{EnlivenError, SwissTable};
use dregg_cell::AuthRequired;
use dregg_redteam::{flip_bit, mint_dalek_keypair, AttackOutcome};
use dregg_types::{generate_keypair, CellId, FederationId, SigningKey};

// --- shared scenario builders ----------------------------------------------

fn introducer() -> (SigningKey, FederationId) {
    let (sk, pk) = generate_keypair();
    (sk, FederationId(pk.0))
}

/// Build a target swiss table with the introducer holding `held` authority on
/// `cell` and return (swiss, target_cell, target_fed).
fn target_with_held(
    table: &mut SwissTable,
    held: AuthRequired,
    held_effects: Option<u32>,
) -> ([u8; 32], CellId, FederationId) {
    let target_cell = CellId([0xEE; 32]);
    let target_fed = FederationId([0xDD; 32]);
    let swiss = table.export_with_options(target_cell, held, 100, None, held_effects, None);
    (swiss, target_cell, target_fed)
}

// ===========================================================================
// ATTACK 1 — confinement: enliven a cap WITHOUT the swiss number (B1)
// Lean claims: a cap is unreachable without its 256-bit bearer secret.
// ===========================================================================

#[test]
fn attack_confinement_guess_swiss_number_is_rejected() {
    let mut table = SwissTable::new();
    let real = table.export(CellId([1; 32]), AuthRequired::Signature, 100, None);

    // Adversary guesses: all-zeros, all-ones, bit-flips of a leaked URI prefix.
    let mut guesses: Vec<[u8; 32]> = vec![[0u8; 32], [0xff; 32]];
    for byte in 0..32 {
        for bit in 0..8 {
            let mut g = real;
            flip_bit(&mut g, byte, bit);
            guesses.push(g); // a single-bit-different swiss number
        }
    }

    let mut any_break = AttackOutcome::Defended;
    for g in &guesses {
        if *g == real {
            continue;
        }
        if table.enliven(g, 100).is_ok() {
            any_break = AttackOutcome::Broken;
        }
    }
    // EVIDENCE: no near-miss guess enlivens. Confinement = entropy of the secret.
    assert_eq!(any_break, AttackOutcome::Defended);
    // Sanity: the *real* secret still works (the table is not just always-deny).
    assert!(table.enliven(&real, 100).is_ok());
    eprintln!(
        "[ATTACK 1] confinement vs {} guesses: {}",
        guesses.len(),
        any_break
    );
}

// ===========================================================================
// ATTACK 2 — non-amplification: granted MORE than held (B3 / Granovetter)
// Lean `handoff_non_amplifying`: granted.rights ≤ held.rights (where held is
// the target's authoritative swiss entry, NOT the cert's self-asserted field).
// ===========================================================================

#[test]
fn attack_amplify_permissions_is_rejected() {
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = dregg_types::PublicKey(intro_fed.0);
    let (recip_sk, recip_pk) = generate_keypair();

    let mut table = SwissTable::new();
    // The introducer only HOLDS `Signature` on the cell...
    let (swiss, target_cell, target_fed) =
        target_with_held(&mut table, AuthRequired::Signature, None);

    // ...but forges a cert claiming to GRANT `None` (strictly weaker requirement
    // = strictly MORE authority; an amplification).
    let cert = HandoffCertificate::create(
        &intro_sk,
        intro_fed,
        target_fed,
        target_cell,
        recip_pk.0,
        AuthRequired::None, // <-- amplification: easier-to-satisfy than held Signature
        None,
        None,
        None,
        swiss,
    );
    let pres = HandoffPresentation::create(cert, &recip_sk);

    let res = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 100);
    // EVIDENCE: the target reads `held` from its OWN swiss entry and rejects.
    assert_eq!(res.err(), Some(HandoffError::Amplification));
    eprintln!(
        "[ATTACK 2] permission amplification: {}",
        AttackOutcome::Defended
    );
}

#[test]
fn attack_amplify_effect_mask_is_rejected() {
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = dregg_types::PublicKey(intro_fed.0);
    let (recip_sk, recip_pk) = generate_keypair();

    let mut table = SwissTable::new();
    // Held: only effect bits 0b0011.
    let (swiss, target_cell, target_fed) =
        target_with_held(&mut table, AuthRequired::Signature, Some(0b0011));

    // Grant a SUPERSET 0b1111 (adds bits 2,3 the introducer never held).
    let cert = HandoffCertificate::create(
        &intro_sk,
        intro_fed,
        target_fed,
        target_cell,
        recip_pk.0,
        AuthRequired::Signature,
        Some(0b1111),
        None,
        None,
        swiss,
    );
    let pres = HandoffPresentation::create(cert, &recip_sk);
    let res = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 100);
    assert_eq!(res.err(), Some(HandoffError::Amplification));

    // Also: held restricted, grant `None` (= unrestricted = all effects) → amplify.
    let mut table2 = SwissTable::new();
    let (swiss2, tc2, tf2) = target_with_held(&mut table2, AuthRequired::Signature, Some(0b0011));
    let cert2 = HandoffCertificate::create(
        &intro_sk,
        intro_fed,
        tf2,
        tc2,
        recip_pk.0,
        AuthRequired::Signature,
        None,
        None,
        None,
        swiss2,
    );
    let pres2 = HandoffPresentation::create(cert2, &recip_sk);
    let res2 = validate_handoff(&pres2, &intro_pk, &mut table2, &[intro_fed], 100);
    assert_eq!(res2.err(), Some(HandoffError::Amplification));
    eprintln!(
        "[ATTACK 2b] effect-mask amplification (both forms): {}",
        AttackOutcome::Defended
    );
}

// ===========================================================================
// ATTACK 3 — unforgeability: forge / tamper the introducer signature (B2)
// ===========================================================================

#[test]
fn attack_forge_introducer_signature_is_rejected() {
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = dregg_types::PublicKey(intro_fed.0);
    let (recip_sk, recip_pk) = generate_keypair();

    let mut table = SwissTable::new();
    let (swiss, target_cell, target_fed) =
        target_with_held(&mut table, AuthRequired::Signature, None);

    let mut cert = HandoffCertificate::create(
        &intro_sk,
        intro_fed,
        target_fed,
        target_cell,
        recip_pk.0,
        AuthRequired::Signature,
        None,
        None,
        None,
        swiss,
    );
    // Tamper a content field AFTER signing (target_cell) — sig no longer covers it.
    cert.target_cell = CellId([0x99; 32]);
    let pres = HandoffPresentation::create(cert, &recip_sk);
    let res = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 100);
    assert_eq!(res.err(), Some(HandoffError::InvalidIntroducerSignature));
    eprintln!(
        "[ATTACK 3] post-sign field tamper: {}",
        AttackOutcome::Defended
    );
}

#[test]
fn attack_intercept_cert_present_as_wrong_recipient_is_rejected() {
    // Network attacker intercepts a cert in transit and tries to present it as
    // themselves (they do NOT own recipient_pk).
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = dregg_types::PublicKey(intro_fed.0);
    let (_legit_recip_sk, legit_recip_pk) = generate_keypair();
    let (attacker_sk, _attacker_pk) = generate_keypair();

    let mut table = SwissTable::new();
    let (swiss, target_cell, target_fed) =
        target_with_held(&mut table, AuthRequired::Signature, None);

    let cert = HandoffCertificate::create(
        &intro_sk,
        intro_fed,
        target_fed,
        target_cell,
        legit_recip_pk.0,
        AuthRequired::Signature,
        None,
        None,
        None,
        swiss,
    );
    // Attacker signs the presentation with THEIR key, not legit_recip's.
    let pres = HandoffPresentation::create(cert, &attacker_sk);
    let res = validate_handoff(&pres, &intro_pk, &mut table, &[intro_fed], 100);
    assert_eq!(res.err(), Some(HandoffError::InvalidRecipientSignature));
    eprintln!(
        "[ATTACK 3b] cert-interception replay: {}",
        AttackOutcome::Defended
    );
}

// ===========================================================================
// ATTACK 4 — DEFENDED (F-2 CLOSED): validate_handoff now validates the swiss
// number READ-ONLY (`SwissTable::check`) and consumes a use (`enliven`) ONLY on
// the success path, AFTER every rejecting check (amplification, target binding)
// has passed. So an attacker presenting an amplifying cert against a known swiss
// number is rejected WITHOUT burning a use of the introducer's budget — the
// resource-griefing / DoS vector is closed.
//
// This test was the F-2 FINDING (asserting the griefed-out state). It is now
// FLIPPED to assert the DEFENDED outcome: after the rejected amplifying
// presentation, the one-shot swiss entry is UNTOUCHED, and the legitimate
// recipient's later valid handoff SUCCEEDS.
// ===========================================================================

#[test]
fn finding_amplifying_handoff_consumes_a_use_on_rejection() {
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = dregg_types::PublicKey(intro_fed.0);
    let (recip_sk, recip_pk) = generate_keypair();

    let mut table = SwissTable::new();
    let target_cell = CellId([0xEE; 32]);
    let target_fed = FederationId([0xDD; 32]);
    // The introducer registered a swiss entry with max_uses = 1 (single handoff).
    let swiss = table.export_with_options(
        target_cell,
        AuthRequired::Signature,
        100,
        None,
        None,
        Some(1), // <-- one-shot
    );

    // Attacker presents an AMPLIFYING cert. It is rejected for amplification, and
    // (F-2 fix) the read-only `check` path does NOT enliven, so the swiss entry's
    // use_count stays at 0.
    let bad_cert = HandoffCertificate::create(
        &intro_sk,
        intro_fed,
        target_fed,
        target_cell,
        recip_pk.0,
        AuthRequired::None, // amplifies
        None,
        None,
        None,
        swiss,
    );
    let bad_pres = HandoffPresentation::create(bad_cert, &recip_sk);
    let bad = validate_handoff(&bad_pres, &intro_pk, &mut table, &[intro_fed], 100);
    assert_eq!(bad.err(), Some(HandoffError::Amplification));

    // EVIDENCE the use was NOT consumed: peek the entry — use_count is still 0.
    assert_eq!(
        table
            .peek(&swiss)
            .expect("swiss entry must survive a rejected presentation")
            .use_count,
        0,
        "a rejected (amplifying) presentation must NOT advance the swiss use budget"
    );

    // Now the LEGITIMATE recipient presents a valid (non-amplifying) cert.
    // Because the rejected attacker did NOT burn the single use, the honest
    // handoff SUCCEEDS — the cap is no longer griefable on the reject path.
    let good_cert = HandoffCertificate::create(
        &intro_sk,
        intro_fed,
        target_fed,
        target_cell,
        recip_pk.0,
        AuthRequired::Signature, // legitimate, non-amplifying
        None,
        None,
        None,
        swiss,
    );
    let good_pres = HandoffPresentation::create(good_cert, &recip_sk);
    let good = validate_handoff(&good_pres, &intro_pk, &mut table, &[intro_fed], 100);

    // DEFENDED: the honest handoff is accepted; the griefing attack failed.
    let acceptance =
        good.expect("honest one-shot handoff must succeed after a rejected amplifying attempt");
    assert_eq!(acceptance.cell_id, target_cell);
    assert_eq!(acceptance.permissions, AuthRequired::Signature);

    // And NOW the single use is spent (the success path enlivened).
    assert_eq!(
        table.peek(&swiss).expect("entry present").use_count,
        1,
        "the success path must consume exactly the one legitimate use"
    );
    eprintln!(
        "[ATTACK 4 / DEFENDED] amplifying-cert rejection no longer consumes a use (F-2 closed): {}",
        AttackOutcome::Defended
    );
}

// ===========================================================================
// ATTACK 5 — DEFENDED (F-3 CLOSED): the EnlivenError taxonomy was a membership
// ORACLE — enliven distinguishes NotFound (absent) from Expired/ExhaustedUses
// (present-but-dead), so a prober could learn whether a guessed 32-byte value is
// a known-but-dead swiss number vs truly unknown.
//
// FIX: the network boundary now collapses every enliven rejection to a single
// opaque message (`EnlivenError::opaque_message()` == "denied"). The rich
// taxonomy survives ONLY for local diagnostics that never cross the wire. This
// test now attacks the BOUNDARY representation a remote caller actually sees and
// asserts it is INDISTINGUISHABLE across present-but-dead vs absent.
// ===========================================================================

#[test]
fn finding_enliven_error_taxonomy_is_a_membership_oracle() {
    let mut table = SwissTable::new();
    // An EXPIRED entry (still present in the table).
    let present_expired = table.export(CellId([7; 32]), AuthRequired::Signature, 10, Some(20));
    let absent = [0x55u8; 32];

    let on_present = table.enliven(&present_expired, 999).unwrap_err(); // Expired (locally)
    let on_absent = table.enliven(&absent, 999).unwrap_err(); // NotFound (locally)

    // The LOCAL taxonomy still differs — that is fine, it never leaves the node.
    // What the ATTACKER sees is the BOUNDARY message, which both map to. That is
    // the surface F-3 closes: the two cases are now indistinguishable on the wire.
    let boundary_present = on_present.to_boundary_message();
    let boundary_absent = on_absent.to_boundary_message();

    // DEFENDED: the boundary representation is IDENTICAL — no membership oracle.
    assert_eq!(boundary_present, boundary_absent);
    assert_eq!(boundary_present, EnlivenError::opaque_message());
    assert_eq!(boundary_present, "denied");
    // And it does NOT echo which arm fired (no "found"/"expired"/"exhausted" tell).
    assert!(!boundary_present.contains("found"));
    assert!(!boundary_present.contains("expired"));
    assert!(!boundary_present.contains("exhausted"));
    eprintln!(
        "[ATTACK 5 / DEFENDED] enliven boundary error is opaque present-vs-absent (F-3 closed): {}",
        AttackOutcome::Defended
    );
}

// ===========================================================================
// ATTACK 6 — untrusted introducer (B2 trust path): a validly-signed cert from
// a federation NOT in known_federations must be rejected.
// ===========================================================================

#[test]
fn attack_untrusted_introducer_is_rejected() {
    let (intro_sk, intro_fed) = introducer();
    let intro_pk = dregg_types::PublicKey(intro_fed.0);
    let (recip_sk, recip_pk) = generate_keypair();
    let mut table = SwissTable::new();
    let (swiss, target_cell, target_fed) =
        target_with_held(&mut table, AuthRequired::Signature, None);

    let cert = HandoffCertificate::create(
        &intro_sk,
        intro_fed,
        target_fed,
        target_cell,
        recip_pk.0,
        AuthRequired::Signature,
        None,
        None,
        None,
        swiss,
    );
    let pres = HandoffPresentation::create(cert, &recip_sk);
    // known_federations is EMPTY: even a perfectly valid signature is untrusted.
    let res = validate_handoff(&pres, &intro_pk, &mut table, &[], 100);
    assert_eq!(res.err(), Some(HandoffError::UntrustedIntroducer));

    // BUT NOTE: the trust check is step 3, AFTER signature verification but the
    // amplification/enliven side effects are step 5. UntrustedIntroducer fires
    // before enliven, so this path does NOT grief the use budget. Good.
    let _ = mint_dalek_keypair; // (silence unused import on some toolchains)
    eprintln!(
        "[ATTACK 6] untrusted introducer: {}",
        AttackOutcome::Defended
    );
}
