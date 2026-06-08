//! HANDOFF-CERTIFICATE UNFORGEABILITY ⟷ LEAN DIFFERENTIAL — the trustless tooth across the FFI
//! gap for the captp Granovetter handoff.
//!
//! The Lean module `Dregg2/Exec/CapTPHandoffSound.lean` DE-VACUIFIES the opaque `attested : Prop`
//! of `Dregg2.Exec.CapTP.HandoffValid` into a concrete ed25519 signature seam over the
//! certificate's signing message (`Crypto.PortalFloor.SignatureKernel`), and PROVES two
//! properties of `validateHandoff2` (the Lean mirror of `validate_handoff`):
//!
//!   * THEOREM (1) `handoff_installs_exactly`: a validated handoff drives the VERIFIED full-state
//!     `validateHandoffA` executor to install EXACTLY the non-amplifying granted cap
//!     (`DelegateSpec`, all 17 kernel fields pinned). The accept side.
//!   * THEOREM (2) `adversary_cannot_forge_at_n_gt_1`: in an n>1 federation, an adversary lacking
//!     the introducer's signing key CANNOT produce a certificate that validates — under the
//!     ed25519 EUF-CMA carrier, validation entails `Signed introPK msg`, contradicting the
//!     adversary's lack of the key. The reject side (§1 introducer-signature check).
//!
//! This test drives the REAL `captp/src/handoff.rs::validate_handoff` and asserts the runtime
//! agrees:
//!   * the §1 introducer-signature check REJECTS a certificate verified against the WRONG public
//!     key (the adversary forged / re-keyed) with `InvalidIntroducerSignature` — Theorem 2's
//!     runtime tooth;
//!   * a tampered certificate (any signed field altered after signing) is REJECTED — the signing
//!     message binds every field, so re-binding requires the secret key;
//!   * the correctly-signed, attenuating certificate is ACCEPTED — Theorem 1's runtime tooth.
//!
//! The existing `handoff_lattice_differential.rs` already pins the §6 non-amplification lattice;
//! this file pins the §1 SIGNATURE / unforgeability leg that `CapTPHandoffSound.lean` adds.

use dregg_captp::{
    FederationId, HandoffCertificate, HandoffError, HandoffPresentation, SwissTable,
    validate_handoff,
};
use dregg_cell::AuthRequired;
use dregg_types::{CellId, generate_keypair};

/// Build a full, correctly-signed handoff and return the pieces needed to drive
/// `validate_handoff` (recipient presentation, the swiss table, and the introducer keypair /
/// federation id). `held`/`granted` permit exercising the accept and amplification paths.
fn build_handoff(
    held: AuthRequired,
    granted: AuthRequired,
) -> (
    HandoffPresentation,
    SwissTable,
    FederationId,
    dregg_types::PublicKey,
) {
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
    (presentation, swiss_table, intro_fed, intro_pk)
}

/// THEOREM (1) RUNTIME TOOTH — the accept side. A correctly-signed, attenuating (here equal)
/// certificate validates: `validate_handoff` returns `Ok`. This is the runtime witness that a
/// genuinely-signed handoff drives the (Lean-verified) install path. Mirrors Lean
/// `forged_handoff_rejected`'s positive twin (the `goodCert` validates).
#[test]
fn correctly_signed_handoff_is_accepted() {
    let (presentation, mut swiss_table, intro_fed, intro_pk) =
        build_handoff(AuthRequired::Signature, AuthRequired::Signature);
    let known = vec![intro_fed];
    let verdict = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 50);
    assert!(
        verdict.is_ok(),
        "a correctly-signed, non-amplifying handoff MUST validate (Theorem 1 accept side); got {verdict:?}"
    );
}

/// THEOREM (2) RUNTIME TOOTH — the unforgeability reject side. An adversary who does NOT hold
/// the introducer's signing key cannot make the handoff validate: verifying the certificate
/// against a DIFFERENT public key (the adversary's own, or any wrong key) is rejected at check
/// §1 with `InvalidIntroducerSignature`. This is the runtime witness for Lean
/// `adversary_cannot_forge_at_n_gt_1` — the certificate names a key, but only the holder of the
/// matching secret could have produced the signature `validate_handoff` checks.
#[test]
fn handoff_against_wrong_introducer_key_is_rejected() {
    let (presentation, mut swiss_table, intro_fed, _intro_pk) =
        build_handoff(AuthRequired::Signature, AuthRequired::Signature);

    // The adversary verifier presents a DIFFERENT introducer public key — they do not hold the
    // real introducer's secret, so the §1 signature check fails. (n>1: two distinct keys.)
    let (_adv_sk, adv_pk) = generate_keypair();
    assert_ne!(
        adv_pk.0, intro_fed.0,
        "test setup: adversary key must differ from the real introducer key (n>1)"
    );

    let known = vec![intro_fed];
    let verdict = validate_handoff(&presentation, &adv_pk, &mut swiss_table, &known, 50);
    assert_eq!(
        verdict.err(),
        Some(HandoffError::InvalidIntroducerSignature),
        "UNFORGEABILITY BREACH — a handoff verified against the WRONG introducer key was NOT \
         rejected with InvalidIntroducerSignature; an adversary lacking the introducer's secret \
         must not be able to validate (Lean adversary_cannot_forge_at_n_gt_1)"
    );
}

/// TAMPER TOOTH — the signing message binds EVERY signed field. If an adversary intercepts a
/// valid certificate and tampers with a signed field (here `target_cell`), the recomputed
/// signing message no longer matches the signature, so §1 rejects it. This is the runtime
/// witness that the de-vacuified `signingMessage` (Lean `HandoffCert2.signingMessage`) genuinely
/// covers the authority-bearing fields — a forged inflation cannot ride a stolen signature.
#[test]
fn tampered_certificate_field_breaks_signature() {
    let (mut presentation, mut swiss_table, intro_fed, intro_pk) =
        build_handoff(AuthRequired::Signature, AuthRequired::Signature);

    // Tamper with a signed field AFTER signing — the signature no longer covers the new bytes.
    presentation.certificate.target_cell = CellId([0xAB; 32]);

    let known = vec![intro_fed];
    let verdict = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 50);
    assert_eq!(
        verdict.err(),
        Some(HandoffError::InvalidIntroducerSignature),
        "TAMPER BREACH — altering a signed certificate field after signing was NOT rejected by \
         the §1 signature check; the signing message must bind every field (Lean signingMessage)"
    );
}

/// PERMISSION-TAMPER TOOTH — inflating the certificate's `permissions` after signing also breaks
/// the signature (the permission tag is in the signing message). So an adversary cannot both
/// escalate authority AND keep a valid signature: the §1 check fires BEFORE the §6 non-
/// amplification check even runs. Belt-and-suspenders with `handoff_lattice_differential.rs`.
#[test]
fn tampered_permissions_break_signature() {
    let (mut presentation, mut swiss_table, intro_fed, intro_pk) =
        build_handoff(AuthRequired::Signature, AuthRequired::Signature);

    // Inflate granted permissions from Signature to None (unauthenticated — an amplification) AFTER
    // signing. The §1 signature check must reject before §6 amplification is even reached.
    presentation.certificate.permissions = AuthRequired::None;

    let known = vec![intro_fed];
    let verdict = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 50);
    assert_eq!(
        verdict.err(),
        Some(HandoffError::InvalidIntroducerSignature),
        "an adversary inflated `permissions` after signing and the §1 signature check did NOT \
         reject it; the permission tag must be bound by the signing message"
    );
}
