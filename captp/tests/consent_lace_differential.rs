//! CONSENT-LACE SETTLEMENT ⟷ LEAN DIFFERENTIAL — the drift-catching tooth across the FFI gap
//! for multi-party signed-consent settlement.
//!
//! `Dregg2/Exec/CapTPConsentLace.lean` is a FAITHFUL, EXECUTABLE Lean model of multi-party
//! suspended settlement whose distributed-authorization exchange is carried as a SIGNED BLOCKLACE:
//! a party's consent over a suspended batch is a present, `signed`-true `Block` authored by that
//! party over the batch digest. It proves, kernel-clean (#assert_axioms ⊆ {propext,
//! Classical.choice, Quot.sound}):
//!
//!   * consent-binding — `settle_requires_signed_authorship`: a batch settles ONLY if EVERY
//!     required party has a present, signed, self-authored APPROVE consent over the batch digest;
//!     an unsigned / wrong-author / wrong-digest consent does NOT count
//!     (`unsigned_does_not_count`, `wrong_author_does_not_count`, `wrong_digest_does_not_count`);
//!   * no-amplification (`laceSettle_preserves_caps`), atomic-settle-or-nothing
//!     (`laceSettle_atomic_aborts_on_unauthorized`) over the verified executor drain;
//!   * equivocation repels — a party that signs a conflicting approve+revoke consent fork is a
//!     DETECTABLE blocklace equivocator and is blocked (`equivocating_party_blocks_settlement`).
//!
//! This test reconstructs the consent-binding decision (`isApprovalFor`) and the n-ary convergence
//! gate (`consentLaceComplete`) with a clause-for-clause Rust mirror and asserts the verdicts equal
//! the `LEAN_*` golden vectors copied VERBATIM from the Lean `#guard`s in §9.1 of that module. A
//! drift on EITHER side fails:
//!   * change the Lean decision → its `#guard` trips at Lean build, AND someone must edit a
//!     `LEAN_*` constant here to match, re-exposing any Rust drift;
//!   * change the Rust mirror   → its `assert_eq!` against `LEAN_*` trips.
//!
//! NOTE on scope (honest): the captp crate does not yet ship a native `consent_lace_settle`
//! entry point — the Lean module IS the reference for this protocol surface. So this differential
//! is a SHARED-LOGIC pin (the same shape as `blocklace/tests/membership_safety_differential.rs`
//! pinning the constitution golden vectors): the Rust mirror below is the executable contract the
//! eventual `captp` runtime path must satisfy, and it is asserted equal to the verified Lean rule.

/// A consent block, mirroring `Dregg2.Authority.Blocklace.Block` stripped to the fields the
/// consent-binding decision reads: `creator` (authorship), `seq` (the batch digest signed over),
/// `signed` (the §8 Ed25519 discharge), and `preds` (carrying the approve/revoke marker).
#[derive(Clone)]
struct ConsentBlock {
    creator: u64,
    seq: u64, // the batch digest
    signed: bool,
    preds: Vec<u64>, // carries APPROVE_MARK or REVOKE_MARK
}

const APPROVE_MARK: u64 = 0xA;
const REVOKE_MARK: u64 = 0xB;

#[derive(Clone, Copy)]
enum Kind {
    Approve,
    Revoke,
}

/// Mirror of `Dregg2.Exec.CapTPConsentLace.consentBlock`: a signed, self-authored consent over a
/// digest asserting a kind.
fn consent_block(party: u64, digest: u64, kind: Kind) -> ConsentBlock {
    ConsentBlock {
        creator: party,
        seq: digest,
        signed: true,
        preds: vec![match kind {
            Kind::Approve => APPROVE_MARK,
            Kind::Revoke => REVOKE_MARK,
        }],
    }
}

/// Mirror of `Dregg2.Exec.CapTPConsentLace.isApprovalFor`, clause-for-clause:
/// `(creator == party) && signed && (seq == digest) && (APPROVE_MARK ∈ preds)`.
fn is_approval_for(b: &ConsentBlock, party: u64, digest: u64) -> bool {
    (b.creator == party) && b.signed && (b.seq == digest) && b.preds.contains(&APPROVE_MARK)
}

/// Mirror of `partySignedConsent`: EXISTS a block in the lace that `is_approval_for`.
fn party_signed_consent(lace: &[ConsentBlock], party: u64, digest: u64) -> bool {
    lace.iter().any(|b| is_approval_for(b, party, digest))
}

/// Mirror of `consentLaceComplete`: EVERY required party has a signed self-authored consent.
fn consent_lace_complete(lace: &[ConsentBlock], parties: &[u64], digest: u64) -> bool {
    parties.iter().all(|&p| party_signed_consent(lace, p, digest))
}

// ───────────────────────── GOLDEN VECTORS (copied from Lean §9.1 `#guard`s) ─────────────────────

/// `#guard (diffCorpus.map (fun b => isApprovalFor b 7 42)) == [true, false, false, false, false]`
const LEAN_IS_APPROVAL_FOR: [bool; 5] = [true, false, false, false, false];

/// `#guard ([7,8,9].map (fun p => partySignedConsent demoLaceMissing9 p 42)) == [true, true, false]`
const LEAN_PARTY_SIGNED_MISSING9: [bool; 3] = [true, true, false];

/// The differential corpus, in the SAME index order as Lean `diffCorpus`:
/// 0 valid signed approve(7,42) · 1 unsigned approve · 2 impersonation(5) · 3 wrong digest(99) ·
/// 4 a revoke (not approve).
fn diff_corpus() -> Vec<ConsentBlock> {
    vec![
        consent_block(7, 42, Kind::Approve),
        ConsentBlock {
            signed: false,
            ..consent_block(7, 42, Kind::Approve)
        },
        consent_block(5, 42, Kind::Approve),
        consent_block(7, 99, Kind::Approve),
        consent_block(7, 42, Kind::Revoke),
    ]
}

/// The 3-party all-signed lace (Lean `demoLaceAllSigned`).
fn lace_all_signed() -> Vec<ConsentBlock> {
    vec![
        consent_block(7, 42, Kind::Approve),
        consent_block(8, 42, Kind::Approve),
        consent_block(9, 42, Kind::Approve),
    ]
}

/// The missing-9 lace (Lean `demoLaceMissing9`).
fn lace_missing9() -> Vec<ConsentBlock> {
    vec![
        consent_block(7, 42, Kind::Approve),
        consent_block(8, 42, Kind::Approve),
    ]
}

/// The fork lace (Lean `demoLaceFork`): 7, 8 sign cleanly; party 9 equivocates with an UNSIGNED
/// approve + a revoke (neither counts as valid consent).
fn lace_fork() -> Vec<ConsentBlock> {
    vec![
        consent_block(7, 42, Kind::Approve),
        consent_block(8, 42, Kind::Approve),
        ConsentBlock {
            signed: false,
            ..consent_block(9, 42, Kind::Approve)
        },
        consent_block(9, 42, Kind::Revoke),
    ]
}

#[test]
fn differential_consent_binding_decision() {
    // The consent-binding decision: ONLY the valid signed self-authored right-digest approve counts.
    let got: Vec<bool> = diff_corpus()
        .iter()
        .map(|b| is_approval_for(b, 7, 42))
        .collect();
    assert_eq!(
        got.as_slice(),
        &LEAN_IS_APPROVAL_FOR,
        "Rust is_approval_for drifted from Lean isApprovalFor golden vector"
    );

    // Specifically: unsigned, wrong-author, wrong-digest, and revoke all FAIL — the three
    // consent-binding teeth + the kind discriminator.
    assert!(!is_approval_for(&diff_corpus()[1], 7, 42), "unsigned must not count");
    assert!(!is_approval_for(&diff_corpus()[2], 7, 42), "impersonation must not count");
    assert!(!is_approval_for(&diff_corpus()[3], 7, 42), "wrong digest must not count");
    assert!(!is_approval_for(&diff_corpus()[4], 7, 42), "a revoke is not an approve");
}

#[test]
fn differential_nary_convergence_gate() {
    // n=3 all-signed ⇒ converged; missing-9 ⇒ not converged. (Lean `#guard`s on consentLaceComplete.)
    assert!(consent_lace_complete(&lace_all_signed(), &[7, 8, 9], 42));
    assert!(!consent_lace_complete(&lace_missing9(), &[7, 8, 9], 42));

    // Per-party verdict over the missing-9 lace: 7 ✓, 8 ✓, 9 ✗.
    let per_party: Vec<bool> = [7u64, 8, 9]
        .iter()
        .map(|&p| party_signed_consent(&lace_missing9(), p, 42))
        .collect();
    assert_eq!(per_party.as_slice(), &LEAN_PARTY_SIGNED_MISSING9);
}

#[test]
fn differential_equivocating_party_contributes_nothing() {
    // On the fork lace, party 9 (the equivocator) has NO counted signed consent — both fork
    // branches fail (the approve is unsigned, the revoke is not an approve). So the n-ary exchange
    // does NOT converge: the byzantine consenter cannot ride its fork into a settlement.
    assert!(!party_signed_consent(&lace_fork(), 9, 42));
    assert!(!consent_lace_complete(&lace_fork(), &[7, 8, 9], 42));
}
