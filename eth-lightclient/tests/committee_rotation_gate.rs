//! **The TRUST-ROOT advance is gated by the archive — and the gate BITES there.**
//!
//! `verified_gate_routing.rs` is the same fact about the CHAIN-following path. This file is about
//! the path that changes WHOSE SIGNATURES THE CLIENT TRUSTS: `verify_committee_update`, reached
//! from [`WeakSubjectivityStore::bootstrap_committee`] and `advance`.
//!
//! ## What this file is a falsifier for
//!
//! Until `dregg_eth_committee_rotation` existed, `verify_committee_update` was a hand-written Rust
//! rule — `branch.len() ∈ {5, 6}` `&&` a SHA-256 fold — and it MUTATED the trusted sync committee
//! through `store::bootstrap_committee` with no archive involved at all. The ETH verify gate was
//! honest and there was a door beside it: the single most trust-bearing decision in the crate went
//! through the one path that never asked Lean anything.
//!
//! **Against that tree this file does not compile** — `verified_gate::committee_rotation_raw`,
//! `committee_rotation_available` and the `nl=…;nr=…` wire did not exist, because there was nothing
//! to ask. And a re-introduced Rust twin cannot satisfy it either:
//!
//!   * [`the_rotation_verdict_is_the_archives_verdict`] pins, case by case over the whole depth ×
//!     reconstruction grid, that the `Ok`/`Err` `verify_committee_update` returns IS the archive's
//!     own `"1"`/`"0"` on the projected wire. A Rust twin agrees with the archive only by
//!     coincidence, and stops agreeing the moment either drifts.
//!   * Swap the gate for **always-accept** and [`forged_rotations_are_refused`] fails — there is no
//!     second opinion to catch a committee that is not committed by the trusted state.
//!   * Swap it for **always-reject** (or always-`"ERR"`, the drift that fail-closes everything and
//!     would otherwise satisfy every reject assertion) and
//!     [`a_genuine_rotation_is_accepted_through_the_store`] fails.
//!   * [`one_field_apart_rotation_verdicts_must_differ`] is the assertion no CONSTANT gate can
//!     satisfy at all.
//!
//! ## Archive-absent posture
//!
//! With no `dregg_eth_committee_rotation` export the trusted committee simply DOES NOT ADVANCE:
//! `verify_committee_update` returns [`Error::VerifiedGateUnavailable`] and the store reports
//! [`StoreError::RotationGateUnavailable`] — deliberately distinct from `UnchainedCommittee`, so a
//! missing verifier can never be read as a verified rejection. There is no skip and no fallback.

use eth_lightclient::ssz::hash_pair;
use eth_lightclient::store::{StoreError, WeakSubjectivityStore};
use eth_lightclient::verified_gate;
use eth_lightclient::{
    committee_rotation_reconstructs, verify_committee_update, Error, SyncCommittee,
    NEXT_SYNC_COMMITTEE_DEPTH, NEXT_SYNC_COMMITTEE_DEPTH_ELECTRA,
    NEXT_SYNC_COMMITTEE_SUBTREE_INDEX, SYNC_COMMITTEE_SIZE,
};

// -------------------- fixtures --------------------

/// The constructive inverse of `is_valid_merkle_branch`: the root a (leaf, branch, index) implies.
fn compute_root(leaf: &[u8; 32], branch: &[[u8; 32]], index: u64) -> [u8; 32] {
    let mut value = *leaf;
    for (i, node) in branch.iter().enumerate() {
        if (index >> i) & 1 == 1 {
            value = hash_pair(node, &value);
        } else {
            value = hash_pair(&value, node);
        }
    }
    value
}

fn committee(tag: u8) -> SyncCommittee {
    let pubkeys: Vec<[u8; 48]> = (0..SYNC_COMMITTEE_SIZE)
        .map(|i| {
            let mut p = [0u8; 48];
            p[0] = (i & 0xff) as u8;
            p[1] = ((i >> 8) & 0xff) as u8;
            p[2] = tag;
            p
        })
        .collect();
    SyncCommittee {
        pubkeys,
        aggregate_pubkey: [0xAB; 48],
    }
}

fn branch_of(depth: usize, tag: u8) -> Vec<[u8; 32]> {
    (0..depth as u8)
        .map(|i| [i.wrapping_add(tag); 32])
        .collect()
}

/// The archive is a HARD requirement, not a skip condition — the same posture
/// `verified_gate_routing.rs` takes for the verify gate. Every test below asserts it, so a cold or
/// stale archive is a loud red, never a quiet green.
fn require_rotation_gate() {
    assert!(
        verified_gate::committee_rotation_available(),
        "the linked archive does not export dregg_eth_committee_rotation, so eth-lightclient \
         cannot render ANY committee-rotation verdict and the trusted sync committee cannot \
         advance at all (it fails closed: verify_committee_update returns \
         Error::VerifiedGateUnavailable). There is no Rust fallback — the Rust depth rule WAS \
         the twin this crate deleted. Seed a HEAD-matching dregg-lean-ffi/libdregg_lean.a and \
         rebuild."
    );
}

// -------------------- the archive is a hard requirement --------------------

/// **The rotation gate is not optional.** Said once, loudly, rather than surfacing as a dozen
/// confusing failures: with no `dregg_eth_committee_rotation` export the trusted committee cannot
/// advance, and the crate says so with a NAMED error rather than installing anything.
#[test]
fn the_rotation_gate_is_a_hard_requirement() {
    if verified_gate::committee_rotation_available() {
        return;
    }
    let c = committee(0);
    let b = branch_of(NEXT_SYNC_COMMITTEE_DEPTH, 1);
    let root = compute_root(&c.hash_tree_root(), &b, NEXT_SYNC_COMMITTEE_SUBTREE_INDEX);
    assert!(
        matches!(
            verify_committee_update(&c, &b, &root),
            Err(Error::VerifiedGateUnavailable(_))
        ),
        "with no rotation gate, a rotation must REFUSE — never silently succeed on a Rust rule"
    );
    // And the store's own vocabulary keeps "we cannot decide" apart from "we refused you".
    let mut store = WeakSubjectivityStore::pin_checkpoint(root, [7u8; 32], 1800);
    assert!(matches!(
        store.bootstrap_committee(c, &b),
        Err(StoreError::RotationGateUnavailable(_))
    ));
}

// -------------------- the entry point IS the archive --------------------

/// The mutation grid: `(branch_depth, tamper)` pairs spanning both admissible depths, the two
/// neighbouring inadmissible ones, the finality depths (7 — admissible on the OTHER gate, which is
/// exactly the confusion a shared wire would create), and the empty branch.
fn grid() -> Vec<(usize, bool)> {
    let mut out = Vec::new();
    for depth in [0usize, 1, 4, 5, 6, 7, 8] {
        out.push((depth, false));
        out.push((depth, true));
    }
    out
}

/// **THE MUTATION CANARY.** For every case in the grid, the entry point's `Ok`/`Err` must equal the
/// ARCHIVE's raw `"1"`/`"0"` on the projections that case produces — case by case, so agreement is
/// not a coincidence of one sample. This is the difference between "the entry point agrees with the
/// gate" and "the entry point IS the gate".
#[test]
fn the_rotation_verdict_is_the_archives_verdict() {
    require_rotation_gate();
    for (depth, tamper) in grid() {
        let c = committee(0);
        let b = branch_of(depth, 1);
        let mut root = compute_root(&c.hash_tree_root(), &b, NEXT_SYNC_COMMITTEE_SUBTREE_INDEX);
        if tamper {
            root[0] ^= 0x01;
        }

        let reconstructs = committee_rotation_reconstructs(&c, &b, &root);
        let raw = verified_gate::committee_rotation_raw(depth, reconstructs)
            .expect("the archive must answer");
        let entry = verify_committee_update(&c, &b, &root);

        assert_eq!(
            entry.is_ok(),
            raw == "1",
            "entry point and archive disagree on wire {} (depth {depth}, tamper {tamper}): \
             entry={entry:?} archive={raw}",
            verified_gate::committee_rotation_wire(depth, reconstructs)
        );
    }
}

/// No CONSTANT gate satisfies this: two rotations one field apart — the SAME committee, the SAME
/// branch, one reconstructing and one not — must get DIFFERENT verdicts through the entry point.
#[test]
fn one_field_apart_rotation_verdicts_must_differ() {
    require_rotation_gate();
    let c = committee(0);
    let b = branch_of(NEXT_SYNC_COMMITTEE_DEPTH, 1);
    let good = compute_root(&c.hash_tree_root(), &b, NEXT_SYNC_COMMITTEE_SUBTREE_INDEX);
    let mut bad = good;
    bad[31] ^= 0x01;

    assert_eq!(verify_committee_update(&c, &b, &good), Ok(()));
    assert_eq!(
        verify_committee_update(&c, &b, &bad),
        Err(Error::BadMerkleBranch)
    );
    assert_ne!(
        verify_committee_update(&c, &b, &good).is_ok(),
        verify_committee_update(&c, &b, &bad).is_ok(),
        "the rotation gate returned the SAME verdict on both sides of the reconstruction \
         boundary — it is a constant, not a gate"
    );
}

/// The depth boundary is the archive's, and it is NOT the finality gate's. Depth 5 and 6 accept;
/// depth 7 — which `dregg_eth_lc_verify`'s finality conjunct DOES accept — is refused here. Two
/// gates, two admissibility rules, and the rotation path must not inherit the wrong one.
#[test]
fn rotation_depth_admissibility_is_not_the_finality_gates() {
    require_rotation_gate();
    for depth in [NEXT_SYNC_COMMITTEE_DEPTH, NEXT_SYNC_COMMITTEE_DEPTH_ELECTRA] {
        assert_eq!(
            verified_gate::committee_rotation_raw(depth, true).as_deref(),
            Ok("1"),
            "depth {depth} is an admissible rotation depth"
        );
    }
    for depth in [0usize, 1, 4, 7, 8] {
        assert_eq!(
            verified_gate::committee_rotation_raw(depth, true).as_deref(),
            Ok("0"),
            "depth {depth} must be refused by the rotation gate"
        );
    }
}

// -------------------- the store: the trust root only moves through the gate --------------------

/// ACCEPT polarity end to end: a genuine rotation under the governance-pinned checkpoint state root
/// installs the committee — through the archive. An always-reject / always-`"ERR"` gate fails here.
#[test]
fn a_genuine_rotation_is_accepted_through_the_store() {
    require_rotation_gate();
    let c = committee(0);
    let b = branch_of(NEXT_SYNC_COMMITTEE_DEPTH_ELECTRA, 0x40);
    let anchor = compute_root(&c.hash_tree_root(), &b, NEXT_SYNC_COMMITTEE_SUBTREE_INDEX);

    let mut store = WeakSubjectivityStore::pin_checkpoint(anchor, [7u8; 32], 1800);
    assert!(
        !store.has_trusted_committee(),
        "fail-closed before bootstrap"
    );
    store
        .bootstrap_committee(c.clone(), &b)
        .expect("a genuine rotation under the pinned anchor must install the committee");
    assert!(store.has_trusted_committee());
    assert_eq!(
        store.current_committee().map(|k| k.pubkeys.clone()),
        Some(c.pubkeys)
    );
}

/// REJECT polarity: an attacker's committee, offered under the SAME pinned anchor with the SAME
/// branch, is refused and the store's committee stays where it was. This is
/// `committeeRotationDecision_binding` observed at the entry point — one state root commits ONE
/// next committee. An always-accept gate fails here, and so does the pre-gate Rust twin under a
/// mutated archive.
#[test]
fn forged_rotations_are_refused() {
    require_rotation_gate();
    let honest = committee(0);
    let b = branch_of(NEXT_SYNC_COMMITTEE_DEPTH_ELECTRA, 0x40);
    let anchor = compute_root(
        &honest.hash_tree_root(),
        &b,
        NEXT_SYNC_COMMITTEE_SUBTREE_INDEX,
    );

    let mut store = WeakSubjectivityStore::pin_checkpoint(anchor, [7u8; 32], 1800);
    let forged = committee(0xFF);
    assert_eq!(
        store.bootstrap_committee(forged, &b),
        Err(StoreError::UnchainedCommittee(Error::BadMerkleBranch)),
        "a committee the pinned anchor does not commit must NOT be installed"
    );
    assert!(
        !store.has_trusted_committee(),
        "a refused rotation must leave the store fail-closed"
    );

    // …and the honest one still works afterwards (the refusal did not wedge the store).
    store
        .bootstrap_committee(honest, &b)
        .expect("the genuine rotation still installs");
    assert!(store.has_trusted_committee());
}

/// The wire this crate ships is the grammar Lean parses. A wire the gate cannot decode is `"ERR"`,
/// which the crate treats as REFUSE — so a grammar drift fail-closes loudly instead of admitting.
#[test]
fn a_foreign_wire_is_err_and_therefore_a_refusal() {
    require_rotation_gate();
    assert_eq!(
        verified_gate::committee_rotation_wire(6, true),
        "nl=6;nr=1",
        "the Rust wire must be the grammar `decodeCommitteeWire` parses"
    );
    // The ETH VERIFY wire is not a rotation wire: feeding it here must be `"ERR"`, never an accept.
    let verify_wire = verified_gate::sync_only(512, 512, 512, true).wire();
    assert_eq!(
        verified_gate::committee_rotation_shadow(&verify_wire).as_deref(),
        Ok("ERR"),
        "the rotation gate must not decode the verify gate's wire"
    );
    for junk in [
        "",
        "garbage",
        "nl=6",
        "nl=6;nr=2",
        "nr=1;nl=6",
        "nl=six;nr=1",
    ] {
        assert_eq!(
            verified_gate::committee_rotation_shadow(junk).as_deref(),
            Ok("ERR"),
            "a malformed rotation wire must be ERR (⇒ REFUSE), never an accept: {junk:?}"
        );
    }
}
