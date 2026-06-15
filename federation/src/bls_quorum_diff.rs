//! # Differential: Lean `Dregg2.Distributed.BlsQuorumCert` model  ⟺  the REAL BLS aggregate-verify.
//!
//! This is the Rust side of the differential for
//! `metatheory/Dregg2/Distributed/BlsQuorumCert.lean` — the DISTRIBUTED-consensus meaning of a BLS
//! quorum certificate, the layer ABOVE the single-cert soundness reduction
//! (`metatheory/Dregg2/Crypto/BlsThreshold.lean`). The Lean side proves, under the canonical BFT
//! corruption bound `f = ⌊n/3⌋`:
//!
//!  * `quorum_has_honest_signer`        — an accepting equal-weight QC at quorum threshold has ≥1
//!                                        HONEST signer (so the corrupt set alone cannot forge a QC).
//!  * `two_quorums_share_honest_member` — two accepting QCs over the same committee share an honest
//!                                        member (under `StrictBft`, `n > 3f`).
//!  * `no_equivocating_qcs`             — no honest member double-signs ⇒ ≤1 message gets a QC/slot.
//!
//! The Lean `faultBudget` / `quorumThreshold` are tiny total transcriptions of `fault_tolerance` /
//! `quorum_threshold` (`federation/src/lib.rs`). The honest-signer / non-equivocation theorems are
//! pure finite combinatorics ON TOP of the SNARK-extracted signer set; the SNARK/BLS pairing is the
//! NAMED irreducible primitive, here driven through the REAL `hints` weighted-threshold aggregate so
//! the model's hypotheses are exercised concretely, not abstractly:
//!
//!  1. **Formula relation** — the Lean `faultBudget`/`quorumThreshold` re-run against the REAL
//!     `fault_tolerance`/`quorum_threshold` over the Lean `#guard` golden values AND an exhaustive
//!     `0..=512` sweep (the Lean side samples; here we close the range), incl. `StrictBft ⇔ 3∤n`.
//!     Post-#170 unification the REAL formulas are the blocklace strict supermajority
//!     `q = ⌊2n/3⌋+1` and `f = ⌊(n−1)/3⌋`; they differ from the Lean transcriptions EXACTLY at
//!     `3 ∣ n` (q one HIGHER, f one LOWER) — the deliberate closure of the `StrictBft` hole this
//!     very Lean module carries ("false at n=3,6,9,…"). Strictly safe-side: Rust demands more
//!     signers and claims less corruption tolerance, so every Lean bound still applies; the
//!     honest-overlap margin now holds UNCONDITIONALLY (no `StrictBft` caveat). Residual lane:
//!     lift the Lean `quorumThreshold` to the supermajority and discharge `StrictBft`.
//!  2. **Honest-signer agreement** — over a REAL committee with a corrupt subset of size `≤ f`, the
//!     real `sign_aggregate` with ONLY the honest signers reaching quorum verifies, while the corrupt
//!     subset alone (`|B| ≤ f < quorum`) CANNOT produce a verifying QC — `aggregate` returns Err
//!     (the `weight_here < threshold` gate, `hints/src/lib.rs:152`). This is the Rust witness of
//!     `quorum_has_honest_signer` / `corrupt_cannot_reach_quorum`.
//!  3. **No-equivocation agreement** — two REAL QCs over the same committee for two different bodies,
//!     each at quorum, share a signer index; with the honest-vote-once discipline that shared signer
//!     is honest. This is the Rust witness of `two_quorums_share_honest_member` / `no_equivocating_qcs`.
//!
//! The BLS pairing/SNARK is exercised through `FederationCommittee::{aggregate,verify}` (the real
//! `hints::{sign_aggregate,verify_aggregate}`), so "a genuine weighted quorum signed" is concrete.

#![cfg(test)]

use crate::threshold::{FederationCommittee, MemberSecret, generate_test_committee};
use crate::{fault_tolerance, quorum_threshold};
use hints::PartialSignature;

// ───────────────────────────── Lean model, transcribed to Rust ─────────────────────────────

/// Lean `faultBudget n = n / 3` (`BlsQuorumCert.lean §1`, = `fault_tolerance`, `lib.rs:169`).
fn lean_fault_budget(n: usize) -> usize {
    n / 3
}

/// Lean `quorumThreshold n = n − n/3` (REUSED from `EpochReconfig`, = `quorum_threshold`, `lib.rs:155`).
fn lean_quorum_threshold(n: usize) -> usize {
    if n == 0 { 0 } else { n - lean_fault_budget(n) }
}

/// Lean `StrictBft n = 3·faultBudget n < n` (`BlsQuorumCert.lean §1`); `strictBft_iff` ⇔ `¬ 3∣n`.
fn lean_strict_bft(n: usize) -> bool {
    3 * lean_fault_budget(n) < n
}

// ───────────────────────────── 1. Formula agreement ─────────────────────────────

#[test]
fn fault_budget_matches_real_golden() {
    // Lean §5b `#guard faultBudget {0,1,2,3,4,7,10}` golden vectors, with the REAL (post-#170)
    // `fault_tolerance = ⌊(n−1)/3⌋` alongside: one LOWER exactly at 3∣n (n ≥ 3f+1 honesty).
    for (n, lean_f, rust_f) in [
        (0, 0, 0),
        (1, 0, 0),
        (2, 0, 0),
        (3, 1, 0), // 3 ∣ n: no 3-member system tolerates a fault
        (4, 1, 1),
        (7, 2, 2),
        (10, 3, 3),
    ] {
        assert_eq!(lean_fault_budget(n), lean_f, "lean faultBudget({n})");
        assert_eq!(fault_tolerance(n), rust_f, "real fault_tolerance({n})");
    }
}

#[test]
fn quorum_threshold_matches_real_golden() {
    // Lean §5b `#guard quorumThreshold {1,2,3,4,7,10}` golden vectors, with the REAL (post-#170)
    // supermajority alongside: one HIGHER exactly at 3∣n (the StrictBft closure).
    for (n, lean_q, rust_q) in [
        (1, 1, 1),
        (2, 2, 2),
        (3, 2, 3),
        (4, 3, 3),
        (7, 5, 5),
        (10, 7, 7),
    ] {
        assert_eq!(
            lean_quorum_threshold(n),
            lean_q,
            "lean quorumThreshold({n})"
        );
        assert_eq!(quorum_threshold(n), rust_q, "real quorum_threshold({n})");
    }
}

#[test]
fn formulas_agree_exhaustively() {
    // The Lean side samples; close the range 0..=512 with the EXACT pinned relation: the real
    // formulas equal the Lean transcriptions away from 3∣n and differ by exactly one AT 3∣n
    // (q one higher, f one lower) — no untracked drift anywhere in the operating range.
    for n in 0..=512usize {
        let div3 = n % 3 == 0;
        assert_eq!(
            fault_tolerance(n),
            lean_fault_budget(n) - usize::from(div3 && n > 0),
            "faultBudget relation at n={n}"
        );
        assert_eq!(
            quorum_threshold(n),
            lean_quorum_threshold(n) + usize::from(div3),
            "quorumThreshold relation at n={n}"
        );
        // Safe-side directions: more signers demanded, less corruption claimed.
        assert!(
            quorum_threshold(n) >= lean_quorum_threshold(n),
            "q dir n={n}"
        );
        assert!(fault_tolerance(n) <= lean_fault_budget(n), "f dir n={n}");
        // `quorum_gt_faultBudget`: a quorum strictly exceeds the corruption budget (n ≥ 1) —
        // holds for BOTH the Lean pair and the real pair.
        if n >= 1 {
            assert!(
                lean_fault_budget(n) < lean_quorum_threshold(n),
                "lean quorum must exceed lean fault budget at n={n}"
            );
            assert!(
                fault_tolerance(n) < quorum_threshold(n),
                "real quorum must exceed real fault budget at n={n}"
            );
            // The unification's whole point: the honest-overlap margin holds UNCONDITIONALLY
            // for the real pair (no StrictBft caveat).
            assert!(
                2 * quorum_threshold(n) - n > fault_tolerance(n),
                "unconditional honest overlap at n={n}"
            );
        }
        // Lean `strictBft_iff`: StrictBft ⇔ ¬(3 ∣ n).
        assert_eq!(
            lean_strict_bft(n),
            n % 3 != 0,
            "strictBft_iff drift at n={n}"
        );
        // Under StrictBft the inclusion–exclusion honest-overlap margin 2q − n > f holds for the
        // LEAN pair; at n=3f it does NOT (the honest subtlety the Lean module carries explicitly,
        // and which the real supermajority pair closes above).
        if n >= 1 {
            let margin = 2 * lean_quorum_threshold(n) - n;
            assert_eq!(
                lean_fault_budget(n) < margin,
                lean_strict_bft(n),
                "overlap margin must track StrictBft at n={n}"
            );
        }
    }
}

// ───────────────────────── 2. Honest-signer agreement (real BLS) ─────────────────────────

/// Helper: aggregate a QC from the given member indices over `msg`, returning whether it both
/// aggregated AND verified against the committee.
fn qc_from(
    committee: &FederationCommittee,
    members: &[MemberSecret],
    idxs: &[usize],
    msg: &[u8],
) -> bool {
    let shares: Vec<(usize, PartialSignature)> = idxs
        .iter()
        .map(|&i| (members[i].index, committee.sign_share(&members[i], msg)))
        .collect();
    match committee.aggregate(&shares, msg) {
        Ok(qc) => committee.verify(&qc, msg).is_ok(),
        Err(_) => false,
    }
}

#[test]
fn honest_quorum_verifies_corrupt_alone_cannot() {
    // n=4, f=fault_tolerance(4)=1, quorum=3. Corrupt set B = {member 3} (|B| = 1 = f).
    let n = 4;
    let f = fault_tolerance(n); // 1
    let q = quorum_threshold(n); // 3
    assert_eq!((f, q), (1, 3));

    let (committee, members) = generate_test_committee(n, q as u64).unwrap();
    let msg = b"bls-quorum-diff:honest-vs-corrupt";

    // The corrupt set alone: {3}. |B| = 1 < quorum 3 ⇒ `aggregate` must REFUSE (weight < threshold).
    // This is the Rust witness of Lean `corrupt_cannot_reach_quorum`: a QC cannot be forged by the
    // corrupt members alone.
    assert!(
        !qc_from(&committee, &members, &[3], msg),
        "corrupt-only sub-quorum (|B|=f<quorum) must NOT produce a verifying QC"
    );

    // An honest quorum {0,1,2} (none corrupt) reaches threshold and verifies — Lean
    // `quorum_has_honest_signer`: the accepting QC's signer set lies entirely OUTSIDE B.
    assert!(
        qc_from(&committee, &members, &[0, 1, 2], msg),
        "an honest quorum of size = threshold must produce a verifying QC"
    );

    // Any quorum that DOES verify must include ≥ quorum−f = 3−1 = 2 honest members; in particular at
    // least one honest member is present. We exercise the boundary: a quorum {1,2,3} (one corrupt,
    // two honest) still has honest members 1,2 outside B — the honest-signer guarantee.
    let honest_in_q123: usize = [1usize, 2, 3].iter().filter(|&&i| i != 3).count();
    assert!(
        honest_in_q123 >= q - f,
        "every verifying quorum carries ≥ quorum−f honest signers"
    );
    assert!(
        qc_from(&committee, &members, &[1, 2, 3], msg),
        "a mixed quorum still verifies (it reaches threshold)"
    );
}

#[test]
fn corrupt_set_below_quorum_at_several_sizes() {
    // Across several committee sizes, the corrupt set (size f) is strictly below the quorum, so a
    // corrupt-only aggregate is always refused — the structural reason a BLS QC is sound at n>1.
    for &n in &[4usize, 7, 10] {
        let f = fault_tolerance(n);
        let q = quorum_threshold(n);
        assert!(f < q, "fault budget below quorum at n={n}");

        let (committee, members) = generate_test_committee(n, q as u64).unwrap();
        let msg = b"bls-quorum-diff:corrupt-below-quorum";

        // The "corrupt set" = the last f members. |B| = f < q ⇒ aggregate refuses.
        let corrupt: Vec<usize> = (n - f..n).collect();
        assert!(
            !qc_from(&committee, &members, &corrupt, msg),
            "corrupt-only set of size f={f} must not reach quorum q={q} at n={n}"
        );

        // The first q members (a genuine quorum) verify.
        let quorum_members: Vec<usize> = (0..q).collect();
        assert!(
            qc_from(&committee, &members, &quorum_members, msg),
            "a genuine quorum of size q={q} must verify at n={n}"
        );
    }
}

// ─────────────────────── 3. No-equivocation agreement (real BLS) ───────────────────────

#[test]
fn two_quorums_share_an_honest_signer() {
    // n=4, quorum=3 ⇒ any two quorums (size 3) over a 4-set overlap in ≥ 2 members (2q−n = 2).
    // With f=1 corrupt, the ≥2-member overlap contains an HONEST member (overlap > f). This is the
    // Rust witness of Lean `two_quorums_share_honest_member` (under StrictBft: 4 is not a 3-multiple).
    let n = 4;
    let f = fault_tolerance(n); // 1
    let q = quorum_threshold(n); // 3
    assert!(crate::quorum_threshold(n) == q);

    // Two conflicting messages, each signed by a (size-q) quorum.
    let (committee, members) = generate_test_committee(n, q as u64).unwrap();
    let msg_a = b"bls-quorum-diff:proposal-A";
    let msg_b = b"bls-quorum-diff:proposal-B";

    let quorum_a = [0usize, 1, 2]; // signs A
    let quorum_b = [1usize, 2, 3]; // signs B

    assert!(
        qc_from(&committee, &members, &quorum_a, msg_a),
        "QC over A verifies"
    );
    assert!(
        qc_from(&committee, &members, &quorum_b, msg_b),
        "QC over B verifies"
    );

    // The signer sets overlap; the overlap exceeds the fault budget, so it contains an honest member.
    let overlap: Vec<usize> = quorum_a
        .iter()
        .copied()
        .filter(|i| quorum_b.contains(i))
        .collect();
    assert!(
        overlap.len() > f,
        "two quorums overlap in more than f members (overlap={overlap:?}, f={f})"
    );

    // Designate corrupt = {3}; the overlap {1,2} avoids it ⇒ a shared HONEST signer exists. With the
    // honest-vote-once discipline, that honest member would have signed BOTH A and B — impossible —
    // so two conflicting QCs cannot both arise from honest validators (`no_equivocating_qcs`).
    let corrupt = [3usize];
    let honest_shared: Vec<usize> = overlap
        .iter()
        .copied()
        .filter(|i| !corrupt.contains(i))
        .collect();
    assert!(
        !honest_shared.is_empty(),
        "the cross-quorum overlap contains an HONEST member (= {honest_shared:?})"
    );
}

#[test]
fn equivocation_requires_an_honest_double_signer() {
    // Generalize: across n=4,7,10, two size-q quorums always overlap by 2q−n > f members, so the
    // overlap is never fully corrupt — there is always an honest member who would have to double-sign
    // for two conflicting QCs to coexist. This pins the Lean `no_equivocating_qcs` precondition.
    for &n in &[4usize, 7, 10] {
        let f = fault_tolerance(n);
        let q = quorum_threshold(n);
        // StrictBft (n not a 3-multiple) ⇒ 2q − n > f.
        assert_eq!(lean_strict_bft(n), n % 3 != 0);
        if lean_strict_bft(n) {
            let overlap_lb = 2 * q - n; // forced overlap lower bound
            assert!(
                overlap_lb > f,
                "forced overlap 2q−n={overlap_lb} must exceed fault budget f={f} at n={n}"
            );
        }
    }
}
