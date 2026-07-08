//! Pedersen-style distributed key generation (DKG) over `R_q^ℓ` — the
//! dealerless real-key path: `n` members JOINTLY generate the group key and
//! NO party ever holds the whole group secret (the property the trusted
//! [`crate::threshold::HermineTestDealer`] deliberately lacks).
//!
//! # Protocol shape (Pedersen's joint-Feldman construction)
//!
//! Round 1 — every member `i ∈ {1, …, n}` acts as a dealer of its OWN secret
//! ([`dkg_deal`]):
//! * samples `sᵢ ∈ R_q^ℓ` SHORT (`‖sᵢ‖∞ ≤` [`SECRET_ETA`], the MLWE shape)
//!   and a degree-`(t−1)` sharing polynomial
//!   `fᵢ(x) = sᵢ + aᵢ,₁·x + … + aᵢ,t₋₁·x^{t−1}` over the module (blinding
//!   coefficients full-range, exactly like the trusted dealer's);
//! * sends the share `fᵢ(j)` to every member `j` (a PRIVATE-channel message);
//! * BROADCASTS Feldman-style commitments to every coefficient: pushing each
//!   `aᵢ,ₖ` through the public map, `Cᵢ,ₖ = A·aᵢ,ₖ ∈ R_q^k` (so
//!   `Cᵢ,₀ = A·sᵢ` is member `i`'s public-key contribution).
//!
//! Round 2 — every member `j` VERIFIES each received share against the
//! sender's broadcast ([`verify_dkg_share`]): by `A`'s linearity,
//!
//! ```text
//! A·fᵢ(j) = Σₖ jᵏ · (A·aᵢ,ₖ) = Σₖ jᵏ · Cᵢ,ₖ ,
//! ```
//!
//! so a malformed/cheating share fails the public check and the verifier
//! learns WHICH dealer cheated (the complaint signal,
//! [`DkgError::Complaint`]). Honest shares are then summed into the member's
//! FINAL share `xⱼ = Σᵢ fᵢ(j)` — a degree-`(t−1)` Shamir share of the group
//! secret `s = Σᵢ sᵢ`, which NOBODY ever materializes. The group public key
//! assembles from broadcasts alone: `t = A·s = Σᵢ Cᵢ,₀`.
//!
//! The final shares are ordinary [`HermineShare`]s: Lagrange reconstruction,
//! partial responses, and the whole signing ceremony
//! ([`crate::threshold::hermine_sign`]) work off them unchanged — the DKG
//! swaps only WHERE the sharing polynomial comes from (a sum of per-member
//! polynomials instead of one dealer's).
//!
//! Note the group secret is a sum of `n` short secrets, so `‖s‖∞ ≤ n·η`:
//! smudging/shortness accounting against DKG keys must budget the shift bound
//! as `N·n·η`, not `N·η` (the tests here do).
//!
//! # Reference boundary — what this DKG is NOT
//!
//! This is a REFERENCE DKG: the trust structure is real (no dealer, shares
//! verifiable, key jointly formed), the deployment machinery is not:
//! * **synchronous & in-process** — [`HermineDkg::run`] plays all `n` members
//!   in one address space; there is no real broadcast channel, no
//!   authenticated point-to-point transport, no round timeouts;
//! * **detection only, no arbitration** — a bad share aborts the ceremony
//!   with the accused dealer's index ([`DkgError::Complaint`]); the full
//!   complaint round (accused dealer publishes the disputed share, majority
//!   disqualification, continuing with the qualified set) is a documented
//!   reference gap;
//! * **public-key bias out of model** — plain Pedersen DKG lets a rushing
//!   adversary bias the DISTRIBUTION of the public key (Gennaro et al.);
//!   production wants the hiding-commitment round on top;
//! * **reference PRNG** (splitmix64 seed schedule; NOT a CSPRNG), not
//!   constant-time, no zeroization; the shared matrix `A` is derived from a
//!   public seed as a CRS stand-in (production: hash-to-matrix from a
//!   nothing-up-my-sleeve seed).
//!
//! Production still needs the network protocol, complaint arbitration, the
//! bias fix, and audit. What this module removes is the trusted dealer.

use crate::linalg::{Matrix, PolyVec};
use crate::ring::{Poly, Q};
use crate::threshold::{horner_eval, sample_poly, sample_short_vec, sample_vec};
use crate::threshold::{HermineShare, SECRET_ETA};

/// One private share message inside a [`DkgDealing`]: dealer `i`'s evaluation
/// `fᵢ(recipient)` destined for that member. In a deployment this travels an
/// authenticated PRIVATE channel; in this in-process reference it is a plain
/// field (which is also what lets tests tamper with it to exercise
/// detection).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DkgShareMsg {
    /// The 1-based member index this share is addressed to.
    pub recipient: u64,
    /// The share vector `fᵢ(recipient) ∈ R_q^ℓ`.
    pub share: PolyVec,
}

/// Everything member `i` produces in DKG round 1 ([`dkg_deal`]): its
/// broadcast commitments, its outgoing private shares, and (dealer-local
/// only) its own secret contribution.
#[derive(Clone)]
pub struct DkgDealing {
    /// The 1-based index of the dealing member.
    pub dealer: u64,
    /// BROADCAST: Feldman-style commitments `Cₖ = A·aₖ` to every coefficient
    /// of the sharing polynomial, `k = 0, …, t−1`; `commitments[0] = A·sᵢ`
    /// is this member's contribution to the group public key.
    pub commitments: Vec<PolyVec>,
    /// PRIVATE messages: `shares[j−1]` is the share for recipient `j`.
    pub shares: Vec<DkgShareMsg>,
    /// This member's own secret `sᵢ` — dealer-LOCAL state, never sent.
    /// Retained ONLY so tests can witness `s = Σᵢ sᵢ` and that no single
    /// member's data is `s`; a real member destroys it after sharing (only
    /// its final aggregated share matters from round 2 on).
    #[cfg_attr(not(test), allow(dead_code))]
    secret: PolyVec,
}

impl DkgDealing {
    /// Test-only witness of this member's secret contribution (see the field
    /// doc).
    #[cfg(test)]
    pub(crate) fn secret(&self) -> &PolyVec {
        &self.secret
    }
}

/// Why a DKG ceremony refused to complete.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DkgError {
    /// Degenerate parameters or malformed dealing set (wrong counts,
    /// duplicate/out-of-range dealer indices, mis-shaped commitment or share
    /// lists).
    BadParameters,
    /// Member `accuser`'s received share from `dealer` failed Feldman
    /// verification — the complaint signal identifying the cheating dealer.
    /// (This reference stops at detection; arbitration is a documented gap.)
    Complaint {
        /// The member whose share check failed.
        accuser: u64,
        /// The dealer whose share/commitments are inconsistent.
        dealer: u64,
    },
}

/// DKG round 1 for one member: sample the member's own short secret `sᵢ` and
/// sharing polynomial, evaluate a share for every recipient `1..=n`, and
/// commit to every coefficient through the public map `A` (Feldman-style).
///
/// `seed` drives this member's sampling only (reference PRNG; a deployment
/// samples from a local CSPRNG). `None` on degenerate parameters
/// (`t == 0`, `t > n`, `n ≥ q`, or `dealer ∉ 1..=n`).
pub fn dkg_deal(a: &Matrix, dealer: u64, n: u64, t: u64, seed: u64) -> Option<DkgDealing> {
    if t == 0 || t > n || n >= Q || dealer == 0 || dealer > n {
        return None;
    }
    // Domain-separate this dealer's stream by index (mirrors the signing
    // ceremony's per-signer mask schedule).
    let mut state = seed ^ dealer.wrapping_mul(0x9e3779b97f4a7c15);
    // The member's own secret: SHORT (MLWE shape) — the constant term.
    let secret = sample_short_vec(&mut state, a.cols, SECRET_ETA);
    // fᵢ(x) = sᵢ + aᵢ,₁·x + … + aᵢ,t₋₁·x^{t−1}; blinding coefficients
    // full-range, exactly like the trusted dealer's sharing polynomial.
    let mut coeffs: Vec<PolyVec> = vec![secret.clone()];
    coeffs.extend((1..t).map(|_| sample_vec(&mut state, a.cols)));
    let commitments = coeffs.iter().map(|c| a.mul_vec(c)).collect();
    let shares = (1..=n)
        .map(|j| DkgShareMsg {
            recipient: j,
            share: horner_eval(&coeffs, &Poly::constant(j)),
        })
        .collect();
    Some(DkgDealing {
        dealer,
        commitments,
        shares,
        secret,
    })
}

/// Feldman share verification: does `share` really equal `fᵢ(recipient)` for
/// the polynomial behind `commitments`? By `A`'s linearity the check is
/// public: `A·share == Σₖ recipientᵏ · commitments[k]` (powers in `ℤ_q`,
/// embedded as constants — the evaluation points are constants, so this is
/// Horner in the image module). A cheating dealer cannot pass this for a
/// share off its committed polynomial without breaking the (M)SIS-hardness
/// of `A` (finding a nonzero preimage of 0).
pub fn verify_dkg_share(
    a: &Matrix,
    commitments: &[PolyVec],
    recipient: u64,
    share: &PolyVec,
) -> bool {
    if share.len() != a.cols || commitments.iter().any(|c| c.len() != a.rows) {
        return false;
    }
    let lhs = a.mul_vec(share);
    // Σₖ recipientᵏ · Cₖ by Horner over the image module.
    let x = Poly::constant(recipient % Q);
    let rhs = commitments
        .iter()
        .rev()
        .fold(PolyVec::zero(a.rows), |acc, c| acc.scale(&x).add(c));
    lhs == rhs
}

/// The completed DKG: the public matrix, the jointly-formed group key, and
/// every member's final aggregated share. Structurally a drop-in for the
/// trusted dealer's outputs — [`crate::threshold::hermine_sign`] /
/// [`crate::threshold::lagrange_reconstruct`] consume the shares unchanged —
/// except that no `group_secret` field CAN exist: the group secret was never
/// materialized anywhere.
pub struct HermineDkg {
    /// The public matrix `A` (the shared CRS all members deal against).
    pub a: Matrix,
    /// The group public key `t = A·s = Σᵢ Cᵢ,₀`, assembled from broadcasts.
    pub group_key: PolyVec,
    /// The signing threshold `t`.
    pub threshold: u64,
    /// Every member's FINAL share `xⱼ = Σᵢ fᵢ(j)`, index `j` at position
    /// `j−1`. (In-process reference: a deployment's member `j` holds only
    /// its own entry.)
    pub shares: Vec<HermineShare>,
}

impl HermineDkg {
    /// Run the whole synchronous in-process ceremony: derive the shared
    /// matrix `A` from `seed` (the CRS stand-in), have every member deal
    /// ([`dkg_deal`]), then verify-and-aggregate ([`HermineDkg::aggregate`]).
    ///
    /// All-honest by construction; the aggregate path (and its complaint
    /// signal) is exercised directly by feeding tampered dealings to
    /// `aggregate`.
    pub fn run(rows: usize, cols: usize, n: u64, t: u64, seed: u64) -> Result<Self, DkgError> {
        if t == 0 || t > n || n >= Q || rows == 0 || cols == 0 {
            return Err(DkgError::BadParameters);
        }
        let mut state = seed;
        let a = Matrix::from_fn(rows, cols, |_, _| sample_poly(&mut state));
        // Domain-separate every member's dealing randomness from the matrix
        // stream (and from each other, inside dkg_deal).
        let deal_seed = seed.wrapping_mul(0x2545f4914f6cdd1d) ^ 0xd6_6001;
        let dealings: Vec<DkgDealing> = (1..=n)
            .map(|i| dkg_deal(&a, i, n, t, deal_seed).expect("params validated above"))
            .collect();
        Self::aggregate(a, n, t, &dealings)
    }

    /// DKG round 2, all members at once: every member `j` Feldman-verifies
    /// every dealer's share for it, then sums them into its final share; the
    /// group key is the sum of the broadcast constant-term commitments.
    ///
    /// The FIRST failing check aborts with [`DkgError::Complaint`] naming
    /// the accuser and the cheating dealer (detection; arbitration is the
    /// documented reference gap). Malformed dealing sets (wrong counts,
    /// duplicate dealers, mis-addressed shares) are [`DkgError::BadParameters`].
    pub fn aggregate(a: Matrix, n: u64, t: u64, dealings: &[DkgDealing]) -> Result<Self, DkgError> {
        if t == 0 || t > n || n >= Q || dealings.len() != n as usize {
            return Err(DkgError::BadParameters);
        }
        // Structural checks: dealer indices are exactly {1, …, n} (in order),
        // t commitments each, one share per recipient, correctly addressed.
        for (idx, d) in dealings.iter().enumerate() {
            let well_formed = d.dealer == idx as u64 + 1
                && d.commitments.len() == t as usize
                && d.shares.len() == n as usize
                && d.shares
                    .iter()
                    .enumerate()
                    .all(|(j, m)| m.recipient == j as u64 + 1);
            if !well_formed {
                return Err(DkgError::BadParameters);
            }
        }
        // Round 2 verification: member j checks every received share against
        // the sender's broadcast commitments.
        for j in 1..=n {
            for d in dealings {
                let msg = &d.shares[(j - 1) as usize];
                if !verify_dkg_share(&a, &d.commitments, j, &msg.share) {
                    return Err(DkgError::Complaint {
                        accuser: j,
                        dealer: d.dealer,
                    });
                }
            }
        }
        // Aggregation: final share xⱼ = Σᵢ fᵢ(j); group key t = Σᵢ Cᵢ,₀.
        let shares = (1..=n)
            .map(|j| HermineShare {
                index: j,
                share: dealings
                    .iter()
                    .map(|d| d.shares[(j - 1) as usize].share.clone())
                    .reduce(|acc, s| acc.add(&s))
                    .expect("n ≥ 1 dealings"),
            })
            .collect();
        let group_key = dealings
            .iter()
            .map(|d| d.commitments[0].clone())
            .reduce(|acc, c| acc.add(&c))
            .expect("n ≥ 1 dealings");
        Ok(Self {
            a,
            group_key,
            threshold: t,
            shares,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring::N;
    use crate::threshold::{
        acceptance_bound, hermine_sign, lagrange_reconstruct, signature_norm, verify_hermine,
        MASK_WIDTH_WIDE,
    };

    /// k=2, ℓ=3, n=5 members, threshold t=3 — the same shape as the trusted
    /// dealer's test committee, now dealt jointly.
    const ROWS: usize = 2;
    const COLS: usize = 3;
    const MEMBERS: u64 = 5;
    const THRESHOLD: u64 = 3;
    const SEED: u64 = 0x00de_add0_6001;

    /// The round-1 transcript `run` would produce, exposed so tests can
    /// inspect per-member secrets and tamper with shares.
    fn dealings() -> (Matrix, Vec<DkgDealing>) {
        let mut state = SEED;
        let a = Matrix::from_fn(ROWS, COLS, |_, _| sample_poly(&mut state));
        let deal_seed = SEED.wrapping_mul(0x2545f4914f6cdd1d) ^ 0xd6_6001;
        let ds = (1..=MEMBERS)
            .map(|i| dkg_deal(&a, i, MEMBERS, THRESHOLD, deal_seed).unwrap())
            .collect();
        (a, ds)
    }

    // -- (1) the group key is jointly formed: t = A·(Σᵢ sᵢ) ------------------

    #[test]
    fn dkg_group_key_matches_sum() {
        let (a, ds) = dealings();
        let dkg = HermineDkg::aggregate(a.clone(), MEMBERS, THRESHOLD, &ds).unwrap();
        // The sum of the members' individual secrets (test-only witness).
        let s_sum = ds
            .iter()
            .map(|d| d.secret().clone())
            .reduce(|acc, s| acc.add(&s))
            .unwrap();
        // The broadcast-assembled group key IS A·(Σᵢ sᵢ)…
        assert_eq!(dkg.group_key, a.mul_vec(&s_sum));
        // …and matches what `run` (the whole ceremony) produces.
        let via_run = HermineDkg::run(ROWS, COLS, MEMBERS, THRESHOLD, SEED).unwrap();
        assert_eq!(via_run.group_key, dkg.group_key);
        // NO single member's data reveals s: neither any individual secret
        // contribution nor any single final share equals the group secret.
        for d in &ds {
            assert_ne!(d.secret(), &s_sum, "one member's secret must not be s");
        }
        for share in &dkg.shares {
            // A 1-member "subset" Lagrange-reconstructs the share itself.
            assert_ne!(
                lagrange_reconstruct(&[share]),
                s_sum,
                "one final share must not be s"
            );
        }
        // And the group secret is genuinely a JOINT object: it differs from
        // every proper-subset partial sum (drop any one contributor and the
        // key changes).
        for skip in 0..ds.len() {
            let partial = ds
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != skip)
                .map(|(_, d)| d.secret().clone())
                .reduce(|acc, s| acc.add(&s))
                .unwrap();
            assert_ne!(a.mul_vec(&partial), dkg.group_key);
        }
    }

    // -- (2) final shares are a real t-of-n sharing of s, and signing works --

    #[test]
    fn dkg_shares_reconstruct() {
        let (a, ds) = dealings();
        let dkg = HermineDkg::aggregate(a, MEMBERS, THRESHOLD, &ds).unwrap();
        let s_sum = ds
            .iter()
            .map(|d| d.secret().clone())
            .reduce(|acc, s| acc.add(&s))
            .unwrap();
        // Any t-subset of FINAL shares Lagrange-reconstructs the SAME group
        // secret s = Σᵢ sᵢ — which maps to the group key.
        for subset in [[0usize, 1, 2], [0, 2, 4], [2, 3, 4]] {
            let shares: Vec<&HermineShare> = subset.iter().map(|&i| &dkg.shares[i]).collect();
            assert_eq!(lagrange_reconstruct(&shares), s_sum);
        }
        assert_eq!(dkg.a.mul_vec(&s_sum), dkg.group_key);
        // Sub-threshold subsets reconstruct something else.
        for subset in [[0usize, 1], [1, 4], [2, 3]] {
            let shares: Vec<&HermineShare> = subset.iter().map(|&i| &dkg.shares[i]).collect();
            assert_ne!(lagrange_reconstruct(&shares), s_sum);
        }
        // END-TO-END: the signing ceremony runs off DKG shares unchanged —
        // no dealer anywhere in this key's history.
        let message = b"dregg-federation-vote-v1:hermine-dkg";
        for subset in [[0usize, 1, 2], [1, 3, 4]] {
            let signers: Vec<&HermineShare> = subset.iter().map(|&i| &dkg.shares[i]).collect();
            let sig = hermine_sign(
                &dkg.a,
                &dkg.group_key,
                &signers,
                0xD6_0000 + subset[0] as u64,
                message,
            )
            .unwrap();
            assert!(verify_hermine(&dkg.a, &dkg.group_key, message, &sig));
            // Shortness still holds — with the DKG's WIDER secret budget
            // (s is a sum of n short secrets, so ‖s‖∞ ≤ n·η → shift ≤ N·n·η).
            let shift = (N as u64) * MEMBERS * crate::threshold::SECRET_ETA;
            let bound = acceptance_bound(THRESHOLD, MASK_WIDTH_WIDE, shift);
            assert!(bound < Q / 2, "DKG acceptance bound must be non-vacuous");
            assert!(signature_norm(&sig.z) <= bound);
        }
        // A sub-threshold signer set still cannot forge.
        let sub: Vec<&HermineShare> = dkg.shares[0..2].iter().collect();
        let sig = hermine_sign(&dkg.a, &dkg.group_key, &sub, 0xD6_FFFF, message).unwrap();
        assert!(!verify_hermine(&dkg.a, &dkg.group_key, message, &sig));
    }

    // -- (3) the teeth: a cheating dealer is caught and named -----------------

    #[test]
    fn dkg_detects_cheating_dealer() {
        let (a, ds) = dealings();
        // Direct check first: every honest share verifies; a tampered one
        // fails Feldman verification.
        for d in &ds {
            for msg in &d.shares {
                assert!(verify_dkg_share(
                    &a,
                    &d.commitments,
                    msg.recipient,
                    &msg.share
                ));
                let mut bad = msg.share.clone();
                bad.0[0] = bad.0[0].add(&Poly::constant(1));
                assert!(!verify_dkg_share(&a, &d.commitments, msg.recipient, &bad));
            }
        }
        // Ceremony-level: dealer 3 sends member 2 a tampered share — the
        // aggregate aborts with the complaint NAMING dealer 3, accused by 2.
        let mut cheat = ds.clone();
        let victim = &mut cheat[2].shares[1]; // dealer 3 (index 2), recipient 2
        victim.share.0[0] = victim.share.0[0].add(&Poly::constant(1));
        match HermineDkg::aggregate(a.clone(), MEMBERS, THRESHOLD, &cheat) {
            Err(DkgError::Complaint { accuser, dealer }) => {
                assert_eq!(accuser, 2);
                assert_eq!(dealer, 3);
            }
            other => panic!(
                "tampered share must raise a complaint, got {:?}",
                other.err()
            ),
        }
        // A tampered BROADCAST (commitment) is caught too: every recipient's
        // check against dealer 1 now fails, so member 1 complains first.
        let mut cheat = ds.clone();
        cheat[0].commitments[1].0[0] = cheat[0].commitments[1].0[0].add(&Poly::constant(1));
        assert_eq!(
            HermineDkg::aggregate(a, MEMBERS, THRESHOLD, &cheat)
                .err()
                .unwrap(),
            DkgError::Complaint {
                accuser: 1,
                dealer: 1
            }
        );
    }

    // -- hygiene: degenerate parameters and malformed dealing sets -----------

    #[test]
    fn dkg_refuses_degenerate_inputs() {
        assert_eq!(
            HermineDkg::run(ROWS, COLS, 5, 0, 1).err().unwrap(),
            DkgError::BadParameters
        ); // t = 0
        assert_eq!(
            HermineDkg::run(ROWS, COLS, 3, 4, 1).err().unwrap(),
            DkgError::BadParameters
        ); // t > n
        assert_eq!(
            HermineDkg::run(0, COLS, 5, 3, 1).err().unwrap(),
            DkgError::BadParameters
        ); // no rows
        assert_eq!(
            HermineDkg::run(ROWS, 0, 5, 3, 1).err().unwrap(),
            DkgError::BadParameters
        ); // no cols
        assert_eq!(
            HermineDkg::run(ROWS, COLS, Q, 3, 1).err().unwrap(),
            DkgError::BadParameters
        ); // n ≥ q

        let (a, ds) = dealings();
        // Missing a dealing.
        assert_eq!(
            HermineDkg::aggregate(a.clone(), MEMBERS, THRESHOLD, &ds[..4])
                .err()
                .unwrap(),
            DkgError::BadParameters
        );
        // Duplicated dealer (index 2 appears where 3 should be).
        let mut dup = ds.clone();
        dup[2] = dup[1].clone();
        assert_eq!(
            HermineDkg::aggregate(a.clone(), MEMBERS, THRESHOLD, &dup)
                .err()
                .unwrap(),
            DkgError::BadParameters
        );
        // Wrong commitment count (a truncated broadcast).
        let mut short = ds.clone();
        short[0].commitments.pop();
        assert_eq!(
            HermineDkg::aggregate(a, MEMBERS, THRESHOLD, &short)
                .err()
                .unwrap(),
            DkgError::BadParameters
        );
        // dkg_deal itself refuses out-of-range dealers.
        let (a, _) = dealings();
        assert!(dkg_deal(&a, 0, MEMBERS, THRESHOLD, 1).is_none());
        assert!(dkg_deal(&a, MEMBERS + 1, MEMBERS, THRESHOLD, 1).is_none());
    }
}
