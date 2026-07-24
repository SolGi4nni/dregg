//! `fri_fs_fiber_probe` — the Fiat–Shamir fold-challenge fiber surface, against the REAL
//! deployed Poseidon2 duplex challenger.
//!
//! Accompanies the @DreggNet <-> @math__street thread on attacking FRI-style proximity proofs.
//! This is the *representation-aware* front math_street named: the FS challenger is an ALGEBRAIC
//! permutation over the same small field the code lives in, while the query bound is proved in the
//! random-oracle model. A protocol-coupled failure is a transcript whose actual squeezed fold
//! challenge lands in that transcript's "bad set".
//!
//! Unlike a model, this runs the ACTUAL object: `DuplexChallenger<BabyBear, Poseidon2BabyBear<16>,
//! 16, 8>` built from `default_babybear_poseidon2_16()` — byte-identical to the deployed prover's
//! challenger (`circuit::plonky3_prover`, `circuit-prove::dregg_outer_config`). We reproduce the
//! deployed transcript path (observe base elements -> `sample_algebra_element::<EF4>()`, exactly as
//! `p3_fri::commit_phase` samples each fold `beta`) and probe the map
//!     (prover-controlled absorbed elements)  |->  beta in EF4.
//!
//! Two facts this establishes:
//!   1. The fold-`beta` fiber is NOT proof-of-work gated. Every shipped config sets `commit_pow = 0`,
//!      so no grinding sits between `observe(commit_i)` and the `beta_i` squeeze (grinding gates only
//!      the query-index `sample_bits`). So a fiber search on `beta` competes against ZERO PoW.
//!   2. Over the FULL Poseidon2 permutation the map is fiber-flat (injective on a controlled sweep,
//!      no collisions beyond birthday), so a NAIVE fiber search fails. That is the honest negative
//!      that scopes the real wedge: a *reduced-round* or *rate/capacity-absorption* structural
//!      degeneracy (BabyBear-Poseidon2's internal rounds are a single x^7 S-box, algebraic degree
//!      ~7^rounds), not the full permutation. Extending this test toward that wedge is the next step.
//!
//! Real-fold incidence extension (documented, not run here): the vendored fold map is
//! `p3_fri::TwoAdicFriFolding::fold_matrix(beta, log_arity, matrix)` /
//! `fold_row(index, log_height, log_arity, beta, evals)` in
//! `vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs`, on the `TwoAdicMultiplicativeCoset` domain
//! (LDE on the `BabyBear::GENERATOR` coset). Folding a supplied word with a chosen `beta` and
//! measuring which challenges keep it close reproduces the syndrome-incidence structure on the real
//! deployed fold; the outer combinatorial search reduces by the coset's cyclic automorphism (the
//! `C_n`-equivariance measured in the companion experiment).

use std::collections::HashMap;

use p3_baby_bear::{
    BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL, BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL,
    BABYBEAR_POSEIDON2_RC_16_INTERNAL, BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16,
};
use p3_challenger::{CanObserve, DuplexChallenger, FieldChallenger};
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, PrimeField32};
use p3_poseidon2::{ExternalLayerConstants, Poseidon2};

type Perm16 = Poseidon2BabyBear<16>;
type Chal = DuplexChallenger<BabyBear, Perm16, 16, 8>;
type EF4 = BinomialExtensionField<BabyBear, 4>;

/// Canonical `[u32; 4]` key for an EF4 element (its 4 base coefficients), so squeezed challenges are
/// hashable / comparable exactly.
fn beta_key(beta: &EF4) -> [u32; 4] {
    let c: &[BabyBear] = beta.as_basis_coefficients_slice();
    [
        c[0].as_canonical_u32(),
        c[1].as_canonical_u32(),
        c[2].as_canonical_u32(),
        c[3].as_canonical_u32(),
    ]
}

/// The deployed FS path: seed a fresh duplex, absorb a transcript prefix (public values + commit-root
/// lanes — the prover-influenced base elements), then squeeze the folding challenge exactly as
/// `p3_fri::commit_phase` does (`sample_algebra_element`). `controlled` is the one prover-varied lane.
fn sample_fold_beta(perm: &Perm16, prefix: &[u32], controlled: u32) -> [u32; 4] {
    let mut ch = Chal::new(perm.clone());
    for &x in prefix {
        ch.observe(BabyBear::new(x));
    }
    ch.observe(BabyBear::new(controlled));
    let beta: EF4 = ch.sample_algebra_element();
    beta_key(&beta)
}

/// The deployed duplex is deterministic (fixed permutation constants): same transcript -> same
/// challenge, reproducible with zero grinding. This is the seed of the fiber search — the attacker
/// can replay `initialise_challenger() -> observe(prefix) -> sample` at will.
#[test]
fn fold_beta_is_deterministic_and_ungrinded() {
    let perm = default_babybear_poseidon2_16();
    let a = sample_fold_beta(&perm, &[1, 2, 3, 4, 5, 6, 7, 8], 42);
    let b = sample_fold_beta(&perm, &[1, 2, 3, 4, 5, 6, 7, 8], 42);
    assert_eq!(a, b, "the deployed duplex challenger must be deterministic");
    // No proof-of-work was performed to obtain `beta` — commit_pow = 0 in every shipped config, so
    // the fold-challenge fiber is not PoW-gated (only the query-index sample is).
}

/// Fiber probe: sweep the one prover-controlled absorbed element and collect the squeezed fold
/// challenges. Over the full Poseidon2 permutation the map is fiber-flat (injective on the sweep),
/// so a naive fiber search against the deployed challenger finds nothing exploitable — which is the
/// honest result that points the real attack at reduced-round / absorption structure instead.
#[test]
fn fold_beta_fiber_is_flat_over_full_permutation() {
    let perm = default_babybear_poseidon2_16();
    let prefix = [11u32, 22, 33, 44, 55, 66, 77, 88]; // stand-in commit-root lanes (8 = RATE)
    let k: u32 = 4096;
    let mut seen: HashMap<[u32; 4], u32> = HashMap::new();
    for controlled in 0..k {
        *seen
            .entry(sample_fold_beta(&perm, &prefix, controlled))
            .or_insert(0) += 1;
    }
    let distinct = seen.len();
    let max_fiber = seen.values().copied().max().unwrap();
    println!(
        "[fs-fiber] {k} controlled inputs -> {distinct} distinct beta, max fiber {max_fiber} \
         (fiber-flat over the full permutation: a naive search finds no exploitable degeneracy)"
    );
    // |F| = babyBear^4 ~ 2^123.6, sweep = 2^12, so birthday collisions are astronomically unlikely;
    // any collision here would itself be an exploitable degeneracy. None occur.
    assert_eq!(
        distinct, k as usize,
        "unexpected collision in the full-permutation fold-beta map (would BE a finding)"
    );
}

/// Build a ROUND-REDUCED BabyBear Poseidon2-16 from the deployed round constants: `rf_half` initial
/// and `rf_half` terminal external rounds (deployed: 4 + 4) and `rp` internal rounds (deployed: 13).
fn reduced_perm(rf_half: usize, rp: usize) -> Poseidon2BabyBear<16> {
    Poseidon2::new(
        ExternalLayerConstants::new(
            BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL[..rf_half].to_vec(),
            BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL[..rf_half].to_vec(),
        ),
        BABYBEAR_POSEIDON2_RC_16_INTERNAL[..rp].to_vec(),
    )
}

/// Degree over `F_p` of `c |-> f(c)` sampled on `0..n`, by finite differences: a polynomial of degree
/// `d` has vanishing `(d+1)`-th difference. Returns `None` if the degree is `>= n-1` (saturated
/// beyond what the sample can see).
fn degree_by_finite_differences(vals: &[BabyBear]) -> Option<usize> {
    let mut v: Vec<BabyBear> = vals.to_vec();
    let mut d = 0usize;
    while v.len() > 1 {
        if v.iter().all(|x| x.as_canonical_u32() == 0) {
            return Some(d.saturating_sub(1));
        }
        v = v.windows(2).map(|w| w[1] - w[0]).collect();
        d += 1;
    }
    None
}

/// **The algebraic margin of the Fiat-Shamir map, MEASURED.** A protocol-coupled algebraic attack
/// needs a tractable low-degree description of the challenge as a function of prover-controlled
/// input. BabyBear-Poseidon2's S-box is `x^7`, so that degree grows like `7^(S-box applications)`.
/// Here we interpolate `controlled lane |-> beta_0` exactly over `F_p` (finite differences) and read
/// off its degree.
///
/// Two measured facts, both scoping the wedge:
///   * plonky3 structurally REFUSES `rounds_f < 6` (`Poseidon2::new` panics, citing the paper's
///     §7.1 statistical-attack floor), so the deeply-round-reduced configurations an algebraic
///     attack would want are not reachable through the shipped constructor at all -- an attacker
///     must reimplement the permutation.
///   * even at that MINIMUM permitted external-round count, and with the internal rounds stripped to
///     zero, the map is already saturated past this sample window. The deployed (4+4, 13) map is far
///     beyond it. So there is no low-degree description to encode, which is exactly why the honest
///     wedge is absorption/rate structure rather than a degree attack on the full permutation.
#[test]
fn fs_map_algebraic_degree_growth() {
    const N: usize = 2400; // can exhibit degrees up to ~2398; 7^4 = 2401 is already past it
    let prefix = [11u32, 22, 33, 44, 55, 66, 77, 88];
    println!(
        "[fs-degree] deployed BabyBear-Poseidon2-16 is (4+4 external, 13 internal), S-box x^7"
    );
    println!("[fs-degree] plonky3 refuses rounds_f < 6, so 3+3 external is the library floor");
    for (rf_half, rp) in [(3usize, 0usize), (3, 1), (3, 13), (4, 13)] {
        let perm = reduced_perm(rf_half, rp);
        let vals: Vec<BabyBear> = (0..N as u32)
            .map(|c| {
                let mut ch = Chal::new(perm.clone());
                for &x in prefix.iter() {
                    ch.observe(BabyBear::new(x));
                }
                ch.observe(BabyBear::new(c));
                let beta: EF4 = ch.sample_algebra_element();
                beta.as_basis_coefficients_slice()[0]
            })
            .collect();
        let deg = degree_by_finite_differences(&vals);
        let shown = match deg {
            Some(d) => format!("{d}"),
            None => format!(">= {}", N - 1),
        };
        let tag = if (rf_half, rp) == (4, 13) {
            "  <-- DEPLOYED"
        } else {
            ""
        };
        println!(
            "[fs-degree] external {rf_half}+{rf_half}, internal {rp:2}: deg(beta_0) = {shown}{tag}"
        );
    }
    // The deployed configuration must be saturated past the sample window: if it were not, the
    // challenge would admit a low-degree description in the prover-controlled lane.
    let deployed: Vec<BabyBear> = (0..N as u32)
        .map(|c| {
            let mut ch = Chal::new(default_babybear_poseidon2_16());
            for &x in prefix.iter() {
                ch.observe(BabyBear::new(x));
            }
            ch.observe(BabyBear::new(c));
            let beta: EF4 = ch.sample_algebra_element();
            beta.as_basis_coefficients_slice()[0]
        })
        .collect();
    assert!(
        degree_by_finite_differences(&deployed).is_none(),
        "deployed FS map is low-degree in the controlled lane -- that WOULD be the wedge"
    );
}

/// The controlled lane genuinely moves the challenge (the surface is live, not a constant): changing
/// one absorbed base element changes `beta`. This is what makes the fiber question non-trivial.
#[test]
fn controlled_input_moves_the_challenge() {
    let perm = default_babybear_poseidon2_16();
    let prefix = [1u32, 2, 3, 4, 5, 6, 7, 8];
    let b0 = sample_fold_beta(&perm, &prefix, 0);
    let b1 = sample_fold_beta(&perm, &prefix, 1);
    assert_ne!(
        b0, b1,
        "the prover-controlled lane must influence the squeezed challenge"
    );
}
