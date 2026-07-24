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

use p3_baby_bear::{BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_challenger::{CanObserve, DuplexChallenger, FieldChallenger};
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, PrimeField32};

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
