//! The MINA-NATIVE-HASH TERMINAL config — `DreggMinaConfig`.
//!
//! The Mina twin of [`crate::dregg_outer_config::DreggOuterConfig`]. One
//! sentence: a proof minted under this config has **Mina-Poseidon Merkle roots
//! and a Mina-Poseidon transcript**, so an o1js/Kimchi verifier hashes
//! **natively** instead of emulating a foreign 31-bit prime.
//!
//! ## ⚑ SUBSTRATE (HOUSE LAW #1)
//!
//! **No AIR, no constraint, no gadget, no `air_accepts` here.** This is prover
//! plumbing — which prime field the commitment hash lives in. `Val = BabyBear`
//! and `Challenge = EF4` are unchanged, every table AIR is untouched, and the
//! AIRs themselves remain Lean-authored. Swapping the hash field changes what
//! the commitment is *computed in*, not what is *being proved*.
//!
//! ## Why this exists — the measurement
//!
//! `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` measured a Mina-side verify of
//! dregg's root at **24,574,325 rows**, ~76% of it hashing, because the proof
//! commits with Poseidon2-over-BabyBear and a Pasta circuit must EMULATE that:
//! **2,600.5 measured rows per permutation**, 2,677 per Merkle level.
//!
//! `bridge/mina-zkapp/scripts/mina-poseidon-merkle-rows.ts` then measured the
//! same objects hashed with Mina-Poseidon:
//!
//! | | Poseidon2-BabyBear (deployed) | Mina-Poseidon (this config) | |
//! |---|---:|---:|---:|
//! | one permutation | 2,600.5 rows | **13** | 200× |
//! | one Merkle level (swap + hash) | 2,677 | **15.5** | 173× |
//! | one depth-22 opening | 58,971 | **342** | 172× |
//! | all 19 queries × 238 levels | 1.21 × 10⁷ | **7.0 × 10⁴** | 173× |
//!
//! Both columns are `getRows()` on o1js circuits KAT'd against the Rust
//! hashers, not estimates. This is the same lever `DreggOuterConfig` pulled for
//! Ethereum (a measured 40.9M → 1.0M R1CS collapse), applied to the chain that
//! did not have it.
//!
//! ## Wiring — two swaps vs [`crate::dregg_outer_config`], nothing else
//!
//! | piece | ETH (`DreggOuterConfig`) | MINA (this) |
//! |---|---|---|
//! | permutation | `Poseidon2Bn254<3>` (α=5, 8 full + 56 partial) | [`MinaPoseidonPerm`] (α=7, **55 full**) |
//! | hash field | `Bn254` (2^253.60) | [`PastaFp`] (**2^254.00**) |
//! | leaf hash | `MultiField32PaddingFreeSponge<_, _, _, 3, 2, 1>` | **same shape** |
//! | compression | `TruncatedPermutation<_, 2, 1, 3>` | **same shape** |
//! | challenger | `MultiField32Challenger<_, _, _, 3, 2>` | **same shape** |
//! | digest | `[Bn254; 1]` | `[PastaFp; 1]` — ONE native element per node |
//! | `Val` / `Challenge` / Pcs shape | BabyBear / EF4 / `TwoAdicFriPcs` | **unchanged** |
//!
//! The three derived challenger constants come out **identical** to the ETH
//! wrap's (absorb radix 31, 8 limbs per rate slot, 7 squeezed limbs) — pinned
//! in `circuit-prove/p3-pasta/tests/mina_poseidon_gold_kat.rs`. So
//! `chain/gnark/multifield_challenger.go`'s numbers are simultaneously the
//! Mina-side transcript spec.
//!
//! ## ⚑ THE FRI KNOBS ARE DELIBERATELY THE ETH WRAP'S, AND THAT IS THE POINT
//!
//! [`MINA_FRI_LOG_BLOWUP`] = 3, arity 2, 38 queries, 16 query-PoW bits,
//! commit-PoW 0, final-poly length 0 — **byte-identical to
//! `DreggOuterConfig`**, asserted in this module's tests.
//!
//! That is not laziness, it is the soundness argument. The FRI ledger reading
//! of this config is *the same entry* the ETH wrap already has
//! (`FriLedgerSound.ethWrapOuterConfig`, `3·38 + 16 = 130` conjectured bits),
//! so **the only thing that changes between the deployed terminal and this one
//! is the hash field.** A config that moved the knobs AND the hash would need
//! its own ledger entry before anyone could say what it bought, and
//! `docs/MINA-FACING-TERMINAL-OPTIONS.md` §8 is explicit that the query count
//! is not a knob this lane may turn on its own reasoning.
//!
//! ⚑ **What Mina makes newly available, named and NOT taken here:** the ETH
//! config's arity and commit-PoW are pinned by *gnark*, not by soundness —
//! `friFoldRowArity2` hardcodes the arity-2 fold and `CheckWitness(ch,
//! cfg.CommitPowBits, 0)` hardcodes a zero PoW witness
//! (`dregg_outer_config.rs:139-158`). **Neither binds a Mina verifier.** The
//! measured value of taking them is small and is why they are not taken
//! blind: after the hash swap, `arity 8 + cap_height 8` together are worth
//! **1.0%** of the Mina-side budget (they shorten Merkle paths, and Merkle
//! paths are ~2% of a Pasta-hashed verify). The query count is the lever that
//! matters — Mina's cost is linear in it — and it is a soundness decision, not
//! a performance one.
//!
//! ## ⚑ WHAT THIS COSTS ON THE DREGG SIDE
//!
//! Kimchi's Poseidon is **55 full rounds** at width 3 with α = 7, against
//! `Poseidon2Bn254<3>`'s 8 full + 56 partial — roughly **2× the S-boxes per
//! permutation**, and *every* round is full (no partial-round saving). The
//! measured price is in `tests/mina_terminal_tooth.rs`. This is dregg-side
//! prover time traded for ~170× fewer Kimchi rows on Mina's side.
//!
//! ## HONEST SCOPE
//!
//! This module builds and validates the CONFIG. What it does **not** do:
//! - it does not deploy anything, pin a VK on chain, or touch the root's knobs
//!   (all ember-gated, `docs/MINA-FACING-TERMINAL-OPTIONS.md` §6);
//! - it does not make the o1js verifier hash natively — that is a separate
//!   change to `bridge/mina-zkapp/src/Poseidon2Merkle.ts`'s permutation, and
//!   until it lands the Mina side still emulates BabyBear no matter what this
//!   config commits with. **A config that nothing consumes is a lever that is
//!   built, not pulled**, and this doc says so rather than letting the row
//!   counts above read as deployed.
//!
//! Landed on top of it: [`crate::apex_shrink`]'s split-config shrink is now
//! generic over the outer config, so a real apex shrinks to a Mina-hashed
//! terminal proof (`tests/mina_terminal_tooth.rs`).

use std::sync::Arc;

use p3_baby_bear::BabyBear;
use p3_challenger::MultiField32Challenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_pasta::{MinaPoseidonPerm, PastaCompress, PastaFp};
use p3_symmetric::MultiField32PaddingFreeSponge;
use p3_uni_stark::{StarkConfig, StarkGenericConfig};

// Re-export the crate's own names so a reader of this module never has to
// guess which `PastaFp` / permutation is meant.
pub use p3_pasta::{
    PASTA_DIGEST_ELEMS as MINA_DIGEST_ELEMS, PASTA_RATE as MINA_RATE, PASTA_WIDTH as MINA_WIDTH,
};

// ============================================================================
// Type wiring
// ============================================================================

/// Challenge extension degree — unchanged from every other dregg config.
/// `|F| = babyBearP^4 ≈ 2^123.6` is the denominator of the per-fold soundness,
/// so the FRI ledger gate pins it.
pub const MINA_EXT_DEGREE: usize = 4;
const D: usize = MINA_EXT_DEGREE;

/// FRI log blowup — **3, the ETH wrap's value**. See the module doc: the knob
/// set is deliberately identical so the ledger reading is the already-modeled
/// `FriLedgerSound.ethWrapOuterConfig` and the hash field is the only change.
pub const MINA_FRI_LOG_BLOWUP: usize = 3;
/// FRI query count — 38. `3·38 + 16 = 130` conjectured bits.
pub const MINA_FRI_NUM_QUERIES: usize = 38;
/// FRI query proof-of-work bits — 16.
pub const MINA_FRI_QUERY_POW_BITS: usize = 16;
/// FRI fold arity exponent — 1, i.e. fold by 2.
///
/// ⚑ On the ETH config this `1` is a **gnark constraint**
/// (`friFoldRowArity2`). Here it is a CHOICE, and it is the conservative one:
/// arity is a soundness lever (`Dregg2.Circuit.FriArityTransfer` prices it at
/// `log₂(m−1)` bits), the o1js FRI walk already implements and KATs the
/// arity-2 fold, and after the hash swap raising it is worth ~1% of the
/// Mina-side budget.
pub const MINA_FRI_MAX_LOG_ARITY: usize = 1;
/// FRI final-polynomial length exponent — 0 (a constant final poly).
pub const MINA_FRI_LOG_FINAL_POLY_LEN: usize = 0;
/// FRI commit-phase proof-of-work bits — 0.
///
/// ⚑ On the ETH config this `0` is **forced**: the gnark circuit passes a
/// hardcoded zero witness and a fixture test fails closed on anything else, so
/// raising it there is a fresh Groth16 setup. **Nothing forces it here.** It is
/// left at 0 so this config's ledger reading is the ETH wrap's; raising it is a
/// real (cheap) lever that needs its own ledger entry first.
pub const MINA_FRI_COMMIT_POW_BITS: usize = 0;

/// Trace/arithmetic field — UNCHANGED. Only hashing moves to Pasta.
pub type MinaVal = BabyBear;
/// Challenge field — unchanged degree-4 BabyBear extension.
pub type MinaChallenge = BinomialExtensionField<BabyBear, D>;
/// The Mina-native permutation: kimchi's own Poseidon over Pasta Fp.
pub type MinaPerm = MinaPoseidonPerm;
/// Leaf hash: BabyBear rows → one Pasta digest.
///
/// ⚑ **16 BabyBear lanes per permutation** (8 shifted radix-2^31 limbs per rate
/// slot × rate 2), against the deployed `PaddingFreeSponge<_, 16, 8, 8>`'s
/// **8**. Half the permutations, and each one 200× cheaper on Mina.
pub type MinaHash = MultiField32PaddingFreeSponge<
    BabyBear,
    PastaFp,
    MinaPerm,
    MINA_WIDTH,
    MINA_RATE,
    MINA_DIGEST_ELEMS,
>;
/// 2-to-1 node compression: permute `[left, right, 0]`, take lane 0 — which IS
/// o1js `Poseidon.hash([left, right])`, one native gate chain, 13 measured rows.
pub type MinaCompress = PastaCompress;
/// The Mina-native MMCS over BabyBear matrices.
pub type MinaValMmcs =
    MerkleTreeMmcs<BabyBear, PastaFp, MinaHash, MinaCompress, 2, MINA_DIGEST_ELEMS>;
/// Extension-field MMCS (FRI commit phase).
pub type MinaChallengeMmcs = ExtensionMmcs<BabyBear, MinaChallenge, MinaValMmcs>;
/// The MultiField Fiat–Shamir challenger: samples in BabyBear, sponge over Pasta.
pub type MinaChallenger =
    MultiField32Challenger<BabyBear, PastaFp, MinaPerm, MINA_WIDTH, MINA_RATE>;
type MinaDft = Radix2DitParallel<BabyBear>;
/// The Mina PCS: the SAME `TwoAdicFriPcs` shape, over the Pasta-native MMCS.
pub type MinaPcs = TwoAdicFriPcs<BabyBear, MinaDft, MinaValMmcs, MinaChallengeMmcs>;
type MinaStarkConfig = StarkConfig<MinaPcs, MinaChallenge, MinaChallenger>;

/// The Mina-facing terminal config. `StarkGenericConfig` with
/// `Val = BabyBear`, `Challenge = EF4`, **Mina-Poseidon commitments +
/// transcript**.
///
/// Like [`crate::dregg_outer_config::DreggOuterConfig`] it deliberately does
/// NOT implement `FriRecursionConfig`: no layer verifies a terminal proof
/// in-circuit on the dregg side — Mina verifies it, in Kimchi.
#[derive(Clone)]
pub struct DreggMinaConfig {
    config: Arc<MinaStarkConfig>,
}

impl core::ops::Deref for DreggMinaConfig {
    type Target = MinaStarkConfig;
    fn deref(&self) -> &MinaStarkConfig {
        &self.config
    }
}

impl StarkGenericConfig for DreggMinaConfig {
    type Challenge = MinaChallenge;
    type Challenger = MinaChallenger;
    type Pcs = MinaPcs;

    fn pcs(&self) -> &MinaPcs {
        self.config.pcs()
    }

    fn initialise_challenger(&self) -> MinaChallenger {
        self.config.initialise_challenger()
    }
}

// ============================================================================
// Config constructors
// ============================================================================

/// Build a [`DreggMinaConfig`] with explicit FRI knobs.
///
/// Use [`create_mina_config`] for the production shape; this variant exists so
/// tests/probes can run cheaper shapes without redefining the hash wiring.
pub fn create_mina_config_with_fri(
    log_blowup: usize,
    log_final_poly_len: usize,
    max_log_arity: usize,
    num_queries: usize,
    commit_pow_bits: usize,
    query_pow_bits: usize,
) -> DreggMinaConfig {
    let perm = MinaPoseidonPerm;
    let hash = MinaHash::new(perm).expect("BabyBear order < Pasta order, RATE < WIDTH");
    let compress = MinaCompress::new(perm);
    // cap_height = 0: a single Pasta root per commitment, which is what makes a
    // Mina-side opening walk exactly one 13-row Poseidon per level.
    let val_mmcs = MinaValMmcs::new(hash, compress, 0);
    let challenge_mmcs = MinaChallengeMmcs::new(val_mmcs.clone());
    let fri_params = FriParameters {
        log_blowup,
        log_final_poly_len,
        max_log_arity,
        num_queries,
        commit_proof_of_work_bits: commit_pow_bits,
        query_proof_of_work_bits: query_pow_bits,
        mmcs: challenge_mmcs,
    };
    let pcs = MinaPcs::new(MinaDft::default(), val_mmcs, fri_params);
    let challenger = MinaChallenger::new(perm).expect("BabyBear order < Pasta order, RATE < WIDTH");
    DreggMinaConfig {
        config: Arc::new(StarkConfig::new(pcs, challenger)),
    }
}

/// The production Mina-facing terminal config: Mina-Poseidon hashing at
/// **log_blowup 3, arity-2 folds, 38 queries, 16 query-PoW bits** — the ETH
/// wrap's exact knob set, so the FRI ledger reading is the already-modeled
/// `FriLedgerSound.ethWrapOuterConfig` and the hash field is the only change.
pub fn create_mina_config() -> DreggMinaConfig {
    thread_local! {
        static MINA_CONFIG: DreggMinaConfig = create_mina_config_with_fri(
            MINA_FRI_LOG_BLOWUP,
            MINA_FRI_LOG_FINAL_POLY_LEN,
            MINA_FRI_MAX_LOG_ARITY,
            MINA_FRI_NUM_QUERIES,
            MINA_FRI_COMMIT_POW_BITS,
            MINA_FRI_QUERY_POW_BITS,
        );
    }
    MINA_CONFIG.with(|c| c.clone())
}

// ============================================================================
// Validation tests
// ============================================================================

#[cfg(test)]
mod tests {
    use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
    use p3_field::integers::QuotientMap;
    use p3_field::{PrimeCharacteristicRing, PrimeField};
    use p3_matrix::dense::RowMajorMatrix;
    use p3_symmetric::{MerkleCap, PseudoCompressionFunction};
    use p3_uni_stark::{Proof, prove, verify};

    use super::*;
    use crate::dregg_outer_config::{
        OUTER_EXT_DEGREE, OUTER_FRI_COMMIT_POW_BITS, OUTER_FRI_LOG_BLOWUP,
        OUTER_FRI_LOG_FINAL_POLY_LEN, OUTER_FRI_MAX_LOG_ARITY, OUTER_FRI_NUM_QUERIES,
        OUTER_FRI_QUERY_POW_BITS,
    };

    /// ⚑ The soundness claim of this module, as a test rather than a sentence:
    /// **the Mina terminal's FRI knobs are the ETH wrap's, element for element.**
    ///
    /// The whole security argument for this config is "the ledger entry is
    /// unchanged; only the hash field moved". If a future edit moves one knob
    /// here, that argument silently stops holding — and it would hold *plausibly*
    /// for a long time, because every number involved is a small integer. So the
    /// argument is pinned where it can go red.
    #[test]
    fn mina_terminal_knobs_are_the_eth_wraps_knobs() {
        assert_eq!(MINA_FRI_LOG_BLOWUP, OUTER_FRI_LOG_BLOWUP);
        assert_eq!(MINA_FRI_NUM_QUERIES, OUTER_FRI_NUM_QUERIES);
        assert_eq!(MINA_FRI_QUERY_POW_BITS, OUTER_FRI_QUERY_POW_BITS);
        assert_eq!(MINA_FRI_MAX_LOG_ARITY, OUTER_FRI_MAX_LOG_ARITY);
        assert_eq!(MINA_FRI_LOG_FINAL_POLY_LEN, OUTER_FRI_LOG_FINAL_POLY_LEN);
        assert_eq!(MINA_FRI_COMMIT_POW_BITS, OUTER_FRI_COMMIT_POW_BITS);
        assert_eq!(MINA_EXT_DEGREE, OUTER_EXT_DEGREE);
        // The conjectured-bit identity the ledger entry is named for.
        assert_eq!(
            MINA_FRI_LOG_BLOWUP * MINA_FRI_NUM_QUERIES + MINA_FRI_QUERY_POW_BITS,
            130
        );
    }

    /// Minimal 2-column Fibonacci AIR — the same shape `dregg_outer_config`'s
    /// round-trip uses, so the two configs are exercised on one object.
    struct MinaFibAir;

    impl<F> BaseAir<F> for MinaFibAir {
        fn width(&self) -> usize {
            2
        }
        fn num_public_values(&self) -> usize {
            3
        }
        fn max_constraint_degree(&self) -> Option<usize> {
            Some(2)
        }
    }

    impl<AB: AirBuilder> Air<AB> for MinaFibAir {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let pis = builder.public_values();
            let (a, b, x) = (pis[0], pis[1], pis[2]);

            let local = main.current_slice();
            let next = main.next_slice();

            let mut when_first_row = builder.when_first_row();
            when_first_row.assert_eq(local[0], a);
            when_first_row.assert_eq(local[1], b);

            let mut when_transition = builder.when_transition();
            when_transition.assert_eq(local[1], next[0]);
            when_transition.assert_eq(local[0] + local[1], next[1]);

            builder.when_last_row().assert_eq(local[1], x);
        }
    }

    fn fib_trace(n: usize) -> (RowMajorMatrix<BabyBear>, Vec<BabyBear>) {
        assert!(n.is_power_of_two());
        let mut values = Vec::with_capacity(2 * n);
        let (mut a, mut b) = (BabyBear::ZERO, BabyBear::ONE);
        for _ in 0..n {
            values.push(a);
            values.push(b);
            let next = a + b;
            a = b;
            b = next;
        }
        let pis = vec![BabyBear::ZERO, BabyBear::ONE, values[2 * n - 1]];
        (RowMajorMatrix::new(values, 2), pis)
    }

    /// The config's own gate: prove a STARK under it and verify it — the
    /// Mina-native MMCS + MultiField challenger round-trip at the production
    /// FRI knobs, with the commitment asserted to really be Pasta-native.
    #[test]
    fn dregg_mina_config_proves_and_verifies_synthetic_stark() {
        let config = create_mina_config();
        let air = MinaFibAir;
        let (trace, pis) = fib_trace(16);

        let mut proof = prove(&config, &air, trace, &pis);

        // The swing vs a BabyBear-committed proof, pinned at the TYPE level: a
        // `Proof<DreggRecursionConfig>` commitment is
        // `MerkleCap<BabyBear, [BabyBear; 8]>`; THIS proof's commitment is one
        // native Pasta element per root.
        let trace_cap: &MerkleCap<BabyBear, [PastaFp; MINA_DIGEST_ELEMS]> =
            &proof.commitments.trace;
        for root in trace_cap.roots() {
            assert!(
                root[0].as_canonical_biguint().bits() > 31,
                "trace root fits in 31 bits — commitment does not look Pasta-native"
            );
        }

        verify(&config, &air, &proof, &pis)
            .expect("Mina-config proof must verify under the same config");

        // REJECT polarity 1: wrong public values must not verify.
        let bad_pis = vec![BabyBear::ZERO, BabyBear::ONE, BabyBear::from_int(12345u32)];
        assert!(
            verify(&config, &air, &proof, &bad_pis).is_err(),
            "Mina config accepted wrong public values"
        );

        // REJECT polarity 2: a tampered opened value must not verify.
        proof.opened_values.trace_local[0] += MinaChallenge::ONE;
        assert!(
            verify(&config, &air, &proof, &pis).is_err(),
            "Mina config accepted a tampered opening"
        );
    }

    /// The transcript boundary constants a Mina-side verifier must reproduce.
    /// Identical to the ETH wrap's — which is a *result*, not a design choice
    /// (Pasta and BN254 happen to land on the same three), and it is worth
    /// having as a test because a Mina verifier written from the gnark spec is
    /// then correct rather than accidentally correct.
    #[test]
    fn dregg_mina_challenger_pack_split_matches_the_eth_wrap() {
        let challenger = create_mina_config().initialise_challenger();
        assert_eq!(challenger.absorb_radix_bits(), 31);
        assert_eq!(challenger.absorb_num_f_elms(), 8);
        assert_eq!(challenger.squeeze_num_f_elms(), 7);
    }

    /// The MMCS compression IS `Poseidon.hash([l, r])` — asserted here too, at
    /// the config's own type, so the identity cannot be true in `p3-pasta` and
    /// false in the thing that ships.
    #[test]
    fn dregg_mina_compress_is_o1js_poseidon_hash_of_a_pair() {
        let compress = MinaCompress::new(MinaPoseidonPerm);
        let (l, r) = (
            PastaFp::from_int(123456789u64),
            PastaFp::from_int(987654321u64),
        );
        assert_eq!(compress.compress([[l], [r]]), [p3_pasta::compress(l, r)]);
        // The o1js gold value for `Poseidon.hash([123456789, 987654321])`,
        // as canonical LITTLE-endian bytes (the hex below is the big-endian
        // literal `poseidon-kat.ts` prints, reversed).
        let want = {
            let hex = "0ef95ec0c90a0dc01fb3010b91b8ddfdbbb7f166f0bf5b8f7ef26b90ae5230d8";
            let mut bytes: Vec<u8> = (0..hex.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
                .collect();
            bytes.reverse();
            PastaFp::from_canonical_bytes_le(&bytes).expect("gold vector is canonical")
        };
        assert_eq!(compress.compress([[l], [r]]), [want]);
        // REJECT: order matters (a symmetric compress lets a prover swap siblings).
        assert_ne!(compress.compress([[l], [r]]), compress.compress([[r], [l]]));
    }

    /// Keep the `Proof` type name resolvable — a compile-time pin that the
    /// round-trip above really is a uni-stark `Proof<DreggMinaConfig>`.
    #[allow(dead_code)]
    fn _type_pin(p: Proof<DreggMinaConfig>) -> Proof<DreggMinaConfig> {
        p
    }
}
