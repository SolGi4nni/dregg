//! The BN254-native-hash OUTER ("shrink") STARK config — `DreggOuterConfig`.
//!
//! This is dregg's analogue of RISC0's `identity_p254` and SP1's `shrink` stage
//! (docs/deos/WRAP-NATIVE-HASH-DECISION.md): one extra recursion layer between
//! the BabyBear apex and the gnark Groth16 wrap whose proof is committed and
//! Fiat–Shamired with **Poseidon2 over the BN254 scalar field** instead of
//! Poseidon2-over-BabyBear. Trace/quotient ARITHMETIC stays BabyBear
//! (`Val = BabyBear`, `Challenge = BinomialExtensionField<BabyBear, 4>`);
//! only the HASH field switches. A proof minted under this config has
//! BN254-native Merkle roots and a BN254-native transcript, so the gnark
//! verifier (`chain/gnark/fri_verify_native.go`) hashes natively —
//! the measured 40.9M → 1.0M R1CS collapse of the wrap's hashing term.
//!
//! ## Wiring (two swaps vs [`crate::plonky3_recursion_impl::recursive::DreggRecursionConfig`])
//!
//! | piece | inner (`DreggRecursionConfig`) | outer (this) |
//! |---|---|---|
//! | permutation | `Poseidon2BabyBear<16>` | [`Poseidon2Bn254<3>`] (t=3, α=5, R_F=8, R_P=56) |
//! | leaf hash | `PaddingFreeSponge<_, 16, 8, 8>` | [`MultiField32PaddingFreeSponge<BabyBear, Bn254, _, 3, 2, 1>`] |
//! | compression | `TruncatedPermutation<_, 2, 8, 16>` | [`TruncatedPermutation<_, 2, 1, 3>`] |
//! | digest | `[BabyBear; 8]` | `[Bn254; 1]` — ONE BN254 element per node/root |
//! | challenger | `DuplexChallenger<BabyBear, _, 16, 8>` | [`MultiField32Challenger<BabyBear, Bn254, _, 3, 2>`] |
//! | Val / Challenge / Pcs shape | BabyBear / EF4 / `TwoAdicFriPcs` | **unchanged** |
//!
//! ## Parameters that MUST stay in sync with `chain/gnark` (pinned to the SAME
//! Plonky3 rev `82cfad7`; a mismatch = the gnark verifier rejects valid proofs)
//!
//! 1. **Poseidon2Bn254<3> round constants** — [`RC3_EXT_INITIAL`] /
//!    [`RC3_INTERNAL`] / [`RC3_EXT_TERMINAL`], the HorizenLabs zkhash RC3 table
//!    (`poseidon2_instance_bn256.rs`, the exact reference plonky3 pins). The
//!    byte-identical hex table lives in `chain/gnark/poseidon2_bn254_constants.go`;
//!    both sides are pinned simultaneously by the shared `[0,1,2]` gold KAT
//!    (`dregg_outer_poseidon2_bn254_matches_gnark_gold_kat` here ↔
//!    `TestPoseidon2Bn254RefMatchesGoldKAT` in `poseidon2_bn254_test.go`).
//! 2. **Challenger pack/split** — `MultiField32Challenger<BabyBear, Bn254, _, 3, 2>`:
//!    absorb packs pending BabyBear values with `reduce_packed` in radix
//!    2^31 (`absorb_radix_bits::<BabyBear>() = 31`), 8 limbs per BN254 rate slot
//!    (`max_absorb_injective_limbs = 8`), zero-padded rate + length tag added to
//!    the capacity slot; squeeze splits each rate cell into 7 little-endian
//!    base-p limbs (`squeeze_field_order_num_limbs = 7`), popped from the end.
//!    Gnark twin: `chain/gnark/multifield_challenger.go` (`mfAbsorbRadixBits=31`,
//!    `mfAbsorbNumFElms=8`, `mfSqueezeNumFElms=7`).
//! 3. **Merkle compression** — `TruncatedPermutation<Poseidon2Bn254<3>, 2, 1, 3>`:
//!    `state = [left, right, 0]`, permute, take `state[0]`. Gnark twin:
//!    `Poseidon2Bn254Compress` (`chain/gnark/poseidon2_bn254.go`).
//! 4. **Leaf hash** — `MultiField32PaddingFreeSponge<BabyBear, Bn254, _, 3, 2, 1>`:
//!    a row of canonical BabyBear values is packed with `reduce_packed_shifted`
//!    (radix 2^31, each digit **+1** — the shifted encoding, NOT the challenger's
//!    unshifted pack), 8 limbs per rate slot, 2 rate slots per permutation,
//!    digest = `state[0]`. ⚠ gnark's current `friMerkleLeafHashNative`
//!    (`fri_verify_native.go`) is a measurement stand-in (unshifted pack, 4
//!    coords/word, one compress) that does NOT yet match this sponge — that
//!    port is a NAMED residual on the gnark side (`fri_verify_native.go` names
//!    the production leaf layout as this config's to define; this config now
//!    defines it: the MMCS row sponge above).
//! 5. **FRI knobs** — [`OUTER_FRI_LOG_BLOWUP`]=3 (blowup 8, rebalanced from 6 on
//!    measured data — ~8× faster shrink prove), log_final_poly_len=0,
//!    max_log_arity=1 (fold by 2), [`OUTER_FRI_NUM_QUERIES`]=38, commit_pow=0,
//!    [`OUTER_FRI_QUERY_POW_BITS`]=16 (3·38+16 = 130 conjectured bits)
//!    (`ivc_turn_chain.rs`) and the exact shape the gnark side compiled and
//!    measured (`fri_verify_native_test.go`: R=18 arity-2 rounds, 19 queries,
//!    QueryPowBits 16). Conjectured soundness 6·19+16 = 130 bits, the same bar
//!    as the inner wrap config.
//! 6. **Digest arity** — `DIGEST_ELEMS = 1` (one BN254 element per node),
//!    binary tree (`N = 2`), `cap_height = 0` (single root).
//!
//! ## HONEST SCOPE
//!
//! This module builds and validates the OUTER CONFIG itself: a synthetic STARK
//! (Fibonacci AIR) proves and verifies round-trip under it, with BN254-native
//! commitments (asserted at the type level and by digest magnitude).
//!
//! The two residuals this doc used to name are now closed:
//!
//! - (a) the apex-verifier AIR proven UNDER this config — LANDED in
//!   [`crate::apex_shrink`]. Note the instantiation is a CONFIG SPLIT, not a
//!   `FriRecursionConfig` impl on this type: the verifier circuit is built at
//!   the INNER config (whose `FriRecursionConfig` describes the proof being
//!   verified) and its tables are committed + proven at THIS config. This
//!   config therefore deliberately never implements `FriRecursionConfig` —
//!   nothing verifies an OUTER proof in-circuit; gnark verifies it natively.
//! - (b) a producible real apex — the rotated-pipeline carrier flag-day landed
//!   (`trace_rotated.rs` now documents 59 carriers) and
//!   `tests/apex_shrink_bn254_tooth.rs` folds a real 2-turn chain and shrinks
//!   its apex under this config.
//!
//! Remaining increment (named in [`crate::apex_shrink`]): the gnark fixture
//! export — feeding a real shrink proof's FRI data to `VerifyFriNative`.

use std::sync::Arc;

use p3_baby_bear::BabyBear;
use p3_bn254::{Bn254, Poseidon2Bn254};
use p3_challenger::MultiField32Challenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::PrimeCharacteristicRing;
use p3_field::extension::BinomialExtensionField;
use p3_field::integers::QuotientMap;
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_poseidon2::ExternalLayerConstants;
use p3_symmetric::{MultiField32PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{StarkConfig, StarkGenericConfig};

// ============================================================================
// Type wiring
// ============================================================================

/// Poseidon2Bn254 state width (t = 3 — the only width the pinned fork supports).
pub const OUTER_WIDTH: usize = 3;
/// Sponge/duplex rate in BN254 elements (capacity = 1).
pub const OUTER_RATE: usize = 2;
/// Digest size in BN254 elements: ONE native field element per Merkle node —
/// this is what makes the gnark opening walk one ~243-R1CS compress per level.
pub const OUTER_DIGEST_ELEMS: usize = 1;
/// Challenge extension degree (unchanged from the inner config). Exported as
/// [`OUTER_EXT_DEGREE`]; `|F| = babyBearP ^ D` is the denominator of the outer config's per-fold
/// soundness, so the FRI ledger gate pins it.
const D: usize = OUTER_EXT_DEGREE;

/// The challenge extension degree of the outer shrink — `|F| = babyBearP ^ 4 ≈ 2^123.6`. Exported so
/// `circuit-prove/tests/fri_params_soundness_budget.rs` can pin it against the Lean-modeled
/// `FriLedgerSound.ethWrapOuterConfig.extDeg`.
pub const OUTER_EXT_DEGREE: usize = 4;

/// FRI log blowup. **Rebalanced from 6 → 3 (blowup 64 → 8) on MEASURED data**: the
/// native-hash swap made per-query gnark verify cheap (~243 R1CS/hash), which inverted
/// the original "high-blowup / few-queries" tuning. The shrink PROVE is dominated by the
/// blowup LDE (NTT); at blowup 8 the real-apex shrink measured **~95s vs ~760s at blowup
/// 64 (≈8× faster)**, for a trivial gnark-verify cost bump (1.02M → 1.46M R1CS, both far
/// under the ~5M Groth16 ceiling). Soundness held: 3·38 + 16 = 130 conjectured bits.
/// (blowup 4 / 57 queries panicked — a config edge; blowup 8 is the stable sweet spot.)
pub const OUTER_FRI_LOG_BLOWUP: usize = 3;
/// FRI query count — 38 queries at blowup 8 (+16 PoW) = 3·38+16 = 130 conjectured bits.
pub const OUTER_FRI_NUM_QUERIES: usize = 38;
/// FRI query proof-of-work bits.
pub const OUTER_FRI_QUERY_POW_BITS: usize = 16;
/// FRI fold arity exponent — **1, i.e. fold by 2**: the arity the gnark ETH-wrap verifier implements
/// (`chain/gnark/fri_verify_native.go`'s `friFoldRowArity2` hardcodes the arity-2 fold; the gnark
/// `FriConfig` carries no arity field at all). Was an inline `1` at [`create_outer_config`]'s call
/// site; exported because arity is a SOUNDNESS lever — it sets the degree of the fold's moment curve
/// and so the good-challenge count (`Dregg2.Circuit.FriArityTransfer`), worth `log₂(m−1)` bits.
pub const OUTER_FRI_MAX_LOG_ARITY: usize = 1;
/// FRI final-polynomial length exponent — 0 (a constant final poly). Was an inline `0`; exported so
/// the ledger gate pins the WHOLE knob set rather than the subset that happened to be `const`.
pub const OUTER_FRI_LOG_FINAL_POLY_LEN: usize = 0;

/// Trace/arithmetic field — UNCHANGED: the shrink layer re-verifies BabyBear
/// arithmetic; only hashing moves to BN254.
pub type OuterVal = BabyBear;
/// Challenge field — unchanged degree-4 BabyBear extension.
pub type OuterChallenge = BinomialExtensionField<BabyBear, D>;
/// The BN254-native permutation (t=3, α=5, 8 full + 56 partial rounds).
pub type OuterPerm = Poseidon2Bn254<OUTER_WIDTH>;
/// Leaf hash: BabyBear rows → one BN254 digest (shifted radix-2^31 packing,
/// 8 limbs/slot, 2 slots/permutation).
pub type OuterHash = MultiField32PaddingFreeSponge<
    BabyBear,
    Bn254,
    OuterPerm,
    OUTER_WIDTH,
    OUTER_RATE,
    OUTER_DIGEST_ELEMS,
>;
/// 2-to-1 node compression: permute `[left, right, 0]`, take lane 0 —
/// the twin of `Poseidon2Bn254Compress` (chain/gnark/poseidon2_bn254.go).
pub type OuterCompress = TruncatedPermutation<OuterPerm, 2, OUTER_DIGEST_ELEMS, OUTER_WIDTH>;
/// The BN254-native MMCS over BabyBear matrices. No SIMD packing on either
/// side (BN254 has no packed backend; BabyBear rows enter the sponge scalar).
pub type OuterValMmcs =
    MerkleTreeMmcs<BabyBear, Bn254, OuterHash, OuterCompress, 2, OUTER_DIGEST_ELEMS>;
/// Extension-field MMCS (FRI commit phase) — flattens EF4 rows to BabyBear
/// coordinates, then the same BN254-native tree.
pub type OuterChallengeMmcs = ExtensionMmcs<BabyBear, OuterChallenge, OuterValMmcs>;
/// The MultiField Fiat–Shamir challenger: samples in BabyBear, sponge over BN254.
pub type OuterChallenger =
    MultiField32Challenger<BabyBear, Bn254, OuterPerm, OUTER_WIDTH, OUTER_RATE>;
type OuterDft = Radix2DitParallel<BabyBear>;
/// The outer PCS: the SAME TwoAdicFriPcs shape as the inner config, over the
/// BN254-native MMCS.
pub type OuterPcs = TwoAdicFriPcs<BabyBear, OuterDft, OuterValMmcs, OuterChallengeMmcs>;
type OuterStarkConfig = StarkConfig<OuterPcs, OuterChallenge, OuterChallenger>;

/// The outer "shrink" config. `StarkGenericConfig` with
/// `Val = BabyBear`, `Challenge = EF4`, BN254-native commitments + transcript.
///
/// Mirrors the `DreggRecursionConfig` wrapper shape (Arc-backed, cheap clone).
/// It deliberately does NOT implement `FriRecursionConfig`: the shrink layer
/// ([`crate::apex_shrink`]) builds the apex-verifier circuit at the INNER
/// config and only COMMITS/PROVES under this one, and no layer ever verifies
/// an outer proof in-circuit (gnark verifies it natively).
#[derive(Clone)]
pub struct DreggOuterConfig {
    config: Arc<OuterStarkConfig>,
}

impl core::ops::Deref for DreggOuterConfig {
    type Target = OuterStarkConfig;
    fn deref(&self) -> &OuterStarkConfig {
        &self.config
    }
}

impl StarkGenericConfig for DreggOuterConfig {
    type Challenge = OuterChallenge;
    type Challenger = OuterChallenger;
    type Pcs = OuterPcs;

    fn pcs(&self) -> &OuterPcs {
        self.config.pcs()
    }

    fn initialise_challenger(&self) -> OuterChallenger {
        self.config.initialise_challenger()
    }
}

// ============================================================================
// Poseidon2Bn254 round constants (HorizenLabs zkhash RC3)
// ============================================================================
//
// MACHINE-EXTRACTED from HorizenLabs/poseidon2 `poseidon2_instance_bn256.rs`
// RC3 — the exact table the pinned plonky3 `bn254/src/poseidon2.rs` names as
// its reference (its own test builds the permutation from zkhash's
// POSEIDON2_BN256_PARAMS). This table is BYTE-IDENTICAL to
// `chain/gnark/poseidon2_bn254_constants.go` (rc3ExtInitial / rc3Internal /
// rc3ExtTerminal) — diff the hex directly. The shared [0,1,2] gold KAT below
// pins constants, S-box, layer order, and both linear layers simultaneously
// on both sides.

pub(crate) const RC3_EXT_INITIAL: [[&str; 3]; 4] = [
    [
        "0x1d066a255517b7fd8bddd3a93f7804ef7f8fcde48bb4c37a59a09a1a97052816",
        "0x29daefb55f6f2dc6ac3f089cebcc6120b7c6fef31367b68eb7238547d32c1610",
        "0x1f2cb1624a78ee001ecbd88ad959d7012572d76f08ec5c4f9e8b7ad7b0b4e1d1",
    ],
    [
        "0x0aad2e79f15735f2bd77c0ed3d14aa27b11f092a53bbc6e1db0672ded84f31e5",
        "0x2252624f8617738cd6f661dd4094375f37028a98f1dece66091ccf1595b43f28",
        "0x1a24913a928b38485a65a84a291da1ff91c20626524b2b87d49f4f2c9018d735",
    ],
    [
        "0x22fc468f1759b74d7bfc427b5f11ebb10a41515ddff497b14fd6dae1508fc47a",
        "0x1059ca787f1f89ed9cd026e9c9ca107ae61956ff0b4121d5efd65515617f6e4d",
        "0x02be9473358461d8f61f3536d877de982123011f0bf6f155a45cbbfae8b981ce",
    ],
    [
        "0x0ec96c8e32962d462778a749c82ed623aba9b669ac5b8736a1ff3a441a5084a4",
        "0x292f906e073677405442d9553c45fa3f5a47a7cdb8c99f9648fb2e4d814df57e",
        "0x274982444157b86726c11b9a0f5e39a5cc611160a394ea460c63f0b2ffe5657e",
    ],
];

pub(crate) const RC3_INTERNAL: [&str; 56] = [
    "0x1a1d063e54b1e764b63e1855bff015b8cedd192f47308731499573f23597d4b5",
    "0x26abc66f3fdf8e68839d10956259063708235dccc1aa3793b91b002c5b257c37",
    "0x0c7c64a9d887385381a578cfed5aed370754427aabca92a70b3c2b12ff4d7be8",
    "0x1cf5998769e9fab79e17f0b6d08b2d1eba2ebac30dc386b0edd383831354b495",
    "0x0f5e3a8566be31b7564ca60461e9e08b19828764a9669bc17aba0b97e66b0109",
    "0x18df6a9d19ea90d895e60e4db0794a01f359a53a180b7d4b42bf3d7a531c976e",
    "0x04f7bf2c5c0538ac6e4b782c3c6e601ad0ea1d3a3b9d25ef4e324055fa3123dc",
    "0x29c76ce22255206e3c40058523748531e770c0584aa2328ce55d54628b89ebe6",
    "0x198d425a45b78e85c053659ab4347f5d65b1b8e9c6108dbe00e0e945dbc5ff15",
    "0x25ee27ab6296cd5e6af3cc79c598a1daa7ff7f6878b3c49d49d3a9a90c3fdf74",
    "0x138ea8e0af41a1e024561001c0b6eb1505845d7d0c55b1b2c0f88687a96d1381",
    "0x306197fb3fab671ef6e7c2cba2eefd0e42851b5b9811f2ca4013370a01d95687",
    "0x1a0c7d52dc32a4432b66f0b4894d4f1a21db7565e5b4250486419eaf00e8f620",
    "0x2b46b418de80915f3ff86a8e5c8bdfccebfbe5f55163cd6caa52997da2c54a9f",
    "0x12d3e0dc0085873701f8b777b9673af9613a1af5db48e05bfb46e312b5829f64",
    "0x263390cf74dc3a8870f5002ed21d089ffb2bf768230f648dba338a5cb19b3a1f",
    "0x0a14f33a5fe668a60ac884b4ca607ad0f8abb5af40f96f1d7d543db52b003dcd",
    "0x28ead9c586513eab1a5e86509d68b2da27be3a4f01171a1dd847df829bc683b9",
    "0x1c6ab1c328c3c6430972031f1bdb2ac9888f0ea1abe71cffea16cda6e1a7416c",
    "0x1fc7e71bc0b819792b2500239f7f8de04f6decd608cb98a932346015c5b42c94",
    "0x03e107eb3a42b2ece380e0d860298f17c0c1e197c952650ee6dd85b93a0ddaa8",
    "0x2d354a251f381a4669c0d52bf88b772c46452ca57c08697f454505f6941d78cd",
    "0x094af88ab05d94baf687ef14bc566d1c522551d61606eda3d14b4606826f794b",
    "0x19705b783bf3d2dc19bcaeabf02f8ca5e1ab5b6f2e3195a9d52b2d249d1396f7",
    "0x09bf4acc3a8bce3f1fcc33fee54fc5b28723b16b7d740a3e60cef6852271200e",
    "0x1803f8200db6013c50f83c0c8fab62843413732f301f7058543a073f3f3b5e4e",
    "0x0f80afb5046244de30595b160b8d1f38bf6fb02d4454c0add41f7fef2faf3e5c",
    "0x126ee1f8504f15c3d77f0088c1cfc964abcfcf643f4a6fea7dc3f98219529d78",
    "0x23c203d10cfcc60f69bfb3d919552ca10ffb4ee63175ddf8ef86f991d7d0a591",
    "0x2a2ae15d8b143709ec0d09705fa3a6303dec1ee4eec2cf747c5a339f7744fb94",
    "0x07b60dee586ed6ef47e5c381ab6343ecc3d3b3006cb461bbb6b5d89081970b2b",
    "0x27316b559be3edfd885d95c494c1ae3d8a98a320baa7d152132cfe583c9311bd",
    "0x1d5c49ba157c32b8d8937cb2d3f84311ef834cc2a743ed662f5f9af0c0342e76",
    "0x2f8b124e78163b2f332774e0b850b5ec09c01bf6979938f67c24bd5940968488",
    "0x1e6843a5457416b6dc5b7aa09a9ce21b1d4cba6554e51d84665f75260113b3d5",
    "0x11cdf00a35f650c55fca25c9929c8ad9a68daf9ac6a189ab1f5bc79f21641d4b",
    "0x21632de3d3bbc5e42ef36e588158d6d4608b2815c77355b7e82b5b9b7eb560bc",
    "0x0de625758452efbd97b27025fbd245e0255ae48ef2a329e449d7b5c51c18498a",
    "0x2ad253c053e75213e2febfd4d976cc01dd9e1e1c6f0fb6b09b09546ba0838098",
    "0x1d6b169ed63872dc6ec7681ec39b3be93dd49cdd13c813b7d35702e38d60b077",
    "0x1660b740a143664bb9127c4941b67fed0be3ea70a24d5568c3a54e706cfef7fe",
    "0x0065a92d1de81f34114f4ca2deef76e0ceacdddb12cf879096a29f10376ccbfe",
    "0x1f11f065202535987367f823da7d672c353ebe2ccbc4869bcf30d50a5871040d",
    "0x26596f5c5dd5a5d1b437ce7b14a2c3dd3bd1d1a39b6759ba110852d17df0693e",
    "0x16f49bc727e45a2f7bf3056efcf8b6d38539c4163a5f1e706743db15af91860f",
    "0x1abe1deb45b3e3119954175efb331bf4568feaf7ea8b3dc5e1a4e7438dd39e5f",
    "0x0e426ccab66984d1d8993a74ca548b779f5db92aaec5f102020d34aea15fba59",
    "0x0e7c30c2e2e8957f4933bd1942053f1f0071684b902d534fa841924303f6a6c6",
    "0x0812a017ca92cf0a1622708fc7edff1d6166ded6e3528ead4c76e1f31d3fc69d",
    "0x21a5ade3df2bc1b5bba949d1db96040068afe5026edd7a9c2e276b47cf010d54",
    "0x01f3035463816c84ad711bf1a058c6c6bd101945f50e5afe72b1a5233f8749ce",
    "0x0b115572f038c0e2028c2aafc2d06a5e8bf2f9398dbd0fdf4dcaa82b0f0c1c8b",
    "0x1c38ec0b99b62fd4f0ef255543f50d2e27fc24db42bc910a3460613b6ef59e2f",
    "0x1c89c6d9666272e8425c3ff1f4ac737b2f5d314606a297d4b1d0b254d880c53e",
    "0x03326e643580356bf6d44008ae4c042a21ad4880097a5eb38b71e2311bb88f8f",
    "0x268076b0054fb73f67cee9ea0e51e3ad50f27a6434b5dceb5bdde2299910a4c9",
];

pub(crate) const RC3_EXT_TERMINAL: [[&str; 3]; 4] = [
    [
        "0x1acd63c67fbc9ab1626ed93491bda32e5da18ea9d8e4f10178d04aa6f8747ad0",
        "0x19f8a5d670e8ab66c4e3144be58ef6901bf93375e2323ec3ca8c86cd2a28b5a5",
        "0x1c0dc443519ad7a86efa40d2df10a011068193ea51f6c92ae1cfbb5f7b9b6893",
    ],
    [
        "0x14b39e7aa4068dbe50fe7190e421dc19fbeab33cb4f6a2c4180e4c3224987d3d",
        "0x1d449b71bd826ec58f28c63ea6c561b7b820fc519f01f021afb1e35e28b0795e",
        "0x1ea2c9a89baaddbb60fa97fe60fe9d8e89de141689d1252276524dc0a9e987fc",
    ],
    [
        "0x0478d66d43535a8cb57e9c1c3d6a2bd7591f9a46a0e9c058134d5cefdb3c7ff1",
        "0x19272db71eece6a6f608f3b2717f9cd2662e26ad86c400b21cde5e4a7b00bebe",
        "0x14226537335cab33c749c746f09208abb2dd1bd66a87ef75039be846af134166",
    ],
    [
        "0x01fd6af15956294f9dfe38c0d976a088b21c21e4a1c2e823f912f44961f9a9ce",
        "0x18e5abedd626ec307bca190b8b2cab1aaee2e62ed229ba5a5ad8518d4e5f2a57",
        "0x0fc1bbceba0590f5abbdffa6d3b35e3297c021a3a409926d0e2d54dc1c84fda6",
    ],
];

/// Parse one canonical hex constant into a BN254 scalar. Pure field arithmetic
/// (no bigint dependency): Horner in base 16.
fn bn254_from_hex(hex: &str) -> Bn254 {
    let digits = hex
        .strip_prefix("0x")
        .expect("poseidon2 bn254 constant must be 0x-prefixed");
    let sixteen = Bn254::from_int(16u64);
    digits.bytes().fold(Bn254::ZERO, |acc, b| {
        let d = (b as char)
            .to_digit(16)
            .expect("poseidon2 bn254 constant: bad hex digit") as u64;
        acc * sixteen + Bn254::from_int(d)
    })
}

/// Build the pinned Poseidon2Bn254<3> permutation from the zkhash RC3 table.
///
/// Deterministic (fixed constants) — every call yields the identical
/// permutation, so prover and verifier challengers/MMCSes always agree.
pub fn dregg_poseidon2_bn254() -> OuterPerm {
    let initial: Vec<[Bn254; OUTER_WIDTH]> = RC3_EXT_INITIAL
        .iter()
        .map(|row| row.map(bn254_from_hex))
        .collect();
    let terminal: Vec<[Bn254; OUTER_WIDTH]> = RC3_EXT_TERMINAL
        .iter()
        .map(|row| row.map(bn254_from_hex))
        .collect();
    let internal: Vec<Bn254> = RC3_INTERNAL.iter().map(|s| bn254_from_hex(s)).collect();
    OuterPerm::new(ExternalLayerConstants::new(initial, terminal), internal)
}

// ============================================================================
// Config constructors
// ============================================================================

/// Build a `DreggOuterConfig` with explicit FRI knobs.
///
/// Use [`create_outer_config`] for the production shape; this variant exists so
/// tests/probes can run cheaper shapes without redefining the hash wiring.
pub fn create_outer_config_with_fri(
    log_blowup: usize,
    log_final_poly_len: usize,
    max_log_arity: usize,
    num_queries: usize,
    commit_pow_bits: usize,
    query_pow_bits: usize,
) -> DreggOuterConfig {
    let perm = dregg_poseidon2_bn254();
    let hash = OuterHash::new(perm.clone()).expect("BabyBear order < BN254 order, RATE < WIDTH");
    let compress = OuterCompress::new(perm.clone());
    // cap_height=0: single BN254 root per commitment (matches the gnark
    // verifier's one-root-per-commit-round transcript observe).
    let val_mmcs = OuterValMmcs::new(hash, compress, 0);
    let challenge_mmcs = OuterChallengeMmcs::new(val_mmcs.clone());
    let fri_params = FriParameters {
        log_blowup,
        log_final_poly_len,
        max_log_arity,
        num_queries,
        commit_proof_of_work_bits: commit_pow_bits,
        query_proof_of_work_bits: query_pow_bits,
        mmcs: challenge_mmcs,
    };
    let pcs = OuterPcs::new(OuterDft::default(), val_mmcs, fri_params);
    let challenger =
        OuterChallenger::new(perm).expect("BabyBear order < BN254 order, RATE < WIDTH");
    DreggOuterConfig {
        config: Arc::new(StarkConfig::new(pcs, challenger)),
    }
}

/// The production outer "shrink" config: BN254-native hashing at **log_blowup 3, arity-2 folds, 38
/// queries, 16 query-PoW bits** — the shape `chain/gnark/fri_verify_native.go` was compiled and
/// measured at, and the config the gnark ETH-wrap circuit actually verifies (it has no knobs of its
/// own; `apex_shrink_gnark_export.rs` transports these to it as `FixtureFriShape`).
///
/// ⚑ This doc used to say "the `ir2_leaf_wrap` FRI shape (log_blowup 6 … 19 queries)". That was stale
/// prose left behind by the deliberate 6→3 / 19→38 rebalance documented at [`OUTER_FRI_LOG_BLOWUP`];
/// the `130` total survived the swap (`3·38+16 = 6·19+16`), which is why the wrong sentence read
/// plausibly for so long. The consts below are the truth.
///
/// The knob set is modeled in Lean as `FriLedgerSound.ethWrapOuterConfig` and its soundness ledger is
/// `friLedger` of that — reported per-config by `tests/fri_params_soundness_budget.rs`. ⚑ Its per-fold
/// posture is **118 bits**, NOT the ~112.6 often quoted for "the arity-2 wrap": ~112.6 is a statement
/// about `log_blowup = 6` (`|κ| = 64`), and this config folds a `|κ| = 8` domain
/// (`FriLedgerSound.ethWrap_is_not_the_112_config`).
pub fn create_outer_config() -> DreggOuterConfig {
    // Fixed knobs ⇒ identical config on every call; build once per thread,
    // clone on access (Arc bump). Same caching discipline as
    // `create_recursion_config`.
    thread_local! {
        static OUTER_CONFIG: DreggOuterConfig = create_outer_config_with_fri(
            OUTER_FRI_LOG_BLOWUP,
            OUTER_FRI_LOG_FINAL_POLY_LEN,
            OUTER_FRI_MAX_LOG_ARITY,
            OUTER_FRI_NUM_QUERIES,
            0, // commit_pow_bits
            OUTER_FRI_QUERY_POW_BITS,
        );
    }
    OUTER_CONFIG.with(|c| c.clone())
}

// ============================================================================
// Validation tests
// ============================================================================

#[cfg(test)]
mod tests {
    use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
    use p3_field::PrimeField;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_symmetric::{MerkleCap, Permutation};
    use p3_uni_stark::{Proof, prove, verify};

    use super::*;

    /// Gold KAT: Poseidon2Bn254<3> permutation of [0,1,2], produced by the
    /// HorizenLabs zkhash plain implementation. THE SAME literal vector as
    /// `bn254KATOutHex` in `chain/gnark/poseidon2_bn254_test.go` — passing on
    /// both sides pins the Rust and gnark permutations to one function.
    const GOLD_KAT_OUT: [&str; 3] = [
        "0x0bb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033",
        "0x303b6f7c86d043bfcbcc80214f26a30277a15d3f74ca654992defe7ff8d03570",
        "0x1ed25194542b12eef8617361c3ba7c52e660b145994427cc86296242cf766ec8",
    ];

    #[test]
    fn dregg_outer_poseidon2_bn254_matches_gnark_gold_kat() {
        let perm = dregg_poseidon2_bn254();
        let mut state = [Bn254::ZERO, Bn254::ONE, Bn254::TWO];
        perm.permute_mut(&mut state);
        let want = GOLD_KAT_OUT.map(bn254_from_hex);
        assert_eq!(
            state, want,
            "Poseidon2Bn254 diverges from the zkhash/gnark gold KAT"
        );

        // REJECT polarity (the KAT comparison is not vacuous): a tampered
        // input must not reproduce the gold output.
        let mut tampered = [Bn254::ZERO, Bn254::ONE, Bn254::from_int(3u64)];
        perm.permute_mut(&mut tampered);
        assert_ne!(
            tampered[0], want[0],
            "tampered input still produced the gold KAT output"
        );
    }

    // ------------------------------------------------------------------
    // Synthetic STARK round-trip under DreggOuterConfig
    // ------------------------------------------------------------------

    /// Minimal 2-column Fibonacci AIR (the p3 uni-stark test shape): first row
    /// pinned to public (a, b), transition is the Fibonacci step, last row's
    /// right column pinned to public x. Non-vacuous boundary + transition
    /// constraints, and public values exercise the MultiField challenger's
    /// BabyBear observe path.
    struct OuterFibAir;

    impl<F> BaseAir<F> for OuterFibAir {
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

    impl<AB: AirBuilder> Air<AB> for OuterFibAir {
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

    /// The lane's deliverable gate: prove a synthetic STARK UNDER the outer
    /// config and verify it — the BN254-native MMCS + MultiField challenger
    /// round-trip, at the production FRI knobs (blowup 6, 19 queries, 16 PoW).
    #[test]
    fn dregg_outer_config_proves_and_verifies_synthetic_stark() {
        let config = create_outer_config();
        let air = OuterFibAir;
        let (trace, pis) = fib_trace(16);

        let mut proof = prove(&config, &air, trace, &pis);

        // The swing vs a BabyBear-committed proof, pinned at the TYPE level:
        // a `Proof<DreggRecursionConfig>` commitment is
        // `MerkleCap<BabyBear, [BabyBear; 8]>` (8 small-field words); THIS
        // proof's commitment is one native BN254 element per root.
        let trace_cap: &MerkleCap<BabyBear, [Bn254; OUTER_DIGEST_ELEMS]> = &proof.commitments.trace;
        // Runtime canary on top of the type pin: a native BN254 digest is a
        // ~254-bit element — with overwhelming probability it does NOT fit in
        // BabyBear's 31 bits (a BabyBear-hash digest word always does).
        for root in trace_cap.roots() {
            assert!(
                root[0].as_canonical_biguint().bits() > 31,
                "trace root fits in 31 bits — commitment does not look BN254-native"
            );
        }

        verify(&config, &air, &proof, &pis)
            .expect("outer-config proof must verify under the same config");

        // REJECT polarity 1: wrong public values must not verify.
        let bad_pis = vec![BabyBear::ZERO, BabyBear::ONE, BabyBear::from_int(12345u32)];
        assert!(
            verify(&config, &air, &proof, &bad_pis).is_err(),
            "outer config accepted wrong public values"
        );

        // REJECT polarity 2: a tampered opened value must not verify.
        proof.opened_values.trace_local[0] += OuterChallenge::ONE;
        assert!(
            verify(&config, &air, &proof, &pis).is_err(),
            "outer config accepted a tampered opening"
        );
    }

    /// The transcript boundary constants the gnark side pins
    /// (`chain/gnark/multifield_challenger.go`): 8 BabyBear limbs pack per
    /// BN254 element in radix 2^31; 7 base-p limbs split per squeezed cell.
    /// If the pinned fork ever changes these derivations, this test fails
    /// BEFORE a silent transcript divergence reaches gnark.
    #[test]
    fn dregg_outer_challenger_pack_split_matches_gnark_constants() {
        let challenger = create_outer_config().initialise_challenger();
        assert_eq!(
            challenger.absorb_radix_bits(),
            31,
            "absorb radix must match gnark mfAbsorbRadixBits = 31"
        );
        assert_eq!(
            challenger.absorb_num_f_elms(),
            8,
            "absorb pack width must match gnark mfAbsorbNumFElms = 8"
        );
        assert_eq!(
            challenger.squeeze_num_f_elms(),
            7,
            "squeeze split width must match gnark mfSqueezeNumFElms = 7"
        );
    }

    /// Compression twin check: the MMCS node compression equals gnark's
    /// `Poseidon2Bn254Compress` (state = [left, right, 0]; permute; lane 0).
    #[test]
    fn dregg_outer_compress_is_perm_of_left_right_zero_lane0() {
        use p3_symmetric::PseudoCompressionFunction;
        let perm = dregg_poseidon2_bn254();
        let compress = OuterCompress::new(perm.clone());
        let (l, r) = (Bn254::from_int(7u64), Bn254::from_int(9u64));
        let got = compress.compress([[l], [r]]);
        let mut state = [l, r, Bn254::ZERO];
        perm.permute_mut(&mut state);
        assert_eq!(got, [state[0]]);
    }

    // Keep the Proof type name used above resolvable (compile-time pin that
    // the round-trip really is a uni-stark `Proof<DreggOuterConfig>`).
    #[allow(dead_code)]
    fn _type_pin(p: Proof<DreggOuterConfig>) -> Proof<DreggOuterConfig> {
        p
    }
}
