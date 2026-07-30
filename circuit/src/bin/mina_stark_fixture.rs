//! **The BabyBear-hashed fixture emitter for `DreggProofVerify`.**
//!
//! ```text
//!   cargo run -p dregg-circuit --release --bin mina_stark_fixture -- \
//!       <degree_bits> <log_blowup> <num_queries> <query_pow_bits> [seed] [tamper]
//! ```
//!
//! One line: prove the Lean-authored `mina-fixture` AIR under
//! [`DreggStarkConfig`] — the SAME `Poseidon2BabyBear<16>` /
//! `PaddingFreeSponge<.,16,8,8>` / `TruncatedPermutation<.,2,8,16>` /
//! `MerkleTreeMmcs` / `DuplexChallenger<.,16,8>` /
//! `BinomialExtensionField<BabyBear,4>` / `TwoAdicFriPcs` stack the deployed
//! root runs, with only the six FRI knobs turned down — verify it, and emit the
//! fixture.
//!
//! ⚑ **Everything this binary does lives in
//! [`dregg_circuit::mina_fixture_emit`]**, generic over the commitment hash
//! suite. Its Pasta twin is `dregg-circuit-prove`'s `mina_pasta_stark_fixture`,
//! and the two are the SAME emitter at two hashes precisely so the fixture
//! schema cannot drift between them. This file is the BabyBear argument to it
//! and nothing else — no AIR, no trace, no JSON layout.
//!
//! ⚑ **It is a `src/bin` target, not an example, deliberately.** Cargo compiles
//! DEV-DEPENDENCIES for an example, and `dregg-circuit`'s dev-deps reach
//! `dregg-lean-ffi`, whose build script fails closed whenever the Lean tree is
//! mid-edit. This emitter needs nothing outside `[dependencies]`, and a gate leg
//! that goes red because an unrelated Lean module is being rewritten is a gate
//! nobody can read.

use dregg_circuit::mina_fixture_emit::{BABYBEAR_DIGEST_ELEMS, BabyBearSuite, FixtureArgs, run};

fn main() {
    run::<BabyBearSuite, BABYBEAR_DIGEST_ELEMS>(&FixtureArgs::from_env());
}
