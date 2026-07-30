//! **The Mina-Poseidon-hashed fixture emitter for an o1js/Kimchi verifier.**
//!
//! ```text
//!   cargo run -p dregg-circuit-prove --release --bin mina_pasta_stark_fixture -- \
//!       <degree_bits> <log_blowup> <num_queries> <query_pow_bits> [seed] [tamper]
//! ```
//!
//! One line: prove the Lean-authored `mina-fixture` AIR under
//! [`DreggMinaConfig`] — `Val = BabyBear`, `Challenge = EF4`, **commitments and
//! transcript in Mina-Poseidon over Pasta `Fp`** — verify it with dregg's own
//! verifier, and emit the fixture. The o1js side can then hash the Merkle paths
//! with `Poseidon.hash` natively (13 measured rows a permutation) instead of
//! emulating Poseidon2-BabyBear at 2,600.
//!
//! ⚑ **Everything this binary does lives in
//! [`dregg_circuit::mina_fixture_emit`]**, generic over the commitment hash
//! suite; the Pasta half is
//! [`dregg_circuit_prove::mina_pasta_fixture_suite::MinaPastaSuite`]. Its
//! BabyBear twin is `dregg-circuit`'s `mina_stark_fixture`, and the two are the
//! SAME emitter at two hashes precisely so the fixture schema cannot drift
//! between them. This file constructs no AIR, no trace and no JSON.

use dregg_circuit::mina_fixture_emit::{FixtureArgs, run};
use dregg_circuit_prove::dregg_mina_config::MINA_DIGEST_ELEMS;
use dregg_circuit_prove::mina_pasta_fixture_suite::MinaPastaSuite;

fn main() {
    run::<MinaPastaSuite, MINA_DIGEST_ELEMS>(&FixtureArgs::from_env());
}
