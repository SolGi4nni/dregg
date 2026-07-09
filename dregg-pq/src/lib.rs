//! `dregg-pq` — the ONE shared post-quantum leaf crate.
//!
//! Before this crate the ML-DSA-65 (FIPS 204) *from-seed derivation + sign +
//! fail-closed verify* triple was copy-pasted into nine crates (cell-crypto,
//! dregg-auth, token, captp, blocklace, federation, turn, lightclient, wasm),
//! each with its own `MlDsaXxxKey::from_ed25519_seed`, and captp additionally
//! embedded the X25519+ML-KEM-768 hybrid session KEM inline (pulling a pinned
//! pre-release `kem` trait crate). This crate is the canonical home for both, so
//! every surface shares ONE audited primitive.
//!
//! ## ML-DSA-65 ([`MlDsaKey`], [`ml_dsa_verify`])
//!
//! One deterministic derivation from a 32-byte ed25519 seed
//! ([`MlDsaKey::from_ed25519_seed`], FIPS 204 `ML-DSA.KeyGen(ξ = seed)`), so a
//! cipherclerk, a node, and a genesis fixture built from one mnemonic agree on
//! the PQ public key with no separate ceremony. **Domain separation is the
//! caller's job**: every surface passes its own FIPS 204 `ctx` string into
//! [`MlDsaKey::sign`] / [`ml_dsa_verify`], so a signature minted for one surface
//! can never be replayed onto another. [`ml_dsa_verify`] is fail-CLOSED — a
//! wrong-length key, wrong-length signature, undecodable key, or failed check
//! all return `false`, never panic.
//!
//! ## Hybrid session KEM ([`hybrid_kem`])
//!
//! X25519 + ML-KEM-768 with the published X-Wing / TLS `X25519MLKEM768`
//! concatenation-KDF combiner, so a recorded handshake is not
//! harvest-now-decrypt-later vulnerable and the derived key depends jointly on
//! BOTH secrets. See the module docs.
//!
//! ml-kem 0.2.3 re-exports the `Encapsulate`/`Decapsulate` traits via its own
//! `ml_kem::kem` module, so this crate depends only on `ml-kem` and never pins
//! the pre-release `kem` crate in its manifest.

pub mod hybrid_kem;
mod mldsa;

pub use mldsa::{
    ML_DSA_PK_LEN, ML_DSA_SIG_LEN, MlDsaKey, ml_dsa_public_from_seed, ml_dsa_sign_from_seed,
    ml_dsa_verify,
};
