//! fhegg-fhe's threshold surface.
//!
//! The wasm-clean party ops (KeygenSession / ThresholdParty / partial_decrypt / combine / the collective-key
//! acceptance gate / the `distributed` t<n process construction) now live in the GPU/tfhe-free
//! [`fhegg_core::threshold`] crate so the browser-extension ceremony party can cross-compile them to wasm32
//! (streamed-cooking-shannon Track B). They are re-exported here at their original paths, so every
//! `crate::threshold::…` / `fhegg_fhe::threshold::…` consumer is UNCHANGED.
//!
//! The two native-only submodules stay in fhegg-fhe because their deps would break wasm-cleanliness:
//! - [`quorum`] — the `t < n` Shamir custody + its ZK decrypt-share certificate (pulls `pq_share_commitment`
//!   / bulletproofs / curve25519).
//! - [`relin`] — honest n-of-n multiparty relinearization + its acceptance gate (pulls `bfv_mul`).

pub use fhegg_core::threshold::*;

/// The `t < n` custody with parties in SEPARATE PROCESSES (uses `mpc_party` + `quorum`).
pub mod distributed;
/// Relinearization for the DISTRIBUTED committee, run on the additive-of-dealers
/// structure `s = sum_d s_d` because the Lagrange custody rows provably cannot
/// carry it. Read the module docs before assuming this is `t`-of-`n`: it is
/// `n`-of-`n`, exactly like the DKG setup it extends.
pub mod distributed_relin;
/// Crash-tolerant `t < n` Shamir custody and opening + the malicious-secure decrypt-share certificate.
pub mod quorum;
/// Honest n-of-n multiparty BFV relinearization-key generation + its Tier-0 acceptance gate.
pub mod relin;
/// The production relying-party caller that drives the `distributed` committee over its authenticated
/// transport: collective-key agreement, the verified commit round, and certificate-checked opening.
pub mod relying_party;
