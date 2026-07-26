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
/// Crash-tolerant `t < n` Shamir custody and opening + the malicious-secure decrypt-share certificate.
pub mod quorum;
/// Honest n-of-n multiparty BFV relinearization-key generation + its Tier-0 acceptance gate.
pub mod relin;
