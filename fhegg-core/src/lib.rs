//! fhEgg core — the wasm-clean primitive surface.
//!
//! The subset of `fhegg-fhe` that must cross-compile to `wasm32` so the browser extension can hold a
//! threshold-BFV share and run `partial_decrypt` in-browser (the distributed no-single-viewer ceremony,
//! streamed-cooking-shannon Track B). `fhegg-fhe` re-exports these at their original paths, so its consumers
//! are unchanged. Nothing here may depend on wgpu/tfhe (the native-only GPU stack) — that is the invariant
//! that keeps the ceremony party compilable to wasm.

pub mod bfv_lean;
pub mod params;
pub mod threshold;
