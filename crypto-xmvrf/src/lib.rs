//! # `crypto-xmvrf` — a post-quantum, hash-based, key-updatable VRF (reference)
//!
//! An executable REFERENCE implementation of a key-updatable, hash-based verifiable
//! random function for consensus **leader sortition** — the XM-VRF family. Pure
//! hash + PRG (blake3), **no lattice**, correctness-first.
//!
//! A VRF (Micali–Rabin–Vadhan, FOCS 1999) is a triple `(keygen, eval, verify)`
//! where `eval(sk, x) = (y, π)` yields an output and a proof, and
//! `verify(pk, x, y, π)` lets anyone check the pair WITHOUT the secret key. The
//! three properties, and where this crate stands on each:
//!
//! 1. **PROVABILITY (correctness)** — honest `eval` output verifies. Exercised by
//!    `tests/provability.rs`.
//! 2. **UNIQUENESS** — for a fixed `pk` and `x`, at most one `y` verifies, holding
//!    even under a MALICIOUSLY chosen `pk`. This is THE property sortition needs
//!    (a double output lets a validator double their committee odds). Here it
//!    reduces to blake3 collision resistance; exercised by `tests/uniqueness.rs`,
//!    including a concrete exhibition of the X-VRF/WOTS+ pitfall and the contrast.
//! 3. **PSEUDORANDOMNESS** — the output looks uniform without `sk`. A statistical
//!    smoke test lives in `tests/pseudorandomness.rs`; the full game is in Lean.
//!
//! ## The X-VRF break and the XM-VRF fix (why this construction)
//!
//! *Breaking X-VRF* (Bodaghi et al., FC24) is a UNIQUENESS attack: WOTS+'s chaining
//! function is only one-way / 2nd-preimage-resistant (NOT collision-resistant), so
//! a malicious public key admits two valid signatures — hence two valid outputs.
//! *Key Updatable Hash Based VRF* (IACR ePrint 2026/052) fixes this by committing
//! the output through a collision-resistant hash (an XMSS-derived, key-updatable
//! tree). This reference keeps that security-relevant invariant — a CR Merkle
//! commitment to each epoch's output — and gets FULL uniqueness right. See
//! [`vrf`] for the construction and the [`vrf`] module's HONEST BOUNDARY for what
//! is simplified, and [`naive_wots`] for the pitfall made concrete.
//!
//! ## Lean framework
//!
//! The abstract security definitions and the uniqueness/pseudorandomness games
//! are in `metatheory/Dregg2/Crypto/VRF.lean` (`Correct`, `UniqueOutputs`,
//! `Pseudorandom`, and the `two_outputs_break_uniqueness` tooth). This crate is the
//! executable counterpart; the proofs are NOT re-derived in Rust.
//!
//! ## Not deployment-grade
//!
//! Pre-audit reference: no constant-time guarantees, no wire-format stability, no
//! side-channel review. Parameters (tree height / many-time bound) are documented
//! reference choices.

pub mod hash;
pub mod merkle;
pub mod naive_wots;
pub mod vrf;

pub use vrf::{keygen_from_seed, verify, EvalError, Output, Proof, PublicKey, SecretKey};
