//! `dregg-deco-prove` — **the DECO/zkTLS Stripe money-in PROVER**: the one
//! genuinely-new crypto leg that completes trustless-live Stripe money-in.
//!
//! The verifier ([`dregg_bridge::stripe_deco::StripeMirrorState::verify_deco_payment`])
//! and the Lean crown (`metatheory/Dregg2/Crypto/Deco.lean`) already landed. What was
//! missing — and what this crate is — is the thing that **PRODUCES** a valid
//! [`dregg_bridge::DecoPaymentAttestation`]: given disclosed Stripe payment facts +
//! a TLS-transcript commitment, recompute the canonical felt `payment_hash` and
//! generate a **genuine STARK proof over the deployed DECO leaf AIR**
//! (`dregg_circuit_prove::deco_leaf_adapter`) binding the disclosed facts to that
//! committed hash.
//!
//! ```text
//!   Stripe API ─ live TLS session ─►  NOTARY (interim; §notary)  ─►  NotaryAttestation
//!    (settled payment disclosed)      records facts + transcript      { facts, transcriptCommit, ed25519 sig }
//!                                      commitment                              │  salt (opening) held by prover
//!                                                                              ▼
//!                                          deco_prove::prove_stripe_deco  ─►  DecoPaymentAttestation
//!                                          (real STARK over the DECO leaf AIR)  { facts, payment_hash, zk_tls_proof=Some(..) }
//!                                                                              │
//!                                                                              ▼
//!                                          bridge::verify_deco_payment  ── Ok ──►  Effect::Mint (Σδ=0)
//! ```
//!
//! ## Two layers, honestly separated
//!
//! **1. The STARK-over-disclosed-facts (REAL, this crate's core — [`prover`]).** The
//! tractable, genuine crypto: [`prover::prove_stripe_deco`] emits a
//! `DecoPaymentAttestation` whose `zk_tls_proof` is a genuine, foldable STARK proof
//! over the deployed DECO leaf AIR. It is UNFORGEABLE at prove time — a forged fact
//! (bumped amount / wrong recipient / tampered identity) is UNSAT at the leaf (the
//! `PiBinding{First}` pins + the in-AIR `hash_fact` recompute), so the prover CANNOT
//! produce a passing attestation for it. The honest output makes
//! [`dregg_bridge::stripe_deco::StripeMirrorState::verify_deco_payment`] return `Ok`
//! (mint); a forged one is refused (`DecoCommitmentMismatch`). This is real regardless
//! of the TLS layer below.
//!
//! **2. The MPC-TLS / notary capture layer ([`notary`]) — the NAMED interim.** The
//! actual "prove a LIVE Stripe API TLS session returned payment X" needs a
//! TLSNotary-style capture (MPC-TLS or a notary). This crate ships the documented
//! **interim**: a notary-attested transcript commitment (a real ed25519 signature over
//! the disclosed facts + their Poseidon2 transcript commitment). It is **NOT yet
//! trustless at the TLS layer** — the trust boundary is a semi-honest notary that
//! honestly observed the real Stripe session. See `docs/deos/DECO-PROVER-STATUS.md`
//! for what is real, what is the named remaining layer, and the exact trust boundary.
//! We do **not** claim live-trustless-TLS from the interim.

pub mod notary;
pub mod prover;

pub use notary::{
    NotaryAttestation, NotaryKeypair, TranscriptCommitment, verify_notary_attestation,
};
pub use prover::{DecoProveError, StripePaymentFacts, prove_stripe_deco, verify_stripe_deco_stark};
