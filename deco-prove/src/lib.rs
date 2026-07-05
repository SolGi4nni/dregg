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
//! **2. The MPC-TLS / notary capture layer — two forms, honestly separated.**
//!
//! *2a. The semi-honest interim ([`notary`]).* A notary-attested transcript commitment
//! (a real ed25519 signature over the disclosed facts + their Poseidon2 transcript
//! commitment). It is **NOT trustless at the TLS layer** — the trust boundary is a
//! semi-honest notary that honestly observed the real Stripe session and did not
//! fabricate the facts.
//!
//! *2b. The tlsn / MPC-TLS realization — the INTERFACE + ADAPTER ([`tlsn_attest`]).* The
//! trustless-shaped replacement: it models the exact object a *verified*
//! `tlsn_core::presentation::PresentationOutput` (TLSNotary v0.1.0-alpha.15) takes and
//! performs the DECO-side binding — server pinning (`api.stripe.com`), notary pinning,
//! the presentation signature, **selective disclosure** of the payment facts out of an
//! *authenticated* HTTP transcript (a redacted amount is refused), the `succeeded` gate —
//! then hands the extracted [`prover::StripePaymentFacts`] to Layer 1 unchanged. It is
//! exercised end-to-end by a **real tlsn-format fixture** (an authenticated
//! `GET https://api.stripe.com/v1/payment_intents/{id}` transcript that redacts the
//! `Authorization: Bearer sk_live_…` secret). ⚑ It is the interface+adapter, **not** a
//! live trustless MPC-TLS run: a genuine verified presentation needs the running `tlsn`
//! notary + the `mpz` 2PC stack + a live Stripe TLS session (git-only, out of lane). The
//! 2PC session-integrity that makes the signature *trustless* is the named remaining
//! wiring.
//!
//! See `docs/deos/DECO-PROVER-STATUS.md` + `docs/deos/TLSN-INTEGRATION.md` for what is
//! real, the exact remaining layer, and the trust boundary. We do **not** claim
//! live-trustless-TLS from either form yet.

pub mod notary;
pub mod prover;
pub mod tlsn_attest;
#[cfg(feature = "tlsn-live")]
pub mod tlsn_live;

pub use notary::{
    NotaryAttestation, NotaryKeypair, TranscriptCommitment, verify_notary_attestation,
};
pub use prover::{DecoProveError, StripePaymentFacts, prove_stripe_deco, verify_stripe_deco_stark};
pub use tlsn_attest::{
    TlsnAdapterError, TlsnPresentation, TlsnStripeConfig, TlsnVerifyingKey,
    tlsn_presentation_to_attestation, verify_tlsn_presentation,
};
