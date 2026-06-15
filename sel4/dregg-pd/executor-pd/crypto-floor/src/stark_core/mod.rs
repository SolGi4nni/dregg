//! The no_std STARK core, carried VERBATIM from the `verifier-stark` PD
//! (`sel4/dregg-pd/verifier-stark/src/stark_core/`), which itself carries the
//! `dregg-circuit` `src/{field,stark}.rs` (BabyBear + BLAKE3 Merkle + FRI +
//! Fiat-Shamir) `std -> core`/`alloc`. Carrying it HERE — into the executor PD's
//! crypto floor — lets the §2 STARK-verify portal do a REAL on-device proof check
//! (not the abstract-Nat fail-closed stub): the executor's proof-carrying turn
//! ships the structured proof bytes, the C shim hands them to
//! `dreggcf_stark_verify_bytes` (lib.rs), and `stark::verify` runs the same
//! cryptographic check the verifier-stark PD runs — ACCEPT a sound proof, REJECT
//! a tampered one (the anti-ghost tooth), byte-for-byte the verifier-stark logic.
//!
//! These two files are intentionally byte-identical to the `verifier-stark`
//! sources (same SHA when carried), so the executor floor and the verifier PD
//! agree on verification by construction — there is ONE STARK verifier in this
//! tree, carried, not a reimplementation.
//!
//! NOTE on the field: this crate already has a *trimmed* `field.rs` at the crate
//! root (the Poseidon2-only surface the hash portals need). That trimmed field
//! and THIS full STARK field are the same BabyBear prime + canonical reduction;
//! they are kept as separate modules only so the KAT'd Poseidon2 surface stays
//! untouched while the STARK core carries its full field verbatim.

pub mod field;
pub mod stark;
