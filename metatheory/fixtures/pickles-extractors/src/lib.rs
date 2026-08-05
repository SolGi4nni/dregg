//! **pickles-extractors, as a library.** Two modules, both shared by the bins in `src/bin/`.
//!
//! * [`wire`] — the two wire encoders (binprot and sexp) for
//!   `PicklesProofProofsVerified2ReprStableV2`. Written and judged by
//!   `src/bin/pickles_proof_wire.rs`; seven real block proofs round-trip through the binprot half
//!   byte-identically and all seven plus a built object are read by Mina's own `proofOfBase64`.
//! * [`marshal`] — **the kimchi→wire marshaller**: a `ProverProof` on Pallas that our own prover
//!   produced, plus the statement scalars `wrap_main` would derive, into that same record.
//! * [`transcript`] — **the prover's side of what Pickles defers**: the SRS accumulator Mina
//!   recomputes before it consults a key, and the previous step proof's real Fiat–Shamir
//!   transcript. It exists because `marshal`'s caller half used to be counters.
//! * [`gates`] — **the ladder, driven**: Mina's own `accumulator_check`, `expand_deferred` and
//!   `run_checks` conditions run against a marshalled object, each reporting its literal verdict,
//!   and the forty public words Pickles demands of the wrap circuit.
//!
//! The split exists because those are different questions. `wire` asks "is this record spelled
//! the way Mina spells it"; `marshal` asks "is this record the one our proof determines";
//! `transcript` asks "are these scalars facts about a proof, or numbers"; `gates` asks "what does
//! Mina say".

pub mod gates;
pub mod marshal;
pub mod transcript;
pub mod wire;
