//! **pickles-extractors, as a library.** Two modules, both shared by the bins in `src/bin/`.
//!
//! * [`wire`] — the two wire encoders (binprot and sexp) for
//!   `PicklesProofProofsVerified2ReprStableV2`. Written and judged by
//!   `src/bin/pickles_proof_wire.rs`; seven real block proofs round-trip through the binprot half
//!   byte-identically and all seven plus a built object are read by Mina's own `proofOfBase64`.
//! * [`marshal`] — **the kimchi→wire marshaller**: a `ProverProof` on Pallas that our own prover
//!   produced, plus the statement scalars `wrap_main` would derive, into that same record.
//!
//! The split exists because those are two different questions. `wire` asks "is this record spelled
//! the way Mina spells it"; `marshal` asks "is this record the one our proof determines".

pub mod marshal;
pub mod wire;
