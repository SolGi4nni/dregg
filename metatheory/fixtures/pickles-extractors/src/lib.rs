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
//! * [`tape`] — ⚑ **the step proof's phase-1 Fq tape, as a Lean object.** The 116 Fq words the wrap
//!   circuit's transcript absorbs (`sg_old`, `x_hat`, `w_comm`, `z_comm`, `t_comm`, the IPA `lr`
//!   pairs and `delta`), the 56 `index_to_field_elements` coordinates of the step key, and the
//!   challenges kimchi's own verifier derived — with both controls measured on the proof object.
//!
//! The split exists because those are different questions. `wire` asks "is this record spelled
//! the way Mina spells it"; `marshal` asks "is this record the one our proof determines";
//! `transcript` asks "are these scalars facts about a proof, or numbers"; `gates` asks "what does
//! Mina say"; `tape` asks "which proof is the wrap circuit's transcript about".
//!
//! ⚑ **`tape` AND `gates` READ ONE PROOF OBJECT, AND THAT IS THE POINT.** Until 2026-08-05 the
//! forty public words came from `pickles_kimchi_marshal`'s step proof while the wrap transcript's
//! absorbed commitments came from a THIRD-PARTY `create_circuit(0,5)` export and the Lean chain
//! fixture came from a THIRD proof, exported by a separate binary that proved with `OsRng`. Three
//! proofs, one pipeline, and every shape agreed — which is exactly why nothing caught it. There is
//! now one `prove_step`, and everything downstream is a function of its return value.

pub mod gates;
pub mod marshal;
pub mod tape;
pub mod transcript;
pub mod wire;
