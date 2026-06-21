//! Shielded actions — privacy M2: single-asset shielded transfer (M2-a toehold).
//!
//! A **shielded transfer** spends input notes and mints output notes with the
//! **value** and the **owner** hidden, leaving a verifiable receipt: the
//! nullifiers (so the chain can reject double-spends) and the output note
//! commitments (so the recipients can later spend them), plus a proof that the
//! transfer is genuine and balanced. Nobody — not the executor, not an
//! observer — learns how much moved or who owned the inputs.
//!
//! # The two-sided construction (census-first weld, NOT a reinvention)
//!
//! Hiding `value` and hiding `owner` are different cryptographic problems and
//! this module welds the *existing* organ for each, rather than building a
//! single monolithic circuit:
//!
//! 1. **Owner / membership / no-double-spend — the hidden STARK side.**
//!    For every input note we reuse the production DSL note-spend circuit
//!    ([`crate::dsl::note_spending::note_spending_dsl_circuit`]), which proves
//!    in-circuit: (b) the input note's commitment is a *member* of the
//!    commitment tree at a public `merkle_root`, and (c) the nullifier is
//!    correctly *derived* from the note + the spender's key (so reusing a note
//!    yields the same nullifier and is rejected by the nullifier set). The
//!    note **owner** and the **spending key** live only in the witness. We run
//!    this circuit through the **hiding** uni-STARK path
//!    ([`crate::dsl::dsl_p3_air::prove_dsl_zk`], `HidingFriPcs`, `ZK = true`),
//!    so the proof's openings reveal nothing about the witness beyond the
//!    public `(nullifier, merkle_root, …)`. *Owner is blind.*
//!
//! 2. **Value balance — the hidden Pedersen side.**
//!    Per-asset value conservation rides the homomorphic Pedersen value
//!    commitments ([`dregg_cell::value_commitment`]): each note carries
//!    `commit(v, r) = v·V + r·R`, and a single Schnorr **conservation proof**
//!    certifies `Σ C_in − Σ C_out = r_excess·R`, i.e. `Σ v_in = Σ v_out`,
//!    without revealing any `v`. Per-output Bulletproof **range proofs** close
//!    the negative-value (mod-order wrap) inflation hole. *Value is blind.*
//!
//! The shielded action is the *conjunction*: a verifier accepts iff (1) every
//! input's hidden membership+nullifier STARK verifies against the published
//! root AND (2) the value-commitment conservation (+ range) proof verifies. The
//! STARK side makes each spent note a real, fresh tree member; the Pedersen
//! side makes the value flow balanced — both blind.
//!
//! # Why this is the right seam (`circuit/src/shielded/`, its own proof)
//!
//! This is its **own** composed proof object over the existing notes / value-
//! commitments / nullifiers / commitment-tree primitives + the p3 `HidingFriPcs`.
//! It is **not** woven into `effect_vm`/`descriptor_ir2`; the two meet only at
//! "a shielded transfer is a kind of conserving turn." VK perturbation is free.
//!
//! # No Rust-authored AIR (standing law)
//!
//! The STARK side carries **zero** hand-written circuit constraints: it is the
//! Lean-emitted/DSL `note_spending_dsl_circuit()` descriptor run through the
//! audited `DslP3Air` symbolic arithmetization, only with the *hiding* config
//! swapped in. This module assembles witnesses and composes proofs; it emits no
//! AIR of its own.
//!
//! # M2 arc status
//!
//! - **M2-a (this module):** single-asset shielded transfer — balance +
//!   membership + nullifier, hidden; the blind verifier. Built here.
//! - **M2-b:** multi-asset pool (ZSA) — `commit_hidden_asset` +
//!   `prove_asset_conservation` + the `AssetEqualityProof` for unequal-leg
//!   splits already exist in `value_commitment.rs`; M2-b lifts the asset_type
//!   into the hidden scalar and folds the asset-equality argument in.
//! - **M2-c:** general shielded *transition* (any kernel action over hidden
//!   state) — the hiding layer applies uniformly because every transition is
//!   already proven in-circuit.
//! - **M2-d ([`attest`]):** ZK attestations — a private cell program issuing a
//!   public verifiable claim ("this hidden cell satisfies predicate P") over its
//!   committed state, the privacy-preserving verifiable-credential jewel. Built
//!   here: [`attest::Predicate`] (`Threshold`/`Positive`/`Membership`/`Equality`)
//!   over a `hash_fact` cell-state commitment, proven through the same
//!   `HidingFriPcs` path. Prove-over-18 / prove-solvent are the worked examples.
//!
//! # M2 privacy ↔ recovery bridge (the common-secret modality)
//!
//! The **council-sealed cell** is the natural M2 companion: a cell whose
//! contents are sealed under a *threshold* (Shamir) common secret
//! (`metatheory/Metatheory/CommonSecret.lean`, `D_G^{≥K}`), so a quorum of
//! council members can threshold-decrypt to *recover* it. This is the **dual**
//! of the shielded transfer's hiding: a shielded note hides value/owner from
//! *everyone*; a council-sealed cell hides it from *everyone below quorum* and
//! reveals it *at quorum*. The same Pedersen/commitment plumbing carries the
//! sealed payload; the threshold key-release is the recovery face. M2 privacy
//! (hide) and M2 recovery (threshold-reveal) are one modality dialed to
//! different `K`.

pub mod attest;
pub mod pool;
pub mod spend_circuit;
mod transfer;

pub use spend_circuit::{
    ShieldedSpendWitness, generate_shielded_spend_trace, shielded_spend_circuit,
    shielded_spend_descriptor,
};
pub use transfer::{
    ShieldedError, ShieldedInputProof, ShieldedTransfer, ShieldedTransferWitness, ShieldedValueLeg,
    prove_shielded_input, prove_shielded_transfer as transfer_from_witnesses,
};
pub use pool::{
    HiddenAssetLeg, MultiAssetPoolTransfer, PoolBalanceMode, PoolInputWitness, prove_pool_transfer,
};
pub use attest::{
    AttestWitness, Predicate, attest_circuit, attest_descriptor, generate_attest_trace,
};
