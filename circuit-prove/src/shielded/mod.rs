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
//!    ([`dregg_circuit::dsl::note_spending::note_spending_dsl_circuit`]), which proves
//!    in-circuit: (b) the input note's commitment is a *member* of the
//!    commitment tree at a public `merkle_root`, and (c) the nullifier is
//!    correctly *derived* from the note + the spender's key (so reusing a note
//!    yields the same nullifier and is rejected by the nullifier set). The
//!    note **owner** and the **spending key** live only in the witness. We run
//!    this circuit through the **hiding** uni-STARK path
//!    ([`dregg_circuit::dsl::dsl_p3_air::prove_dsl_zk`], `HidingFriPcs`, `ZK = true`),
//!    so the proof's openings reveal nothing about the witness beyond the
//!    public `(nullifier, merkle_root, …)`. *Owner is blind.*
//!
//! 2. **Value — the hidden VALUE LINK, in the AIR** ([`transfer_link`], the Lean-emitted
//!    `dregg-shielded-transfer-value-link::v1`). ⚑ FLAG DAY: this REPLACED the Pedersen side.
//!    The retired shape carried a prover-chosen Ristretto `commit(v,r)` per leg, a Schnorr
//!    conservation proof over `Σ C_in = Σ C_out`, and a Bulletproof range proof per output —
//!    and nothing tied the leg's `v` to the value the spend STARK proved for the note, so a
//!    note worth `1` funded legs worth `1_000_000`. That gap is not checkable across the two
//!    systems (BabyBear cannot open a Ristretto point without curve arithmetic in-AIR;
//!    a sigma protocol cannot open a Poseidon2 image without the hash in-group —
//!    `cell-crypto/src/value_link_zk.rs` says so and names this exit). So the value is bound
//!    where the spend already binds it: one Lean relation reads ONE set of canonical 16-bit
//!    limb columns for both the spent note's sixteen carrier lanes and the minted note's
//!    commitment. *Value is blind, and it is bound.* Range proofs are gone with the group that
//!    needed them: the limb cells' booleanity is forced in the AIR, so `0 ≤ v < 2^64` is a
//!    property of the trace.
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
pub mod deshield;
pub mod deshield_link;
pub mod pool;
pub mod shield_opening;
pub mod spend_complete;
mod transfer;
pub mod transfer_link;
pub mod transfer_link_2out;
pub mod wide_value_binding;

pub use attest::{
    AttestWitness, Predicate, attest_circuit, attest_descriptor, generate_attest_trace,
};
pub use deshield::{
    DEPLOYED_DESHIELD_INPUTS, DeshieldCredit, DeshieldError, ShieldedDeshield,
    ShieldedDeshieldWitness, prove_shielded_deshield,
};
pub use deshield_link::{
    ShieldedDeshieldLinkClaim, ShieldedDeshieldLinkError, ShieldedDeshieldLinkProof,
    ShieldedDeshieldLinkWitness, credit_from_public_limbs, credit_limbs_of,
    generate_shielded_deshield_link_trace, prove_shielded_deshield_link,
    shielded_deshield_value_link_descriptor, shielded_deshield_value_link_descriptor_json,
    verify_shielded_deshield_link,
};
pub use pool::{
    HiddenAssetLeg, MultiAssetPoolTransfer, PoolBalanceMode, PoolInputWitness, prove_pool_transfer,
};
pub use spend_complete::{
    ShieldedSpendCompleteClaim, ShieldedSpendCompleteError, ShieldedSpendCompleteProof,
    ShieldedSpendCompleteWitness, ShieldedSpendMembership, TREE_DEPTH, WIDE_LANES,
    generate_shielded_spend_complete_trace, prove_shielded_spend_complete,
    shielded_spend_complete_descriptor, verify_shielded_spend_complete,
    verify_shielded_spend_complete_parts,
};
pub use transfer::{
    DEPLOYED_INPUTS, SUPPORTED_OUTPUTS, ShieldedError, ShieldedInputProof, ShieldedTransfer,
    ShieldedTransferSplitWitness, ShieldedTransferWitness, prove_shielded_input,
    prove_shielded_transfer, prove_shielded_transfer_split,
};
pub use transfer_link::{
    ShieldedTransferLinkClaim, ShieldedTransferLinkError, ShieldedTransferLinkProof,
    ShieldedTransferLinkWitness, generate_shielded_transfer_link_trace,
    note_commitment_felt_from_bytes, prove_shielded_transfer_link,
    shielded_transfer_value_link_descriptor, shielded_transfer_value_link_descriptor_json,
    verify_shielded_transfer_link,
};
pub use transfer_link_2out::{
    LINK_2OUT_OUTPUTS, ShieldedLink2OutMint, ShieldedTransferLink2OutClaim,
    ShieldedTransferLink2OutProof, ShieldedTransferLink2OutWitness,
    generate_shielded_transfer_link_2out_trace, prove_shielded_transfer_link_2out,
    prove_shielded_transfer_link_2out_from_trace, shielded_transfer_value_link_2out_descriptor,
    shielded_transfer_value_link_2out_descriptor_json, verify_shielded_transfer_link_2out,
};
pub use wide_value_binding::{
    BINDING_BLIND_LANES, LIMB_BITS, U64_LIMBS, WIDE_VALUE_BINDING_LANES, WideValueBindingClaim,
    WideValueBindingError, WideValueBindingProof, WideValueBindingWitness,
    generate_wide_value_binding_trace, prove_wide_value_binding, verify_same_opening,
    verify_wide_sidecar_proof, wide_value_binding_descriptor, wide_value_binding_descriptor_json,
};
