//! `dregg-circuit-prove`: the HEAVY PROVE surface for dregg circuits.
//!
//! This crate is the prover-only half of the `dregg-circuit` split. It hosts the
//! items that need the three RECURSION-ONLY Plonky3 crates (`p3-recursion`,
//! `p3-circuit`, `p3-circuit-prover`) — the IVC turn chain, joint-turn recursive
//! aggregation, the recursive witness bundle, the custom proof-bind engine, the
//! effect-VM `p3-air` recursion bridge, the LogUp lookup AIR, and the shielded-
//! action prover.
//!
//! The VERIFY floor — descriptor parsing/verification (`verify_vm_descriptor2`),
//! the AIRs, the PI-reconstruction trace generators the executor needs, and the
//! prove_batch-based (recursion-free) provers — lives in [`dregg_circuit`]. That
//! partition is what keeps `cargo tree -p dregg-circuit` free of the recursion
//! prover: a verify-only consumer depends on `dregg-circuit` alone; a producer
//! depends on this crate.
//!
//! Everything here was previously `#[cfg(feature = "prover")]` inside
//! `dregg-circuit`; the gate is gone because this whole crate IS the prover.

pub mod accumulator;
pub mod apex_shrink;
pub mod apex_shrink_gnark_export;
/// The MINA/PASTA fixture exporter — a native-Pasta shrink terminal into the
/// o1js Kimchi verifier (`bridge/mina-zkapp/src/MinaShrinkVerify.ts`).
pub mod apex_shrink_mina_export;
/// ⚑ The REASON ASSERTION for every binding-node refusal tooth on the p3-recursion rail. Lifted
/// out of `tests/binding_tooth/` on 2026-08-10 so the in-lib fold teeth (which cannot see a
/// `tests/` module) can say WHICH refusal they mean — see the module header.
pub mod binding_tooth;
pub mod blinded_membership_leaf_adapter;
pub mod carrier_pin_twin;
pub mod caveat_admission_leaf_adapter;
pub mod cert_f_air;
pub mod cert_qp_air;
pub mod collaborative_basefold;
pub mod collaborative_basefold_mmcs;
pub mod collaborative_shamir_rows;
pub mod custom_cohort_spine;
pub mod custom_leaf_adapter;
pub mod custom_proof_bind;
pub mod dark_amm_private;
pub mod dark_bazaar_private;
pub mod dark_bazaar_private_poa;
pub mod dark_bazaar_private_poa_settlement;
pub mod deco_leaf_adapter;
pub mod descent_census;
/// The MINA-facing terminal config — `DreggOuterConfig`'s twin over Pasta.
pub mod dregg_mina_config;
pub mod dregg_outer_config;
pub mod dsl_leaf_adapter;
pub mod effect_vm_p3_air;
pub mod factory_leaf_adapter;
pub mod faithful_note_spend;
pub mod faithful_note_spend_exact_v3;
pub mod faithful_note_spend_exact_v3_identity;
pub mod field_delta_range_air;
pub mod gnark_witness_export;
pub use gnark_witness_export::export_gnark_witness_json;
/// ⚑ THE CHILD-VK IDENTITY PIN every 2-to-1 fold in this crate takes: the expected preprocessed
/// commitment of each child, `connect`ed to `alloc_const`s of that value, so a child of identical
/// table shape and different preprocessed CONTENT (a descriptor with the same constraint structure
/// and different round constants) is refused by the parent's witness solver rather than folded.
///
/// ⚠ **CLOSURE KIND: RECURSION WIRING PLUS A CONSUMER REFUSAL — NOT A CONSTRAINT.** This module
/// authors **no AIR** (House Law #1: every AIR under these towers comes out of Lean). `alloc_const`
/// + `connect` in the Rust-authored recursion verifier is not a Lean-authored gate, and what it
/// establishes "proves on a box": it inherits the undischarged FRI/STARK floor. And a *tracked* pin
/// read alone says only "this parent folded the children it folded" — what makes it NAME a circuit
/// is the consumer comparing the parent `RecursionVk` fingerprint against its anchor. Write "every
/// fold takes the pin"; do not write "every fold FORCES child VK identity by constraint".
///
/// ⚠ It was called `mina_fold_vk_pin` while only the Mina tower used it. It is not Mina-specific
/// and never was — the leaf adapters, the joint-turn nodes, the cohort spine, the solvency union
/// and the accumulator all take the same pin. The Mina-scoped name is gone rather than aliased.
pub mod fold_vk_pin;
pub mod gpu_backend;
pub mod gpu_hidingfri_fold;
pub mod hatchery_leaf_adapter;
pub mod ivc_turn_chain;
pub mod joint_turn_aggregation;
pub mod joint_turn_recursive;
pub mod lean_lookup_air;
pub mod membership_leaf_adapter;
pub mod merge_pool;
/// ⚑ The DEFERRED IPA ACCUMULATOR CHECK as a RECURSION TREE: the Lean-authored
/// `dregg-mina-accumulator-{seg,final}::v1` leaves, and the fold that carries the accumulator POINT
/// from segment to segment INSIDE the recursion. The leg upstream's verifier does natively.
pub mod mina_accumulator_fold;
/// ⚑⚑⚑ **THE LEAF ADAPTER THAT MAKES TIE 1 A WELD.** One circuit verifying BOTH the gated
/// body-preimage STARK and one `state_body_hash` chain-link STARK, so both raw descriptor PI
/// vectors are in scope and `MinaBodyPreimageSeams`' twenty-five Lean-authored seams can be
/// APPLIED. Exposes the chain leaf's own 200-lane claim, so it is a drop-in for
/// `mina_phase2_chain_leaf::prove_chain_link_leaf_with` under the same fold.
pub mod mina_body_preimage_adapter;
/// ⚑⚑ **A KIMCHI VERIFIER GADGET, IN PLONKY3'S OWN RECURSION.** The top fold that welds the
/// phase-2 transcript chain ROOT to the endo/conjunction finalize ROOT, so the ξ the finalize
/// conjuncts check is the one the block's OWN sponge squeezed. ⚠ **An implementation, unverified,
/// with a named path to verification** — see the module header's §"THE VERIFICATION PATH". It
/// authors NO AIR: every AIR under it comes out of Lean.
pub mod mina_kimchi_verifier_gadget;
/// The Pasta half of `dregg_circuit::mina_fixture_emit`: `DreggMinaConfig` as a
/// fixture hash suite, plus the CHECKED `MultiField32Challenger` replica whose
/// per-permutation sponge states the Pasta fixture publishes.
pub mod mina_pasta_fixture_suite;
/// ⚑ The 46-permutation Fq transcript of Mina devnet block 539508 as a RECURSION TREE: the
/// Lean-authored `dregg-pasta-fq-chainlink::v1` leaf, and the fold that carries the sponge state
/// from link to link INSIDE the recursion.
pub mod mina_phase2_chain_leaf;
/// ⚑⚑ **THE IPA CLOSING CHECK AS A RECURSION TREE.** The Lean-authored
/// `dregg-mina-wrap-closing-{seg,final,srs}::v1` leaves — kimchi's own combined MSM at
/// `sg_rand_base = −z₁·rand_base`, the coefficient at which `sg` leaves the equation — and the fold
/// that carries the accumulator POINT between segments with `cb.connect`. This is the leg
/// `opening_is_vacuous_when_sg_is_free` was waiting for.
pub mod mina_wrap_closing_fold;
/// ⚑ THE FINALIZE CONJUNCTION AND THE ENDOMORPHISM LIFT, FOLDED — the Lean-authored
/// `dregg-mina-wrap-conjunction::v1` and `dregg-mina-xi-endo-lift::v1` as recursion leaves, and the
/// node that `cb.connect`s their 32 published ξ limbs so the two halves are ONE value in-circuit
/// rather than two that a host-side test compares.
pub mod mina_wrap_finalize_fold;
pub mod mina_wrap_opening_fold;
pub mod mpt_holding_leaf;
pub mod note_spend_leaf_adapter;
pub mod packed_interleaved_merkle;
pub mod plonky3_recursion_impl;
pub mod presentation_leaf_adapter;
pub mod private_book_bfv_slice;
pub mod private_book_bfv_terminal;
pub mod private_graph_rewrite;
pub mod private_graph_rewrite_cell;
pub mod private_preference;
pub mod private_preference_cell;
pub mod private_quest_graph;
pub mod private_raid_assignment;
pub mod private_shuffle;
pub mod private_shuffle_fair;
pub mod recursive_witness_bundle;
pub mod seam;
pub mod shielded;
pub mod shielded_exact_apex_v4;
pub mod shielded_whole_note_swap_substrate;
pub mod solvency_leaf_adapter;
pub mod sovereign_leaf_adapter;
pub mod zkoracle_leaf_adapter;
