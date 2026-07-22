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
pub mod blinded_membership_leaf_adapter;
pub mod bridge_leaf_adapter;
pub mod carrier_pin_twin;
pub mod caveat_admission_leaf_adapter;
pub mod cert_f_air;
pub mod cert_qp_air;
pub mod collaborative_basefold;
pub mod collaborative_basefold_mmcs;
pub mod collaborative_shamir_rows;
pub mod custom_leaf_adapter;
pub mod custom_proof_bind;
pub mod dark_amm_private;
pub mod dark_bazaar_private;
pub mod deco_leaf_adapter;
pub mod descent_census;
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
pub mod gpu_backend;
pub mod gpu_hidingfri_fold;
pub mod hatchery_leaf_adapter;
pub mod ivc_turn_chain;
pub mod joint_turn_aggregation;
pub mod joint_turn_recursive;
pub mod lean_lookup_air;
pub mod membership_leaf_adapter;
pub mod merge_pool;
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
pub mod shielded;
pub mod shielded_exact_apex_v4;
pub mod shielded_ring_clearing_air;
pub mod shielded_ring_clearing_nleg_air;
pub mod shielded_spend_leaf_adapter;
pub mod shielded_whole_note_swap_substrate;
pub mod solvency_leaf_adapter;
pub mod sovereign_leaf_adapter;
pub mod zkoracle_leaf_adapter;
