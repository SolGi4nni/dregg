//! Cell-bound carrier for the Lean-authored private graph-rewrite relation.
//!
//! The reusable base relation has a compact 29-felt receipt ABI.  A genuine
//! `Effect::Custom` proof must additionally begin with the platform's canonical
//! `[cell_old_commit8 || cell_new_commit8]` state-binding prefix.  This module
//! drives the separate Lean-emitted wrapper descriptor whose public inputs are
//!
//! ```text
//! [cell_old8, cell_new8,
//!  domain, session, version, shape, index,
//!  ruleset_root8, graph_old_root8, graph_new_root8]
//! ```
//!
//! The retained recursion bundle declares `graph_new_root8` as an application
//! root stored in cell fields `0..8`.  Consequently the custom fold can connect
//! both cell roots to the real transition and the proved semantic graph output
//! to what the post-state actually stores.  History linkage supplies the
//! adjacent `graph_new -> graph_old` seam between reductions.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
};
use dregg_circuit::effect_vm::custom_state_binding::AppRootBinding;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::stark_zk::{
    DreggZkStarkConfig, ZK_EXT_DEGREE, ZK_FRI_LOG_BLOWUP, ZK_FRI_LOG_FINAL_POLY_LEN,
    ZK_FRI_MAX_LOG_ARITY, ZK_FRI_NUM_QUERIES, ZK_FRI_QUERY_POW_BITS, create_zk_config,
};

use crate::joint_turn_aggregation::{CustomIr2VkRecipe, CustomIr2WitnessBundle};
use crate::private_graph_rewrite::{
    DIGEST_WIDTH, PrivateGraphRewriteWitness, PublicStatement, trace_and_public,
};

pub const PRIVATE_GRAPH_REWRITE_CELL_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/private-graph-rewrite-cell-4x2.json");

pub const CELL_TRACE_WIDTH: usize = 326;
pub const CELL_PUBLIC_INPUT_COUNT: usize = 45;
pub const CELL_APP_PI_BASE: usize = 16;
pub const GRAPH_NEW_ROOT_PI_BASE: usize = 37;
pub const GRAPH_ROOT_FIELD_KEY: usize = 0;
pub const PLONKY3_REV: &str = "82cfad73cd734d37a0d51953094f970c531817ec";

pub const HIDING_VERIFIER_MANIFEST: &str = "private-graph-rewrite-cell-4x2-v1|BabyBear|Poseidon2-W16|HidingFriPcs|salt=4|random-codewords=4";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CellPublicStatement {
    pub old_commit: [u32; DIGEST_WIDTH],
    pub new_commit: [u32; DIGEST_WIDTH],
    pub rewrite: PublicStatement,
}

impl CellPublicStatement {
    pub fn as_u32_vec(self) -> Vec<u32> {
        let mut out = Vec::with_capacity(CELL_PUBLIC_INPUT_COUNT);
        out.extend(self.old_commit);
        out.extend(self.new_commit);
        out.extend(self.rewrite.as_u32_vec());
        out
    }

    pub fn as_felts(self) -> Vec<BabyBear> {
        self.as_u32_vec().into_iter().map(BabyBear::new).collect()
    }

    pub fn validate(self) -> Result<(), String> {
        for (side, root) in [("old", self.old_commit), ("new", self.new_commit)] {
            for (lane, value) in root.into_iter().enumerate() {
                if value >= BABYBEAR_P {
                    return Err(format!(
                        "private graph cell {side} commitment lane {lane}={value} is noncanonical"
                    ));
                }
            }
        }
        self.rewrite.validate()
    }

    pub fn try_from_u32s(values: &[u32]) -> Result<Self, String> {
        if values.len() != CELL_PUBLIC_INPUT_COUNT {
            return Err(format!(
                "private graph rewrite cell expects {CELL_PUBLIC_INPUT_COUNT} public inputs, got {}",
                values.len()
            ));
        }
        let statement = Self {
            old_commit: values[0..8].try_into().expect("length checked"),
            new_commit: values[8..16].try_into().expect("length checked"),
            rewrite: PublicStatement::try_from_u32s(&values[CELL_APP_PI_BASE..])?,
        };
        statement.validate()?;
        Ok(statement)
    }
}

pub struct PrivateGraphRewriteCellZkProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl PrivateGraphRewriteCellZkProof {
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|error| format!("private graph cell proof encode failed: {error}"))
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        let proof = postcard::from_bytes(bytes)
            .map_err(|error| format!("private graph cell proof decode failed: {error}"))?;
        Ok(Self { proof })
    }
}

pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let descriptor = parse_vm_descriptor2(PRIVATE_GRAPH_REWRITE_CELL_DESCRIPTOR_JSON)?;
    if descriptor.name != "private-graph-rewrite-cell-4x2::injective-swapnet-poseidon2-v1"
        || descriptor.trace_width != CELL_TRACE_WIDTH
        || descriptor.public_input_count != CELL_PUBLIC_INPUT_COUNT
    {
        return Err("private graph rewrite cell emitted descriptor shape drifted".to_string());
    }
    Ok(descriptor)
}

pub fn air_fingerprint() -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-private-graph-rewrite-cell-air-v1");
    hasher.update(PRIVATE_GRAPH_REWRITE_CELL_DESCRIPTOR_JSON.as_bytes());
    *hasher.finalize().as_bytes()
}

pub fn hiding_verifier_config_fingerprint() -> [u8; 32] {
    let mut hasher =
        blake3::Hasher::new_derive_key("dregg-private-graph-rewrite-cell-hiding-config-v1");
    hasher.update(HIDING_VERIFIER_MANIFEST.as_bytes());
    hasher.update(PLONKY3_REV.as_bytes());
    for knob in [
        ZK_FRI_LOG_BLOWUP,
        ZK_FRI_LOG_FINAL_POLY_LEN,
        ZK_FRI_MAX_LOG_ARITY,
        ZK_FRI_NUM_QUERIES,
        ZK_FRI_QUERY_POW_BITS,
        ZK_EXT_DEGREE,
    ] {
        hasher.update(&(knob as u64).to_le_bytes());
    }
    hasher.update(&air_fingerprint());
    *hasher.finalize().as_bytes()
}

pub fn non_hiding_verifier_config_fingerprint() -> [u8; 32] {
    let mut hasher =
        blake3::Hasher::new_derive_key("dregg-private-graph-rewrite-cell-non-hiding-config-v1");
    hasher.update(b"DreggStarkConfig|non-hiding FriPcs");
    hasher.update(PLONKY3_REV.as_bytes());
    hasher.update(&air_fingerprint());
    *hasher.finalize().as_bytes()
}

pub fn proving_system_canonical_bytes() -> Vec<u8> {
    let mut out = vec![0];
    out.extend_from_slice(&(PLONKY3_REV.len() as u64).to_le_bytes());
    out.extend_from_slice(PLONKY3_REV.as_bytes());
    out
}

pub fn vk_recipe() -> CustomIr2VkRecipe {
    CustomIr2VkRecipe::source_hash(
        PRIVATE_GRAPH_REWRITE_CELL_DESCRIPTOR_JSON
            .as_bytes()
            .to_vec(),
        air_fingerprint(),
        hiding_verifier_config_fingerprint(),
        proving_system_canonical_bytes(),
    )
}

pub fn canonical_vk_hash() -> [u8; 32] {
    vk_recipe().canonical_vk_hash()
}

fn trace_and_statement(
    domain: u32,
    session: u32,
    index: u32,
    witness: &PrivateGraphRewriteWitness,
    old_commit: [u32; DIGEST_WIDTH],
    new_commit: [u32; DIGEST_WIDTH],
) -> Result<
    (
        EffectVmDescriptor2,
        Vec<Vec<BabyBear>>,
        CellPublicStatement,
        Vec<BabyBear>,
    ),
    String,
> {
    let (_base_descriptor, mut trace, rewrite) = trace_and_public(domain, session, index, witness)?;
    let public = CellPublicStatement {
        old_commit,
        new_commit,
        rewrite,
    };
    public.validate()?;
    for row in &mut trace {
        row.extend(old_commit.map(BabyBear::new));
        row.extend(new_commit.map(BabyBear::new));
        debug_assert_eq!(row.len(), CELL_TRACE_WIDTH);
    }
    let public_inputs = public.as_felts();
    Ok((descriptor()?, trace, public, public_inputs))
}

/// Mint both the privacy-facing HidingFri proof and the exact retained direct-
/// IR2 bundle consumed by the recursive custom-state/app-root carrier.
pub fn prove_zk(
    domain: u32,
    session: u32,
    index: u32,
    witness: &PrivateGraphRewriteWitness,
    old_commit: [u32; DIGEST_WIDTH],
    new_commit: [u32; DIGEST_WIDTH],
) -> Result<
    (
        PrivateGraphRewriteCellZkProof,
        CellPublicStatement,
        CustomIr2WitnessBundle,
    ),
    String,
> {
    let (descriptor, trace, public, public_inputs) =
        trace_and_statement(domain, session, index, witness, old_commit, new_commit)?;
    let proof = prove_vm_descriptor2_for_config(
        &descriptor,
        &trace,
        &public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &create_zk_config(),
    )?;
    let retained = CustomIr2WitnessBundle {
        descriptor,
        base_trace: trace,
        public_inputs,
        vk_recipe: vk_recipe(),
        app_root_binding: AppRootBinding {
            app_root_pi_offset: GRAPH_NEW_ROOT_PI_BASE,
            app_root_len: DIGEST_WIDTH,
            field_key: GRAPH_ROOT_FIELD_KEY,
        },
        post_fields_root_binding: None,
    };
    Ok((PrivateGraphRewriteCellZkProof { proof }, public, retained))
}

pub fn verify_zk(
    proof: &PrivateGraphRewriteCellZkProof,
    public: CellPublicStatement,
) -> Result<(), String> {
    public.validate()?;
    verify_vm_descriptor2_with_config(
        &descriptor()?,
        &proof.proof,
        &public.as_felts(),
        &create_zk_config(),
    )
}

pub fn verify_postcard(proof_bytes: &[u8], public_values: &[u32]) -> Result<(), String> {
    let proof = PrivateGraphRewriteCellZkProof::from_postcard(proof_bytes)?;
    verify_zk(&proof, CellPublicStatement::try_from_u32s(public_values)?)
}

pub fn decode_public_input_bytes(bytes: &[u8]) -> Result<Vec<u32>, String> {
    if bytes.len() != 4 * CELL_PUBLIC_INPUT_COUNT {
        return Err(format!(
            "private graph rewrite cell PI bytes must be {}, got {}",
            4 * CELL_PUBLIC_INPUT_COUNT,
            bytes.len()
        ));
    }
    bytes
        .chunks_exact(4)
        .map(|chunk| {
            let value = u32::from_le_bytes(chunk.try_into().expect("chunk width"));
            if value >= BABYBEAR_P {
                Err(format!("noncanonical BabyBear public input {value}"))
            } else {
                Ok(value)
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::custom_leaf_adapter::prove_direct_ir2_leaf_with_app_root_commitment;
    use crate::custom_proof_bind::custom_proof_pi_commitment;
    use crate::ivc_turn_chain::{
        CUSTOM_PROGRAM_VK_PI_LO, DEPLOYED_CUSTOM_PROGRAM_VK_PI_LEN, SEG_ANCHOR_WIDTH,
        ir2_leaf_wrap_config, prove_descriptor_leaf_expose_segment_and_claims,
    };
    use crate::joint_turn_recursive::{
        CUSTOM_COMMIT_LEN, CUSTOM_COMMIT_PI_LO, prove_direct_ir2_binding_node_app_root_segmented,
    };
    use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;
    use crate::private_graph_rewrite::{
        BoundedContext, BoundedGraph, BoundedPattern, BoundedRule, HostEdgeSlot, RuleEdgeSlot,
    };
    use dregg_circuit::descriptor_ir2::{VmConstraint2, prove_vm_descriptor2_for_config};
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};

    fn pattern(slots: [RuleEdgeSlot; 2]) -> BoundedPattern {
        BoundedPattern { slots }
    }

    fn witness() -> PrivateGraphRewriteWitness {
        let context = BoundedContext {
            slots: [HostEdgeSlot::edge(4, 7, 8), HostEdgeSlot::edge(5, 8, 9)],
        };
        PrivateGraphRewriteWitness {
            old_graph: BoundedGraph {
                slots: [
                    HostEdgeSlot::edge(1, 4, 5),
                    context.slots[0],
                    HostEdgeSlot::padding(),
                    context.slots[1],
                ],
            },
            new_graph: BoundedGraph {
                slots: [
                    context.slots[0],
                    context.slots[1],
                    HostEdgeSlot::edge(2, 4, 5),
                    HostEdgeSlot::edge(3, 5, 6),
                ],
            },
            rules: [
                BoundedRule {
                    lhs: pattern([RuleEdgeSlot::edge(1, 0, 1), RuleEdgeSlot::padding()]),
                    rhs: pattern([RuleEdgeSlot::edge(2, 0, 1), RuleEdgeSlot::edge(3, 1, 2)]),
                },
                BoundedRule {
                    lhs: pattern([RuleEdgeSlot::edge(6, 2, 3), RuleEdgeSlot::padding()]),
                    rhs: pattern([RuleEdgeSlot::edge(7, 3, 2), RuleEdgeSlot::padding()]),
                },
            ],
            sigma: [4, 5, 6, 7],
            context,
            old_blind: [101, 102, 103, 104],
            new_blind: [201, 202, 203, 204],
            rule_blinds: [[301, 302, 303, 304], [401, 402, 403, 404]],
            rule_slot: false,
        }
    }

    #[test]
    fn cell_wrapper_proves_state_prefix_and_retains_graph_app_root_weld() {
        let old_commit = core::array::from_fn(|lane| 1_000 + lane as u32);
        let new_commit = core::array::from_fn(|lane| 2_000 + lane as u32);
        let (proof, public, retained) =
            prove_zk(11, 77, 9, &witness(), old_commit, new_commit).unwrap();
        verify_zk(&proof, public).unwrap();
        assert_eq!(&public.as_u32_vec()[0..8], &old_commit);
        assert_eq!(&public.as_u32_vec()[8..16], &new_commit);
        assert_eq!(
            &public.as_u32_vec()[GRAPH_NEW_ROOT_PI_BASE..GRAPH_NEW_ROOT_PI_BASE + 8],
            &public.rewrite.new_root
        );
        assert_eq!(retained.public_inputs.len(), CELL_PUBLIC_INPUT_COUNT);
        assert_eq!(retained.vk_recipe.canonical_vk_hash(), canonical_vk_hash());
        assert_eq!(
            retained.app_root_binding,
            AppRootBinding {
                app_root_pi_offset: GRAPH_NEW_ROOT_PI_BASE,
                app_root_len: 8,
                field_key: GRAPH_ROOT_FIELD_KEY,
            }
        );

        let proof_bytes = proof.to_postcard().unwrap();
        verify_postcard(&proof_bytes, &public.as_u32_vec()).unwrap();
    }

    #[test]
    fn every_cell_and_graph_join_is_proof_bound() {
        let old_commit = core::array::from_fn(|lane| 1_000 + lane as u32);
        let new_commit = core::array::from_fn(|lane| 2_000 + lane as u32);
        let (proof, public, _) = prove_zk(11, 77, 9, &witness(), old_commit, new_commit).unwrap();
        for mutate in 0..7 {
            let mut bad = public;
            match mutate {
                0 => bad.old_commit[0] += 1,
                1 => bad.new_commit[0] += 1,
                2 => bad.rewrite.domain += 1,
                3 => bad.rewrite.session += 1,
                4 => bad.rewrite.ruleset_root[0] += 1,
                5 => bad.rewrite.old_root[0] += 1,
                6 => bad.rewrite.new_root[0] += 1,
                _ => unreachable!(),
            }
            assert!(
                verify_zk(&proof, bad).is_err(),
                "mutation {mutate} verified"
            );
        }
    }

    const DIRECT_LEG_PI_COUNT: usize = 90;
    const DIRECT_GRAPH_FIELD_PI: usize = 66;

    /// Faithful wide-leg stand-in for the direct recursive binding node.  It
    /// exposes the PI commitment, all eight committed graph-root fields, the
    /// canonical program VK, and the final old/new state anchors.
    fn direct_leg_leaf(
        claim: [BabyBear; 8],
        graph_root: [BabyBear; 8],
        vk8: [BabyBear; 8],
        old8: [BabyBear; 8],
        new8: [BabyBear; 8],
        config: &DreggRecursionConfig,
    ) -> p3_recursion::RecursionOutput<DreggRecursionConfig> {
        let old_lo = DIRECT_LEG_PI_COUNT - 2 * SEG_ANCHOR_WIDTH;
        let new_lo = DIRECT_LEG_PI_COUNT - SEG_ANCHOR_WIDTH;
        let trace_width = 8 + 8 + 8 + 8 + 8;
        let pin = |col, pi_index| {
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col,
                pi_index,
            })
        };
        let mut constraints = Vec::new();
        for lane in 0..8 {
            constraints.push(pin(lane, CUSTOM_COMMIT_PI_LO + lane));
            constraints.push(pin(8 + lane, DIRECT_GRAPH_FIELD_PI + lane));
            constraints.push(pin(16 + lane, CUSTOM_PROGRAM_VK_PI_LO + lane));
            constraints.push(pin(24 + lane, old_lo + lane));
            constraints.push(pin(32 + lane, new_lo + lane));
        }
        let descriptor = EffectVmDescriptor2 {
            name: "private-graph-cell-direct-leg-standin".to_string(),
            trace_width,
            public_input_count: DIRECT_LEG_PI_COUNT,
            tables: vec![],
            constraints,
            hash_sites: vec![],
            ranges: vec![],
        };
        let mut row = Vec::with_capacity(trace_width);
        row.extend_from_slice(&claim);
        row.extend_from_slice(&graph_root);
        row.extend_from_slice(&vk8);
        row.extend_from_slice(&old8);
        row.extend_from_slice(&new8);
        let trace = (0..4).map(|_| row.clone()).collect::<Vec<_>>();
        let mut public = vec![BabyBear::ZERO; DIRECT_LEG_PI_COUNT];
        public[CUSTOM_COMMIT_PI_LO..CUSTOM_COMMIT_PI_LO + 8].copy_from_slice(&claim);
        public[DIRECT_GRAPH_FIELD_PI..DIRECT_GRAPH_FIELD_PI + 8].copy_from_slice(&graph_root);
        public[CUSTOM_PROGRAM_VK_PI_LO..CUSTOM_PROGRAM_VK_PI_LO + 8].copy_from_slice(&vk8);
        public[old_lo..old_lo + 8].copy_from_slice(&old8);
        public[new_lo..new_lo + 8].copy_from_slice(&new8);
        let proof = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
            &descriptor,
            &trace,
            &public,
            &MemBoundaryWitness::default(),
            &[],
            &UMemBoundaryWitness::default(),
            config,
        )
        .expect("faithful direct graph leg proves");
        prove_descriptor_leaf_expose_segment_and_claims(
            &descriptor,
            &proof,
            &public,
            config,
            &[
                (CUSTOM_COMMIT_PI_LO, CUSTOM_COMMIT_LEN),
                (DIRECT_GRAPH_FIELD_PI, 8),
                (CUSTOM_PROGRAM_VK_PI_LO, DEPLOYED_CUSTOM_PROGRAM_VK_PI_LEN),
            ],
        )
        .expect("direct graph leg exposes commitment, graph root, VK, and anchors")
    }

    #[test]
    #[ignore = "heavy: exact private-graph IR2 leaf + 8-lane app-root recursive fold"]
    fn private_graph_cell_direct_fold_binds_state_vk_and_stored_graph_root() {
        let old_u32 = core::array::from_fn(|lane| 1_000 + lane as u32);
        let new_u32 = core::array::from_fn(|lane| 2_000 + lane as u32);
        let (_proof, public, bundle) = prove_zk(11, 77, 9, &witness(), old_u32, new_u32).unwrap();
        let config = ir2_leaf_wrap_config();
        let direct = prove_direct_ir2_leaf_with_app_root_commitment(
            &bundle.descriptor,
            &bundle.base_trace,
            &bundle.public_inputs,
            &bundle.vk_recipe,
            &bundle.app_root_binding,
            &config,
        )
        .expect("exact private graph direct leaf proves");
        let claim = custom_proof_pi_commitment(&bundle.public_inputs);
        let leg = direct_leg_leaf(
            claim,
            public.rewrite.new_root.map(BabyBear::new),
            bundle.vk_recipe.canonical_vk_felts(),
            old_u32.map(BabyBear::new),
            new_u32.map(BabyBear::new),
            &config,
        );
        prove_direct_ir2_binding_node_app_root_segmented(&leg, &direct, &config, 8)
            .expect("graph proof folds only when state, VK, and stored graph root all agree");
    }
}
