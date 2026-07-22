//! Hiding, cell-bound proof of the Descent fixed-eight relic custody census.
//!
//! The exact relation is authored in Lean by
//! `Dregg2.Games.DescentCensusDescriptor`. Rust only fills the emitted
//! 16-row trace from the cell's canonical overflow-field map. The retained
//! direct-IR2 bundle welds both the six counted registers and the native-eight
//! `fields_root` into the recursive Custom leg.

use std::collections::BTreeMap;

use dregg_cell::{FieldElement, state::fields_root_leaves};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    chip_absorb_all_lanes, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2_with_config,
};
use dregg_circuit::effect_vm::custom_state_binding::{AppRootBinding, PostFieldsRootBinding};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf, heap_node8};
use dregg_circuit::stark_zk::{
    DreggZkStarkConfig, ZK_EXT_DEGREE, ZK_FRI_LOG_BLOWUP, ZK_FRI_LOG_FINAL_POLY_LEN,
    ZK_FRI_MAX_LOG_ARITY, ZK_FRI_NUM_QUERIES, ZK_FRI_QUERY_POW_BITS, create_zk_config,
};

use crate::joint_turn_aggregation::{CustomIr2VkRecipe, CustomIr2WitnessBundle};

pub const DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/descent-custody-census-fixed8-v1.json");

pub const RELICS: usize = 8;
pub const ZONES: usize = 6;
pub const DIGEST: usize = 8;
pub const TRACE_WIDTH: usize = 582;
pub const PUBLIC_INPUT_COUNT: usize = 30;
pub const PI_FIELDS_ROOT: usize = 16;
pub const PI_COUNTS: usize = 24;
pub const COUNT_FIELD_KEY: usize = 0;
pub const PLONKY3_REV: &str = "82cfad73cd734d37a0d51953094f970c531817ec";
pub const HIDING_VERIFIER_MANIFEST: &str = "descent-custody-census-fixed8-v1|BabyBear|Poseidon2-W16|HidingFriPcs|salt=4|random-codewords=4";

pub const RELIC_KEYS: [u64; RELICS] = [16, 17, 18, 19, 20, 21, 22, 23];
pub const RELIC_ADDRS: [u32; RELICS] = [
    1_903_373_793,
    206_503_848,
    186_807_208,
    1_229_116_775,
    1_194_514_939,
    1_456_787_871,
    1_049_436_545,
    14_058_645,
];
pub const RELIC_NEXT_ADDRS: [u32; RELICS] = [
    2_013_265_920,
    529_176_517,
    206_503_848,
    1_456_787_871,
    1_229_116_775,
    1_903_373_793,
    1_194_514_939,
    186_807_208,
];
pub const ZONE_CODES: [u64; ZONES] = [8, 9, 1, 2, 3, 4];

const STATE_SPAN: usize = 16;
const PATH_BASE: usize = STATE_SPAN;
const PATH_SPAN: usize = 70;
const COUNT_COL_BASE: usize = PATH_BASE + RELICS * PATH_SPAN;

const fn path_base(relic: usize) -> usize {
    PATH_BASE + relic * PATH_SPAN
}
const fn raw_col(relic: usize) -> usize {
    path_base(relic)
}
const fn value_hash_col(relic: usize, lane: usize) -> usize {
    path_base(relic) + 1 + lane
}
const fn leaf_col(relic: usize, lane: usize) -> usize {
    path_base(relic) + 9 + lane
}
const fn cur_col(relic: usize, lane: usize) -> usize {
    path_base(relic) + 17 + lane
}
const fn sibling_col(relic: usize, lane: usize) -> usize {
    path_base(relic) + 25 + lane
}
const fn left_col(relic: usize, lane: usize) -> usize {
    path_base(relic) + 33 + lane
}
const fn right_col(relic: usize, lane: usize) -> usize {
    path_base(relic) + 41 + lane
}
const fn parent_col(relic: usize, lane: usize) -> usize {
    path_base(relic) + 49 + lane
}
const fn dir_col(relic: usize) -> usize {
    path_base(relic) + 57
}
const fn eq_col(relic: usize, zone: usize) -> usize {
    path_base(relic) + 58 + zone
}
const fn inv_col(relic: usize, zone: usize) -> usize {
    path_base(relic) + 64 + zone
}
const fn count_col(zone: usize) -> usize {
    COUNT_COL_BASE + zone
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CensusStatement {
    pub old_commit: [u32; DIGEST],
    pub new_commit: [u32; DIGEST],
    pub post_fields_root: [u32; DIGEST],
    /// `[pack, bank, hoard_1, hoard_2, hoard_3, hoard_4]`.
    pub counts: [u32; ZONES],
}

impl CensusStatement {
    pub fn as_felts(self) -> Vec<BabyBear> {
        self.old_commit
            .into_iter()
            .chain(self.new_commit)
            .chain(self.post_fields_root)
            .chain(self.counts)
            .map(BabyBear::new)
            .collect()
    }

    pub fn validate(self) -> Result<(), String> {
        for (i, value) in self
            .old_commit
            .into_iter()
            .chain(self.new_commit)
            .chain(self.post_fields_root)
            .chain(self.counts)
            .enumerate()
        {
            if value >= BABYBEAR_P {
                return Err(format!(
                    "descent census PI {i}={value} is noncanonical for BabyBear"
                ));
            }
        }
        if self.counts.iter().any(|&count| count > RELICS as u32) {
            return Err("descent census count exceeds the fixed relic population".to_string());
        }
        Ok(())
    }

    pub fn try_from_u32s(values: &[u32]) -> Result<Self, String> {
        if values.len() != PUBLIC_INPUT_COUNT {
            return Err(format!(
                "descent census expects {PUBLIC_INPUT_COUNT} PIs, got {}",
                values.len()
            ));
        }
        let statement = Self {
            old_commit: values[0..8].try_into().expect("length checked"),
            new_commit: values[8..16].try_into().expect("length checked"),
            post_fields_root: values[16..24].try_into().expect("length checked"),
            counts: values[24..30].try_into().expect("length checked"),
        };
        statement.validate()?;
        Ok(statement)
    }
}

pub struct DescentCensusZkProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl DescentCensusZkProof {
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|error| format!("descent census proof encode failed: {error}"))
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        postcard::from_bytes(bytes)
            .map(|proof| Self { proof })
            .map_err(|error| format!("descent census proof decode failed: {error}"))
    }
}

pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let descriptor = parse_vm_descriptor2(DESCRIPTOR_JSON)?;
    if descriptor.name != "dregg-descent-custody-census-fixed8-v1"
        || descriptor.trace_width != TRACE_WIDTH
        || descriptor.public_input_count != PUBLIC_INPUT_COUNT
    {
        return Err("descent census emitted descriptor shape drifted".to_string());
    }
    Ok(descriptor)
}

pub fn air_fingerprint() -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key("dregg-descent-census-air-v1");
    hash.update(DESCRIPTOR_JSON.as_bytes());
    *hash.finalize().as_bytes()
}

pub fn hiding_verifier_config_fingerprint() -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key("dregg-descent-census-hiding-config-v1");
    hash.update(HIDING_VERIFIER_MANIFEST.as_bytes());
    hash.update(PLONKY3_REV.as_bytes());
    for knob in [
        ZK_FRI_LOG_BLOWUP,
        ZK_FRI_LOG_FINAL_POLY_LEN,
        ZK_FRI_MAX_LOG_ARITY,
        ZK_FRI_NUM_QUERIES,
        ZK_FRI_QUERY_POW_BITS,
        ZK_EXT_DEGREE,
    ] {
        hash.update(&(knob as u64).to_le_bytes());
    }
    hash.update(&air_fingerprint());
    *hash.finalize().as_bytes()
}

pub fn proving_system_canonical_bytes() -> Vec<u8> {
    let mut bytes = vec![0];
    bytes.extend_from_slice(&(PLONKY3_REV.len() as u64).to_le_bytes());
    bytes.extend_from_slice(PLONKY3_REV.as_bytes());
    bytes
}

pub fn vk_recipe() -> CustomIr2VkRecipe {
    CustomIr2VkRecipe::source_hash(
        DESCRIPTOR_JSON.as_bytes().to_vec(),
        air_fingerprint(),
        hiding_verifier_config_fingerprint(),
        proving_system_canonical_bytes(),
    )
}

pub fn canonical_vk_hash() -> [u8; 32] {
    vk_recipe().canonical_vk_hash()
}

fn field_to_u64(value: &FieldElement) -> u64 {
    u64::from_be_bytes(value[24..32].try_into().expect("fixed 8-byte tail"))
}

fn build_trace_and_statement(
    fields: &BTreeMap<u64, FieldElement>,
    old_commit: [u32; DIGEST],
    new_commit: [u32; DIGEST],
) -> Result<(Vec<Vec<BabyBear>>, CensusStatement), String> {
    let leaves = fields_root_leaves(fields);
    let tree = CanonicalHeapTree8::new(leaves, HEAP_TREE_DEPTH);
    let root = tree.root8().limbs();
    let mut trace = vec![vec![BabyBear::ZERO; TRACE_WIDTH]; HEAP_TREE_DEPTH];
    let mut counts = [0u32; ZONES];

    for row in &mut trace {
        for lane in 0..DIGEST {
            row[lane] = BabyBear::new(old_commit[lane]);
            row[8 + lane] = BabyBear::new(new_commit[lane]);
        }
    }

    for relic in 0..RELICS {
        let value = fields.get(&RELIC_KEYS[relic]).ok_or_else(|| {
            format!(
                "descent census: custody key {} is absent from post-state fields",
                RELIC_KEYS[relic]
            )
        })?;
        let raw = field_to_u64(value);
        if raw > u8::MAX as u64 {
            return Err(format!(
                "descent census: custody key {} has non-byte code {raw}",
                RELIC_KEYS[relic]
            ));
        }

        let addr = BabyBear::new(RELIC_ADDRS[relic]);
        let position = tree
            .position_of(addr)
            .ok_or_else(|| format!("descent census: canonical tree lacks relic leaf {relic}"))?;
        let leaf: HeapLeaf = tree.sorted_leaves()[position];
        if leaf.addr.as_u32() != RELIC_ADDRS[relic]
            || leaf.next_addr.as_u32() != RELIC_NEXT_ADDRS[relic]
        {
            return Err(format!(
                "descent census: relic {relic} IMT linkage drifted: addr={}, next={} \
                 (expected {}, {})",
                leaf.addr.as_u32(),
                leaf.next_addr.as_u32(),
                RELIC_ADDRS[relic],
                RELIC_NEXT_ADDRS[relic]
            ));
        }

        let mut encoded = [BabyBear::ZERO; 8];
        encoded[7] = BabyBear::new((raw as u32) << 24);
        let value_hash = chip_absorb_all_lanes(8, &encoded);
        if value_hash[0] != leaf.value {
            return Err(format!(
                "descent census: key {} is not canonical field_from_u64({raw})",
                RELIC_KEYS[relic]
            ));
        }
        let leaf_digest = leaf.digest8();
        let (siblings, directions) = tree
            .prove_membership(position)
            .ok_or_else(|| format!("descent census: cannot open relic leaf {relic}"))?;
        if siblings.len() != HEAP_TREE_DEPTH || directions.len() != HEAP_TREE_DEPTH {
            return Err("descent census: canonical path depth drifted".to_string());
        }

        let mut cur = leaf_digest;
        for level in 0..HEAP_TREE_DEPTH {
            let sibling = siblings[level];
            let dir = directions[level];
            let (left, right) = if dir == 0 {
                (cur, sibling)
            } else {
                (sibling, cur)
            };
            let parent = heap_node8(left, right);
            let row = &mut trace[level];
            row[raw_col(relic)] = BabyBear::new(raw as u32);
            row[dir_col(relic)] = BabyBear::new(dir as u32);
            for lane in 0..DIGEST {
                row[value_hash_col(relic, lane)] = value_hash[lane];
                row[leaf_col(relic, lane)] = leaf_digest[lane];
                row[cur_col(relic, lane)] = cur[lane];
                row[sibling_col(relic, lane)] = sibling[lane];
                row[left_col(relic, lane)] = left[lane];
                row[right_col(relic, lane)] = right[lane];
                row[parent_col(relic, lane)] = parent[lane];
            }
            for (zone, target) in ZONE_CODES.into_iter().enumerate() {
                let target = BabyBear::new(target as u32);
                let diff = BabyBear::new(raw as u32) - target;
                let equal = diff == BabyBear::ZERO;
                row[eq_col(relic, zone)] = if equal { BabyBear::ONE } else { BabyBear::ZERO };
                row[inv_col(relic, zone)] = diff.inverse().unwrap_or(BabyBear::ZERO);
                if level == 0 && equal {
                    counts[zone] += 1;
                }
            }
            cur = parent;
        }
        if cur != root {
            return Err(format!(
                "descent census: relic {relic} opening does not recompose fields_root"
            ));
        }
    }

    for row in &mut trace {
        for zone in 0..ZONES {
            row[count_col(zone)] = BabyBear::new(counts[zone]);
        }
    }
    let statement = CensusStatement {
        old_commit,
        new_commit,
        post_fields_root: root.map(BabyBear::as_u32),
        counts,
    };
    statement.validate()?;
    Ok((trace, statement))
}

pub fn prove_zk(
    fields: &BTreeMap<u64, FieldElement>,
    old_commit: [u32; DIGEST],
    new_commit: [u32; DIGEST],
) -> Result<
    (
        DescentCensusZkProof,
        CensusStatement,
        CustomIr2WitnessBundle,
    ),
    String,
> {
    let descriptor = descriptor()?;
    let (trace, statement) = build_trace_and_statement(fields, old_commit, new_commit)?;
    let public_inputs = statement.as_felts();
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
            app_root_pi_offset: PI_COUNTS,
            app_root_len: ZONES,
            field_key: COUNT_FIELD_KEY,
        },
        post_fields_root_binding: Some(PostFieldsRootBinding {
            fields_root_pi_offset: PI_FIELDS_ROOT,
        }),
    };
    Ok((DescentCensusZkProof { proof }, statement, retained))
}

pub fn verify_zk(proof: &DescentCensusZkProof, statement: CensusStatement) -> Result<(), String> {
    statement.validate()?;
    verify_vm_descriptor2_with_config(
        &descriptor()?,
        &proof.proof,
        &statement.as_felts(),
        &create_zk_config(),
    )
}

pub fn verify_postcard(proof_bytes: &[u8], public_values: &[u32]) -> Result<(), String> {
    let proof = DescentCensusZkProof::from_postcard(proof_bytes)?;
    verify_zk(&proof, CensusStatement::try_from_u32s(public_values)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn field_from_u64(value: u64) -> FieldElement {
        let mut out = [0u8; 32];
        out[24..].copy_from_slice(&value.to_be_bytes());
        out
    }

    fn sample_fields() -> BTreeMap<u64, FieldElement> {
        RELIC_KEYS
            .into_iter()
            .zip([1, 8, 8, 9, 2, 3, 4, 9])
            .map(|(key, code)| (key, field_from_u64(code)))
            .collect()
    }

    #[test]
    fn trace_recomposes_real_root_and_counts_all_six_zones() {
        let (_trace, statement) = build_trace_and_statement(&sample_fields(), [11; 8], [22; 8])
            .expect("honest fixed-eight census trace");
        assert_eq!(statement.counts, [2, 2, 1, 1, 1, 1]);
    }

    #[test]
    fn a_noncanonical_custody_encoding_is_refused() {
        let mut fields = sample_fields();
        let mut bad = field_from_u64(8);
        bad[0] = 1;
        fields.insert(RELIC_KEYS[0], bad);
        assert!(build_trace_and_statement(&fields, [11; 8], [22; 8]).is_err());
    }

    #[test]
    fn a_canonical_but_out_of_vocabulary_code_is_air_unsatisfiable() {
        let mut fields = sample_fields();
        fields.insert(RELIC_KEYS[0], field_from_u64(7));
        let (trace, statement) = build_trace_and_statement(&fields, [11; 8], [22; 8])
            .expect("code 7 is canonically encoded but must be rejected by AIR authority");
        let error = match prove_vm_descriptor2_for_config(
            &descriptor().expect("emitted descriptor"),
            &trace,
            &statement.as_felts(),
            &MemBoundaryWitness::default(),
            &[],
            &UMemBoundaryWitness::default(),
            &create_zk_config(),
        ) {
            Ok(_) => panic!("one-hot zone gate must make code 7 unsatisfiable"),
            Err(error) => error,
        };
        assert!(
            error.contains("constraint") || error.contains("gate") || error.contains("preflight"),
            "typed proving refusal should identify AIR failure, got: {error}"
        );
    }

    #[test]
    fn an_extra_interleaved_field_is_refused_by_exact_imt_successors() {
        let mut fields = sample_fields();
        // Search a small key whose hashed address changes one fixed successor.
        let key = (24u64..10_000)
            .find(|key| {
                let mut candidate = fields.clone();
                candidate.insert(*key, field_from_u64(0));
                build_trace_and_statement(&candidate, [11; 8], [22; 8]).is_err()
            })
            .expect("some extra key lands between fixed IMT leaves");
        fields.insert(key, field_from_u64(0));
        assert!(build_trace_and_statement(&fields, [11; 8], [22; 8]).is_err());
    }
}
