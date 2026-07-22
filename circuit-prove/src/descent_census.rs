//! Hiding, cell-bound proof of the Descent fixed-eight relic custody census.
//!
//! The exact relation is authored in Lean by
//! `Dregg2.Games.DescentCensusDescriptor`. Rust only fills the emitted
//! 16-row trace from the cell's canonical overflow-field map. The retained
//! direct-IR2 bundle welds both the six counted registers and the native-eight
//! `fields_root` into the recursive Custom leg.

use std::collections::BTreeMap;

use dregg_cell::{FieldElement, state::exact_fields_root_leaves};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
};
use dregg_circuit::descriptor_ir2_canonical::canonical_effect_vm_descriptor2_bytes;
use dregg_circuit::effect_vm::custom_state_binding::{AppRootBinding, PostFieldsRootBinding};
use dregg_circuit::exact_nullifier_aafi::{raw_to_u16_le, u64_to_u16_le};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::heap_root::HEAP_TREE_DEPTH;
use dregg_circuit::openable_fields_root::{
    CanonicalExactFieldsTree8, EXACT_FIELDS_NODE_DOMAIN, exact_fields_node8,
};
use dregg_circuit::poseidon2::{Poseidon2State, hash_many_8};
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
pub const TRACE_WIDTH: usize = 2_206;
pub const PUBLIC_INPUT_COUNT: usize = 30;
pub const PI_FIELDS_ROOT: usize = 16;
pub const PI_COUNTS: usize = 24;
pub const COUNT_FIELD_KEY: usize = 0;
pub const PREDICATE_NAME: &str = "dregg-descent-custody-census-fixed8-v2";
pub const PLONKY3_REV: &str = "82cfad73cd734d37a0d51953094f970c531817ec";
pub const HIDING_VERIFIER_MANIFEST: &str = "descent-custody-census-fixed8-v2|BabyBear|Poseidon2-state16|exact-fields-v2|HidingFriPcs|salt=4|random-codewords=4";
pub const APP_WRITE_POLICY_MANIFEST: &str = "descent-custody-census-fixed8-app-write-policy-v1";
pub const APP_WRITE_POLICY_VERSION: u32 = 1;
pub const APP_WRITE_ENCODING_DREGG_U64_BE: u8 = 1;

/// Consensus identity for the executor semantics paired with this proof.
///
/// The verifier is not fully identified by its AIR and FRI knobs: the executor
/// also interprets six public scalars as a particular contiguous cell write.
/// This tuple is folded into the verifier source fingerprint so none of those
/// semantics can drift while retaining the same custom VK.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DescentCensusAppWritePolicy {
    pub version: u32,
    pub app_root_pi_offset: usize,
    pub field_key: usize,
    pub app_root_len: usize,
    pub encoding_tag: u8,
}

pub const APP_WRITE_POLICY: DescentCensusAppWritePolicy = DescentCensusAppWritePolicy {
    version: APP_WRITE_POLICY_VERSION,
    app_root_pi_offset: PI_COUNTS,
    field_key: COUNT_FIELD_KEY,
    app_root_len: ZONES,
    encoding_tag: APP_WRITE_ENCODING_DREGG_U64_BE,
};

pub const RELIC_KEYS: [u64; RELICS] = [16, 17, 18, 19, 20, 21, 22, 23];
pub const ZONE_CODES: [u64; ZONES] = [8, 9, 1, 2, 3, 4];

const STATE_SPAN: usize = 16;
const PATH_BASE: usize = STATE_SPAN;
const KEY_LIMBS: usize = 4;
const VALUE_LIMBS: usize = 16;
const LEAF_STATE_STEPS: usize = 7;
const NODE_STATE_STEPS: usize = 6;
const PATH_SPAN: usize = 273;
const COUNT_COL_BASE: usize = PATH_BASE + RELICS * PATH_SPAN;

const fn path_base(relic: usize) -> usize {
    PATH_BASE + relic * PATH_SPAN
}
const fn key_base(relic: usize) -> usize {
    path_base(relic)
}
#[cfg(test)]
const fn key_col(relic: usize, lane: usize) -> usize {
    key_base(relic) + lane
}
const fn value_base(relic: usize) -> usize {
    key_base(relic) + KEY_LIMBS
}
const fn leaf_state_base(relic: usize) -> usize {
    value_base(relic) + VALUE_LIMBS
}
const fn cur_base(relic: usize) -> usize {
    leaf_state_base(relic) + 16 * LEAF_STATE_STEPS
}
const fn cur_col(relic: usize, lane: usize) -> usize {
    cur_base(relic) + lane
}
const fn sibling_base(relic: usize) -> usize {
    cur_base(relic) + DIGEST
}
const fn sibling_col(relic: usize, lane: usize) -> usize {
    sibling_base(relic) + lane
}
const fn left_base(relic: usize) -> usize {
    sibling_base(relic) + DIGEST
}
const fn left_col(relic: usize, lane: usize) -> usize {
    left_base(relic) + lane
}
const fn right_base(relic: usize) -> usize {
    left_base(relic) + DIGEST
}
const fn right_col(relic: usize, lane: usize) -> usize {
    right_base(relic) + lane
}
const fn node_state_base(relic: usize) -> usize {
    right_base(relic) + DIGEST
}
const fn dir_col(relic: usize) -> usize {
    node_state_base(relic) + 16 * NODE_STATE_STEPS
}
const fn eq_col(relic: usize, zone: usize) -> usize {
    dir_col(relic) + 1 + zone
}
const fn inv_col(relic: usize, zone: usize) -> usize {
    dir_col(relic) + 1 + ZONES + zone
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
    if descriptor.name != PREDICATE_NAME
        || descriptor.trace_width != TRACE_WIDTH
        || descriptor.public_input_count != PUBLIC_INPUT_COUNT
    {
        return Err("descent census emitted descriptor shape drifted".to_string());
    }
    Ok(descriptor)
}

pub fn canonical_descriptor_bytes_for(descriptor: &EffectVmDescriptor2) -> Result<Vec<u8>, String> {
    canonical_effect_vm_descriptor2_bytes(descriptor)
        .map_err(|error| format!("canonical Descent census descriptor encoding failed: {error}"))
}

pub fn canonical_descriptor_bytes() -> Vec<u8> {
    canonical_descriptor_bytes_for(
        &descriptor().expect("checked-in Descent census descriptor must parse and stay pinned"),
    )
    .expect("checked-in Descent census descriptor must have a canonical typed encoding")
}

fn air_fingerprint_for_descriptor(descriptor: &EffectVmDescriptor2) -> Result<[u8; 32], String> {
    let descriptor_bytes = canonical_descriptor_bytes_for(descriptor)?;
    let mut hash = blake3::Hasher::new_derive_key("dregg-descent-census-air-v2");
    hash.update(&descriptor_bytes);
    Ok(*hash.finalize().as_bytes())
}

pub fn air_fingerprint() -> [u8; 32] {
    air_fingerprint_for_descriptor(
        &descriptor().expect("checked-in Descent census descriptor must parse and stay pinned"),
    )
    .expect("checked-in Descent census descriptor must have a canonical typed encoding")
}

fn app_write_policy_fingerprint_for(policy: DescentCensusAppWritePolicy) -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key("dregg-descent-census-app-write-policy-v1");
    hash.update(APP_WRITE_POLICY_MANIFEST.as_bytes());
    hash.update(&policy.version.to_le_bytes());
    hash.update(&(policy.app_root_pi_offset as u64).to_le_bytes());
    hash.update(&(policy.field_key as u64).to_le_bytes());
    hash.update(&(policy.app_root_len as u64).to_le_bytes());
    hash.update(&[policy.encoding_tag]);
    *hash.finalize().as_bytes()
}

pub fn app_write_policy_fingerprint() -> [u8; 32] {
    app_write_policy_fingerprint_for(APP_WRITE_POLICY)
}

fn hiding_verifier_config_fingerprint_for_air_and_policy(
    air: [u8; 32],
    policy: DescentCensusAppWritePolicy,
) -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key("dregg-descent-census-hiding-config-v2");
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
    hash.update(&air);
    hash.update(&app_write_policy_fingerprint_for(policy));
    *hash.finalize().as_bytes()
}

fn hiding_verifier_config_fingerprint_for_air(air: [u8; 32]) -> [u8; 32] {
    hiding_verifier_config_fingerprint_for_air_and_policy(air, APP_WRITE_POLICY)
}

pub fn hiding_verifier_config_fingerprint() -> [u8; 32] {
    hiding_verifier_config_fingerprint_for_air(air_fingerprint())
}

pub fn proving_system_canonical_bytes() -> Vec<u8> {
    let mut bytes = vec![0];
    bytes.extend_from_slice(&(PLONKY3_REV.len() as u64).to_le_bytes());
    bytes.extend_from_slice(PLONKY3_REV.as_bytes());
    bytes
}

fn vk_recipe_for_descriptor_and_policy(
    descriptor: &EffectVmDescriptor2,
    policy: DescentCensusAppWritePolicy,
) -> Result<CustomIr2VkRecipe, String> {
    let air = air_fingerprint_for_descriptor(descriptor)?;
    Ok(CustomIr2VkRecipe::source_hash(
        canonical_descriptor_bytes_for(descriptor)?,
        air,
        hiding_verifier_config_fingerprint_for_air_and_policy(air, policy),
        proving_system_canonical_bytes(),
    ))
}

fn vk_recipe_for_descriptor(descriptor: &EffectVmDescriptor2) -> Result<CustomIr2VkRecipe, String> {
    vk_recipe_for_descriptor_and_policy(descriptor, APP_WRITE_POLICY)
}

#[cfg(test)]
fn canonical_vk_hash_for_descriptor(descriptor: &EffectVmDescriptor2) -> Result<[u8; 32], String> {
    Ok(vk_recipe_for_descriptor(descriptor)?.canonical_vk_hash())
}

#[cfg(test)]
fn canonical_vk_hash_for_descriptor_and_policy(
    descriptor: &EffectVmDescriptor2,
    policy: DescentCensusAppWritePolicy,
) -> Result<[u8; 32], String> {
    Ok(vk_recipe_for_descriptor_and_policy(descriptor, policy)?.canonical_vk_hash())
}

pub fn vk_recipe() -> CustomIr2VkRecipe {
    vk_recipe_for_descriptor(
        &descriptor().expect("checked-in Descent census descriptor must parse and stay pinned"),
    )
    .expect("checked-in Descent census descriptor must have a canonical typed encoding")
}

pub fn canonical_vk_hash() -> [u8; 32] {
    vk_recipe().canonical_vk_hash()
}

fn field_to_u64(value: &FieldElement) -> u64 {
    u64::from_be_bytes(value[24..32].try_into().expect("fixed 8-byte tail"))
}

fn sponge_states(preimage: &[BabyBear]) -> Vec<[BabyBear; 16]> {
    let mut sponge = Poseidon2State::new();
    sponge.state[4] = BabyBear::new(preimage.len() as u32);
    let mut states = Vec::with_capacity(preimage.len().div_ceil(4) + 1);
    for chunk in preimage.chunks(4) {
        for (lane, value) in chunk.iter().copied().enumerate() {
            sponge.state[lane] += value;
        }
        sponge.permute();
        states.push(sponge.state);
    }
    sponge.permute();
    states.push(sponge.state);
    states
}

fn sponge_digest(states: &[[BabyBear; 16]]) -> [BabyBear; DIGEST] {
    let absorb = states[states.len() - 2];
    let squeeze = states[states.len() - 1];
    core::array::from_fn(|lane| {
        if lane < 4 {
            absorb[lane]
        } else {
            squeeze[lane - 4]
        }
    })
}

fn write(row: &mut [BabyBear], base: usize, values: &[BabyBear]) {
    row[base..base + values.len()].copy_from_slice(values);
}

fn write_states(row: &mut [BabyBear], base: usize, states: &[[BabyBear; 16]]) {
    for (step, state) in states.iter().enumerate() {
        write(row, base + 16 * step, state);
    }
}

fn build_trace_and_statement_with_custody_check(
    fields: &BTreeMap<u64, FieldElement>,
    old_commit: [u32; DIGEST],
    new_commit: [u32; DIGEST],
    enforce_canonical_custody: bool,
) -> Result<(Vec<Vec<BabyBear>>, CensusStatement), String> {
    let tree =
        CanonicalExactFieldsTree8::try_new(exact_fields_root_leaves(fields), HEAP_TREE_DEPTH)
            .map_err(|error| format!("descent census: invalid exact fields tree: {error}"))?;
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
        if enforce_canonical_custody && raw > u8::MAX as u64 {
            return Err(format!(
                "descent census: custody key {} has non-byte code {raw}",
                RELIC_KEYS[relic]
            ));
        }

        let position = tree
            .position_of(RELIC_KEYS[relic])
            .ok_or_else(|| format!("descent census: canonical tree lacks relic leaf {relic}"))?;
        let leaf = tree.sorted_leaves()[position];
        if leaf.key() != RELIC_KEYS[relic] || !leaf.is_present() || leaf.value() != *value {
            return Err(format!(
                "descent census: relic {relic} exact leaf identity drifted"
            ));
        }

        let mut canonical_value = [0u8; 32];
        canonical_value[24..].copy_from_slice(&raw.to_be_bytes());
        if enforce_canonical_custody && value != &canonical_value {
            return Err(format!(
                "descent census: key {} is not canonical field_from_u64({raw})",
                RELIC_KEYS[relic]
            ));
        }
        let key_limbs = u64_to_u16_le(RELIC_KEYS[relic]).map(|limb| BabyBear::new(limb.into()));
        let value_limbs = raw_to_u16_le(*value).map(|limb| BabyBear::new(limb.into()));
        let leaf_preimage = leaf.preimage();
        let leaf_states = sponge_states(&leaf_preimage);
        if leaf_states.len() != LEAF_STATE_STEPS
            || sponge_digest(&leaf_states) != leaf.digest8()
            || leaf.digest8() != hash_many_8(&leaf_preimage)
        {
            return Err("descent census: exact leaf state16 schedule drifted".to_string());
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
            let mut node_preimage = [BabyBear::ZERO; 1 + 2 * DIGEST];
            node_preimage[0] = BabyBear::new(EXACT_FIELDS_NODE_DOMAIN);
            node_preimage[1..1 + DIGEST].copy_from_slice(&left);
            node_preimage[1 + DIGEST..].copy_from_slice(&right);
            let node_states = sponge_states(&node_preimage);
            let parent = sponge_digest(&node_states);
            if node_states.len() != NODE_STATE_STEPS
                || parent != exact_fields_node8(left, right)
                || parent != hash_many_8(&node_preimage)
            {
                return Err(format!(
                    "descent census: exact node state16 schedule drifted at level {level}"
                ));
            }
            let row = &mut trace[level];
            write(row, key_base(relic), &key_limbs);
            write(row, value_base(relic), &value_limbs);
            write_states(row, leaf_state_base(relic), &leaf_states);
            write_states(row, node_state_base(relic), &node_states);
            row[dir_col(relic)] = BabyBear::new(dir as u32);
            for lane in 0..DIGEST {
                row[cur_col(relic, lane)] = cur[lane];
                row[sibling_col(relic, lane)] = sibling[lane];
                row[left_col(relic, lane)] = left[lane];
                row[right_col(relic, lane)] = right[lane];
            }
            for (zone, target) in ZONE_CODES.into_iter().enumerate() {
                let target = BabyBear::new((256 * target) as u32);
                let diff = value_limbs[15] - target;
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

fn build_trace_and_statement(
    fields: &BTreeMap<u64, FieldElement>,
    old_commit: [u32; DIGEST],
    new_commit: [u32; DIGEST],
) -> Result<(Vec<Vec<BabyBear>>, CensusStatement), String> {
    build_trace_and_statement_with_custody_check(fields, old_commit, new_commit, true)
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
            app_root_pi_offset: APP_WRITE_POLICY.app_root_pi_offset,
            app_root_len: APP_WRITE_POLICY.app_root_len,
            field_key: APP_WRITE_POLICY.field_key,
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

/// Decode the canonical custom-registry byte ABI (`u32` little-endian per PI).
pub fn decode_public_input_bytes(bytes: &[u8]) -> Result<Vec<u32>, String> {
    if bytes.len() != 4 * PUBLIC_INPUT_COUNT {
        return Err(format!(
            "descent census custom PI bytes must be {}, got {}",
            4 * PUBLIC_INPUT_COUNT,
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
    use dregg_circuit::cap_root::fold_bytes32;
    use dregg_circuit::openable_fields_root::ExactFieldsLeaf;

    const DESCRIPTOR_HEADER: &str = concat!(
        "{\"name\":\"dregg-descent-custody-census-fixed8-v2\",",
        "\"ir\":2,\"trace_width\":2206,\"public_input_count\":30,"
    );

    fn whitespace_and_top_level_key_reordered_json() -> String {
        let body = DESCRIPTOR_JSON
            .strip_prefix(DESCRIPTOR_HEADER)
            .expect("Descent census descriptor header remains recognized");
        format!(
            "{{\n  \"public_input_count\" : 30,\n  \"trace_width\" : 2206,\n  \
             \"name\" : \"{PREDICATE_NAME}\",\n  \"ir\" : 2,\n  {body}\n"
        )
    }

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

    /// Descriptor preflight currently reports an unsatisfied AIR either as a
    /// typed `Err` or as a panic from Plonky3's debug constraint checker.  Both
    /// are valid refusal poles; only a produced proof is an acceptance.
    fn air_refuses(trace: &[Vec<BabyBear>], public: &[BabyBear]) -> bool {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2_for_config(
                &descriptor().expect("emitted descriptor"),
                trace,
                public,
                &MemBoundaryWitness::default(),
                &[],
                &UMemBoundaryWitness::default(),
                &create_zk_config(),
            )
        }));
        !matches!(result, Ok(Ok(_)))
    }

    #[test]
    fn exact_leaf_and_node_state_schedules_match_the_live_hash_many_8() {
        let tree = CanonicalExactFieldsTree8::try_new(
            exact_fields_root_leaves(&sample_fields()),
            HEAP_TREE_DEPTH,
        )
        .expect("exact fields tree");
        for key in RELIC_KEYS {
            let position = tree.position_of(key).expect("relic leaf");
            let leaf = tree.sorted_leaves()[position];
            let states = sponge_states(&leaf.preimage());
            assert_eq!(states.len(), LEAF_STATE_STEPS);
            assert_eq!(sponge_digest(&states), leaf.digest8());
            assert_eq!(leaf.digest8(), hash_many_8(&leaf.preimage()));
        }
    }

    #[test]
    fn json_format_is_not_identity_but_typed_descriptor_and_runtime_policy_semantics_are() {
        let canonical = descriptor().expect("canonical Lean JSON parses");
        let alternate = parse_vm_descriptor2(&whitespace_and_top_level_key_reordered_json())
            .expect("equivalent reordered JSON parses");
        assert_eq!(canonical, alternate);
        assert_eq!(
            canonical_descriptor_bytes_for(&canonical).unwrap(),
            canonical_descriptor_bytes_for(&alternate).unwrap()
        );
        assert_eq!(
            air_fingerprint_for_descriptor(&canonical).unwrap(),
            air_fingerprint_for_descriptor(&alternate).unwrap()
        );
        assert_eq!(
            canonical_vk_hash_for_descriptor(&canonical).unwrap(),
            canonical_vk_hash_for_descriptor(&alternate).unwrap()
        );

        let mut typed_mutation = canonical.clone();
        typed_mutation.trace_width += 1;
        assert_ne!(
            air_fingerprint_for_descriptor(&canonical).unwrap(),
            air_fingerprint_for_descriptor(&typed_mutation).unwrap()
        );
        assert_ne!(
            canonical_vk_hash_for_descriptor(&canonical).unwrap(),
            canonical_vk_hash_for_descriptor(&typed_mutation).unwrap()
        );

        let policy = APP_WRITE_POLICY;
        let policy_mutations = [
            DescentCensusAppWritePolicy {
                version: policy.version + 1,
                ..policy
            },
            DescentCensusAppWritePolicy {
                app_root_pi_offset: policy.app_root_pi_offset + 1,
                ..policy
            },
            DescentCensusAppWritePolicy {
                field_key: policy.field_key + 1,
                ..policy
            },
            DescentCensusAppWritePolicy {
                app_root_len: policy.app_root_len + 1,
                ..policy
            },
            DescentCensusAppWritePolicy {
                encoding_tag: policy.encoding_tag ^ 1,
                ..policy
            },
        ];
        let air = air_fingerprint_for_descriptor(&canonical).unwrap();
        for mutation in policy_mutations {
            assert_ne!(
                app_write_policy_fingerprint_for(policy),
                app_write_policy_fingerprint_for(mutation)
            );
            assert_ne!(
                hiding_verifier_config_fingerprint_for_air_and_policy(air, policy),
                hiding_verifier_config_fingerprint_for_air_and_policy(air, mutation)
            );
            assert_ne!(
                canonical_vk_hash_for_descriptor_and_policy(&canonical, policy).unwrap(),
                canonical_vk_hash_for_descriptor_and_policy(&canonical, mutation).unwrap()
            );
        }
    }

    #[test]
    fn exact_modular_alias_is_host_refused_and_air_unsatisfiable() {
        let canonical = field_from_u64(8);
        let mut old_fold_alias = canonical;
        old_fold_alias[28..32].copy_from_slice(&[1, 0, 0, 0x80]);
        assert_ne!(old_fold_alias, canonical);
        assert_eq!(
            fold_bytes32(&old_fold_alias),
            fold_bytes32(&canonical),
            "this is the concrete V1 +p alias the exact schema removes"
        );

        let mut fields = sample_fields();
        fields.insert(RELIC_KEYS[0], old_fold_alias);
        assert!(build_trace_and_statement(&fields, [11; 8], [22; 8]).is_err());

        // Model a hostile prover bypassing the host canonical-code check.  Its
        // exact FLD2/FLN2 path is otherwise honestly recomputed to the malicious
        // root; the Lean value-limb/one-hot authority still makes it UNSAT.
        let (trace, statement) =
            build_trace_and_statement_with_custody_check(&fields, [11; 8], [22; 8], false)
                .expect("unchecked hostile witness can be materialized for the AIR tooth");
        assert!(
            air_refuses(&trace, &statement.as_felts()),
            "the exact +p alias must be AIR-unsatisfiable"
        );
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
    fn wrong_raw_key_limb_is_air_unsatisfiable() {
        let (mut trace, statement) =
            build_trace_and_statement(&sample_fields(), [11; 8], [22; 8]).unwrap();
        for row in &mut trace {
            row[key_col(0, 0)] += BabyBear::ONE;
        }
        assert!(
            air_refuses(&trace, &statement.as_felts()),
            "raw relic key 16 must not be substitutable"
        );
    }

    #[test]
    fn a_canonical_but_out_of_vocabulary_code_is_air_unsatisfiable() {
        let mut fields = sample_fields();
        fields.insert(RELIC_KEYS[0], field_from_u64(7));
        let (trace, statement) = build_trace_and_statement(&fields, [11; 8], [22; 8])
            .expect("code 7 is canonically encoded but must be rejected by AIR authority");
        assert!(
            air_refuses(&trace, &statement.as_felts()),
            "one-hot zone gate must make code 7 unsatisfiable"
        );
    }

    #[test]
    fn exact_tree_refuses_duplicates_and_preserves_old_colliding_keys() {
        let value = field_from_u64(1);
        assert!(
            CanonicalExactFieldsTree8::try_new(
                vec![
                    ExactFieldsLeaf::present(1, value),
                    ExactFieldsLeaf::present(1, value),
                ],
                HEAP_TREE_DEPTH,
            )
            .is_err()
        );

        let old_alias = 1 + BABYBEAR_P as u64;
        assert_eq!(
            dregg_cell::state::field_key_hash(1),
            dregg_cell::state::field_key_hash(old_alias),
            "V1 reduced this pair to one sort address"
        );
        let tree = CanonicalExactFieldsTree8::try_new(
            vec![
                ExactFieldsLeaf::present(1, value),
                ExactFieldsLeaf::present(old_alias, value),
            ],
            HEAP_TREE_DEPTH,
        )
        .expect("V2 carries both distinct raw keys without silent deduplication");
        assert_ne!(
            tree.sorted_leaves()[0].digest8(),
            tree.sorted_leaves()[1].digest8()
        );
        assert_eq!(tree.position_of(1), Some(0));
        assert_eq!(tree.position_of(old_alias), Some(1));
    }

    #[test]
    fn extra_fields_recompose_honestly_without_fixed_successor_assumptions() {
        let mut fields = sample_fields();
        let (_, before) = build_trace_and_statement(&fields, [11; 8], [22; 8]).unwrap();
        fields.insert(20_000, field_from_u64(0));
        let (_, after) = build_trace_and_statement(&fields, [11; 8], [22; 8])
            .expect("exact membership paths tolerate unrelated canonical fields");
        assert_eq!(before.counts, after.counts);
        assert_ne!(before.post_fields_root, after.post_fields_root);
    }
}
