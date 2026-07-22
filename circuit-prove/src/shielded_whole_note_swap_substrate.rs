//! Hiding producer/verifier for the Lean-authored shielded whole-note swap substrate.
//!
//! This module is deliberately a strict witness filler, not a second statement definition.  The
//! exact descriptor bytes are authored by
//! `Dregg2.Circuit.Emit.ShieldedWholeNoteSwapSubstrateDescriptor` and checked into the by-name
//! registry.  One
//! hidden selected-note opening drives the full nullifier, the wide value/asset binding, the
//! selected swap input, and the appended FNI4 leaf.  The producer derives all 100 public lanes;
//! callers cannot provide detached roots or compatibility scalars.
//!
//! The bounded market rule is a whole-note two-party swap.  Output zero transfers the
//! counterparty's complete value/asset to the selected owner; output one transfers the selected
//! value/asset to the counterparty owner.  This makes per-asset conservation structural.  It is
//! not yet a partial-fill order book.
//!
//! Proof-system floor: BabyBear + Poseidon2-W16 + HidingFRI at the pinned Plonky3 revision.  The
//! AIR proves the private computation, output-note commitment, and binary depth-32 linked exact
//! append.  It does **not** prove the nineteen Dark-AMM lanes, twenty-seven ring lanes, or fixed
//! pricing/ring rule of `ShieldedExactApexV4`; its FWS1 consequence domain is deliberately distinct
//! from semantic-v4 FXC4.
//!
//! ## Security boundary — proof substrate, not settlement authority
//!
//! This v1 relation does **not** authenticate either hidden input against the historical-note
//! root, prove `selected_secret -> selected.owner`, authenticate the counterparty opening as a
//! market reserve/input, or prove the semantic transition from `before_outer_commit` to
//! `after_outer_commit`.  Those values are bound into substrate-only FWS1, but a surrounding composition
//! must still prove those four welds.  Consequently this module exposes an opaque proof and no
//! settlement-authority token.  Treating this proof alone as a complete private swap would be a
//! security bug.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    chip_permute_state16, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2_with_config,
};
use dregg_circuit::descriptor_ir2_canonical::canonical_effect_vm_descriptor2_bytes;
use dregg_circuit::exact_nullifier_aafi::TaggedKeyWire;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::poseidon2::hash_many_8;
use dregg_circuit::stark_zk::{
    DreggZkStarkConfig, ZK_EXT_DEGREE, ZK_FRI_LOG_BLOWUP, ZK_FRI_LOG_FINAL_POLY_LEN,
    ZK_FRI_MAX_LOG_ARITY, ZK_FRI_NUM_QUERIES, ZK_FRI_QUERY_POW_BITS, create_zk_config,
};

pub const DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/shielded-whole-note-swap-substrate-v1.json");
pub const PREDICATE_NAME: &str = "shielded-whole-note-swap-substrate-v1::one-opening-aafi32-v1";
pub const TRACE_WIDTH: usize = 15_611;
pub const TRACE_HEIGHT: usize = 2;
pub const PUBLIC_INPUT_COUNT: usize = 100;
pub const TREE_DEPTH: usize = 32;
pub const ROOT_LANES: usize = 8;
pub const KEY_LANES: usize = 16;
pub const WIDE_LANES: usize = 16;
pub const OPENING_LANES: usize = 20;
pub const PLONKY3_REV: &str = crate::private_graph_rewrite::PLONKY3_REV;
pub const HIDING_VERIFIER_MANIFEST: &str = "shielded-whole-note-swap-substrate-v1|BabyBear|Poseidon2-W16|HidingFriPcs|salt=4|random-codewords=4";
pub const MAX_PROOF_BYTES: usize = 64 * 1024 * 1024;
pub const EXPECTED_PROOF_INSTANCES: usize = 3;
pub const EXPECTED_HIDING_DEGREE_BITS: [usize; EXPECTED_PROOF_INSTANCES] = [2, 11, 5];
pub const PROOF_SUBSTRATE_ONLY: &str = "missing Dark-AMM/ring pricing semantics, input membership, selected spend authority, counterparty provenance, and outer transition";

const FNI4: u32 = 0x464e_4934;
const FNE4: u32 = 0x464e_4534;
const FNN4: u32 = 0x464e_4e34;
const FNS4: u32 = 0x464e_5334;
const FXO4: u32 = 0x4658_4f34;
/// ASCII `FWS1`: consequence schema for this narrow whole-note swap only.
///
/// This is intentionally not semantic-v4 `FXC4`; absent a future explicit refinement/weld, the
/// two public statement types and consequence schemas cannot be converted into one another.
pub const WHOLE_NOTE_SWAP_CONSEQUENCE_DOMAIN: u32 = 0x4657_5331;
const NULLIFIER_FORK0: u32 = 0x4e46_3430;
const NULLIFIER_FORK1: u32 = 0x4e46_3431;
const NOTE_FORK0: u32 = 0x4e54_3430;
const NOTE_FORK1: u32 = 0x4e54_3431;
const FIELD_HI_CANON_MAX: u16 = 0x7800;

const SELECTED_BASE: usize = 0;
const COUNTER_BASE: usize = 20;
const OUTPUT0_BASE: usize = 40;
const OUTPUT1_BASE: usize = 60;
const SECRET_BASE: usize = 80;
const NULLIFIER_BASE: usize = 96;
const NULLIFIER_HIGH_BASE: usize = 112;
const NULLIFIER_SLACK_BASE: usize = 128;
const NULLIFIER_ZERO_BASE: usize = 144;
const NULLIFIER_INV_BASE: usize = 160;
const BINDING_BASE: usize = 176;
const PRIOR_ROOT_BASE: usize = 192;
const SUCCESSOR_ROOT_BASE: usize = 200;
const PRE_COUNT_BASE: usize = 208;
const POST_COUNT_BASE: usize = 212;
const HISTORICAL_HEIGHT_BASE: usize = 216;
const HISTORICAL_ROOT_BASE: usize = 220;
const BEFORE_OUTER_BASE: usize = 228;
const AFTER_OUTER_BASE: usize = 236;
const OUTPUT0_COMMIT_BASE: usize = 244;
const OUTPUT1_COMMIT_BASE: usize = 260;
const OUTPUT_ROOT_BASE: usize = 276;
const CONSEQUENCE_BASE: usize = 284;
const LOW_ADDR_TAG: usize = 292;
const LOW_ADDR_BASE: usize = 293;
const LOW_BINDING_BASE: usize = 309;
const LOW_NEXT_TAG: usize = 325;
const LOW_NEXT_BASE: usize = 326;
const LOW_POS_BITS: usize = 342;
const APP_POS_BITS: usize = 374;
const LOW_SIB_BASE: usize = 406;
const APP_SIB_BASE: usize = 662;
const LEX_LOW_AUX_BASE: usize = 918;
const LEX_NEXT_AUX_BASE: usize = 935;
const COUNT_CARRY_BASE: usize = 952;
const NULLIFIER0_STATE: usize = 955;
const NULLIFIER1_STATE: usize = 1131;
const WIDE0_STATE: usize = 1307;
const WIDE1_STATE: usize = 1403;
const LOW_OLD_LEAF_STATE: usize = 1499;
const LOW_NEW_LEAF_STATE: usize = 1723;
const APPENDED_LEAF_STATE: usize = 1947;
const OUTPUT0_NOTE0_STATE: usize = 2171;
const OUTPUT0_NOTE1_STATE: usize = 2283;
const OUTPUT1_NOTE0_STATE: usize = 2395;
const OUTPUT1_NOTE1_STATE: usize = 2507;
const OUTPUT_ROOT_STATE: usize = 2619;
const PRE_STATE_COMMIT_STATE: usize = 2779;
const POST_STATE_COMMIT_STATE: usize = 2859;
const PRE_STATE_COPY: usize = 2939;
const POST_STATE_COPY: usize = 2947;
const CONSEQUENCE_REAL_STATE: usize = 2955;
const NODE_STATE_BASE: usize = 3323;
const NODE_STATE_STRIDE: usize = 96;

const PI_HEIGHT: usize = 0;
const PI_HISTORICAL_ROOT: usize = 4;
const PI_NULLIFIER: usize = 12;
const PI_BINDING: usize = 28;
const PI_SUCCESSOR_ROOT: usize = 44;
const PI_PRIOR_ROOT: usize = 52;
const PI_PRE_COUNT: usize = 60;
const PI_POST_COUNT: usize = 64;
const PI_CONSEQUENCE: usize = 68;
const PI_OUTPUT_ROOT: usize = 76;
const PI_BEFORE_OUTER: usize = 84;
const PI_AFTER_OUTER: usize = 92;

const _: () = {
    assert!(FNI4 < BABYBEAR_P);
    assert!(FNE4 < BABYBEAR_P);
    assert!(FNN4 < BABYBEAR_P);
    assert!(FNS4 < BABYBEAR_P);
    assert!(FXO4 < BABYBEAR_P);
    assert!(WHOLE_NOTE_SWAP_CONSEQUENCE_DOMAIN < BABYBEAR_P);
    assert!(NODE_STATE_BASE + 4 * TREE_DEPTH * NODE_STATE_STRIDE == TRACE_WIDTH);
    assert!(PI_AFTER_OUTER + ROOT_LANES == PUBLIC_INPUT_COUNT);
};

/// Canonical 100-lane statement for the narrow FWS1 whole-note swap substrate.
///
/// This is deliberately distinct from
/// `crate::shielded_exact_apex_v4::ShieldedExactApexV4Public`. It neither carries nor implies the
/// Dark-AMM/ring lanes and fixed rule needed by the semantic apex.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShieldedWholeNoteSwapSubstratePublic {
    lanes: [u32; PUBLIC_INPUT_COUNT],
}

impl ShieldedWholeNoteSwapSubstratePublic {
    pub fn try_from_u32s(lanes: &[u32]) -> Result<Self, String> {
        if lanes.len() != PUBLIC_INPUT_COUNT {
            return Err(format!(
                "whole-note swap substrate public lane count {} != {PUBLIC_INPUT_COUNT}",
                lanes.len()
            ));
        }
        let mut exact = [0u32; PUBLIC_INPUT_COUNT];
        exact.copy_from_slice(lanes);
        for (index, value) in exact.iter().copied().enumerate() {
            if value >= BABYBEAR_P {
                return Err(format!(
                    "whole-note swap substrate lane {index}={value} is noncanonical"
                ));
            }
            let is_u16 = (PI_HEIGHT..PI_HISTORICAL_ROOT).contains(&index)
                || (PI_NULLIFIER..PI_BINDING).contains(&index)
                || (PI_PRE_COUNT..PI_CONSEQUENCE).contains(&index);
            if is_u16 && value > u16::MAX as u32 {
                return Err(format!(
                    "whole-note swap substrate u16 lane {index}={value} is noncanonical"
                ));
            }
        }
        let read_u64 = |base: usize| {
            (0..4).fold(0u64, |value, lane| {
                value | (u64::from(exact[base + lane]) << (16 * lane))
            })
        };
        let pre_count = read_u64(PI_PRE_COUNT);
        let post_count = read_u64(PI_POST_COUNT);
        if pre_count.checked_add(1) != Some(post_count) {
            return Err(format!(
                "whole-note swap substrate count transition {pre_count}->{post_count} is not +1"
            ));
        }
        Ok(Self { lanes: exact })
    }

    pub const fn as_u32_array(&self) -> &[u32; PUBLIC_INPUT_COUNT] {
        &self.lanes
    }

    pub fn output_notes_root(&self) -> [u32; ROOT_LANES] {
        self.lanes[PI_OUTPUT_ROOT..PI_BEFORE_OUTER]
            .try_into()
            .expect("fixed whole-note swap output-root width")
    }
}

/// One fully hidden note opening.  Each `u64` is encoded as four exact little-endian u16 limbs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HiddenNoteOpeningV4 {
    pub value: u64,
    pub asset: u64,
    pub randomness: u64,
    pub owner: u64,
    pub nonce: u64,
}

impl HiddenNoteOpeningV4 {
    fn limbs(self) -> [u16; OPENING_LANES] {
        let mut out = [0u16; OPENING_LANES];
        for (field, value) in [
            self.value,
            self.asset,
            self.randomness,
            self.owner,
            self.nonce,
        ]
        .into_iter()
        .enumerate()
        {
            out[field * 4..field * 4 + 4].copy_from_slice(&u64_limbs(value));
        }
        out
    }
}

/// One fixed depth-32 binary authentication path, bottom-up.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BinaryExactPathV4 {
    pub position: u32,
    pub siblings: [[u32; ROOT_LANES]; TREE_DEPTH],
}

/// Complete private witness.  All verifier-facing roots are derived from this structure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShieldedWholeNoteSwapSubstrateWitness {
    pub selected: HiddenNoteOpeningV4,
    pub counterparty: HiddenNoteOpeningV4,
    pub selected_secret: [u16; KEY_LANES],
    pub output_randomness: [u64; 2],
    pub output_nonce: [u64; 2],
    pub predecessor_addr: TaggedKeyWire,
    pub predecessor_binding: [u32; WIDE_LANES],
    pub predecessor_next: TaggedKeyWire,
    pub predecessor_path: BinaryExactPathV4,
    pub append_path: BinaryExactPathV4,
    pub pre_count: u64,
    pub historical_height: u64,
    pub historical_note_root: [u32; ROOT_LANES],
    pub before_outer_commit: [u32; ROOT_LANES],
    pub after_outer_commit: [u32; ROOT_LANES],
}

/// Opaque proof under the sole code-owned HidingFRI configuration.
pub struct ShieldedWholeNoteSwapSubstrateZkProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl ShieldedWholeNoteSwapSubstrateZkProof {
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|error| format!("whole-note swap substrate proof encode failed: {error}"))
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() > MAX_PROOF_BYTES {
            return Err(format!(
                "whole-note swap substrate proof is {} bytes; limit is {MAX_PROOF_BYTES}",
                bytes.len()
            ));
        }
        let (proof, trailing) = postcard::take_from_bytes::<Ir2BatchProof<DreggZkStarkConfig>>(
            bytes,
        )
        .map_err(|error| format!("whole-note swap substrate proof decode failed: {error}"))?;
        if !trailing.is_empty() {
            return Err(format!(
                "whole-note swap substrate proof has {} trailing bytes",
                trailing.len()
            ));
        }
        validate_hiding_proof_shape(&proof)?;
        let canonical = postcard::to_allocvec(&proof).map_err(|error| {
            format!("whole-note swap substrate canonical proof re-encode failed: {error}")
        })?;
        if canonical.as_slice() != bytes {
            return Err(
                "whole-note swap substrate proof uses a non-canonical postcard encoding"
                    .to_string(),
            );
        }
        Ok(Self { proof })
    }
}

fn validate_hiding_proof_shape(proof: &Ir2BatchProof<DreggZkStarkConfig>) -> Result<(), String> {
    if proof.degree_bits.as_slice() != EXPECTED_HIDING_DEGREE_BITS {
        return Err(format!(
            "whole-note swap substrate proof degree vector {:?} != pinned HidingFRI vector {:?}",
            proof.degree_bits, EXPECTED_HIDING_DEGREE_BITS
        ));
    }
    if proof.opened_values.instances.len() != EXPECTED_PROOF_INSTANCES {
        return Err(format!(
            "whole-note swap substrate proof has {} opened instances, expected {EXPECTED_PROOF_INSTANCES}",
            proof.opened_values.instances.len()
        ));
    }
    if proof.commitments.random.is_none()
        || proof
            .opened_values
            .instances
            .iter()
            .any(|instance| instance.base_opened_values.random.is_none())
    {
        return Err(
            "whole-note swap substrate proof is not a complete HidingFRI proof".to_string(),
        );
    }
    Ok(())
}

pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let descriptor = parse_vm_descriptor2(DESCRIPTOR_JSON)?;
    if descriptor.name != PREDICATE_NAME
        || descriptor.trace_width != TRACE_WIDTH
        || descriptor.public_input_count != PUBLIC_INPUT_COUNT
    {
        return Err("whole-note swap substrate emitted descriptor shape drifted".to_string());
    }
    Ok(descriptor)
}

fn canonical_descriptor_bytes_for(descriptor: &EffectVmDescriptor2) -> Result<Vec<u8>, String> {
    canonical_effect_vm_descriptor2_bytes(descriptor).map_err(|error| {
        format!("canonical whole-note swap substrate descriptor encoding failed: {error}")
    })
}

fn air_fingerprint_for_descriptor(descriptor: &EffectVmDescriptor2) -> Result<[u8; 32], String> {
    let descriptor_bytes = canonical_descriptor_bytes_for(descriptor)?;
    let mut hash =
        blake3::Hasher::new_derive_key("dregg-shielded-whole-note-swap-substrate-v1-air-v1");
    hash.update(&descriptor_bytes);
    Ok(*hash.finalize().as_bytes())
}

pub fn air_fingerprint() -> [u8; 32] {
    air_fingerprint_for_descriptor(
        &descriptor()
            .expect("checked-in whole-note swap substrate descriptor must parse and stay pinned"),
    )
    .expect("checked-in whole-note swap substrate descriptor must have a canonical typed encoding")
}

fn hiding_verifier_config_fingerprint_for_air(air: [u8; 32]) -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key(
        "dregg-shielded-whole-note-swap-substrate-v1-hiding-config-v1",
    );
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
    *hash.finalize().as_bytes()
}

pub fn hiding_verifier_config_fingerprint() -> [u8; 32] {
    hiding_verifier_config_fingerprint_for_air(air_fingerprint())
}

fn proving_system_canonical_bytes() -> Vec<u8> {
    let mut bytes = vec![0];
    bytes.extend_from_slice(&(PLONKY3_REV.len() as u64).to_le_bytes());
    bytes.extend_from_slice(PLONKY3_REV.as_bytes());
    bytes
}

fn canonical_vk_hash_for_descriptor(descriptor: &EffectVmDescriptor2) -> Result<[u8; 32], String> {
    let descriptor_bytes = canonical_descriptor_bytes_for(descriptor)?;
    let air = air_fingerprint_for_descriptor(descriptor)?;
    let source = hiding_verifier_config_fingerprint_for_air(air);
    let mut verifier = blake3::Hasher::new_derive_key("dregg-verifier-fingerprint-v1");
    verifier.update(&[0]);
    verifier.update(&source);
    let verifier = *verifier.finalize().as_bytes();
    let proving_system = proving_system_canonical_bytes();

    let mut hash = blake3::Hasher::new_derive_key("dregg-vk-v2");
    hash.update(&(descriptor_bytes.len() as u64).to_le_bytes());
    hash.update(&descriptor_bytes);
    hash.update(&air);
    hash.update(&verifier);
    hash.update(&(proving_system.len() as u64).to_le_bytes());
    hash.update(&proving_system);
    Ok(*hash.finalize().as_bytes())
}

pub fn canonical_vk_hash() -> [u8; 32] {
    canonical_vk_hash_for_descriptor(
        &descriptor()
            .expect("checked-in whole-note swap substrate descriptor must parse and stay pinned"),
    )
    .expect("checked-in whole-note swap substrate descriptor must have a canonical typed encoding")
}

fn felt_u16(value: u16) -> BabyBear {
    BabyBear::new(u32::from(value))
}

fn u64_limbs(value: u64) -> [u16; 4] {
    core::array::from_fn(|lane| ((value >> (16 * lane)) & 0xffff) as u16)
}

fn put_u16s(row: &mut [BabyBear], base: usize, values: &[u16]) {
    for (lane, value) in values.iter().copied().enumerate() {
        row[base + lane] = felt_u16(value);
    }
}

fn put_u32s(row: &mut [BabyBear], base: usize, values: &[u32]) -> Result<(), String> {
    for (lane, value) in values.iter().copied().enumerate() {
        if value >= BABYBEAR_P {
            return Err(format!(
                "noncanonical BabyBear lane {lane}={value} at column {base}"
            ));
        }
        row[base + lane] = BabyBear::new(value);
    }
    Ok(())
}

fn put_digest(row: &mut [BabyBear], base: usize, value: [BabyBear; ROOT_LANES]) {
    row[base..base + ROOT_LANES].copy_from_slice(&value);
}

fn tagged_preimage(out: &mut Vec<BabyBear>, key: TaggedKeyWire) {
    out.push(BabyBear::new(u32::from(key.tag)));
    out.extend(key.raw_u16_le.map(felt_u16));
}

/// Fill the exact rate-four full-state schedule used by Lean's `spongePlan` and return its
/// squeeze-permute-squeeze digest.
fn fill_sponge(
    row: &mut [BabyBear],
    state_base: usize,
    inputs: &[BabyBear],
) -> [BabyBear; ROOT_LANES] {
    debug_assert!(!inputs.is_empty());
    let mut state = [BabyBear::ZERO; 16];
    state[4] = BabyBear::new(inputs.len() as u32);
    let chunks = inputs.len().div_ceil(4);
    let mut first_squeeze = [BabyBear::ZERO; 4];
    for (stage, chunk) in inputs.chunks(4).enumerate() {
        for (lane, value) in chunk.iter().copied().enumerate() {
            state[lane] += value;
        }
        state = chip_permute_state16(state);
        row[state_base + 16 * stage..state_base + 16 * (stage + 1)].copy_from_slice(&state);
        if stage + 1 == chunks {
            first_squeeze.copy_from_slice(&state[..4]);
        }
    }
    state = chip_permute_state16(state);
    row[state_base + 16 * chunks..state_base + 16 * (chunks + 1)].copy_from_slice(&state);
    [
        first_squeeze[0],
        first_squeeze[1],
        first_squeeze[2],
        first_squeeze[3],
        state[0],
        state[1],
        state[2],
        state[3],
    ]
}

fn opening_felts(opening: HiddenNoteOpeningV4) -> [BabyBear; OPENING_LANES] {
    opening.limbs().map(felt_u16)
}

fn wide_transcript(selected: &[BabyBear; OPENING_LANES], fork: u32) -> Vec<BabyBear> {
    let mut out = vec![
        BabyBear::new(fork),
        BabyBear::new(0x4452),
        BabyBear::new(0x4547),
        BabyBear::new(0x4757),
        BabyBear::new(0x5051),
        BabyBear::ONE,
        BabyBear::ONE,
        BabyBear::new(12),
    ];
    out.extend_from_slice(&selected[..12]);
    out
}

fn nullifier_transcript(
    selected: &[BabyBear; OPENING_LANES],
    secret: [u16; KEY_LANES],
    fork: u32,
) -> Vec<BabyBear> {
    let mut out = vec![BabyBear::new(fork), BabyBear::new(FNI4)];
    out.extend(secret.map(felt_u16));
    out.extend_from_slice(selected);
    out
}

fn note_transcript(opening: &[BabyBear; OPENING_LANES], fork: u32) -> Vec<BabyBear> {
    let mut out = vec![BabyBear::new(fork), BabyBear::ONE];
    out.extend_from_slice(opening);
    out
}

fn linked_leaf_preimage(
    addr: TaggedKeyWire,
    binding: [BabyBear; WIDE_LANES],
    next: TaggedKeyWire,
) -> Vec<BabyBear> {
    let mut out = Vec::with_capacity(51);
    out.push(BabyBear::new(FNI4));
    tagged_preimage(&mut out, addr);
    out.extend(binding);
    tagged_preimage(&mut out, next);
    out
}

fn state_preimage(root: [BabyBear; ROOT_LANES], count: u64) -> Vec<BabyBear> {
    let mut out = vec![BabyBear::new(FNS4)];
    out.extend(root);
    out.extend(u64_limbs(count).map(felt_u16));
    out
}

fn node_state_base(chain: usize, level: usize) -> usize {
    NODE_STATE_BASE + (chain * TREE_DEPTH + level) * NODE_STATE_STRIDE
}

fn parent(
    row: &mut [BabyBear],
    chain: usize,
    level: usize,
    current: [BabyBear; ROOT_LANES],
    sibling: [BabyBear; ROOT_LANES],
    bit: bool,
) -> [BabyBear; ROOT_LANES] {
    let (left, right) = if bit {
        (sibling, current)
    } else {
        (current, sibling)
    };
    let mut input = vec![BabyBear::new(FNN4)];
    input.extend(left);
    input.extend(right);
    fill_sponge(row, node_state_base(chain, level), &input)
}

fn strict_lex_aux(left: [u16; KEY_LANES], right: [u16; KEY_LANES]) -> Result<[u16; 17], String> {
    let first = left
        .iter()
        .zip(right.iter())
        .position(|(left, right)| left != right)
        .ok_or_else(|| "exact predecessor bracket has equal endpoints".to_string())?;
    if left[first] >= right[first] {
        return Err("exact predecessor bracket is not strictly increasing".to_string());
    }
    let mut aux = [0u16; 17];
    aux[first] = 1;
    aux[16] = right[first] - left[first] - 1;
    Ok(aux)
}

fn bracket_aux(
    left: TaggedKeyWire,
    right: [u16; KEY_LANES],
    lower: bool,
) -> Result<[u16; 17], String> {
    match (lower, left.tag) {
        (true, 0) | (false, 2) if left.raw_u16_le == [0; KEY_LANES] => {
            let mut aux = [0u16; 17];
            aux[0] = 1;
            Ok(aux)
        }
        (true, 1) => strict_lex_aux(left.raw_u16_le, right),
        (false, 1) => strict_lex_aux(right, left.raw_u16_le),
        _ => Err("noncanonical exact predecessor/successor tag".to_string()),
    }
}

fn output_openings(witness: &ShieldedWholeNoteSwapSubstrateWitness) -> [HiddenNoteOpeningV4; 2] {
    [
        HiddenNoteOpeningV4 {
            value: witness.counterparty.value,
            asset: witness.counterparty.asset,
            randomness: witness.output_randomness[0],
            owner: witness.selected.owner,
            nonce: witness.output_nonce[0],
        },
        HiddenNoteOpeningV4 {
            value: witness.selected.value,
            asset: witness.selected.asset,
            randomness: witness.output_randomness[1],
            owner: witness.counterparty.owner,
            nonce: witness.output_nonce[1],
        },
    ]
}

fn canonical_root(name: &str, root: [u32; ROOT_LANES]) -> Result<[BabyBear; ROOT_LANES], String> {
    for (lane, value) in root.iter().copied().enumerate() {
        if value >= BABYBEAR_P {
            return Err(format!(
                "{name} lane {lane}={value} is noncanonical for BabyBear"
            ));
        }
    }
    Ok(root.map(BabyBear::new))
}

fn build_row(
    witness: &ShieldedWholeNoteSwapSubstrateWitness,
) -> Result<(Vec<BabyBear>, ShieldedWholeNoteSwapSubstratePublic), String> {
    if witness.pre_count > u64::from(u32::MAX) {
        return Err("v4 exact accumulator is full".to_string());
    }
    if witness.append_path.position != witness.pre_count as u32 {
        return Err("append path position is not the exact pre-count cursor".to_string());
    }
    if witness.predecessor_path.position == witness.append_path.position {
        return Err("predecessor and append paths target the same leaf".to_string());
    }
    let post_count = witness
        .pre_count
        .checked_add(1)
        .ok_or_else(|| "v4 count overflow".to_string())?;

    canonical_root("historical note root", witness.historical_note_root)?;
    canonical_root("before outer commit", witness.before_outer_commit)?;
    canonical_root("after outer commit", witness.after_outer_commit)?;
    let predecessor_binding = canonical_root16("predecessor binding", witness.predecessor_binding)?;
    let predecessor_addr = witness
        .predecessor_addr
        .decode()
        .map_err(|error| format!("invalid predecessor address: {error}"))?;
    let predecessor_next = witness
        .predecessor_next
        .decode()
        .map_err(|error| format!("invalid predecessor successor: {error}"))?;
    if matches!(
        predecessor_addr,
        dregg_circuit::exact_nullifier_aafi::ExactTaggedKey::Top
    ) || matches!(
        predecessor_next,
        dregg_circuit::exact_nullifier_aafi::ExactTaggedKey::Bot
    ) {
        return Err("invalid predecessor endpoint ordering".to_string());
    }

    let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
    let selected = opening_felts(witness.selected);
    let counterparty = opening_felts(witness.counterparty);
    let outputs = output_openings(witness).map(opening_felts);
    row[SELECTED_BASE..SELECTED_BASE + OPENING_LANES].copy_from_slice(&selected);
    row[COUNTER_BASE..COUNTER_BASE + OPENING_LANES].copy_from_slice(&counterparty);
    row[OUTPUT0_BASE..OUTPUT0_BASE + OPENING_LANES].copy_from_slice(&outputs[0]);
    row[OUTPUT1_BASE..OUTPUT1_BASE + OPENING_LANES].copy_from_slice(&outputs[1]);
    put_u16s(&mut row, SECRET_BASE, &witness.selected_secret);

    let nullifier0 = fill_sponge(
        &mut row,
        NULLIFIER0_STATE,
        &nullifier_transcript(&selected, witness.selected_secret, NULLIFIER_FORK0),
    );
    let nullifier1 = fill_sponge(
        &mut row,
        NULLIFIER1_STATE,
        &nullifier_transcript(&selected, witness.selected_secret, NULLIFIER_FORK1),
    );
    let nullifier_hash: [BabyBear; KEY_LANES] = core::array::from_fn(|lane| {
        if lane < 8 {
            nullifier0[lane]
        } else {
            nullifier1[lane - 8]
        }
    });
    let nullifier: [u16; KEY_LANES] = nullifier_hash.map(|felt| (felt.as_u32() & 0xffff) as u16);
    let nullifier_high: [u16; KEY_LANES] = nullifier_hash.map(|felt| (felt.as_u32() >> 16) as u16);
    let nullifier_slack = nullifier_high.map(|high| FIELD_HI_CANON_MAX - high);
    put_u16s(&mut row, NULLIFIER_BASE, &nullifier);
    put_u16s(&mut row, NULLIFIER_HIGH_BASE, &nullifier_high);
    put_u16s(&mut row, NULLIFIER_SLACK_BASE, &nullifier_slack);
    for lane in 0..KEY_LANES {
        let slack = BabyBear::new(u32::from(nullifier_slack[lane]));
        if nullifier_slack[lane] == 0 {
            row[NULLIFIER_ZERO_BASE + lane] = BabyBear::ONE;
            row[NULLIFIER_INV_BASE + lane] = BabyBear::ZERO;
        } else {
            row[NULLIFIER_ZERO_BASE + lane] = BabyBear::ZERO;
            row[NULLIFIER_INV_BASE + lane] = slack
                .inverse()
                .expect("nonzero canonical packing slack has an inverse");
        }
    }

    let wide0 = fill_sponge(&mut row, WIDE0_STATE, &wide_transcript(&selected, 0));
    let wide1 = fill_sponge(&mut row, WIDE1_STATE, &wide_transcript(&selected, 1));
    let binding: [BabyBear; WIDE_LANES] = core::array::from_fn(|lane| {
        if lane < 8 {
            wide0[lane]
        } else {
            wide1[lane - 8]
        }
    });
    row[BINDING_BASE..BINDING_BASE + WIDE_LANES].copy_from_slice(&binding);

    row[LOW_ADDR_TAG] = BabyBear::new(u32::from(witness.predecessor_addr.tag));
    put_u16s(
        &mut row,
        LOW_ADDR_BASE,
        &witness.predecessor_addr.raw_u16_le,
    );
    row[LOW_BINDING_BASE..LOW_BINDING_BASE + WIDE_LANES].copy_from_slice(&predecessor_binding);
    row[LOW_NEXT_TAG] = BabyBear::new(u32::from(witness.predecessor_next.tag));
    put_u16s(
        &mut row,
        LOW_NEXT_BASE,
        &witness.predecessor_next.raw_u16_le,
    );
    put_u16s(
        &mut row,
        LEX_LOW_AUX_BASE,
        &bracket_aux(witness.predecessor_addr, nullifier, true)?,
    );
    put_u16s(
        &mut row,
        LEX_NEXT_AUX_BASE,
        &bracket_aux(witness.predecessor_next, nullifier, false)?,
    );

    for level in 0..TREE_DEPTH {
        row[LOW_POS_BITS + level] = BabyBear::new((witness.predecessor_path.position >> level) & 1);
        row[APP_POS_BITS + level] = BabyBear::new((witness.append_path.position >> level) & 1);
        put_u32s(
            &mut row,
            LOW_SIB_BASE + level * ROOT_LANES,
            &witness.predecessor_path.siblings[level],
        )?;
        put_u32s(
            &mut row,
            APP_SIB_BASE + level * ROOT_LANES,
            &witness.append_path.siblings[level],
        )?;
    }
    put_u16s(&mut row, PRE_COUNT_BASE, &u64_limbs(witness.pre_count));
    put_u16s(&mut row, POST_COUNT_BASE, &u64_limbs(post_count));
    put_u16s(
        &mut row,
        HISTORICAL_HEIGHT_BASE,
        &u64_limbs(witness.historical_height),
    );
    put_u32s(
        &mut row,
        HISTORICAL_ROOT_BASE,
        &witness.historical_note_root,
    )?;
    put_u32s(&mut row, BEFORE_OUTER_BASE, &witness.before_outer_commit)?;
    put_u32s(&mut row, AFTER_OUTER_BASE, &witness.after_outer_commit)?;
    let pre = witness.pre_count;
    row[COUNT_CARRY_BASE] = BabyBear::new(u32::from((pre & 0xffff) == 0xffff));
    row[COUNT_CARRY_BASE + 1] = BabyBear::new(u32::from((pre & 0xffff_ffff) == 0xffff_ffff));
    row[COUNT_CARRY_BASE + 2] =
        BabyBear::new(u32::from((pre & 0xffff_ffff_ffff) == 0xffff_ffff_ffff));

    let old_leaf = fill_sponge(
        &mut row,
        LOW_OLD_LEAF_STATE,
        &linked_leaf_preimage(
            witness.predecessor_addr,
            predecessor_binding,
            witness.predecessor_next,
        ),
    );
    let low_new_leaf = fill_sponge(
        &mut row,
        LOW_NEW_LEAF_STATE,
        &linked_leaf_preimage(
            witness.predecessor_addr,
            predecessor_binding,
            TaggedKeyWire {
                tag: 1,
                raw_u16_le: nullifier,
            },
        ),
    );
    let appended_leaf = fill_sponge(
        &mut row,
        APPENDED_LEAF_STATE,
        &linked_leaf_preimage(
            TaggedKeyWire {
                tag: 1,
                raw_u16_le: nullifier,
            },
            binding,
            witness.predecessor_next,
        ),
    );
    let empty_leaf = hash_many_8(&[BabyBear::new(FNE4)]);

    let output0_commit0 = fill_sponge(
        &mut row,
        OUTPUT0_NOTE0_STATE,
        &note_transcript(&outputs[0], NOTE_FORK0),
    );
    let output0_commit1 = fill_sponge(
        &mut row,
        OUTPUT0_NOTE1_STATE,
        &note_transcript(&outputs[0], NOTE_FORK1),
    );
    let output1_commit0 = fill_sponge(
        &mut row,
        OUTPUT1_NOTE0_STATE,
        &note_transcript(&outputs[1], NOTE_FORK0),
    );
    let output1_commit1 = fill_sponge(
        &mut row,
        OUTPUT1_NOTE1_STATE,
        &note_transcript(&outputs[1], NOTE_FORK1),
    );
    let mut output0_commit = [BabyBear::ZERO; WIDE_LANES];
    let mut output1_commit = [BabyBear::ZERO; WIDE_LANES];
    output0_commit[..8].copy_from_slice(&output0_commit0);
    output0_commit[8..].copy_from_slice(&output0_commit1);
    output1_commit[..8].copy_from_slice(&output1_commit0);
    output1_commit[8..].copy_from_slice(&output1_commit1);
    row[OUTPUT0_COMMIT_BASE..OUTPUT0_COMMIT_BASE + WIDE_LANES].copy_from_slice(&output0_commit);
    row[OUTPUT1_COMMIT_BASE..OUTPUT1_COMMIT_BASE + WIDE_LANES].copy_from_slice(&output1_commit);
    let mut output_root_preimage = vec![BabyBear::new(FXO4)];
    output_root_preimage.extend(output0_commit);
    output_root_preimage.extend(output1_commit);
    let output_root = fill_sponge(&mut row, OUTPUT_ROOT_STATE, &output_root_preimage);
    put_digest(&mut row, OUTPUT_ROOT_BASE, output_root);

    let mut roots = [old_leaf, low_new_leaf, empty_leaf, appended_leaf];
    for level in 0..TREE_DEPTH {
        for (chain, root) in roots.iter_mut().enumerate() {
            let path = if chain < 2 {
                &witness.predecessor_path
            } else {
                &witness.append_path
            };
            let sibling = canonical_root("exact path sibling", path.siblings[level])?;
            *root = parent(
                &mut row,
                chain,
                level,
                *root,
                sibling,
                ((path.position >> level) & 1) == 1,
            );
        }
    }
    if roots[1] != roots[2] {
        return Err("predecessor rewrite root does not match append-path pre-root".to_string());
    }
    let prior_root = roots[0];
    let successor_root = roots[3];
    put_digest(&mut row, PRIOR_ROOT_BASE, prior_root);
    put_digest(&mut row, SUCCESSOR_ROOT_BASE, successor_root);

    let pre_state = fill_sponge(
        &mut row,
        PRE_STATE_COMMIT_STATE,
        &state_preimage(prior_root, witness.pre_count),
    );
    let post_state = fill_sponge(
        &mut row,
        POST_STATE_COMMIT_STATE,
        &state_preimage(successor_root, post_count),
    );
    put_digest(&mut row, PRE_STATE_COPY, pre_state);
    put_digest(&mut row, POST_STATE_COPY, post_state);

    let mut consequence_preimage = vec![
        BabyBear::new(WHOLE_NOTE_SWAP_CONSEQUENCE_DOMAIN),
        BabyBear::ONE,
        BabyBear::ZERO,
        BabyBear::new(2),
    ];
    consequence_preimage.extend(nullifier.map(felt_u16));
    consequence_preimage.extend(binding);
    consequence_preimage.extend(pre_state);
    consequence_preimage.extend(post_state);
    consequence_preimage.extend(output_root);
    consequence_preimage.extend(u64_limbs(witness.historical_height).map(felt_u16));
    consequence_preimage.extend(witness.historical_note_root.map(BabyBear::new));
    consequence_preimage.extend(witness.before_outer_commit.map(BabyBear::new));
    consequence_preimage.extend(witness.after_outer_commit.map(BabyBear::new));
    let consequence = fill_sponge(&mut row, CONSEQUENCE_REAL_STATE, &consequence_preimage);
    put_digest(&mut row, CONSEQUENCE_BASE, consequence);

    let mut public_lanes = [0u32; PUBLIC_INPUT_COUNT];
    copy_public(
        &row,
        HISTORICAL_HEIGHT_BASE,
        &mut public_lanes,
        PI_HEIGHT,
        4,
    );
    copy_public(
        &row,
        HISTORICAL_ROOT_BASE,
        &mut public_lanes,
        PI_HISTORICAL_ROOT,
        8,
    );
    copy_public(&row, NULLIFIER_BASE, &mut public_lanes, PI_NULLIFIER, 16);
    copy_public(&row, BINDING_BASE, &mut public_lanes, PI_BINDING, 16);
    copy_public(
        &row,
        SUCCESSOR_ROOT_BASE,
        &mut public_lanes,
        PI_SUCCESSOR_ROOT,
        8,
    );
    copy_public(&row, PRIOR_ROOT_BASE, &mut public_lanes, PI_PRIOR_ROOT, 8);
    copy_public(&row, PRE_COUNT_BASE, &mut public_lanes, PI_PRE_COUNT, 4);
    copy_public(&row, POST_COUNT_BASE, &mut public_lanes, PI_POST_COUNT, 4);
    copy_public(&row, CONSEQUENCE_BASE, &mut public_lanes, PI_CONSEQUENCE, 8);
    copy_public(&row, OUTPUT_ROOT_BASE, &mut public_lanes, PI_OUTPUT_ROOT, 8);
    copy_public(
        &row,
        BEFORE_OUTER_BASE,
        &mut public_lanes,
        PI_BEFORE_OUTER,
        8,
    );
    copy_public(&row, AFTER_OUTER_BASE, &mut public_lanes, PI_AFTER_OUTER, 8);
    let public = ShieldedWholeNoteSwapSubstratePublic::try_from_u32s(&public_lanes)
        .map_err(|error| format!("derived whole-note swap public statement refused: {error}"))?;
    Ok((row, public))
}

fn canonical_root16(name: &str, root: [u32; WIDE_LANES]) -> Result<[BabyBear; WIDE_LANES], String> {
    for (lane, value) in root.iter().copied().enumerate() {
        if value >= BABYBEAR_P {
            return Err(format!(
                "{name} lane {lane}={value} is noncanonical for BabyBear"
            ));
        }
    }
    Ok(root.map(BabyBear::new))
}

fn copy_public(
    row: &[BabyBear],
    row_base: usize,
    public: &mut [u32; PUBLIC_INPUT_COUNT],
    public_base: usize,
    width: usize,
) {
    for lane in 0..width {
        public[public_base + lane] = row[row_base + lane].as_u32();
    }
}

/// Derive the exact trace and public statement without proving.
pub fn trace_and_public(
    witness: &ShieldedWholeNoteSwapSubstrateWitness,
) -> Result<
    (
        EffectVmDescriptor2,
        Vec<Vec<BabyBear>>,
        ShieldedWholeNoteSwapSubstratePublic,
    ),
    String,
> {
    let (row, public) = build_row(witness)?;
    let trace = vec![row.clone(), row];
    Ok((descriptor()?, trace, public))
}

/// Produce a fresh-randomness HidingFRI proof.  No non-hiding producer is exported.
pub fn prove_substrate_zk(
    witness: &ShieldedWholeNoteSwapSubstrateWitness,
) -> Result<
    (
        ShieldedWholeNoteSwapSubstrateZkProof,
        ShieldedWholeNoteSwapSubstratePublic,
    ),
    String,
> {
    let (descriptor, trace, public) = trace_and_public(witness)?;
    let public_felts = public.as_u32_array().map(BabyBear::new);
    let proof = prove_vm_descriptor2_for_config(
        &descriptor,
        &trace,
        &public_felts,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &create_zk_config(),
    )?;
    validate_hiding_proof_shape(&proof)?;
    Ok((ShieldedWholeNoteSwapSubstrateZkProof { proof }, public))
}

pub fn verify_substrate_zk(
    proof: &ShieldedWholeNoteSwapSubstrateZkProof,
    public: ShieldedWholeNoteSwapSubstratePublic,
) -> Result<(), String> {
    validate_hiding_proof_shape(&proof.proof)?;
    let public_felts = public.as_u32_array().map(BabyBear::new);
    verify_vm_descriptor2_with_config(
        &descriptor()?,
        &proof.proof,
        &public_felts,
        &create_zk_config(),
    )
}

pub fn verify_substrate_postcard(proof_bytes: &[u8], public_values: &[u32]) -> Result<(), String> {
    let proof = ShieldedWholeNoteSwapSubstrateZkProof::from_postcard(proof_bytes)?;
    let public = ShieldedWholeNoteSwapSubstratePublic::try_from_u32s(public_values)
        .map_err(|error| format!("whole-note swap substrate public decode failed: {error}"))?;
    verify_substrate_zk(&proof, public)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::exact_nullifier_aafi::ExactTaggedKey;

    const DESCRIPTOR_HEADER: &str = concat!(
        "{\"name\":\"shielded-whole-note-swap-substrate-v1::one-opening-aafi32-v1\",",
        "\"ir\":2,\"trace_width\":15611,\"public_input_count\":100,"
    );

    fn whitespace_and_top_level_key_reordered_json() -> String {
        let body = DESCRIPTOR_JSON
            .strip_prefix(DESCRIPTOR_HEADER)
            .expect("whole-note swap substrate descriptor header remains recognized");
        format!(
            "{{\n  \"public_input_count\" : 100,\n  \"trace_width\" : 15611,\n  \
             \"name\" : \"{PREDICATE_NAME}\",\n  \"ir\" : 2,\n  {body}\n"
        )
    }

    fn empty_subtree_roots() -> [[u32; ROOT_LANES]; TREE_DEPTH] {
        let mut siblings = [[0u32; ROOT_LANES]; TREE_DEPTH];
        let mut current = hash_many_8(&[BabyBear::new(FNE4)]);
        for sibling in &mut siblings {
            *sibling = current.map(BabyBear::as_u32);
            let mut input = vec![BabyBear::new(FNN4)];
            input.extend(current);
            input.extend(current);
            current = hash_many_8(&input);
        }
        siblings
    }

    fn fixture() -> ShieldedWholeNoteSwapSubstrateWitness {
        let selected = HiddenNoteOpeningV4 {
            value: 0x1234_5678_9abc_def0,
            asset: 0x1020_3040_5060_7080,
            randomness: 41,
            owner: 51,
            nonce: 61,
        };
        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
        let selected_felts = opening_felts(selected);
        let binding0 = fill_sponge(&mut row, WIDE0_STATE, &wide_transcript(&selected_felts, 0));
        let binding1 = fill_sponge(&mut row, WIDE1_STATE, &wide_transcript(&selected_felts, 1));
        let binding: [BabyBear; WIDE_LANES] = core::array::from_fn(|lane| {
            if lane < 8 {
                binding0[lane]
            } else {
                binding1[lane - 8]
            }
        });
        let old_leaf = hash_many_8(&linked_leaf_preimage(
            ExactTaggedKey::Bot.wire(),
            [BabyBear::ZERO; WIDE_LANES],
            ExactTaggedKey::Top.wire(),
        ));
        let nullifier0 = fill_sponge(
            &mut row,
            NULLIFIER0_STATE,
            &nullifier_transcript(&selected_felts, [7; KEY_LANES], NULLIFIER_FORK0),
        );
        let nullifier1 = fill_sponge(
            &mut row,
            NULLIFIER1_STATE,
            &nullifier_transcript(&selected_felts, [7; KEY_LANES], NULLIFIER_FORK1),
        );
        let nullifier_hash: [BabyBear; KEY_LANES] = core::array::from_fn(|lane| {
            if lane < 8 {
                nullifier0[lane]
            } else {
                nullifier1[lane - 8]
            }
        });
        let nullifier = nullifier_hash.map(|felt| (felt.as_u32() & 0xffff) as u16);
        let low_new = hash_many_8(&linked_leaf_preimage(
            ExactTaggedKey::Bot.wire(),
            [BabyBear::ZERO; WIDE_LANES],
            TaggedKeyWire {
                tag: 1,
                raw_u16_le: nullifier,
            },
        ));
        let defaults = empty_subtree_roots();
        let mut predecessor_siblings = defaults;
        predecessor_siblings[0] = hash_many_8(&[BabyBear::new(FNE4)]).map(BabyBear::as_u32);
        let mut append_siblings = defaults;
        append_siblings[0] = low_new.map(BabyBear::as_u32);
        let _ = (binding, old_leaf);
        ShieldedWholeNoteSwapSubstrateWitness {
            selected,
            counterparty: HiddenNoteOpeningV4 {
                value: 73,
                asset: 83,
                randomness: 93,
                owner: 103,
                nonce: 113,
            },
            selected_secret: [7; KEY_LANES],
            output_randomness: [127, 131],
            output_nonce: [137, 139],
            predecessor_addr: ExactTaggedKey::Bot.wire(),
            predecessor_binding: [0; WIDE_LANES],
            predecessor_next: ExactTaggedKey::Top.wire(),
            predecessor_path: BinaryExactPathV4 {
                position: 0,
                siblings: predecessor_siblings,
            },
            append_path: BinaryExactPathV4 {
                position: 1,
                siblings: append_siblings,
            },
            pre_count: 1,
            historical_height: 17,
            historical_note_root: core::array::from_fn(|lane| 200 + lane as u32),
            before_outer_commit: core::array::from_fn(|lane| 300 + lane as u32),
            after_outer_commit: core::array::from_fn(|lane| 400 + lane as u32),
        }
    }

    fn wide_binding(opening: HiddenNoteOpeningV4) -> [u32; WIDE_LANES] {
        let opening = opening_felts(opening);
        let left = hash_many_8(&wide_transcript(&opening, 0));
        let right = hash_many_8(&wide_transcript(&opening, 1));
        core::array::from_fn(|lane| {
            if lane < 8 {
                left[lane].as_u32()
            } else {
                right[lane - 8].as_u32()
            }
        })
    }

    #[test]
    fn descriptor_and_one_opening_trace_are_exact() {
        let descriptor = descriptor().expect("Lean descriptor parses and is pinned");
        assert_eq!(descriptor.trace_width, TRACE_WIDTH);
        assert_eq!(descriptor.public_input_count, PUBLIC_INPUT_COUNT);
        assert_ne!(air_fingerprint(), hiding_verifier_config_fingerprint());
        let (_, trace, public) = trace_and_public(&fixture()).expect("honest one-opening trace");
        assert_eq!(trace.len(), TRACE_HEIGHT);
        assert_eq!(trace[0].len(), TRACE_WIDTH);
        assert_eq!(trace[0], trace[1]);
        assert_eq!(public.as_u32_array().len(), PUBLIC_INPUT_COUNT);

        // A public u16 nullifier lane and its hidden high limb must be the unique canonical
        // packing of the sponge result.  In particular, the field value cannot be represented
        // again as `hash + BABYBEAR_P` by choosing a different low/high pair.
        for lane in 0..KEY_LANES {
            let low = trace[0][NULLIFIER_BASE + lane].as_u32();
            let high = trace[0][NULLIFIER_HIGH_BASE + lane].as_u32();
            let slack = trace[0][NULLIFIER_SLACK_BASE + lane].as_u32();
            let zero = trace[0][NULLIFIER_ZERO_BASE + lane].as_u32();
            assert_eq!(high + slack, u32::from(FIELD_HI_CANON_MAX));
            assert!(low + (high << 16) < BABYBEAR_P);
            assert_eq!(zero, u32::from(slack == 0));
            if zero == 1 {
                assert_eq!(low, 0);
            }
        }
    }

    #[test]
    fn json_format_is_not_identity_but_typed_descriptor_semantics_are() {
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
    }

    #[test]
    fn value_asset_mod_p_aliases_and_detached_roots_change_statement_or_refuse() {
        let base = fixture();
        let (_, _, base_public) = trace_and_public(&base).unwrap();

        let mut value_alias = base.clone();
        value_alias.selected.value += u64::from(BABYBEAR_P);
        assert_ne!(
            wide_binding(base.selected),
            wide_binding(value_alias.selected)
        );
        assert!(match trace_and_public(&value_alias) {
            Ok((_, _, public)) => public != base_public,
            Err(_) => true,
        });

        let mut asset_alias = base.clone();
        asset_alias.selected.asset += u64::from(BABYBEAR_P);
        assert_ne!(
            wide_binding(base.selected),
            wide_binding(asset_alias.selected)
        );
        assert!(match trace_and_public(&asset_alias) {
            Ok((_, _, public)) => public != base_public,
            Err(_) => true,
        });

        let mut detached = base.clone();
        detached.selected.nonce ^= 1;
        assert!(match trace_and_public(&detached) {
            Ok((_, _, public)) => public != base_public,
            Err(_) => true,
        });

        let mut bad_successor_path = base.clone();
        bad_successor_path.append_path.siblings[0][0] ^= 1;
        assert!(trace_and_public(&bad_successor_path).is_err());
    }

    #[test]
    fn security_seams_are_explicit_and_counterparty_is_not_yet_authenticated() {
        assert!(PROOF_SUBSTRATE_ONLY.contains("input membership"));
        assert!(PROOF_SUBSTRATE_ONLY.contains("spend authority"));
        assert!(PROOF_SUBSTRATE_ONLY.contains("counterparty provenance"));
        assert!(PROOF_SUBSTRATE_ONLY.contains("outer transition"));

        let base = fixture();
        let (_, _, base_public) = trace_and_public(&base).unwrap();
        let mut manufactured_counterparty = base.clone();
        manufactured_counterparty.counterparty.value = u64::MAX;
        manufactured_counterparty.counterparty.asset ^= 0x55aa;
        let (_, _, changed_public) = trace_and_public(&manufactured_counterparty)
            .expect("v1 intentionally lacks the surrounding counterparty provenance weld");
        assert_ne!(
            base_public.output_notes_root(),
            changed_public.output_notes_root()
        );
    }

    #[test]
    fn output_root_and_exact_successor_are_not_host_inputs() {
        let (_, trace, public) = trace_and_public(&fixture()).unwrap();
        assert_eq!(
            &public.as_u32_array()[PI_OUTPUT_ROOT..PI_OUTPUT_ROOT + 8],
            &trace[0][OUTPUT_ROOT_BASE..OUTPUT_ROOT_BASE + 8]
                .iter()
                .map(|felt| felt.as_u32())
                .collect::<Vec<_>>()
        );
        assert_eq!(
            &public.as_u32_array()[PI_SUCCESSOR_ROOT..PI_SUCCESSOR_ROOT + 8],
            &trace[0][SUCCESSOR_ROOT_BASE..SUCCESSOR_ROOT_BASE + 8]
                .iter()
                .map(|felt| felt.as_u32())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn shielded_whole_note_swap_substrate_hiding_proof_and_hostile_publics() {
        let (mut proof, public) =
            prove_substrate_zk(&fixture()).expect("honest HidingFRI proof substrate");
        verify_substrate_zk(&proof, public).expect("honest proof verifies");
        assert!(proof.proof.commitments.random.is_some());

        let encoded = proof.to_postcard().expect("canonical proof encoding");
        let decoded = ShieldedWholeNoteSwapSubstrateZkProof::from_postcard(&encoded)
            .expect("canonical complete HidingFRI proof decodes");
        verify_substrate_zk(&decoded, public).expect("transported proof verifies");
        let mut trailing = encoded.clone();
        trailing.push(0);
        assert!(ShieldedWholeNoteSwapSubstrateZkProof::from_postcard(&trailing).is_err());
        assert!(
            ShieldedWholeNoteSwapSubstrateZkProof::from_postcard(&vec![0; MAX_PROOF_BYTES + 1])
                .is_err()
        );

        let random_commitment = proof.proof.commitments.random.take();
        let stripped_commitment = proof.to_postcard().expect("encode stripped commitment");
        assert!(
            ShieldedWholeNoteSwapSubstrateZkProof::from_postcard(&stripped_commitment).is_err()
        );
        proof.proof.commitments.random = random_commitment;
        let random_opening = proof.proof.opened_values.instances[0]
            .base_opened_values
            .random
            .take();
        let stripped_opening = proof.to_postcard().expect("encode stripped opening");
        assert!(ShieldedWholeNoteSwapSubstrateZkProof::from_postcard(&stripped_opening).is_err());
        proof.proof.opened_values.instances[0]
            .base_opened_values
            .random = random_opening;

        for lane in [PI_NULLIFIER, PI_BINDING, PI_SUCCESSOR_ROOT, PI_OUTPUT_ROOT] {
            let mut hostile = *public.as_u32_array();
            hostile[lane] = (hostile[lane] + 1) % BABYBEAR_P;
            if lane == PI_NULLIFIER && hostile[lane] > u16::MAX as u32 {
                hostile[lane] = 0;
            }
            let hostile = ShieldedWholeNoteSwapSubstratePublic::try_from_u32s(&hostile).unwrap();
            assert!(
                verify_substrate_zk(&proof, hostile).is_err(),
                "hostile PI lane {lane}"
            );
        }
    }
}
