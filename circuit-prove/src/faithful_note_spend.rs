//! Predicate-specific HidingFRI prover for the faithful hidden-note spend.
//!
//! The AIR is Lean-authored (`FaithfulNoteSpendDescriptorPlan`) and emitted as
//! `faithful-note-spend-v2.json`.  This module only fills that fixed ABI and
//! deliberately exposes no non-hiding or predicate-less verification entry.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, TableSem, UMemBoundaryWitness,
    VmConstraint2, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
use dregg_circuit::poseidon2::{Poseidon2State, hash_many_8};
use dregg_circuit::stark_zk::{DreggZkStarkConfig, create_zk_config};
use dregg_commit::poseidon2_tree::{
    Poseidon2NoteProof16, commitment_to_lanes16, note_leaf16, note_node8,
};

pub const PREDICATE_NAME: &str = "faithful-note-spend-v2::exact-note16-root8-hiding";
pub const DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/faithful-note-spend-v2.json");

pub const TREE_DEPTH: usize = 16;
pub const TRACE_WIDTH: usize = 1023;
pub const PUBLIC_INPUT_COUNT: usize = 44;
const EXPECTED_CONSTRAINT_COUNT: usize = 393;
const EXPECTED_STATE16_LOOKUPS: usize = 50;
const EXPECTED_PROOF_INSTANCES: usize = 3; // main, state16 chip, nibble table
const EXPECTED_HIDING_MAIN_DEGREE_BITS: usize = 5; // log2(16 rows) + HidingFRI doubling

const DIGEST_LANES: usize = 8;
const STATE_LANES: usize = 16;
const BYTES32_U16_LIMBS: usize = 16;
const U64_U16_LIMBS: usize = 4;

const NOTE_COMMITMENT_V2_DOMAIN: u32 = 0x464e_4332; // FNC2
const NOTE_NULLIFIER_V2_DOMAIN: u32 = 0x464e_4632; // FNF2
const NOTE_OWNER_V2_DOMAIN: u32 = 0x464e_4f32; // FNO2
const NOTE_LEAF_DOMAIN: u32 = 0x4e4c_4638; // NLF8
const NOTE_NODE_DOMAIN: u32 = 0x4e4e_4438; // NND8
const FIELD_HI_CANON_MAX: u32 = 0x7800;

// Lean `FaithfulNoteSpendDescriptorPlan` row geometry.
const CUR_BASE: usize = 0;
const SIB0_BASE: usize = 8;
const SIB1_BASE: usize = 16;
const SIB2_BASE: usize = 24;
const POS_B0: usize = 32;
const POS_B1: usize = 33;
const OWNER_BASE: usize = 34;
const VALUE_BASE: usize = 50;
const ASSET_BASE: usize = 54;
const NONCE_BASE: usize = 58;
const RANDOMNESS_BASE: usize = 74;
const SPENDING_KEY_BASE: usize = 90;
const OWNER_STATE_BASE: usize = 106;
const OWNER_STATE_STEPS: usize = 6;
const OWNER_SLACK_BASE: usize = 202;
const OWNER_ZERO_BASE: usize = 210;
const OWNER_INV_BASE: usize = 218;
const COMMITMENT_STATE_BASE: usize = 226;
const COMMITMENT_STATE_STEPS: usize = 16;
const COMMITMENT_RAW_BASE: usize = 482;
const COMMITMENT_SLACK_BASE: usize = 498;
const COMMITMENT_ZERO_BASE: usize = 506;
const COMMITMENT_INV_BASE: usize = 514;
const NULLIFIER_STATE_BASE: usize = 522;
const NULLIFIER_STATE_STEPS: usize = 12;
const NULLIFIER_RAW_BASE: usize = 714;
const NULLIFIER_SLACK_BASE: usize = 730;
const NULLIFIER_ZERO_BASE: usize = 738;
const NULLIFIER_INV_BASE: usize = 746;
const LEAF_STATE_BASE: usize = 754;
const LEAF_STATE_STEPS: usize = 6;
const NODE_STATE_BASE: usize = 850;
const NODE_STATE_STEPS: usize = 10;
const HEIGHT_BASE: usize = 1010;
const SUCCESSOR_NULLIFIER_ROOT_BASE: usize = 1014;
const LEVEL_COL: usize = 1022;

/// Hidden opening consumed by the FNC2/FNF2 relation.
///
/// `owner` is the public FNO2 shielded address.  The AIR derives that address
/// from `spending_key`, while FNC2 commits the address and FNF2 reuses the key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaithfulNoteOpening {
    pub owner: [u8; 32],
    pub value: u64,
    pub asset_type: u64,
    pub creation_nonce: [u8; 32],
    pub randomness: [u8; 32],
    pub spending_key: [u8; 32],
}

/// Host-owned roots and checkpoint selected for proving.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FaithfulNoteSpendClaim {
    pub root_height: u64,
    pub historical_note_root: [u32; DIGEST_LANES],
    pub successor_nullifier_root: [u32; DIGEST_LANES],
}

/// Exact 44-felt public statement reconstructed by the predicate verifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FaithfulNoteSpendPublic {
    pub root_height: u64,
    pub historical_note_root: [u32; DIGEST_LANES],
    pub nullifier: [u8; 32],
    pub value: u64,
    pub asset_type: u64,
    pub successor_nullifier_root: [u32; DIGEST_LANES],
}

impl FaithfulNoteSpendPublic {
    pub fn validate(self) -> Result<(), String> {
        validate_root("historical note", self.historical_note_root)?;
        validate_root("successor nullifier", self.successor_nullifier_root)
    }

    pub fn as_u32_array(self) -> [u32; PUBLIC_INPUT_COUNT] {
        let mut out = [0u32; PUBLIC_INPUT_COUNT];
        out[0..4].copy_from_slice(&u64_u16_u32(self.root_height));
        out[4..12].copy_from_slice(&self.historical_note_root);
        out[12..28].copy_from_slice(&bytes32_u16_u32(&self.nullifier));
        out[28..32].copy_from_slice(&u64_u16_u32(self.value));
        out[32..36].copy_from_slice(&u64_u16_u32(self.asset_type));
        out[36..44].copy_from_slice(&self.successor_nullifier_root);
        out
    }

    pub fn as_felts(self) -> [BabyBear; PUBLIC_INPUT_COUNT] {
        self.as_u32_array().map(BabyBear::new)
    }

    pub fn try_from_u32s(values: &[u32]) -> Result<Self, String> {
        if values.len() != PUBLIC_INPUT_COUNT {
            return Err(format!(
                "faithful note spend expects {PUBLIC_INPUT_COUNT} public inputs, got {}",
                values.len()
            ));
        }
        for (index, &value) in values.iter().enumerate() {
            let is_u16 = index < 4 || (12..36).contains(&index);
            if is_u16 && value > u16::MAX as u32 {
                return Err(format!(
                    "public input {index}={value} is not a canonical u16"
                ));
            }
            let is_root = (4..12).contains(&index) || (36..44).contains(&index);
            if is_root && value >= BABYBEAR_P {
                return Err(format!(
                    "public root input {index}={value} is noncanonical for BabyBear"
                ));
            }
        }
        let public = Self {
            root_height: u64_from_u16s(&values[0..4]),
            historical_note_root: values[4..12].try_into().expect("length checked"),
            nullifier: bytes32_from_u16s(&values[12..28]),
            value: u64_from_u16s(&values[28..32]),
            asset_type: u64_from_u16s(&values[32..36]),
            successor_nullifier_root: values[36..44].try_into().expect("length checked"),
        };
        public.validate()?;
        Ok(public)
    }
}

/// Opaque HidingFRI proof.  The inner type is intentionally not exposed, so
/// callers cannot route it through a non-hiding/predicate-less verifier.
pub struct FaithfulNoteSpendZkProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl FaithfulNoteSpendZkProof {
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|error| format!("faithful note spend proof encode failed: {error}"))
    }

    /// Strict decode: consume the entire byte string and reject a proof whose
    /// main instance is not exactly the fixed sixteen-row HidingFRI relation.
    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        let (proof, trailing) =
            postcard::take_from_bytes::<Ir2BatchProof<DreggZkStarkConfig>>(bytes)
                .map_err(|error| format!("faithful note spend proof decode failed: {error}"))?;
        if !trailing.is_empty() {
            return Err(format!(
                "faithful note spend proof has {} trailing bytes",
                trailing.len()
            ));
        }
        validate_proof_shape(&proof)?;
        Ok(Self { proof })
    }
}

pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let descriptor = parse_vm_descriptor2(DESCRIPTOR_JSON)?;
    if descriptor.name != PREDICATE_NAME
        || descriptor.trace_width != TRACE_WIDTH
        || descriptor.public_input_count != PUBLIC_INPUT_COUNT
        || descriptor.tables.len() != 4
        || descriptor.constraints.len() != EXPECTED_CONSTRAINT_COUNT
        || !descriptor.hash_sites.is_empty()
        || !descriptor.ranges.is_empty()
    {
        return Err("faithful note spend Lean-emitted descriptor shape drifted".to_string());
    }
    let tables_match = matches!(
        descriptor.tables.as_slice(),
        [main, state16, range15, range16]
            if main.id == 0 && main.name == "main" && main.arity == TRACE_WIDTH
                && matches!(&main.sem, TableSem::Main)
                && state16.id == 9 && state16.name == "poseidon2_state16_chip"
                && state16.arity == 33 && matches!(&state16.sem, TableSem::Poseidon2Chip)
                && range15.id == 84 && range15.name == "range_w15" && range15.arity == 1
                && matches!(&range15.sem, TableSem::Range { bits: 15 })
                && range16.id == 85 && range16.name == "range_w16" && range16.arity == 1
                && matches!(&range16.sem, TableSem::Range { bits: 16 })
    );
    if !tables_match {
        return Err("faithful note spend descriptor table ABI drifted".to_string());
    }
    let state16_lookups = descriptor
        .constraints
        .iter()
        .filter(|constraint| {
            matches!(constraint, VmConstraint2::Lookup(lookup) if lookup.table == 9 && lookup.tuple.len() == 33)
        })
        .count();
    if state16_lookups != EXPECTED_STATE16_LOOKUPS {
        return Err(format!(
            "faithful note spend descriptor has {state16_lookups} full-state lookups, expected {EXPECTED_STATE16_LOOKUPS}"
        ));
    }
    let mut pins = descriptor
        .constraints
        .iter()
        .filter_map(|constraint| match constraint {
            VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }) => {
                Some((*row, *col, *pi_index))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    pins.sort_by_key(|(_, _, pi)| *pi);
    let mut expected_pins = Vec::with_capacity(PUBLIC_INPUT_COUNT);
    expected_pins.extend((0..4).map(|i| (VmRow::First, HEIGHT_BASE + i, i)));
    for (i, col) in [978, 979, 980, 981, 994, 995, 996, 997]
        .into_iter()
        .enumerate()
    {
        expected_pins.push((VmRow::Last, col, 4 + i));
    }
    expected_pins.extend((0..16).map(|i| (VmRow::First, NULLIFIER_RAW_BASE + i, 12 + i)));
    expected_pins.extend((0..4).map(|i| (VmRow::First, VALUE_BASE + i, 28 + i)));
    expected_pins.extend((0..4).map(|i| (VmRow::First, ASSET_BASE + i, 32 + i)));
    expected_pins.extend((0..8).map(|i| (VmRow::First, SUCCESSOR_NULLIFIER_ROOT_BASE + i, 36 + i)));
    if pins != expected_pins {
        return Err("faithful note spend descriptor public-pin ABI drifted".to_string());
    }
    Ok(descriptor)
}

/// Prove an exact depth-16 membership path and the FNC2/FNF2 derivations under
/// HidingFRI.  Both the path depth and the claimed historical root are checked
/// natively before the expensive prover is entered.
pub fn prove_zk(
    opening: &FaithfulNoteOpening,
    path: &Poseidon2NoteProof16,
    claim: FaithfulNoteSpendClaim,
) -> Result<(FaithfulNoteSpendZkProof, FaithfulNoteSpendPublic), String> {
    let (trace, public) = trace_and_public(opening, path, claim)?;
    let public_inputs = public.as_felts();
    let proof = prove_vm_descriptor2_for_config(
        &descriptor()?,
        &trace,
        &public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &create_zk_config(),
    )?;
    validate_proof_shape(&proof)?;
    Ok((FaithfulNoteSpendZkProof { proof }, public))
}

/// Verify only the exact Lean descriptor under the HidingFRI configuration.
pub fn verify_zk(
    proof: &FaithfulNoteSpendZkProof,
    public: FaithfulNoteSpendPublic,
) -> Result<(), String> {
    public.validate()?;
    validate_proof_shape(&proof.proof)?;
    verify_vm_descriptor2_with_config(
        &descriptor()?,
        &proof.proof,
        &public.as_felts(),
        &create_zk_config(),
    )
}

pub fn verify_postcard(proof_bytes: &[u8], public_values: &[u32]) -> Result<(), String> {
    let proof = FaithfulNoteSpendZkProof::from_postcard(proof_bytes)?;
    verify_zk(
        &proof,
        FaithfulNoteSpendPublic::try_from_u32s(public_values)?,
    )
}

fn validate_proof_shape(proof: &Ir2BatchProof<DreggZkStarkConfig>) -> Result<(), String> {
    if proof.degree_bits.len() != EXPECTED_PROOF_INSTANCES {
        return Err(format!(
            "faithful note spend proof has {} instances, expected {EXPECTED_PROOF_INSTANCES}",
            proof.degree_bits.len()
        ));
    }
    if proof.degree_bits[0] != EXPECTED_HIDING_MAIN_DEGREE_BITS {
        return Err(format!(
            "faithful note spend main instance has degree bits {}, expected fixed depth-16 HidingFRI degree {EXPECTED_HIDING_MAIN_DEGREE_BITS}",
            proof.degree_bits[0]
        ));
    }
    if proof.commitments.random.is_none()
        || proof
            .opened_values
            .instances
            .iter()
            .any(|instance| instance.base_opened_values.random.is_none())
    {
        return Err("faithful note spend proof is not a HidingFRI proof".to_string());
    }
    Ok(())
}

pub(crate) fn trace_and_public(
    opening: &FaithfulNoteOpening,
    path: &Poseidon2NoteProof16,
    claim: FaithfulNoteSpendClaim,
) -> Result<(Vec<Vec<BabyBear>>, FaithfulNoteSpendPublic), String> {
    validate_root("historical note", claim.historical_note_root)?;
    validate_root("successor nullifier", claim.successor_nullifier_root)?;
    if path.siblings.len() != TREE_DEPTH || path.positions.len() != TREE_DEPTH {
        return Err(format!(
            "faithful note spend requires exactly {TREE_DEPTH} Merkle levels, got {} siblings and {} positions",
            path.siblings.len(),
            path.positions.len()
        ));
    }
    if let Some(position) = path
        .positions
        .iter()
        .copied()
        .find(|position| *position >= 4)
    {
        return Err(format!(
            "faithful note spend path position {position} is outside 0..4"
        ));
    }

    let owner = bytes32_u16(&opening.owner);
    let value = u64_u16(opening.value);
    let asset = u64_u16(opening.asset_type);
    let nonce = bytes32_u16(&opening.creation_nonce);
    let randomness = bytes32_u16(&opening.randomness);
    let spending_key = bytes32_u16(&opening.spending_key);

    let mut owner_preimage = Vec::with_capacity(17);
    owner_preimage.push(BabyBear::new(NOTE_OWNER_V2_DOMAIN));
    owner_preimage.extend(spending_key);
    let owner_states = sponge_states(&owner_preimage);
    debug_assert_eq!(owner_states.len(), OWNER_STATE_STEPS);
    let owner_digest = sponge_digest(&owner_states);
    if owner_digest != hash_many_8(&owner_preimage) {
        return Err("FNO2 state schedule diverged from native hash_many_8".to_string());
    }
    if digest8_to_bytes32(owner_digest) != opening.owner {
        return Err(
            "faithful note spend owner is not the FNO2 address of the hidden spending key"
                .to_string(),
        );
    }

    let mut commitment_preimage = Vec::with_capacity(57);
    commitment_preimage.push(BabyBear::new(NOTE_COMMITMENT_V2_DOMAIN));
    commitment_preimage.extend(owner);
    commitment_preimage.extend(value);
    commitment_preimage.extend(asset);
    commitment_preimage.extend(nonce);
    commitment_preimage.extend(randomness);
    let commitment_states = sponge_states(&commitment_preimage);
    debug_assert_eq!(commitment_states.len(), COMMITMENT_STATE_STEPS);
    let commitment_digest = sponge_digest(&commitment_states);
    if commitment_digest != hash_many_8(&commitment_preimage) {
        return Err("FNC2 state schedule diverged from native hash_many_8".to_string());
    }
    let commitment_bytes = digest8_to_bytes32(commitment_digest);
    let commitment_leaf = commitment_to_lanes16(&commitment_bytes);
    if path.leaf != commitment_leaf {
        return Err(
            "faithful note spend path leaf is not the FNC2 commitment of this opening/key"
                .to_string(),
        );
    }

    let mut nullifier_preimage = Vec::with_capacity(41);
    nullifier_preimage.push(BabyBear::new(NOTE_NULLIFIER_V2_DOMAIN));
    nullifier_preimage.extend(commitment_digest);
    nullifier_preimage.extend(spending_key);
    nullifier_preimage.extend(nonce);
    let nullifier_states = sponge_states(&nullifier_preimage);
    debug_assert_eq!(nullifier_states.len(), NULLIFIER_STATE_STEPS);
    let nullifier_digest = sponge_digest(&nullifier_states);
    if nullifier_digest != hash_many_8(&nullifier_preimage) {
        return Err("FNF2 state schedule diverged from native hash_many_8".to_string());
    }
    let nullifier = digest8_to_bytes32(nullifier_digest);

    let mut leaf_preimage = Vec::with_capacity(17);
    leaf_preimage.push(BabyBear::new(NOTE_LEAF_DOMAIN));
    leaf_preimage.extend(commitment_leaf);
    let leaf_states = sponge_states(&leaf_preimage);
    debug_assert_eq!(leaf_states.len(), LEAF_STATE_STEPS);
    let leaf_digest = sponge_digest(&leaf_states);
    if leaf_digest != note_leaf16(&commitment_leaf) {
        return Err("faithful note leaf state schedule diverged from live note tree".to_string());
    }

    let mut current = leaf_digest;
    let mut trace = Vec::with_capacity(TREE_DEPTH);
    for level in 0..TREE_DEPTH {
        let position = path.positions[level] as usize;
        let siblings = path.siblings[level];
        let children = children_at_position(current, siblings, position);
        let mut node_preimage = Vec::with_capacity(33);
        node_preimage.push(BabyBear::new(NOTE_NODE_DOMAIN));
        for child in children {
            node_preimage.extend(child);
        }
        let node_states = sponge_states(&node_preimage);
        debug_assert_eq!(node_states.len(), NODE_STATE_STEPS);
        let parent = sponge_digest(&node_states);
        if parent != note_node8(&children) {
            return Err(format!(
                "faithful note node state schedule diverged from live tree at level {level}"
            ));
        }

        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
        write(&mut row, CUR_BASE, &current);
        write(&mut row, SIB0_BASE, &siblings[0]);
        write(&mut row, SIB1_BASE, &siblings[1]);
        write(&mut row, SIB2_BASE, &siblings[2]);
        row[POS_B0] = BabyBear::new((position & 1) as u32);
        row[POS_B1] = BabyBear::new(((position >> 1) & 1) as u32);
        write(&mut row, OWNER_BASE, &owner);
        write(&mut row, VALUE_BASE, &value);
        write(&mut row, ASSET_BASE, &asset);
        write(&mut row, NONCE_BASE, &nonce);
        write(&mut row, RANDOMNESS_BASE, &randomness);
        write(&mut row, SPENDING_KEY_BASE, &spending_key);
        write_states(&mut row, OWNER_STATE_BASE, &owner_states);
        fill_pack(
            &mut row,
            owner_digest,
            OWNER_BASE,
            OWNER_SLACK_BASE,
            OWNER_ZERO_BASE,
            OWNER_INV_BASE,
        )?;
        write_states(&mut row, COMMITMENT_STATE_BASE, &commitment_states);
        fill_pack(
            &mut row,
            commitment_digest,
            COMMITMENT_RAW_BASE,
            COMMITMENT_SLACK_BASE,
            COMMITMENT_ZERO_BASE,
            COMMITMENT_INV_BASE,
        )?;
        write_states(&mut row, NULLIFIER_STATE_BASE, &nullifier_states);
        fill_pack(
            &mut row,
            nullifier_digest,
            NULLIFIER_RAW_BASE,
            NULLIFIER_SLACK_BASE,
            NULLIFIER_ZERO_BASE,
            NULLIFIER_INV_BASE,
        )?;
        write_states(&mut row, LEAF_STATE_BASE, &leaf_states);
        write_states(&mut row, NODE_STATE_BASE, &node_states);
        write(&mut row, HEIGHT_BASE, &u64_u16(claim.root_height));
        write(
            &mut row,
            SUCCESSOR_NULLIFIER_ROOT_BASE,
            &claim.successor_nullifier_root.map(BabyBear::new),
        );
        row[LEVEL_COL] = BabyBear::new(level as u32);
        trace.push(row);
        current = parent;
    }

    let derived_root = current.map(BabyBear::as_u32);
    if derived_root != claim.historical_note_root {
        return Err(
            "faithful note spend path does not recompose to the claimed historical root"
                .to_string(),
        );
    }
    let public = FaithfulNoteSpendPublic {
        root_height: claim.root_height,
        historical_note_root: claim.historical_note_root,
        nullifier,
        value: opening.value,
        asset_type: opening.asset_type,
        successor_nullifier_root: claim.successor_nullifier_root,
    };
    public.validate()?;
    Ok((trace, public))
}

fn sponge_states(preimage: &[BabyBear]) -> Vec<[BabyBear; STATE_LANES]> {
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

fn sponge_digest(states: &[[BabyBear; STATE_LANES]]) -> [BabyBear; DIGEST_LANES] {
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

fn children_at_position(
    current: [BabyBear; DIGEST_LANES],
    siblings: [[BabyBear; DIGEST_LANES]; 3],
    position: usize,
) -> [[BabyBear; DIGEST_LANES]; 4] {
    let mut children = [[BabyBear::ZERO; DIGEST_LANES]; 4];
    let mut sibling = 0;
    for (slot, child) in children.iter_mut().enumerate() {
        if slot == position {
            *child = current;
        } else {
            *child = siblings[sibling];
            sibling += 1;
        }
    }
    children
}

fn fill_pack(
    row: &mut [BabyBear],
    digest: [BabyBear; DIGEST_LANES],
    raw_base: usize,
    slack_base: usize,
    zero_base: usize,
    inv_base: usize,
) -> Result<(), String> {
    for (lane, felt) in digest.into_iter().enumerate() {
        let value = felt.as_u32();
        let lo = value & 0xffff;
        let hi = value >> 16;
        let slack = FIELD_HI_CANON_MAX - hi;
        let is_zero = u32::from(slack == 0);
        row[raw_base + 2 * lane] = BabyBear::new(lo);
        row[raw_base + 2 * lane + 1] = BabyBear::new(hi);
        row[slack_base + lane] = BabyBear::new(slack);
        row[zero_base + lane] = BabyBear::new(is_zero);
        row[inv_base + lane] = if slack == 0 {
            BabyBear::ZERO
        } else {
            BabyBear::new(slack)
                .inverse()
                .ok_or_else(|| "nonzero canonical-pack slack lacked inverse".to_string())?
        };
    }
    Ok(())
}

fn write(row: &mut [BabyBear], base: usize, values: &[BabyBear]) {
    row[base..base + values.len()].copy_from_slice(values);
}

fn write_states(row: &mut [BabyBear], base: usize, states: &[[BabyBear; STATE_LANES]]) {
    for (step, state) in states.iter().enumerate() {
        write(row, base + STATE_LANES * step, state);
    }
}

fn bytes32_u16(value: &[u8; 32]) -> [BabyBear; BYTES32_U16_LIMBS] {
    core::array::from_fn(|lane| {
        let offset = 2 * lane;
        BabyBear::new(u16::from_le_bytes([value[offset], value[offset + 1]]) as u32)
    })
}

fn bytes32_u16_u32(value: &[u8; 32]) -> [u32; BYTES32_U16_LIMBS] {
    bytes32_u16(value).map(BabyBear::as_u32)
}

fn u64_u16(value: u64) -> [BabyBear; U64_U16_LIMBS] {
    u64_u16_u32(value).map(BabyBear::new)
}

fn u64_u16_u32(value: u64) -> [u32; U64_U16_LIMBS] {
    core::array::from_fn(|lane| ((value >> (16 * lane)) & 0xffff) as u32)
}

fn u64_from_u16s(limbs: &[u32]) -> u64 {
    limbs
        .iter()
        .copied()
        .enumerate()
        .fold(0u64, |value, (lane, limb)| {
            value | ((limb as u64) << (16 * lane))
        })
}

fn bytes32_from_u16s(limbs: &[u32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (lane, limb) in limbs.iter().copied().enumerate() {
        out[2 * lane..2 * lane + 2].copy_from_slice(&(limb as u16).to_le_bytes());
    }
    out
}

fn digest8_to_bytes32(digest: [BabyBear; DIGEST_LANES]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (lane, felt) in digest.into_iter().enumerate() {
        out[4 * lane..4 * lane + 4].copy_from_slice(&felt.as_u32().to_le_bytes());
    }
    out
}

fn validate_root(name: &str, root: [u32; DIGEST_LANES]) -> Result<(), String> {
    for (lane, value) in root.into_iter().enumerate() {
        if value >= BABYBEAR_P {
            return Err(format!(
                "{name} root lane {lane}={value} is noncanonical for BabyBear"
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::note::Note;
    use dregg_commit::poseidon2_tree::Poseidon2NoteTree16;

    fn fixture() -> (
        Note,
        FaithfulNoteOpening,
        Poseidon2NoteProof16,
        FaithfulNoteSpendClaim,
    ) {
        let spending_key = core::array::from_fn(|i| 0xc0u8.wrapping_add(i as u8));
        let note = Note::with_nonce(
            Note::faithful_owner_v2(&spending_key),
            [
                0x8899_aabb_ccdd_eeff,
                0x0123_4567_89ab_cdef,
                0,
                0,
                0,
                0,
                0,
                0,
            ],
            core::array::from_fn(|i| 0x40u8.wrapping_add(i as u8)),
            core::array::from_fn(|i| 0x80u8.wrapping_add(i as u8)),
        );
        let commitment = note.faithful_commitment_v2();
        let mut tree = Poseidon2NoteTree16::new();
        tree.append_commitment(&commitment.0);
        let historical_note_root = tree.root().limbs().map(BabyBear::as_u32);
        let path = tree
            .prove_membership(0)
            .expect("one inserted note has a path");
        let opening = FaithfulNoteOpening {
            owner: note.owner,
            value: note.fields[1],
            asset_type: note.fields[0],
            creation_nonce: note.creation_nonce,
            randomness: note.randomness,
            spending_key,
        };
        let claim = FaithfulNoteSpendClaim {
            root_height: 0x1122_3344_5566_7788,
            historical_note_root,
            successor_nullifier_root: core::array::from_fn(|lane| 0x1000 + lane as u32),
        };
        (note, opening, path, claim)
    }

    #[test]
    fn faithful_note_spend_descriptor_and_native_witness_match() {
        let descriptor = descriptor().expect("Lean-emitted descriptor decodes");
        assert_eq!(descriptor.trace_width, TRACE_WIDTH);
        assert_eq!(descriptor.public_input_count, PUBLIC_INPUT_COUNT);

        let mut pins = descriptor
            .constraints
            .iter()
            .filter_map(|constraint| match constraint {
                VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }) => {
                    Some((*row, *col, *pi_index))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        pins.sort_by_key(|(_, _, pi)| *pi);
        assert_eq!(pins.len(), PUBLIC_INPUT_COUNT);
        assert_eq!(pins[0], (VmRow::First, HEIGHT_BASE, 0));
        assert_eq!(pins[4], (VmRow::Last, 978, 4));
        assert_eq!(pins[12], (VmRow::First, NULLIFIER_RAW_BASE, 12));
        assert_eq!(pins[28], (VmRow::First, VALUE_BASE, 28));
        assert_eq!(pins[32], (VmRow::First, ASSET_BASE, 32));
        assert_eq!(pins[36], (VmRow::First, SUCCESSOR_NULLIFIER_ROOT_BASE, 36));

        let (note, opening, path, claim) = fixture();
        let (trace, public) =
            trace_and_public(&opening, &path, claim).expect("honest witness fills exact ABI");
        assert_eq!(trace.len(), TREE_DEPTH);
        assert!(trace.iter().all(|row| row.len() == TRACE_WIDTH));
        assert_eq!(
            public.nullifier,
            note.faithful_nullifier_v2(&opening.spending_key).0
        );
        assert_eq!(
            FaithfulNoteSpendPublic::try_from_u32s(&public.as_u32_array()).unwrap(),
            public
        );

        let mut short = path.clone();
        short.siblings.pop();
        short.positions.pop();
        assert!(trace_and_public(&opening, &short, claim).is_err());
        let mut wrong_root = claim;
        wrong_root.historical_note_root[7] += 1;
        assert!(trace_and_public(&opening, &path, wrong_root).is_err());
        let mut wrong_key = opening.clone();
        wrong_key.spending_key[31] ^= 0x80;
        assert!(trace_and_public(&wrong_key, &path, claim).is_err());
    }

    /// Real HidingFRI proof + hostile statement teeth.  This is intentionally
    /// ignored in the default fast gauntlet; run focused in release mode.
    #[test]
    #[ignore = "real 1023-column HidingFRI proof; run focused under --release"]
    fn faithful_note_spend_hiding_proves_and_all_public_mutations_refuse() {
        let (_note, opening, path, claim) = fixture();
        let (proof, public) = prove_zk(&opening, &path, claim).expect("honest FNSP proves");
        verify_zk(&proof, public).expect("honest FNSP verifies");

        let bytes = proof.to_postcard().expect("proof encodes");
        let decoded = FaithfulNoteSpendZkProof::from_postcard(&bytes).expect("proof decodes");
        verify_zk(&decoded, public).expect("transported proof verifies");
        verify_postcard(&bytes, &public.as_u32_array()).expect("strict postcard verifier accepts");
        let mut with_trailer = bytes.clone();
        with_trailer.push(0);
        assert!(FaithfulNoteSpendZkProof::from_postcard(&with_trailer).is_err());

        let mutations: [fn(&mut FaithfulNoteSpendPublic); 6] = [
            |p| p.root_height ^= 1u64 << 63,
            |p| p.historical_note_root[7] = (p.historical_note_root[7] + 1) % BABYBEAR_P,
            |p| p.nullifier[31] ^= 0x80,
            |p| p.value ^= 1u64 << 63,
            |p| p.asset_type ^= 1u64 << 63,
            |p| p.successor_nullifier_root[6] = (p.successor_nullifier_root[6] + 1) % BABYBEAR_P,
        ];
        for mutate in mutations {
            let mut forged = public;
            mutate(&mut forged);
            assert!(verify_zk(&proof, forged).is_err());
        }
    }
}
