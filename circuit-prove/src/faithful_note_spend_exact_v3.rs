//! Complete witness composition for the staged exact-nullifier FNSP-v3 descriptor.
//!
//! This module joins three independently checked producers without reimplementing any of them:
//!
//! * [`crate::faithful_note_spend`] fills the inherited hidden FNO2/FNC2/FNF2 note-opening and
//!   exact depth-16 note-membership band (columns `0..1023`, public inputs `0..44`);
//! * [`dregg_circuit::exact_nullifier_aafi_trace`] validates and fills the exact append-order
//!   nullifier transition through column `2442`;
//! * [`dregg_circuit::exact_nullifier_aafi_rotated_trace`] welds its FNS3 before/after checkpoints
//!   into the carried 179-felt state and fills both chip-faithful wide commitment chains through
//!   column `3760`.
//!
//! The shared columns are compared on **all sixteen rows before any merge**.  The first sixty
//! public inputs are derived from the hidden-note/exact rows at the descriptor-bound rows; the
//! final sixteen come from the wide marshaller.  No caller supplies a root/count/checkpoint PI.
//!
//! This is intentionally a staged proving surface.  The descriptor is not in the deployed
//! registry and has no pinned verification-key/provenance entry, so producing and verifying the
//! proof below is not a live FNSP-v3 cutover claim.

use crate::faithful_note_spend::{
    FaithfulNoteOpening, FaithfulNoteSpendClaim, FaithfulNoteSpendPublic,
    PUBLIC_INPUT_COUNT as V2_PUBLIC_INPUT_COUNT, TRACE_WIDTH as V2_TRACE_WIDTH,
    TREE_DEPTH as NOTE_TREE_DEPTH, trace_and_public,
};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, TableSem, UMemBoundaryWitness,
    VmConstraint2, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2_with_config,
};
use dregg_circuit::exact_nullifier_aafi::{ExactAafiWitness, u16_le_to_raw, u16_le_to_u64};
use dregg_circuit::exact_nullifier_aafi_rotated_trace::{
    ExactAafiRotatedTraceWitness, OUTER_PUBLIC_INPUTS, ROTATED_PAYLOAD_WIDTH,
    ROTATED_PUBLIC_INPUT_COUNT, ROTATED_TRACE_WIDTH, marshal_exact_aafi_rotated_trace,
};
use dregg_circuit::exact_nullifier_aafi_trace::{
    EXACT_AAFI_TRACE_ROWS, LEVEL_COL, NULLIFIER_RAW_BASE, POST_COUNT_BASE, PRE_COUNT_BASE,
    SUCCESSOR_NULLIFIER_ROOT_BASE, VALUE_BASE, marshal_exact_aafi_trace, node_digest_cols,
};
use dregg_circuit::field::BABYBEAR_P;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
use dregg_circuit::stark_zk::{DreggZkStarkConfig, create_zk_config};
use dregg_commit::poseidon2_tree::Poseidon2NoteProof16;

pub const STAGED_DESCRIPTOR_JSON: &str = include_str!(
    "../../circuit/staged-descriptors/fnsp-v3/faithful-note-spend-exact-aafi-fns3-rotated-wide-state.json"
);
pub const STAGED_PREDICATE_NAME: &str =
    "faithful-note-spend-v3-plan::exact-aafi-fns3-rotated-wide-state";
pub const STAGED_TRACE_WIDTH: usize = ROTATED_TRACE_WIDTH;
pub const STAGED_PUBLIC_INPUT_COUNT: usize = ROTATED_PUBLIC_INPUT_COUNT;
const EXPECTED_CONSTRAINT_COUNT: usize = 1258;
const EXPECTED_STATE16_LOOKUPS: usize = 128;
const EXPECTED_WIDE_LOOKUPS: usize = 120;
const EXPECTED_RANGE15_LOOKUPS: usize = 48;
const EXPECTED_RANGE16_LOOKUPS: usize = 132;
const EXPECTED_DESCRIPTOR_TABLES: usize = 5;
// The two graduated range table IDs share the one canonical byte-table AIR/commitment.  Therefore
// the five descriptor table definitions produce four committed batch instances in this order:
// main, wide Poseidon2, state16 Poseidon2, byte/range.
const EXPECTED_PROOF_INSTANCES: usize = 4;
const EXPECTED_HIDING_DEGREE_BITS: [usize; EXPECTED_PROOF_INSTANCES] = [5, 8, 11, 5];
pub const STAGED_PUBLIC_WIRE_BYTES: usize = STAGED_PUBLIC_INPUT_COUNT * 4;

const PI_PRIOR_ROOT_BASE: usize = 44;
const PI_PRE_COUNT_BASE: usize = 52;
const PI_POST_COUNT_BASE: usize = 56;
const PI_OUTER_BASE: usize = 60;

const _: () = {
    assert!(V2_TRACE_WIDTH == 1023);
    assert!(V2_PUBLIC_INPUT_COUNT == 44);
    assert!(NOTE_TREE_DEPTH == EXACT_AAFI_TRACE_ROWS);
    assert!(STAGED_TRACE_WIDTH == 3760);
    assert!(STAGED_PUBLIC_INPUT_COUNT == 76);
    assert!(OUTER_PUBLIC_INPUTS == 16);
};

/// Host-owned note-tree checkpoint.  Exact nullifier roots/counts are deliberately absent: they
/// are derived from the hostile-input-validated [`ExactAafiWitness`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FaithfulNoteSpendExactV3Claim {
    pub root_height: u64,
    pub historical_note_root: [u32; 8],
}

/// Complete sixteen-row witness and exact 76-felt statement for the staged descriptor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaithfulNoteSpendExactV3Witness {
    rows: Vec<Vec<BabyBear>>,
    public_inputs: [BabyBear; STAGED_PUBLIC_INPUT_COUNT],
    inherited_public: FaithfulNoteSpendPublic,
}

impl FaithfulNoteSpendExactV3Witness {
    pub fn rows(&self) -> &[Vec<BabyBear>] {
        &self.rows
    }

    pub fn public_inputs(&self) -> &[BabyBear; STAGED_PUBLIC_INPUT_COUNT] {
        &self.public_inputs
    }

    pub fn inherited_public(&self) -> FaithfulNoteSpendPublic {
        self.inherited_public
    }

    pub fn public_statement(&self) -> StagedFaithfulNoteSpendExactV3Public {
        StagedFaithfulNoteSpendExactV3Public {
            lanes: self.public_inputs,
        }
    }
}

/// Canonical public statement for the exact staged predicate.  Its wire form is exactly 76
/// little-endian canonical BabyBear `u32` lanes (304 bytes), without length prefixes or trailing
/// extension space.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StagedFaithfulNoteSpendExactV3Public {
    lanes: [BabyBear; STAGED_PUBLIC_INPUT_COUNT],
}

impl StagedFaithfulNoteSpendExactV3Public {
    pub fn try_from_u32s(values: &[u32]) -> Result<Self, String> {
        if values.len() != STAGED_PUBLIC_INPUT_COUNT {
            return Err(format!(
                "staged exact FNSP-v3 expects {STAGED_PUBLIC_INPUT_COUNT} public lanes, got {}",
                values.len()
            ));
        }
        let mut lanes = [BabyBear::ZERO; STAGED_PUBLIC_INPUT_COUNT];
        for (index, value) in values.iter().copied().enumerate() {
            if value >= BABYBEAR_P {
                return Err(format!(
                    "staged exact FNSP-v3 public lane {index}={value} is noncanonical for BabyBear"
                ));
            }
            lanes[index] = BabyBear::new(value);
        }
        Ok(Self { lanes })
    }

    pub fn as_felts(&self) -> &[BabyBear; STAGED_PUBLIC_INPUT_COUNT] {
        &self.lanes
    }

    pub fn as_u32_array(&self) -> [u32; STAGED_PUBLIC_INPUT_COUNT] {
        self.lanes.map(BabyBear::as_u32)
    }

    pub fn to_le_bytes(&self) -> [u8; STAGED_PUBLIC_WIRE_BYTES] {
        let mut bytes = [0u8; STAGED_PUBLIC_WIRE_BYTES];
        for (index, value) in self.as_u32_array().into_iter().enumerate() {
            bytes[4 * index..4 * index + 4].copy_from_slice(&value.to_le_bytes());
        }
        bytes
    }

    pub fn from_le_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() != STAGED_PUBLIC_WIRE_BYTES {
            return Err(format!(
                "staged exact FNSP-v3 public wire expects {STAGED_PUBLIC_WIRE_BYTES} bytes, got {}",
                bytes.len()
            ));
        }
        let mut values = [0u32; STAGED_PUBLIC_INPUT_COUNT];
        for (index, chunk) in bytes.chunks_exact(4).enumerate() {
            values[index] = u32::from_le_bytes(chunk.try_into().expect("four-byte chunk"));
        }
        Self::try_from_u32s(&values)
    }
}

/// Opaque HidingFRI proof for the exact staged JSON.  This type is intentionally not accepted by
/// the deployed FNSP-v2 verifier/registry.
pub struct StagedFaithfulNoteSpendExactV3Proof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl StagedFaithfulNoteSpendExactV3Proof {
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|error| format!("staged exact FNSP-v3 proof encode failed: {error}"))
    }

    /// Strict transport decode: consume the complete byte string and require the exact four
    /// committed HidingFRI instances produced by the five-table staged descriptor.
    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        let (proof, trailing) =
            postcard::take_from_bytes::<Ir2BatchProof<DreggZkStarkConfig>>(bytes)
                .map_err(|error| format!("staged exact FNSP-v3 proof decode failed: {error}"))?;
        if !trailing.is_empty() {
            return Err(format!(
                "staged exact FNSP-v3 proof has {} trailing bytes",
                trailing.len()
            ));
        }
        validate_proof_shape(&proof)?;
        Ok(Self { proof })
    }
}

fn validate_proof_shape(proof: &Ir2BatchProof<DreggZkStarkConfig>) -> Result<(), String> {
    if proof.degree_bits.as_slice() != EXPECTED_HIDING_DEGREE_BITS {
        return Err(format!(
            "staged exact FNSP-v3 proof degree vector {:?} != fixed HidingFRI vector {:?}",
            proof.degree_bits, EXPECTED_HIDING_DEGREE_BITS
        ));
    }
    if proof.opened_values.instances.len() != EXPECTED_PROOF_INSTANCES {
        return Err(format!(
            "staged exact FNSP-v3 proof has {} opened instances, expected {EXPECTED_PROOF_INSTANCES}",
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
        return Err("staged exact FNSP-v3 proof is not a complete HidingFRI proof".to_owned());
    }
    Ok(())
}

/// Parse and pin the exact unregistered Lean emission used by this composition lane.
pub fn staged_descriptor() -> Result<EffectVmDescriptor2, String> {
    let descriptor = parse_vm_descriptor2(STAGED_DESCRIPTOR_JSON)?;
    if descriptor.name != STAGED_PREDICATE_NAME
        || descriptor.trace_width != STAGED_TRACE_WIDTH
        || descriptor.public_input_count != STAGED_PUBLIC_INPUT_COUNT
        || descriptor.tables.len() != EXPECTED_DESCRIPTOR_TABLES
        || descriptor.constraints.len() != EXPECTED_CONSTRAINT_COUNT
        || !descriptor.hash_sites.is_empty()
        || !descriptor.ranges.is_empty()
    {
        return Err("staged exact FNSP-v3 descriptor shape drifted".to_owned());
    }
    let tables_match = matches!(
        descriptor.tables.as_slice(),
        [main, state16, wide, range15, range16]
            if main.id == 0 && main.name == "main" && main.arity == STAGED_TRACE_WIDTH
                && matches!(&main.sem, TableSem::Main)
                && state16.id == 9 && state16.name == "poseidon2_state16_chip"
                && state16.arity == 33 && matches!(&state16.sem, TableSem::Poseidon2Chip)
                && wide.id == 1 && wide.name == "poseidon2_chip" && wide.arity == 25
                && matches!(&wide.sem, TableSem::Poseidon2Chip)
                && range15.id == 84 && range15.name == "range_w15" && range15.arity == 1
                && matches!(&range15.sem, TableSem::Range { bits: 15 })
                && range16.id == 85 && range16.name == "range_w16" && range16.arity == 1
                && matches!(&range16.sem, TableSem::Range { bits: 16 })
    );
    if !tables_match {
        return Err("staged exact FNSP-v3 table ABI drifted".to_owned());
    }
    let mut lookup_counts = [0usize; 4];
    let mut pins = Vec::new();
    for constraint in &descriptor.constraints {
        match constraint {
            VmConstraint2::Lookup(lookup) => match lookup.table {
                9 => lookup_counts[0] += 1,
                1 => lookup_counts[1] += 1,
                84 => lookup_counts[2] += 1,
                85 => lookup_counts[3] += 1,
                table => return Err(format!("unexpected staged lookup table {table}")),
            },
            VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }) => {
                pins.push((*row, *col, *pi_index));
            }
            _ => {}
        }
    }
    if lookup_counts
        != [
            EXPECTED_STATE16_LOOKUPS,
            EXPECTED_WIDE_LOOKUPS,
            EXPECTED_RANGE15_LOOKUPS,
            EXPECTED_RANGE16_LOOKUPS,
        ]
    {
        return Err(format!(
            "staged exact FNSP-v3 lookup ABI drifted: {lookup_counts:?}"
        ));
    }
    pins.sort_by_key(|(_, _, pi)| *pi);
    if pins.len() != STAGED_PUBLIC_INPUT_COUNT
        || pins
            .iter()
            .enumerate()
            .any(|(expected, (_, _, actual))| expected != *actual)
    {
        return Err("staged exact FNSP-v3 public-pin ABI drifted".to_owned());
    }
    Ok(descriptor)
}

fn compare_shared_band(
    inherited: &[Vec<BabyBear>],
    exact: &ExactAafiRotatedTraceWitness,
) -> Result<(), String> {
    if inherited.len() != EXACT_AAFI_TRACE_ROWS
        || exact.rows().len() != EXACT_AAFI_TRACE_ROWS
        || inherited.iter().any(|row| row.len() != V2_TRACE_WIDTH)
        || exact
            .rows()
            .iter()
            .any(|row| row.len() != STAGED_TRACE_WIDTH)
    {
        return Err("inherited/exact witness geometry mismatch".to_owned());
    }
    for row_index in 0..EXACT_AAFI_TRACE_ROWS {
        let left = &inherited[row_index];
        let right = &exact.rows()[row_index];
        for (name, base, width) in [
            ("value", VALUE_BASE, 4usize),
            ("nullifier", NULLIFIER_RAW_BASE, 16usize),
            (
                "successor-nullifier-root",
                SUCCESSOR_NULLIFIER_ROOT_BASE,
                8usize,
            ),
            ("level", LEVEL_COL, 1usize),
        ] {
            for lane in 0..width {
                if left[base + lane] != right[base + lane] {
                    return Err(format!(
                        "inherited/exact {name} mismatch at row {row_index}, lane {lane}"
                    ));
                }
            }
        }
    }
    Ok(())
}

fn exact_public_prefix(
    rows: &[Vec<BabyBear>],
    inherited_public: FaithfulNoteSpendPublic,
    outer_public: &[BabyBear; OUTER_PUBLIC_INPUTS],
) -> Result<[BabyBear; STAGED_PUBLIC_INPUT_COUNT], String> {
    let mut public_inputs = [BabyBear::ZERO; STAGED_PUBLIC_INPUT_COUNT];
    public_inputs[..V2_PUBLIC_INPUT_COUNT].copy_from_slice(&inherited_public.as_felts());
    let last = &rows[EXACT_AAFI_TRACE_ROWS - 1];
    for (lane, col) in node_digest_cols(0).into_iter().enumerate() {
        public_inputs[PI_PRIOR_ROOT_BASE + lane] = last[col];
    }
    public_inputs[PI_PRE_COUNT_BASE..PI_POST_COUNT_BASE]
        .copy_from_slice(&rows[0][PRE_COUNT_BASE..PRE_COUNT_BASE + 4]);
    public_inputs[PI_POST_COUNT_BASE..PI_OUTER_BASE]
        .copy_from_slice(&rows[0][POST_COUNT_BASE..POST_COUNT_BASE + 4]);
    public_inputs[PI_OUTER_BASE..].copy_from_slice(outer_public);

    let descriptor = staged_descriptor()?;
    for constraint in &descriptor.constraints {
        if let VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }) = constraint {
            let bound_row = match row {
                VmRow::First => &rows[0],
                VmRow::Last => &rows[EXACT_AAFI_TRACE_ROWS - 1],
            };
            if bound_row[*col] != public_inputs[*pi_index] {
                return Err(format!(
                    "composed public binding mismatch at pi {pi_index}, column {col}"
                ));
            }
        }
    }
    Ok(public_inputs)
}

/// Compose the complete witness without accepting any exact accumulator PI from the caller.
pub fn compose_staged_exact_v3_witness(
    opening: &FaithfulNoteOpening,
    note_path: &Poseidon2NoteProof16,
    claim: FaithfulNoteSpendExactV3Claim,
    exact_transition: &ExactAafiWitness,
    before_rotated_payload: [BabyBear; ROTATED_PAYLOAD_WIDTH],
) -> Result<FaithfulNoteSpendExactV3Witness, String> {
    // Validate the hostile exact transition before deriving either dependent witness.
    let core = marshal_exact_aafi_trace(exact_transition)
        .map_err(|error| format!("exact nullifier trace refused: {error}"))?;
    if exact_transition.inserted_key.tag != 1 {
        return Err("exact inserted nullifier is not the canonical REAL arm".to_owned());
    }
    if u16_le_to_u64(exact_transition.inserted_value_u16_le) != opening.value {
        return Err("hidden note value does not equal the exact inserted value".to_owned());
    }

    let v2_claim = FaithfulNoteSpendClaim {
        root_height: claim.root_height,
        historical_note_root: claim.historical_note_root,
        successor_nullifier_root: exact_transition.successor_root.map(BabyBear::as_u32),
    };
    let (inherited_rows, inherited_public) = trace_and_public(opening, note_path, v2_claim)?;
    let inserted_raw = u16_le_to_raw(exact_transition.inserted_key.raw_u16_le);
    if inherited_public.nullifier != inserted_raw {
        return Err(
            "inherited public FNF2 nullifier does not equal the exact inserted key".to_owned(),
        );
    }

    // The outer constructor validates the carried BEFORE FNS3 checkpoint before producing any
    // merged witness.
    let outer = marshal_exact_aafi_rotated_trace(&core, before_rotated_payload)
        .map_err(|error| format!("exact rotated trace refused: {error}"))?;
    compare_shared_band(&inherited_rows, &outer)?;

    let mut rows = outer.rows().to_vec();
    for row_index in 0..EXACT_AAFI_TRACE_ROWS {
        rows[row_index][..V2_TRACE_WIDTH].copy_from_slice(&inherited_rows[row_index]);
    }
    let public_inputs = exact_public_prefix(&rows, inherited_public, outer.outer_public_inputs())?;
    Ok(FaithfulNoteSpendExactV3Witness {
        rows,
        public_inputs,
        inherited_public,
    })
}

/// Produce a real HidingFRI proof for the staged JSON.  This proves descriptor satisfiability, but
/// does not register a verifier key or authorize any live state transition.
pub fn prove_staged_exact_v3_zk(
    witness: &FaithfulNoteSpendExactV3Witness,
) -> Result<StagedFaithfulNoteSpendExactV3Proof, String> {
    let descriptor = staged_descriptor()?;
    let proof = prove_vm_descriptor2_for_config(
        &descriptor,
        witness.rows(),
        witness.public_inputs(),
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &create_zk_config(),
    )?;
    validate_proof_shape(&proof)?;
    Ok(StagedFaithfulNoteSpendExactV3Proof { proof })
}

/// Verify only the exact staged JSON under the HidingFRI configuration.
pub fn verify_staged_exact_v3_zk(
    proof: &StagedFaithfulNoteSpendExactV3Proof,
    public_inputs: &[BabyBear; STAGED_PUBLIC_INPUT_COUNT],
) -> Result<(), String> {
    validate_proof_shape(&proof.proof)?;
    verify_vm_descriptor2_with_config(
        &staged_descriptor()?,
        &proof.proof,
        public_inputs,
        &create_zk_config(),
    )
}

/// Strict transport verifier for only this exact staged descriptor and HidingFRI configuration.
pub fn verify_staged_exact_v3_postcard(
    proof_bytes: &[u8],
    public_values: &[u32],
) -> Result<(), String> {
    let proof = StagedFaithfulNoteSpendExactV3Proof::from_postcard(proof_bytes)?;
    let public = StagedFaithfulNoteSpendExactV3Public::try_from_u32s(public_values)?;
    verify_staged_exact_v3_zk(&proof, public.as_felts())
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::note::Note;
    use dregg_circuit::exact_nullifier_aafi::ExactNullifierAafi;
    use dregg_circuit::exact_nullifier_aafi_rotated_trace::NULLIFIER_OFFSETS;
    use dregg_commit::poseidon2_tree::Poseidon2NoteTree16;

    fn fixture() -> (
        FaithfulNoteOpening,
        Poseidon2NoteProof16,
        FaithfulNoteSpendExactV3Claim,
        ExactAafiWitness,
        [BabyBear; ROTATED_PAYLOAD_WIDTH],
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
        let mut tree = Poseidon2NoteTree16::new();
        tree.append_commitment(&note.faithful_commitment_v2().0);
        let path = tree.prove_membership(0).expect("inserted note has path");
        let opening = FaithfulNoteOpening {
            owner: note.owner,
            value: note.fields[1],
            asset_type: note.fields[0],
            creation_nonce: note.creation_nonce,
            randomness: note.randomness,
            spending_key,
        };
        let nullifier = note.faithful_nullifier_v2(&spending_key).0;
        let exact = ExactNullifierAafi::new()
            .prepare_insert(nullifier, opening.value)
            .expect("fresh FNF2 nullifier inserts into exact accumulator");
        let mut before = [BabyBear::ZERO; ROTATED_PAYLOAD_WIDTH];
        for (lane, offset) in NULLIFIER_OFFSETS.iter().copied().enumerate() {
            before[offset] = exact.prior_state_commit[lane];
        }
        let claim = FaithfulNoteSpendExactV3Claim {
            root_height: 0x1122_3344_5566_7788,
            historical_note_root: tree.root().limbs().map(BabyBear::as_u32),
        };
        (opening, path, claim, exact, before)
    }

    #[test]
    fn complete_composition_fills_exact_geometry_and_all_pins() {
        let (opening, path, claim, exact, before) = fixture();
        let witness = compose_staged_exact_v3_witness(&opening, &path, claim, &exact, before)
            .expect("three honest producers compose");
        assert_eq!(witness.rows().len(), EXACT_AAFI_TRACE_ROWS);
        assert!(
            witness
                .rows()
                .iter()
                .all(|row| row.len() == STAGED_TRACE_WIDTH)
        );
        assert_eq!(witness.public_inputs().len(), STAGED_PUBLIC_INPUT_COUNT);
        assert_eq!(
            &witness.public_inputs()[PI_PRIOR_ROOT_BASE..PI_PRE_COUNT_BASE],
            exact.prior_root.as_slice()
        );
        assert_eq!(
            &witness.public_inputs()[PI_PRE_COUNT_BASE..PI_POST_COUNT_BASE],
            exact
                .prior_count
                .to_le_bytes()
                .chunks_exact(2)
                .map(|bytes| BabyBear::new(u16::from_le_bytes([bytes[0], bytes[1]]) as u32))
                .collect::<Vec<_>>()
                .as_slice()
        );
        staged_descriptor().expect("exact staged descriptor remains pinned");
    }

    #[test]
    fn public_statement_transport_is_exact_and_canonical() {
        let (opening, path, claim, exact, before) = fixture();
        let witness = compose_staged_exact_v3_witness(&opening, &path, claim, &exact, before)
            .expect("complete statement composes");
        let public = witness.public_statement();
        assert_eq!(
            StagedFaithfulNoteSpendExactV3Public::try_from_u32s(&public.as_u32_array())
                .expect("canonical lanes decode"),
            public
        );
        let wire = public.to_le_bytes();
        assert_eq!(wire.len(), STAGED_PUBLIC_WIRE_BYTES);
        assert_eq!(
            StagedFaithfulNoteSpendExactV3Public::from_le_bytes(&wire)
                .expect("exact public wire decodes"),
            public
        );

        assert!(
            StagedFaithfulNoteSpendExactV3Public::try_from_u32s(
                &public.as_u32_array()[..STAGED_PUBLIC_INPUT_COUNT - 1]
            )
            .is_err()
        );
        let mut too_long = public.as_u32_array().to_vec();
        too_long.push(0);
        assert!(StagedFaithfulNoteSpendExactV3Public::try_from_u32s(&too_long).is_err());
        let mut noncanonical = public.as_u32_array();
        noncanonical[PI_POST_COUNT_BASE] = BABYBEAR_P;
        assert!(StagedFaithfulNoteSpendExactV3Public::try_from_u32s(&noncanonical).is_err());
        assert!(
            StagedFaithfulNoteSpendExactV3Public::from_le_bytes(
                &wire[..STAGED_PUBLIC_WIRE_BYTES - 1]
            )
            .is_err()
        );
        let mut wire_with_trailer = wire.to_vec();
        wire_with_trailer.push(0);
        assert!(StagedFaithfulNoteSpendExactV3Public::from_le_bytes(&wire_with_trailer).is_err());
        let mut noncanonical_wire = wire;
        noncanonical_wire[0..4].copy_from_slice(&BABYBEAR_P.to_le_bytes());
        assert!(StagedFaithfulNoteSpendExactV3Public::from_le_bytes(&noncanonical_wire).is_err());
    }

    #[test]
    fn cross_band_nullifier_value_and_rotated_checkpoint_mismatches_refuse() {
        let (opening, path, claim, exact, before) = fixture();

        let wrong_nullifier = ExactNullifierAafi::new()
            .prepare_insert([0x5a; 32], opening.value)
            .expect("independently valid exact insertion");
        let mut wrong_nullifier_before = before;
        for (lane, offset) in NULLIFIER_OFFSETS.iter().copied().enumerate() {
            wrong_nullifier_before[offset] = wrong_nullifier.prior_state_commit[lane];
        }
        assert!(
            compose_staged_exact_v3_witness(
                &opening,
                &path,
                claim,
                &wrong_nullifier,
                wrong_nullifier_before,
            )
            .unwrap_err()
            .contains("FNF2 nullifier")
        );

        let wrong_value = ExactNullifierAafi::new()
            .prepare_insert(
                u16_le_to_raw(exact.inserted_key.raw_u16_le),
                opening.value + 1,
            )
            .expect("independently valid exact insertion");
        assert!(
            compose_staged_exact_v3_witness(&opening, &path, claim, &wrong_value, before)
                .unwrap_err()
                .contains("exact inserted value")
        );

        let mut wrong_checkpoint = before;
        wrong_checkpoint[NULLIFIER_OFFSETS[3]] += BabyBear::ONE;
        assert!(
            compose_staged_exact_v3_witness(&opening, &path, claim, &exact, wrong_checkpoint)
                .unwrap_err()
                .contains("exact rotated trace refused")
        );
    }

    /// Real 3,760-column HidingFRI proof and verification.  Kept out of the default fast set.
    #[test]
    #[ignore = "real staged FNSP-v3 HidingFRI proof; run focused under --release"]
    fn staged_exact_v3_hiding_proves_and_verifies() {
        let (opening, path, claim, exact, before) = fixture();
        let witness = compose_staged_exact_v3_witness(&opening, &path, claim, &exact, before)
            .expect("complete staged witness composes");
        let public = witness.public_statement();
        let mut proof = prove_staged_exact_v3_zk(&witness).expect("complete staged witness proves");
        assert_eq!(proof.proof.degree_bits, EXPECTED_HIDING_DEGREE_BITS);
        verify_staged_exact_v3_zk(&proof, public.as_felts()).expect("staged exact proof verifies");

        let proof_bytes = proof.to_postcard().expect("proof serializes");
        let transported = StagedFaithfulNoteSpendExactV3Proof::from_postcard(&proof_bytes)
            .expect("strict transported proof decodes");
        verify_staged_exact_v3_zk(&transported, public.as_felts())
            .expect("transported staged proof verifies");
        verify_staged_exact_v3_postcard(&proof_bytes, &public.as_u32_array())
            .expect("strict postcard verifier accepts exact transport");

        let mut with_trailer = proof_bytes.clone();
        with_trailer.push(0);
        assert!(StagedFaithfulNoteSpendExactV3Proof::from_postcard(&with_trailer).is_err());
        assert!(
            StagedFaithfulNoteSpendExactV3Proof::from_postcard(
                &proof_bytes[..proof_bytes.len() - 1]
            )
            .is_err()
        );

        let mut corrupted = proof_bytes.clone();
        let corrupt_index = corrupted.len() / 2;
        corrupted[corrupt_index] ^= 0x80;
        let corrupt_refused = match StagedFaithfulNoteSpendExactV3Proof::from_postcard(&corrupted) {
            Err(_) => true,
            Ok(decoded) => verify_staged_exact_v3_zk(&decoded, public.as_felts()).is_err(),
        };
        assert!(corrupt_refused, "corrupt proof transport must refuse");

        let original_main_degree = proof.proof.degree_bits[0];
        proof.proof.degree_bits[0] += 1;
        let wrong_shape = proof.to_postcard().expect("wrong-shape proof serializes");
        proof.proof.degree_bits[0] = original_main_degree;
        assert!(StagedFaithfulNoteSpendExactV3Proof::from_postcard(&wrong_shape).is_err());

        let removed_instance = proof
            .proof
            .opened_values
            .instances
            .pop()
            .expect("genuine proof has four opened instances");
        let short_batch = proof.to_postcard().expect("short batch serializes");
        proof.proof.opened_values.instances.push(removed_instance);
        assert!(StagedFaithfulNoteSpendExactV3Proof::from_postcard(&short_batch).is_err());

        let random_commitment = proof
            .proof
            .commitments
            .random
            .take()
            .expect("genuine proof has a hiding commitment");
        let nonhiding_commitment = proof
            .to_postcard()
            .expect("non-hiding commitment shape serializes");
        proof.proof.commitments.random = Some(random_commitment);
        assert!(StagedFaithfulNoteSpendExactV3Proof::from_postcard(&nonhiding_commitment).is_err());

        let random_opening = proof.proof.opened_values.instances[0]
            .base_opened_values
            .random
            .take()
            .expect("genuine main instance has hiding openings");
        let nonhiding_opening = proof
            .to_postcard()
            .expect("non-hiding opening shape serializes");
        proof.proof.opened_values.instances[0]
            .base_opened_values
            .random = Some(random_opening);
        assert!(StagedFaithfulNoteSpendExactV3Proof::from_postcard(&nonhiding_opening).is_err());

        let mut forged = public.as_u32_array();
        forged[PI_OUTER_BASE + 7] = (forged[PI_OUTER_BASE + 7] + 1) % BABYBEAR_P;
        assert!(verify_staged_exact_v3_postcard(&proof_bytes, &forged).is_err());
        assert!(
            verify_staged_exact_v3_postcard(
                &proof_bytes,
                &public.as_u32_array()[..STAGED_PUBLIC_INPUT_COUNT - 1]
            )
            .is_err()
        );
        let mut noncanonical = public.as_u32_array();
        noncanonical[0] = BABYBEAR_P;
        assert!(verify_staged_exact_v3_postcard(&proof_bytes, &noncanonical).is_err());
    }
}
