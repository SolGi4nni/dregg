//! Additive, non-live transport boundary for the exact FNSP-v3 relation.
//!
//! This module deliberately does not alter the deployed FNSP-v2 carrier or install a verifier in
//! the executor.  The v3 carrier transports only a checkpoint height and an opaque proof.  Its
//! predicate identity and verifier configuration are code-owned, while all state claims in the
//! exact 76-lane statement are derived independently of the proof bytes.

use core::fmt;

use crate::action::Effect;
use dregg_circuit::exact_nullifier_aafi::{ValidatedExactAafiTransition, exact_state_commit};
use dregg_circuit::exact_nullifier_aafi_rotated_trace::{
    ExactAafiRotatedTraceWitness, NULLIFIER_OFFSETS,
};
use dregg_circuit::field::BABYBEAR_P;

pub const FAITHFUL_NOTE_SPEND_EXACT_V3_MAGIC: [u8; 4] = *b"FNSP";
pub const FAITHFUL_NOTE_SPEND_EXACT_V3_VERSION: u8 = 3;
pub const FAITHFUL_NOTE_SPEND_EXACT_V3_PREDICATE: &str =
    "faithful-note-spend-v3-plan::exact-aafi-fns3-rotated-wide-state";
pub const FAITHFUL_NOTE_SPEND_EXACT_V3_ACTION: &str = "note-spend";
pub const FAITHFUL_NOTE_SPEND_EXACT_V3_RESOURCE: &str = "faithful-note-tree";
pub const FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_INPUT_COUNT: usize = 76;
pub const FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_WIRE_BYTES: usize =
    FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_INPUT_COUNT * size_of::<u32>();

/// Hostile-allocation ceiling for the opaque exact proof (4 MiB).
pub const MAX_EXACT_V3_INNER_PROOF_BYTES: usize = 4 * 1024 * 1024;

const RESERVED_LEN: usize = 3;
const VERSION_OFFSET: usize = FAITHFUL_NOTE_SPEND_EXACT_V3_MAGIC.len();
const RESERVED_OFFSET: usize = VERSION_OFFSET + size_of::<u8>();
const ROOT_HEIGHT_OFFSET: usize = RESERVED_OFFSET + RESERVED_LEN;
const PROOF_LEN_OFFSET: usize = ROOT_HEIGHT_OFFSET + size_of::<u64>();
pub const FAITHFUL_NOTE_SPEND_EXACT_V3_HEADER_LEN: usize = PROOF_LEN_OFFSET + size_of::<u32>();

const PI_HEIGHT: usize = 0;
const PI_HISTORICAL_ROOT: usize = 4;
const PI_NULLIFIER: usize = 12;
const PI_VALUE: usize = 28;
const PI_ASSET_TYPE: usize = 32;
const PI_SUCCESSOR_ROOT: usize = 36;
const PI_PRIOR_ROOT: usize = 44;
const PI_PRE_COUNT: usize = 52;
const PI_POST_COUNT: usize = 56;
const PI_BEFORE_COMMIT: usize = 60;
const PI_AFTER_COMMIT: usize = 68;

const _: () = {
    assert!(FAITHFUL_NOTE_SPEND_EXACT_V3_HEADER_LEN == 20);
    assert!(PI_AFTER_COMMIT + 8 == FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_INPUT_COUNT);
};

/// Strict, code-owned FNSP-v3 carrier.
///
/// Canonical little-endian wire:
///
/// ```text
/// "FNSP" || 3:u8 || reserved:[0;3] || root_height:u64
///        || inner_proof_len:u32 || inner_proof_bytes
/// ```
///
/// No proof-controlled predicate name, descriptor name, or verification-key bytes are present.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaithfulNoteSpendExactV3ProofCarrier {
    root_height: u64,
    inner_proof_bytes: Vec<u8>,
}

impl FaithfulNoteSpendExactV3ProofCarrier {
    pub fn new(
        root_height: u64,
        inner_proof_bytes: Vec<u8>,
    ) -> Result<Self, FaithfulNoteSpendExactV3Error> {
        validate_proof_len(inner_proof_bytes.len())?;
        Ok(Self {
            root_height,
            inner_proof_bytes,
        })
    }

    pub const fn root_height(&self) -> u64 {
        self.root_height
    }

    pub fn inner_proof_bytes(&self) -> &[u8] {
        &self.inner_proof_bytes
    }

    pub fn into_inner_proof_bytes(self) -> Vec<u8> {
        self.inner_proof_bytes
    }

    pub fn encode(&self) -> Vec<u8> {
        let proof_len = u32::try_from(self.inner_proof_bytes.len())
            .expect("validated exact FNSP-v3 proof length fits u32");
        let mut out =
            Vec::with_capacity(FAITHFUL_NOTE_SPEND_EXACT_V3_HEADER_LEN + proof_len as usize);
        out.extend_from_slice(&FAITHFUL_NOTE_SPEND_EXACT_V3_MAGIC);
        out.push(FAITHFUL_NOTE_SPEND_EXACT_V3_VERSION);
        out.extend_from_slice(&[0; RESERVED_LEN]);
        out.extend_from_slice(&self.root_height.to_le_bytes());
        out.extend_from_slice(&proof_len.to_le_bytes());
        out.extend_from_slice(&self.inner_proof_bytes);
        out
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, FaithfulNoteSpendExactV3Error> {
        if bytes.len() < FAITHFUL_NOTE_SPEND_EXACT_V3_HEADER_LEN {
            return Err(FaithfulNoteSpendExactV3Error::Truncated {
                needed: FAITHFUL_NOTE_SPEND_EXACT_V3_HEADER_LEN,
                actual: bytes.len(),
            });
        }
        if bytes[..FAITHFUL_NOTE_SPEND_EXACT_V3_MAGIC.len()] != FAITHFUL_NOTE_SPEND_EXACT_V3_MAGIC {
            return Err(FaithfulNoteSpendExactV3Error::InvalidMagic);
        }
        let version = bytes[VERSION_OFFSET];
        if version != FAITHFUL_NOTE_SPEND_EXACT_V3_VERSION {
            return Err(FaithfulNoteSpendExactV3Error::UnsupportedVersion(version));
        }
        let reserved: [u8; RESERVED_LEN] = bytes[RESERVED_OFFSET..ROOT_HEIGHT_OFFSET]
            .try_into()
            .expect("fixed exact FNSP-v3 reserved field");
        if reserved != [0; RESERVED_LEN] {
            return Err(FaithfulNoteSpendExactV3Error::NonZeroReserved(reserved));
        }
        let root_height = u64::from_le_bytes(
            bytes[ROOT_HEIGHT_OFFSET..PROOF_LEN_OFFSET]
                .try_into()
                .expect("fixed exact FNSP-v3 root height"),
        );
        let proof_len = u32::from_le_bytes(
            bytes[PROOF_LEN_OFFSET..FAITHFUL_NOTE_SPEND_EXACT_V3_HEADER_LEN]
                .try_into()
                .expect("fixed exact FNSP-v3 proof length"),
        ) as usize;
        validate_proof_len(proof_len)?;
        let expected = FAITHFUL_NOTE_SPEND_EXACT_V3_HEADER_LEN + proof_len;
        if bytes.len() < expected {
            return Err(FaithfulNoteSpendExactV3Error::Truncated {
                needed: expected,
                actual: bytes.len(),
            });
        }
        if bytes.len() > expected {
            return Err(FaithfulNoteSpendExactV3Error::TrailingBytes {
                expected,
                actual: bytes.len(),
            });
        }
        Self::new(
            root_height,
            bytes[FAITHFUL_NOTE_SPEND_EXACT_V3_HEADER_LEN..].to_vec(),
        )
    }
}

/// Exact state inputs obtained from validated transition and rotated-trace producers.
///
/// Fields are private so the normal constructor cannot smuggle proof-controlled roots, counts, or
/// state commitments into the public statement.  The constructor also refuses a transition and
/// rotated witness that came from different pre/post exact accumulator states.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FaithfulNoteSpendExactV3StateInputs {
    prior_root: [u32; 8],
    successor_root: [u32; 8],
    pre_count: u64,
    post_count: u64,
    before_commit: [u32; 8],
    after_commit: [u32; 8],
}

impl FaithfulNoteSpendExactV3StateInputs {
    pub fn derive(
        transition: &ValidatedExactAafiTransition,
        rotated: &ExactAafiRotatedTraceWitness,
    ) -> Result<Self, FaithfulNoteSpendExactV3Error> {
        let expected_before = exact_state_commit(transition.prior_root(), transition.prior_count());
        let expected_after =
            exact_state_commit(transition.successor_root(), transition.successor_count());
        for (lane, offset) in NULLIFIER_OFFSETS.iter().copied().enumerate() {
            if rotated.before_payload()[offset] != expected_before[lane]
                || rotated.after_payload()[offset] != expected_after[lane]
            {
                return Err(FaithfulNoteSpendExactV3Error::StateProducerMismatch { lane });
            }
        }
        Ok(Self {
            prior_root: transition.prior_root().map(|felt| felt.as_u32()),
            successor_root: transition.successor_root().map(|felt| felt.as_u32()),
            pre_count: transition.prior_count(),
            post_count: transition.successor_count(),
            before_commit: rotated.before_commit().map(|felt| felt.as_u32()),
            after_commit: rotated.after_commit().map(|felt| felt.as_u32()),
        })
    }
}

/// Exact 76-lane public statement for the staged v3 predicate.
///
/// Construction consumes signed `Effect::NoteSpend` fields and the independently derived state
/// object above.  The proof bytes contribute only `root_height`, never roots, counts, outer
/// commitments, predicate identity, or a VK.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FaithfulNoteSpendExactV3PublicStatement {
    lanes: [u32; FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_INPUT_COUNT],
}

impl FaithfulNoteSpendExactV3PublicStatement {
    pub fn from_signed_effect(
        effect: &Effect,
        state: &FaithfulNoteSpendExactV3StateInputs,
    ) -> Result<Self, FaithfulNoteSpendExactV3Error> {
        let Effect::NoteSpend {
            nullifier,
            note_tree_root,
            value,
            asset_type,
            spending_proof,
            ..
        } = effect
        else {
            return Err(FaithfulNoteSpendExactV3Error::NotNoteSpend);
        };
        let carrier = FaithfulNoteSpendExactV3ProofCarrier::decode(spending_proof)?;
        validate_root8_bytes("historical note", note_tree_root)?;

        let mut lanes = [0u32; FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_INPUT_COUNT];
        write_u64_u16(
            &mut lanes[PI_HEIGHT..PI_HISTORICAL_ROOT],
            carrier.root_height(),
        );
        write_root8_bytes(&mut lanes[PI_HISTORICAL_ROOT..PI_NULLIFIER], note_tree_root);
        write_bytes32_u16(&mut lanes[PI_NULLIFIER..PI_VALUE], &nullifier.0);
        write_u64_u16(&mut lanes[PI_VALUE..PI_ASSET_TYPE], *value);
        write_u64_u16(&mut lanes[PI_ASSET_TYPE..PI_SUCCESSOR_ROOT], *asset_type);
        lanes[PI_SUCCESSOR_ROOT..PI_PRIOR_ROOT].copy_from_slice(&state.successor_root);
        lanes[PI_PRIOR_ROOT..PI_PRE_COUNT].copy_from_slice(&state.prior_root);
        write_u64_u16(&mut lanes[PI_PRE_COUNT..PI_POST_COUNT], state.pre_count);
        write_u64_u16(
            &mut lanes[PI_POST_COUNT..PI_BEFORE_COMMIT],
            state.post_count,
        );
        lanes[PI_BEFORE_COMMIT..PI_AFTER_COMMIT].copy_from_slice(&state.before_commit);
        lanes[PI_AFTER_COMMIT..].copy_from_slice(&state.after_commit);
        debug_assert!(lanes.iter().all(|lane| *lane < BABYBEAR_P));
        Ok(Self { lanes })
    }

    pub const fn as_u32_array(&self) -> &[u32; FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_INPUT_COUNT] {
        &self.lanes
    }

    pub fn encode_public_inputs(self) -> [u8; FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_WIRE_BYTES] {
        let mut out = [0u8; FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_WIRE_BYTES];
        for (index, value) in self.lanes.into_iter().enumerate() {
            out[index * 4..index * 4 + 4].copy_from_slice(&value.to_le_bytes());
        }
        out
    }

    /// Strictly decode the verifier-facing wire.  This is not an authoring constructor: live
    /// producers must use [`Self::from_signed_effect`] so state fields cannot come from proof bytes.
    pub(crate) fn decode_verifier_wire(
        bytes: &[u8],
    ) -> Result<Self, FaithfulNoteSpendExactV3Error> {
        if bytes.len() != FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_WIRE_BYTES {
            return Err(FaithfulNoteSpendExactV3Error::InvalidPublicWireLength {
                expected: FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_WIRE_BYTES,
                actual: bytes.len(),
            });
        }
        let mut lanes = [0u32; FAITHFUL_NOTE_SPEND_EXACT_V3_PUBLIC_INPUT_COUNT];
        for (index, chunk) in bytes.chunks_exact(4).enumerate() {
            let value = u32::from_le_bytes(chunk.try_into().expect("four-byte public lane"));
            if value >= BABYBEAR_P {
                return Err(FaithfulNoteSpendExactV3Error::NonCanonicalPublicLane {
                    lane: index,
                    value,
                });
            }
            if is_u16_public_lane(index) && value > u16::MAX as u32 {
                return Err(FaithfulNoteSpendExactV3Error::NonCanonicalU16Lane {
                    lane: index,
                    value,
                });
            }
            lanes[index] = value;
        }
        Ok(Self { lanes })
    }
}

fn is_u16_public_lane(lane: usize) -> bool {
    (PI_HEIGHT..PI_HISTORICAL_ROOT).contains(&lane)
        || (PI_NULLIFIER..PI_SUCCESSOR_ROOT).contains(&lane)
        || (PI_PRE_COUNT..PI_BEFORE_COMMIT).contains(&lane)
}

fn write_u64_u16(out: &mut [u32], value: u64) {
    debug_assert_eq!(out.len(), 4);
    for (lane, shift) in [0, 16, 32, 48].into_iter().enumerate() {
        out[lane] = ((value >> shift) & 0xffff) as u32;
    }
}

fn write_bytes32_u16(out: &mut [u32], value: &[u8; 32]) {
    debug_assert_eq!(out.len(), 16);
    for (lane, chunk) in value.chunks_exact(2).enumerate() {
        out[lane] = u16::from_le_bytes([chunk[0], chunk[1]]) as u32;
    }
}

fn write_root8_bytes(out: &mut [u32], value: &[u8; 32]) {
    debug_assert_eq!(out.len(), 8);
    for (lane, chunk) in value.chunks_exact(4).enumerate() {
        out[lane] = u32::from_le_bytes(chunk.try_into().expect("four-byte root lane"));
    }
}

fn validate_root8_bytes(
    name: &'static str,
    value: &[u8; 32],
) -> Result<(), FaithfulNoteSpendExactV3Error> {
    for (lane, chunk) in value.chunks_exact(4).enumerate() {
        let value = u32::from_le_bytes(chunk.try_into().expect("four-byte root lane"));
        if value >= BABYBEAR_P {
            return Err(FaithfulNoteSpendExactV3Error::NonCanonicalRoot { name, lane, value });
        }
    }
    Ok(())
}

fn validate_proof_len(len: usize) -> Result<(), FaithfulNoteSpendExactV3Error> {
    if len == 0 {
        return Err(FaithfulNoteSpendExactV3Error::EmptyProof);
    }
    if len > MAX_EXACT_V3_INNER_PROOF_BYTES {
        return Err(FaithfulNoteSpendExactV3Error::ProofTooLarge {
            actual: len,
            maximum: MAX_EXACT_V3_INNER_PROOF_BYTES,
        });
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FaithfulNoteSpendExactV3Error {
    Truncated {
        needed: usize,
        actual: usize,
    },
    InvalidMagic,
    UnsupportedVersion(u8),
    NonZeroReserved([u8; RESERVED_LEN]),
    EmptyProof,
    ProofTooLarge {
        actual: usize,
        maximum: usize,
    },
    TrailingBytes {
        expected: usize,
        actual: usize,
    },
    NotNoteSpend,
    NonCanonicalRoot {
        name: &'static str,
        lane: usize,
        value: u32,
    },
    StateProducerMismatch {
        lane: usize,
    },
    InvalidPublicWireLength {
        expected: usize,
        actual: usize,
    },
    NonCanonicalPublicLane {
        lane: usize,
        value: u32,
    },
    NonCanonicalU16Lane {
        lane: usize,
        value: u32,
    },
}

impl fmt::Display for FaithfulNoteSpendExactV3Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Truncated { needed, actual } => {
                write!(
                    f,
                    "exact FNSP-v3 carrier truncated: need {needed} bytes, got {actual}"
                )
            }
            Self::InvalidMagic => f.write_str("invalid exact FNSP-v3 carrier magic"),
            Self::UnsupportedVersion(version) => {
                write!(f, "unsupported exact FNSP-v3 carrier version {version}")
            }
            Self::NonZeroReserved(bytes) => {
                write!(f, "exact FNSP-v3 reserved bytes are nonzero: {bytes:?}")
            }
            Self::EmptyProof => f.write_str("exact FNSP-v3 carrier has an empty proof"),
            Self::ProofTooLarge { actual, maximum } => write!(
                f,
                "exact FNSP-v3 proof is {actual} bytes; maximum is {maximum}"
            ),
            Self::TrailingBytes { expected, actual } => write!(
                f,
                "exact FNSP-v3 carrier has trailing bytes: expected {expected}, got {actual}"
            ),
            Self::NotNoteSpend => f.write_str("exact FNSP-v3 statement requires NoteSpend"),
            Self::NonCanonicalRoot { name, lane, value } => {
                write!(
                    f,
                    "exact FNSP-v3 {name} root lane {lane} is noncanonical: {value}"
                )
            }
            Self::StateProducerMismatch { lane } => write!(
                f,
                "exact FNSP-v3 transition/rotated state producers disagree at FNS3 lane {lane}"
            ),
            Self::InvalidPublicWireLength { expected, actual } => write!(
                f,
                "exact FNSP-v3 public wire expects {expected} bytes, got {actual}"
            ),
            Self::NonCanonicalPublicLane { lane, value } => write!(
                f,
                "exact FNSP-v3 public lane {lane} is noncanonical: {value}"
            ),
            Self::NonCanonicalU16Lane { lane, value } => write!(
                f,
                "exact FNSP-v3 u16 public lane {lane} is noncanonical: {value}"
            ),
        }
    }
}

impl std::error::Error for FaithfulNoteSpendExactV3Error {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::action::Event;
    use dregg_cell::{CellId, FIELD_ZERO, Nullifier};
    use dregg_circuit::exact_nullifier_aafi::{ExactNullifierAafi, validate_exact_aafi_witness};
    use dregg_circuit::exact_nullifier_aafi_rotated_trace::{
        ROTATED_PAYLOAD_WIDTH, marshal_exact_aafi_rotated_trace,
    };
    use dregg_circuit::exact_nullifier_aafi_trace::marshal_exact_aafi_trace;
    use dregg_circuit::field::BabyBear;

    fn sample_carrier() -> FaithfulNoteSpendExactV3ProofCarrier {
        FaithfulNoteSpendExactV3ProofCarrier::new(0x1122_3344_5566_7788, vec![1, 2, 3, 4])
            .expect("sample v3 carrier")
    }

    fn derived_state() -> FaithfulNoteSpendExactV3StateInputs {
        let witness = ExactNullifierAafi::new()
            .prepare_insert([0x5a; 32], 0x8877_6655_4433_2211)
            .expect("fresh exact insertion");
        let validated = validate_exact_aafi_witness(&witness).expect("valid exact witness");
        let core = marshal_exact_aafi_trace(&witness).expect("valid exact trace");
        let mut before = [BabyBear::ZERO; ROTATED_PAYLOAD_WIDTH];
        for (lane, offset) in NULLIFIER_OFFSETS.iter().copied().enumerate() {
            before[offset] = witness.prior_state_commit[lane];
        }
        let rotated = marshal_exact_aafi_rotated_trace(&core, before).expect("valid rotated trace");
        FaithfulNoteSpendExactV3StateInputs::derive(&validated, &rotated)
            .expect("matching producers derive state")
    }

    fn note_spend(carrier: &FaithfulNoteSpendExactV3ProofCarrier) -> Effect {
        let mut note_tree_root = [0u8; 32];
        for lane in 0..8 {
            note_tree_root[lane * 4..lane * 4 + 4]
                .copy_from_slice(&(100 + lane as u32).to_le_bytes());
        }
        Effect::NoteSpend {
            nullifier: Nullifier([0x5a; 32]),
            note_tree_root,
            value: 0x8877_6655_4433_2211,
            asset_type: 0x0123_4567_89ab_cdef,
            spending_proof: carrier.encode(),
            value_commitment: None,
        }
    }

    #[test]
    fn v3_carrier_round_trips_and_v2_cross_route_refuses() {
        let carrier = sample_carrier();
        let bytes = carrier.encode();
        assert_eq!(bytes.len(), FAITHFUL_NOTE_SPEND_EXACT_V3_HEADER_LEN + 4);
        assert_eq!(&bytes[..4], b"FNSP");
        assert_eq!(bytes[VERSION_OFFSET], 3);
        assert_eq!(
            FaithfulNoteSpendExactV3ProofCarrier::decode(&bytes),
            Ok(carrier)
        );
        assert!(matches!(
            crate::faithful_note_spend::FaithfulNoteSpendProofCarrier::decode(&bytes),
            Err(crate::faithful_note_spend::FaithfulNoteSpendCarrierError::Truncated { .. })
                | Err(
                    crate::faithful_note_spend::FaithfulNoteSpendCarrierError::UnsupportedVersion(
                        3
                    )
                )
        ));

        let v2 = crate::faithful_note_spend::FaithfulNoteSpendProofCarrier::new(
            7,
            dregg_circuit::Faithful8::ZERO.to_bytes32(),
            vec![9],
        )
        .expect("v2 fixture")
        .encode();
        assert!(matches!(
            FaithfulNoteSpendExactV3ProofCarrier::decode(&v2),
            Err(FaithfulNoteSpendExactV3Error::UnsupportedVersion(2))
        ));
    }

    #[test]
    fn v3_carrier_refuses_malformed_noncanonical_and_unbounded_wires() {
        let encoded = sample_carrier().encode();
        for end in 0..encoded.len() {
            assert!(matches!(
                FaithfulNoteSpendExactV3ProofCarrier::decode(&encoded[..end]),
                Err(FaithfulNoteSpendExactV3Error::Truncated { .. })
            ));
        }
        let mut trailing = encoded.clone();
        trailing.push(0);
        assert!(matches!(
            FaithfulNoteSpendExactV3ProofCarrier::decode(&trailing),
            Err(FaithfulNoteSpendExactV3Error::TrailingBytes { .. })
        ));
        let mut reserved = encoded.clone();
        reserved[RESERVED_OFFSET] = 1;
        assert!(matches!(
            FaithfulNoteSpendExactV3ProofCarrier::decode(&reserved),
            Err(FaithfulNoteSpendExactV3Error::NonZeroReserved([1, 0, 0]))
        ));
        let mut empty = encoded.clone();
        empty[PROOF_LEN_OFFSET..FAITHFUL_NOTE_SPEND_EXACT_V3_HEADER_LEN]
            .copy_from_slice(&0u32.to_le_bytes());
        assert!(matches!(
            FaithfulNoteSpendExactV3ProofCarrier::decode(&empty),
            Err(FaithfulNoteSpendExactV3Error::EmptyProof)
        ));
        let mut oversized = encoded;
        oversized[PROOF_LEN_OFFSET..FAITHFUL_NOTE_SPEND_EXACT_V3_HEADER_LEN].copy_from_slice(
            &u32::try_from(MAX_EXACT_V3_INNER_PROOF_BYTES + 1)
                .expect("bound fits u32")
                .to_le_bytes(),
        );
        assert!(matches!(
            FaithfulNoteSpendExactV3ProofCarrier::decode(&oversized),
            Err(FaithfulNoteSpendExactV3Error::ProofTooLarge { .. })
        ));
    }

    #[test]
    fn signed_effect_and_derived_state_make_exact_canonical_76_lane_statement() {
        let carrier = sample_carrier();
        let state = derived_state();
        let statement = FaithfulNoteSpendExactV3PublicStatement::from_signed_effect(
            &note_spend(&carrier),
            &state,
        )
        .expect("signed effect plus derived state");
        let lanes = statement.as_u32_array();
        assert_eq!(
            &lanes[PI_HEIGHT..PI_HISTORICAL_ROOT],
            &[0x7788, 0x5566, 0x3344, 0x1122]
        );
        assert_eq!(
            &lanes[PI_HISTORICAL_ROOT..PI_NULLIFIER],
            &[100, 101, 102, 103, 104, 105, 106, 107]
        );
        assert_eq!(
            &lanes[PI_SUCCESSOR_ROOT..PI_PRIOR_ROOT],
            &state.successor_root
        );
        assert_eq!(&lanes[PI_PRIOR_ROOT..PI_PRE_COUNT], &state.prior_root);
        assert_eq!(
            &lanes[PI_BEFORE_COMMIT..PI_AFTER_COMMIT],
            &state.before_commit
        );
        assert_eq!(&lanes[PI_AFTER_COMMIT..], &state.after_commit);

        let wire = statement.encode_public_inputs();
        assert_eq!(wire.len(), 76 * 4);
        assert_eq!(
            FaithfulNoteSpendExactV3PublicStatement::decode_verifier_wire(&wire),
            Ok(statement)
        );
        assert!(
            FaithfulNoteSpendExactV3PublicStatement::decode_verifier_wire(&wire[..wire.len() - 1])
                .is_err()
        );
        let mut noncanonical = wire;
        noncanonical[PI_PRIOR_ROOT * 4..PI_PRIOR_ROOT * 4 + 4]
            .copy_from_slice(&BABYBEAR_P.to_le_bytes());
        assert!(matches!(
            FaithfulNoteSpendExactV3PublicStatement::decode_verifier_wire(&noncanonical),
            Err(FaithfulNoteSpendExactV3Error::NonCanonicalPublicLane {
                lane: PI_PRIOR_ROOT,
                ..
            })
        ));
        let mut noncanonical_u16 = wire;
        noncanonical_u16[PI_HEIGHT * 4..PI_HEIGHT * 4 + 4]
            .copy_from_slice(&(u16::MAX as u32 + 1).to_le_bytes());
        assert!(matches!(
            FaithfulNoteSpendExactV3PublicStatement::decode_verifier_wire(&noncanonical_u16),
            Err(FaithfulNoteSpendExactV3Error::NonCanonicalU16Lane {
                lane: PI_HEIGHT,
                ..
            })
        ));
    }

    #[test]
    fn statement_refuses_non_note_effect_and_noncanonical_signed_root() {
        let state = derived_state();
        let carrier = sample_carrier();
        let other = Effect::EmitEvent {
            cell: CellId::from_bytes([0; 32]),
            event: Event {
                topic: [0; 32],
                data: vec![FIELD_ZERO],
            },
        };
        assert!(matches!(
            FaithfulNoteSpendExactV3PublicStatement::from_signed_effect(&other, &state),
            Err(FaithfulNoteSpendExactV3Error::NotNoteSpend)
        ));

        let mut effect = note_spend(&carrier);
        if let Effect::NoteSpend { note_tree_root, .. } = &mut effect {
            note_tree_root[..4].copy_from_slice(&BABYBEAR_P.to_le_bytes());
        }
        assert!(matches!(
            FaithfulNoteSpendExactV3PublicStatement::from_signed_effect(&effect, &state),
            Err(FaithfulNoteSpendExactV3Error::NonCanonicalRoot { lane: 0, .. })
        ));
    }

    #[test]
    fn derived_state_refuses_mixed_transition_and_rotated_producers() {
        let witness_a = ExactNullifierAafi::new()
            .prepare_insert([1; 32], 7)
            .expect("transition A");
        let witness_b = ExactNullifierAafi::new()
            .prepare_insert([2; 32], 7)
            .expect("transition B");
        let validated_a = validate_exact_aafi_witness(&witness_a).expect("valid A");
        let core_b = marshal_exact_aafi_trace(&witness_b).expect("trace B");
        let mut before_b = [BabyBear::ZERO; ROTATED_PAYLOAD_WIDTH];
        for (lane, offset) in NULLIFIER_OFFSETS.iter().copied().enumerate() {
            before_b[offset] = witness_b.prior_state_commit[lane];
        }
        let rotated_b = marshal_exact_aafi_rotated_trace(&core_b, before_b).expect("rotated B");
        assert!(matches!(
            FaithfulNoteSpendExactV3StateInputs::derive(&validated_a, &rotated_b),
            Err(FaithfulNoteSpendExactV3Error::StateProducerMismatch { .. })
        ));
    }
}
