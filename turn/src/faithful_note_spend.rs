//! Versioned carrier for a `NoteSpend` proof against historical faithful note-root state.
//!
//! The carrier is deliberately independent of [`crate::action::Effect`]. It can be placed in
//! the existing opaque `NoteSpend::spending_proof` bytes without changing the effect schema or
//! executor dispatch. The carrier and its canonical public-statement lowering bind the inner
//! proof to the exact historical frontier and exact successor state that finalization resolves.

use core::fmt;

/// Domain tag at the start of every faithful note-spend proof carrier.
pub const FAITHFUL_NOTE_SPEND_MAGIC: [u8; 4] = *b"FNSP";

/// Executor-owned predicate identity for the v2 faithful hidden spend relation.
///
/// This name is never accepted from proof bytes.  The production verifier maps
/// it to one exact Lean-emitted descriptor and one exact HidingFRI config.
pub const FAITHFUL_NOTE_SPEND_PREDICATE: &str = "faithful-note-spend-v2::exact-note16-root8-hiding";

/// Number of BabyBear public inputs in the exact faithful-spend statement:
/// `height_u16[4] || historical_root8 || nullifier_u16[16] || value_u16[4]
/// || asset_type_u16[4] || successor_nullifier_root8`.
pub const FAITHFUL_NOTE_SPEND_PUBLIC_INPUT_COUNT: usize = 44;

/// Wire version emitted and accepted by this module.
///
/// Version 2 adds the exact faithful-eight successor nullifier root.  There is
/// deliberately no v1 compatibility decoder: a proof that does not bind the
/// state transition which finalization persists is not a faithful spend proof.
pub const FAITHFUL_NOTE_SPEND_VERSION: u8 = 2;

/// Maximum accepted size of the opaque inner proof (4 MiB).
///
/// IR-v2 batch proofs may legitimately exceed a few hundred KiB.  This keeps a
/// strict hostile-allocation ceiling without excluding the existing prover's
/// larger note-spend instances.
pub const MAX_INNER_PROOF_BYTES: usize = 4 * 1024 * 1024;

const RESERVED_LEN: usize = 3;
const PROOF_LEN_LEN: usize = size_of::<u32>();
const FAITHFUL_ROOT_BYTES: usize = 32;

/// Number of bytes before the opaque inner proof.
pub const FAITHFUL_NOTE_SPEND_HEADER_LEN: usize = FAITHFUL_NOTE_SPEND_MAGIC.len()
    + size_of::<u8>()
    + RESERVED_LEN
    + size_of::<u64>()
    + FAITHFUL_ROOT_BYTES
    + PROOF_LEN_LEN;

const VERSION_OFFSET: usize = FAITHFUL_NOTE_SPEND_MAGIC.len();
const RESERVED_OFFSET: usize = VERSION_OFFSET + size_of::<u8>();
const ROOT_HEIGHT_OFFSET: usize = RESERVED_OFFSET + RESERVED_LEN;
const SUCCESSOR_ROOT_OFFSET: usize = ROOT_HEIGHT_OFFSET + size_of::<u64>();
const PROOF_LEN_OFFSET: usize = SUCCESSOR_ROOT_OFFSET + FAITHFUL_ROOT_BYTES;

/// A validated proof carrier tied to one historical faithful note-root height.
///
/// Wire layout (all integers little-endian):
///
/// ```text
/// "FNSP" || version:u8 || reserved:[0;3] || root_height:u64
///        || successor_nullifier_root8:[u8;32]
///        || inner_proof_len:u32 || inner_proof_bytes
/// ```
///
/// `inner_proof_bytes` is always non-empty and no larger than
/// [`MAX_INNER_PROOF_BYTES`]. Decoding consumes the entire input; trailing bytes
/// are never ignored.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaithfulNoteSpendProofCarrier {
    root_height: u64,
    successor_nullifier_root: [u8; FAITHFUL_ROOT_BYTES],
    inner_proof_bytes: Vec<u8>,
}

impl FaithfulNoteSpendProofCarrier {
    /// Construct a carrier after enforcing the inner-proof size invariant.
    pub fn new(
        root_height: u64,
        successor_nullifier_root: [u8; FAITHFUL_ROOT_BYTES],
        inner_proof_bytes: Vec<u8>,
    ) -> Result<Self, FaithfulNoteSpendCarrierError> {
        validate_faithful_root(&successor_nullifier_root)?;
        validate_proof_len(inner_proof_bytes.len())?;
        Ok(Self {
            root_height,
            successor_nullifier_root,
            inner_proof_bytes,
        })
    }

    /// Historical faithful note-root height against which the proof was made.
    pub const fn root_height(&self) -> u64 {
        self.root_height
    }

    /// Exact successor of the spent-nullifier accumulator claimed by the proof.
    ///
    /// Full-node finalization recomputes this root from durable pre-state plus
    /// the signed turn's exact `(nullifier, value)` records and requires byte
    /// equality before committing either state or receipt.
    pub const fn successor_nullifier_root(&self) -> [u8; FAITHFUL_ROOT_BYTES] {
        self.successor_nullifier_root
    }

    /// Opaque proof understood by the note-spend verifier.
    pub fn inner_proof_bytes(&self) -> &[u8] {
        &self.inner_proof_bytes
    }

    /// Consume the carrier and return its opaque inner proof.
    pub fn into_inner_proof_bytes(self) -> Vec<u8> {
        self.inner_proof_bytes
    }

    /// Encode the canonical v2 wire form.
    pub fn encode(&self) -> Vec<u8> {
        let proof_len = u32::try_from(self.inner_proof_bytes.len())
            .expect("validated faithful note-spend proof length fits u32");
        let mut out = Vec::with_capacity(FAITHFUL_NOTE_SPEND_HEADER_LEN + proof_len as usize);
        out.extend_from_slice(&FAITHFUL_NOTE_SPEND_MAGIC);
        out.push(FAITHFUL_NOTE_SPEND_VERSION);
        out.extend_from_slice(&[0; RESERVED_LEN]);
        out.extend_from_slice(&self.root_height.to_le_bytes());
        out.extend_from_slice(&self.successor_nullifier_root);
        out.extend_from_slice(&proof_len.to_le_bytes());
        out.extend_from_slice(&self.inner_proof_bytes);
        out
    }

    /// Decode one canonical v2 carrier, rejecting malformed or non-canonical input.
    pub fn decode(bytes: &[u8]) -> Result<Self, FaithfulNoteSpendCarrierError> {
        if bytes.len() < FAITHFUL_NOTE_SPEND_HEADER_LEN {
            return Err(FaithfulNoteSpendCarrierError::Truncated {
                needed: FAITHFUL_NOTE_SPEND_HEADER_LEN,
                actual: bytes.len(),
            });
        }

        if bytes[..FAITHFUL_NOTE_SPEND_MAGIC.len()] != FAITHFUL_NOTE_SPEND_MAGIC {
            return Err(FaithfulNoteSpendCarrierError::InvalidMagic);
        }

        let version = bytes[VERSION_OFFSET];
        if version != FAITHFUL_NOTE_SPEND_VERSION {
            return Err(FaithfulNoteSpendCarrierError::UnsupportedVersion(version));
        }

        let reserved: [u8; RESERVED_LEN] = bytes[RESERVED_OFFSET..RESERVED_OFFSET + RESERVED_LEN]
            .try_into()
            .expect("fixed faithful note-spend reserved field");
        if reserved != [0; RESERVED_LEN] {
            return Err(FaithfulNoteSpendCarrierError::NonZeroReserved(reserved));
        }

        let root_height = u64::from_le_bytes(
            bytes[ROOT_HEIGHT_OFFSET..ROOT_HEIGHT_OFFSET + size_of::<u64>()]
                .try_into()
                .expect("fixed faithful note-spend root-height field"),
        );
        let successor_nullifier_root: [u8; FAITHFUL_ROOT_BYTES] = bytes
            [SUCCESSOR_ROOT_OFFSET..PROOF_LEN_OFFSET]
            .try_into()
            .expect("fixed faithful note-spend successor-root field");
        validate_faithful_root(&successor_nullifier_root)?;
        let proof_len = u32::from_le_bytes(
            bytes[PROOF_LEN_OFFSET..PROOF_LEN_OFFSET + PROOF_LEN_LEN]
                .try_into()
                .expect("fixed faithful note-spend proof-length field"),
        ) as usize;
        validate_proof_len(proof_len)?;

        let expected_len = FAITHFUL_NOTE_SPEND_HEADER_LEN + proof_len;
        if bytes.len() < expected_len {
            return Err(FaithfulNoteSpendCarrierError::Truncated {
                needed: expected_len,
                actual: bytes.len(),
            });
        }
        if bytes.len() > expected_len {
            return Err(FaithfulNoteSpendCarrierError::TrailingBytes {
                expected: expected_len,
                actual: bytes.len(),
            });
        }

        Self::new(
            root_height,
            successor_nullifier_root,
            bytes[FAITHFUL_NOTE_SPEND_HEADER_LEN..].to_vec(),
        )
    }
}

/// Exact public statement passed to the predicate-specific HidingFRI verifier.
///
/// Byte strings use injective sixteen-`u16` decomposition.  Full `u64`s use
/// four `u16` limbs.  Root octets remain canonical BabyBear `u32`s; unlike a
/// generic `BabyBear::new`, this lowering never reduces an attacker value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FaithfulNoteSpendPublicStatement {
    pub root_height: u64,
    pub historical_note_root: [u8; 32],
    pub nullifier: [u8; 32],
    pub value: u64,
    pub asset_type: u64,
    pub successor_nullifier_root: [u8; 32],
}

impl FaithfulNoteSpendPublicStatement {
    /// Construct the proof statement from signed effect fields plus the strict
    /// FNSP transition claim.
    pub fn from_effect(
        carrier: &FaithfulNoteSpendProofCarrier,
        historical_note_root: [u8; 32],
        nullifier: [u8; 32],
        value: u64,
        asset_type: u64,
    ) -> Result<Self, FaithfulNoteSpendCarrierError> {
        validate_root_named("historical note", &historical_note_root)?;
        Ok(Self {
            root_height: carrier.root_height(),
            historical_note_root,
            nullifier,
            value,
            asset_type,
            successor_nullifier_root: carrier.successor_nullifier_root(),
        })
    }

    /// Canonical verifier ABI: one little-endian `u32` per BabyBear PI.
    pub fn encode_public_inputs(self) -> Vec<u8> {
        let mut felts = Vec::with_capacity(FAITHFUL_NOTE_SPEND_PUBLIC_INPUT_COUNT);
        push_u64_u16(&mut felts, self.root_height);
        push_root8(&mut felts, &self.historical_note_root);
        push_bytes32_u16(&mut felts, &self.nullifier);
        push_u64_u16(&mut felts, self.value);
        push_u64_u16(&mut felts, self.asset_type);
        push_root8(&mut felts, &self.successor_nullifier_root);
        debug_assert_eq!(felts.len(), FAITHFUL_NOTE_SPEND_PUBLIC_INPUT_COUNT);

        let mut out = Vec::with_capacity(felts.len() * 4);
        for felt in felts {
            out.extend_from_slice(&felt.to_le_bytes());
        }
        out
    }
}

fn push_u64_u16(out: &mut Vec<u32>, value: u64) {
    for shift in [0, 16, 32, 48] {
        out.push(((value >> shift) & 0xffff) as u32);
    }
}

fn push_bytes32_u16(out: &mut Vec<u32>, value: &[u8; 32]) {
    for chunk in value.chunks_exact(2) {
        out.push(u16::from_le_bytes([chunk[0], chunk[1]]) as u32);
    }
}

fn push_root8(out: &mut Vec<u32>, root: &[u8; 32]) {
    for chunk in root.chunks_exact(4) {
        out.push(u32::from_le_bytes(
            chunk.try_into().expect("four-byte root lane"),
        ));
    }
}

fn validate_faithful_root(
    root: &[u8; FAITHFUL_ROOT_BYTES],
) -> Result<(), FaithfulNoteSpendCarrierError> {
    validate_root_named("successor nullifier", root)
}

fn validate_root_named(
    root_name: &'static str,
    root: &[u8; FAITHFUL_ROOT_BYTES],
) -> Result<(), FaithfulNoteSpendCarrierError> {
    for (lane, bytes) in root.chunks_exact(4).enumerate() {
        let value = u32::from_le_bytes(bytes.try_into().expect("four-byte root lane"));
        if value >= dregg_circuit::field::BABYBEAR_P {
            return Err(FaithfulNoteSpendCarrierError::NonCanonicalRoot {
                root_name,
                lane,
                value,
            });
        }
    }
    Ok(())
}

fn validate_proof_len(len: usize) -> Result<(), FaithfulNoteSpendCarrierError> {
    if len == 0 {
        return Err(FaithfulNoteSpendCarrierError::EmptyProof);
    }
    if len > MAX_INNER_PROOF_BYTES {
        return Err(FaithfulNoteSpendCarrierError::ProofTooLarge {
            actual: len,
            maximum: MAX_INNER_PROOF_BYTES,
        });
    }
    Ok(())
}

/// Strict carrier construction/decoding failure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FaithfulNoteSpendCarrierError {
    /// The byte string ended before the declared carrier did.
    Truncated { needed: usize, actual: usize },
    /// The four-byte domain tag was not [`FAITHFUL_NOTE_SPEND_MAGIC`].
    InvalidMagic,
    /// Only [`FAITHFUL_NOTE_SPEND_VERSION`] is currently supported.
    UnsupportedVersion(u8),
    /// Reserved bytes must remain zero until a future version assigns them meaning.
    NonZeroReserved([u8; RESERVED_LEN]),
    /// Every faithful-eight root lane must be a canonical BabyBear encoding.
    NonCanonicalRoot {
        root_name: &'static str,
        lane: usize,
        value: u32,
    },
    /// A proof carrier without an inner proof is invalid.
    EmptyProof,
    /// The inner proof exceeded the resource ceiling.
    ProofTooLarge { actual: usize, maximum: usize },
    /// Canonical decoding consumes the whole byte string.
    TrailingBytes { expected: usize, actual: usize },
}

impl fmt::Display for FaithfulNoteSpendCarrierError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Truncated { needed, actual } => {
                write!(
                    f,
                    "faithful note-spend carrier truncated: need {needed} bytes, got {actual}"
                )
            }
            Self::InvalidMagic => f.write_str("invalid faithful note-spend carrier magic"),
            Self::UnsupportedVersion(version) => {
                write!(
                    f,
                    "unsupported faithful note-spend carrier version {version}"
                )
            }
            Self::NonZeroReserved(reserved) => write!(
                f,
                "faithful note-spend carrier reserved bytes are nonzero: {reserved:?}"
            ),
            Self::NonCanonicalRoot {
                root_name,
                lane,
                value,
            } => write!(
                f,
                "faithful note-spend {root_name} root lane {lane} is noncanonical: {value}"
            ),
            Self::EmptyProof => f.write_str("faithful note-spend carrier has an empty inner proof"),
            Self::ProofTooLarge { actual, maximum } => write!(
                f,
                "faithful note-spend inner proof is {actual} bytes; maximum is {maximum}"
            ),
            Self::TrailingBytes { expected, actual } => write!(
                f,
                "faithful note-spend carrier has trailing bytes: expected {expected}, got {actual}"
            ),
        }
    }
}

impl std::error::Error for FaithfulNoteSpendCarrierError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> FaithfulNoteSpendProofCarrier {
        FaithfulNoteSpendProofCarrier::new(
            42,
            dregg_circuit::Faithful8::ZERO.to_bytes32(),
            vec![0xde, 0xad, 0xbe, 0xef],
        )
        .expect("valid carrier")
    }

    #[test]
    fn carrier_round_trips_canonical_v2_bytes() {
        let carrier = sample();
        let encoded = carrier.encode();

        assert_eq!(&encoded[..4], b"FNSP");
        assert_eq!(encoded[VERSION_OFFSET], 2);
        assert_eq!(
            &encoded[RESERVED_OFFSET..ROOT_HEIGHT_OFFSET],
            &[0; RESERVED_LEN]
        );
        assert_eq!(
            &encoded[ROOT_HEIGHT_OFFSET..SUCCESSOR_ROOT_OFFSET],
            &42u64.to_le_bytes()
        );
        assert_eq!(
            &encoded[SUCCESSOR_ROOT_OFFSET..PROOF_LEN_OFFSET],
            &dregg_circuit::Faithful8::ZERO.to_bytes32()
        );
        assert_eq!(FaithfulNoteSpendProofCarrier::decode(&encoded), Ok(carrier));
    }

    #[test]
    fn construction_rejects_empty_and_oversized_proofs() {
        assert_eq!(
            FaithfulNoteSpendProofCarrier::new(0, [0; 32], Vec::new()),
            Err(FaithfulNoteSpendCarrierError::EmptyProof)
        );
        assert_eq!(
            FaithfulNoteSpendProofCarrier::new(0, [0; 32], vec![0; MAX_INNER_PROOF_BYTES + 1],),
            Err(FaithfulNoteSpendCarrierError::ProofTooLarge {
                actual: MAX_INNER_PROOF_BYTES + 1,
                maximum: MAX_INNER_PROOF_BYTES,
            })
        );
    }

    #[test]
    fn decode_rejects_truncation_and_trailing_bytes() {
        let encoded = sample().encode();
        for prefix_len in 0..encoded.len() {
            assert!(matches!(
                FaithfulNoteSpendProofCarrier::decode(&encoded[..prefix_len]),
                Err(FaithfulNoteSpendCarrierError::Truncated { .. })
            ));
        }

        let mut with_trailer = encoded;
        with_trailer.push(0);
        assert!(matches!(
            FaithfulNoteSpendProofCarrier::decode(&with_trailer),
            Err(FaithfulNoteSpendCarrierError::TrailingBytes { .. })
        ));
    }

    #[test]
    fn decode_rejects_unknown_version_and_nonzero_reserved_bytes() {
        let mut invalid_magic = sample().encode();
        invalid_magic[0] ^= 1;
        assert_eq!(
            FaithfulNoteSpendProofCarrier::decode(&invalid_magic),
            Err(FaithfulNoteSpendCarrierError::InvalidMagic)
        );

        let mut noncanonical_root = sample().encode();
        noncanonical_root[SUCCESSOR_ROOT_OFFSET..SUCCESSOR_ROOT_OFFSET + 4]
            .copy_from_slice(&dregg_circuit::field::BABYBEAR_P.to_le_bytes());
        assert_eq!(
            FaithfulNoteSpendProofCarrier::decode(&noncanonical_root),
            Err(FaithfulNoteSpendCarrierError::NonCanonicalRoot {
                root_name: "successor nullifier",
                lane: 0,
                value: dregg_circuit::field::BABYBEAR_P,
            })
        );

        let mut unknown_version = sample().encode();
        unknown_version[VERSION_OFFSET] = FAITHFUL_NOTE_SPEND_VERSION + 1;
        assert_eq!(
            FaithfulNoteSpendProofCarrier::decode(&unknown_version),
            Err(FaithfulNoteSpendCarrierError::UnsupportedVersion(3))
        );

        let mut nonzero_reserved = sample().encode();
        nonzero_reserved[RESERVED_OFFSET + 1] = 7;
        assert_eq!(
            FaithfulNoteSpendProofCarrier::decode(&nonzero_reserved),
            Err(FaithfulNoteSpendCarrierError::NonZeroReserved([0, 7, 0]))
        );
    }

    #[test]
    fn decode_rejects_empty_and_declared_oversized_proofs() {
        let mut empty = sample().encode();
        empty[PROOF_LEN_OFFSET..FAITHFUL_NOTE_SPEND_HEADER_LEN]
            .copy_from_slice(&0u32.to_le_bytes());
        assert_eq!(
            FaithfulNoteSpendProofCarrier::decode(&empty),
            Err(FaithfulNoteSpendCarrierError::EmptyProof)
        );

        let mut oversized = sample().encode();
        let declared = u32::try_from(MAX_INNER_PROOF_BYTES + 1).expect("maximum fits u32");
        oversized[PROOF_LEN_OFFSET..FAITHFUL_NOTE_SPEND_HEADER_LEN]
            .copy_from_slice(&declared.to_le_bytes());
        assert_eq!(
            FaithfulNoteSpendProofCarrier::decode(&oversized),
            Err(FaithfulNoteSpendCarrierError::ProofTooLarge {
                actual: MAX_INNER_PROOF_BYTES + 1,
                maximum: MAX_INNER_PROOF_BYTES,
            })
        );
    }

    #[test]
    fn public_statement_is_exact_44_felts_and_rejects_root_aliases() {
        let carrier = sample();
        let mut historical = [0u8; 32];
        for lane in 0..8 {
            historical[lane * 4..lane * 4 + 4].copy_from_slice(&(100 + lane as u32).to_le_bytes());
        }
        let statement = FaithfulNoteSpendPublicStatement::from_effect(
            &carrier,
            historical,
            core::array::from_fn(|i| i as u8),
            0xfedc_ba98_7654_3210,
            0x0123_4567_89ab_cdef,
        )
        .unwrap();
        let bytes = statement.encode_public_inputs();
        assert_eq!(bytes.len(), 4 * FAITHFUL_NOTE_SPEND_PUBLIC_INPUT_COUNT);
        let pis: Vec<u32> = bytes
            .chunks_exact(4)
            .map(|chunk| u32::from_le_bytes(chunk.try_into().unwrap()))
            .collect();
        assert_eq!(&pis[0..4], &[42, 0, 0, 0]);
        assert_eq!(&pis[4..12], &[100, 101, 102, 103, 104, 105, 106, 107]);
        assert_eq!(&pis[28..32], &[0x3210, 0x7654, 0xba98, 0xfedc]);
        assert_eq!(&pis[32..36], &[0xcdef, 0x89ab, 0x4567, 0x0123]);

        historical[..4].copy_from_slice(&dregg_circuit::field::BABYBEAR_P.to_le_bytes());
        assert!(matches!(
            FaithfulNoteSpendPublicStatement::from_effect(&carrier, historical, [1; 32], 7, 8,),
            Err(FaithfulNoteSpendCarrierError::NonCanonicalRoot {
                root_name: "historical note",
                lane: 0,
                ..
            })
        ));
    }
}
