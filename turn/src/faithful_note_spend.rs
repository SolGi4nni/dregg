//! Versioned carrier for a `NoteSpend` proof against historical faithful note-root state.
//!
//! The carrier is deliberately independent of [`crate::action::Effect`]. It can be placed in
//! the existing opaque `NoteSpend::spending_proof` bytes without changing the effect schema or
//! executor dispatch. The inner proof remains opaque here; this module only binds it to the
//! historical root height that a verifier must resolve.

use core::fmt;

/// Domain tag at the start of every faithful note-spend proof carrier.
pub const FAITHFUL_NOTE_SPEND_MAGIC: [u8; 4] = *b"FNSP";

/// Wire version emitted and accepted by this module.
pub const FAITHFUL_NOTE_SPEND_VERSION: u8 = 1;

/// Maximum accepted size of the opaque inner proof (4 MiB).
///
/// IR-v2 batch proofs may legitimately exceed a few hundred KiB.  This keeps a
/// strict hostile-allocation ceiling without excluding the existing prover's
/// larger note-spend instances.
pub const MAX_INNER_PROOF_BYTES: usize = 4 * 1024 * 1024;

const RESERVED_LEN: usize = 3;
const PROOF_LEN_LEN: usize = size_of::<u32>();

/// Number of bytes before the opaque inner proof.
pub const FAITHFUL_NOTE_SPEND_HEADER_LEN: usize = FAITHFUL_NOTE_SPEND_MAGIC.len()
    + size_of::<u8>()
    + RESERVED_LEN
    + size_of::<u64>()
    + PROOF_LEN_LEN;

const VERSION_OFFSET: usize = FAITHFUL_NOTE_SPEND_MAGIC.len();
const RESERVED_OFFSET: usize = VERSION_OFFSET + size_of::<u8>();
const ROOT_HEIGHT_OFFSET: usize = RESERVED_OFFSET + RESERVED_LEN;
const PROOF_LEN_OFFSET: usize = ROOT_HEIGHT_OFFSET + size_of::<u64>();

/// A validated proof carrier tied to one historical faithful note-root height.
///
/// Wire layout (all integers little-endian):
///
/// ```text
/// "FNSP" || version:u8 || reserved:[0;3] || root_height:u64
///        || inner_proof_len:u32 || inner_proof_bytes
/// ```
///
/// `inner_proof_bytes` is always non-empty and no larger than
/// [`MAX_INNER_PROOF_BYTES`]. Decoding consumes the entire input; trailing bytes
/// are never ignored.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaithfulNoteSpendProofCarrier {
    root_height: u64,
    inner_proof_bytes: Vec<u8>,
}

impl FaithfulNoteSpendProofCarrier {
    /// Construct a carrier after enforcing the inner-proof size invariant.
    pub fn new(
        root_height: u64,
        inner_proof_bytes: Vec<u8>,
    ) -> Result<Self, FaithfulNoteSpendCarrierError> {
        validate_proof_len(inner_proof_bytes.len())?;
        Ok(Self {
            root_height,
            inner_proof_bytes,
        })
    }

    /// Historical faithful note-root height against which the proof was made.
    pub const fn root_height(&self) -> u64 {
        self.root_height
    }

    /// Opaque proof understood by the note-spend verifier.
    pub fn inner_proof_bytes(&self) -> &[u8] {
        &self.inner_proof_bytes
    }

    /// Consume the carrier and return its opaque inner proof.
    pub fn into_inner_proof_bytes(self) -> Vec<u8> {
        self.inner_proof_bytes
    }

    /// Encode the canonical v1 wire form.
    pub fn encode(&self) -> Vec<u8> {
        let proof_len = u32::try_from(self.inner_proof_bytes.len())
            .expect("validated faithful note-spend proof length fits u32");
        let mut out = Vec::with_capacity(FAITHFUL_NOTE_SPEND_HEADER_LEN + proof_len as usize);
        out.extend_from_slice(&FAITHFUL_NOTE_SPEND_MAGIC);
        out.push(FAITHFUL_NOTE_SPEND_VERSION);
        out.extend_from_slice(&[0; RESERVED_LEN]);
        out.extend_from_slice(&self.root_height.to_le_bytes());
        out.extend_from_slice(&proof_len.to_le_bytes());
        out.extend_from_slice(&self.inner_proof_bytes);
        out
    }

    /// Decode one canonical v1 carrier, rejecting malformed or non-canonical input.
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
            bytes[FAITHFUL_NOTE_SPEND_HEADER_LEN..].to_vec(),
        )
    }
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
        FaithfulNoteSpendProofCarrier::new(42, vec![0xde, 0xad, 0xbe, 0xef]).expect("valid carrier")
    }

    #[test]
    fn carrier_round_trips_canonical_v1_bytes() {
        let carrier = sample();
        let encoded = carrier.encode();

        assert_eq!(&encoded[..4], b"FNSP");
        assert_eq!(encoded[VERSION_OFFSET], 1);
        assert_eq!(
            &encoded[RESERVED_OFFSET..ROOT_HEIGHT_OFFSET],
            &[0; RESERVED_LEN]
        );
        assert_eq!(
            &encoded[ROOT_HEIGHT_OFFSET..PROOF_LEN_OFFSET],
            &42u64.to_le_bytes()
        );
        assert_eq!(FaithfulNoteSpendProofCarrier::decode(&encoded), Ok(carrier));
    }

    #[test]
    fn construction_rejects_empty_and_oversized_proofs() {
        assert_eq!(
            FaithfulNoteSpendProofCarrier::new(0, Vec::new()),
            Err(FaithfulNoteSpendCarrierError::EmptyProof)
        );
        assert_eq!(
            FaithfulNoteSpendProofCarrier::new(0, vec![0; MAX_INNER_PROOF_BYTES + 1]),
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

        let mut unknown_version = sample().encode();
        unknown_version[VERSION_OFFSET] = FAITHFUL_NOTE_SPEND_VERSION + 1;
        assert_eq!(
            FaithfulNoteSpendProofCarrier::decode(&unknown_version),
            Err(FaithfulNoteSpendCarrierError::UnsupportedVersion(2))
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
}
